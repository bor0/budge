#!/usr/bin/env python3
"""Translate a pure Prolog program and its queries into Budge-TP.

    python3 prolog2btp.py prog.pl [--query GOAL] [--all] [--max-steps N] | python3 budge-tp.py

Each clause  H :- B1, ..., Bn.  becomes a rule  B1 -> ... -> Bn -> H  (a fact
has no hypotheses). Terms are written in full, f(a, [X|T]) as F(A,[x|t]), so
substituting text is substituting terms; clause variables become lowercase
letters, atoms uppercase. Budge-TP has no search and no unification, so the
queries ( ?- G.  in the file, or --query) are run here, by SLD resolution
(depth first, with the occurs check), and each answer's proof tree is
written out: one theorem per resolution step, naming the clause and the
value of each of its variables. Budge-TP checks every step; this file is
only the search, and need not be trusted.

Control has no logical content and is dropped from the rules: ! (cut) only
prunes the search, so a proof found with it is still a proof from the
clauses read as implications; true is dropped; X = Y stays as =(x,y),
proved by rEq : =(x,x). Unbound variables left in an answer become letters
(α, β, ...): the theorem holds for every value of them.

Arithmetic: is/2 and < > =< >= =:= =\\= over + - * / // mod and exp. A
number is a numeral with at most four decimals (0.5, -12); * / and exp cut
their results to four. When a program uses them, built-in rules ($-named,
checked like the rest) do the arithmetic on digit strings from digit tables
and a table of e^x; see the arithmetic section below.

Not supported (an error): negation (\\+), disjunction, if-then-else, other
built-ins, assert/retract, op/3, DCG (-->), strings.
"""
import re
import sys
import unicodedata
from decimal import Decimal, ROUND_DOWN, localcontext

# ---------------------------------------------------------------- terms

class Var:
    __slots__ = ('name', 'ref')

    def __init__(self, name):
        self.name, self.ref = name, None


def atom(name):
    return (name, ())


NIL = atom('[]')


def cons(h, t):
    return ('[|]', (h, t))


def deref(t):
    while isinstance(t, Var) and t.ref is not None:
        t = t.ref
    return t


# ---------------------------------------------------------------- reading

INFIX = {':-': (1200, 'xfx'), '-->': (1200, 'xfx'), ';': (1100, 'xfy'), '|': (1100, 'xfy'),
         '->': (1050, 'xfy'), ',': (1000, 'xfy'),
         '=': (700, 'xfx'), '\\=': (700, 'xfx'), '==': (700, 'xfx'), '\\==': (700, 'xfx'),
         'is': (700, 'xfx'), '<': (700, 'xfx'), '>': (700, 'xfx'), '=<': (700, 'xfx'),
         '>=': (700, 'xfx'), '=:=': (700, 'xfx'), '=\\=': (700, 'xfx'), '=..': (700, 'xfx'),
         '+': (500, 'yfx'), '-': (500, 'yfx'), '*': (400, 'yfx'), '/': (400, 'yfx'),
         '//': (400, 'yfx'), 'mod': (400, 'yfx'), '**': (200, 'xfx'), '^': (200, 'xfy')}
PREFIX = {':-': (1200, 'fx'), '?-': (1200, 'fx'), '\\+': (900, 'fy'), '-': (200, 'fy')}

TOKEN = re.compile(r"""
    (?P<space>\s+|%[^\n]*|/\*.*?\*/)
  | (?P<end>\.(?=\s|%|$))
  | (?P<var>[A-Z_][A-Za-z0-9_]*)
  | (?P<name>[a-z][A-Za-z0-9_]*)
  | (?P<num>\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)
  | (?P<quoted>'(?:[^'\\]|\\.|'')*')
  | (?P<punct>[()\[\],|])
  | (?P<solo>[!;])
  | (?P<sym>[+\-*/\\^<>=~:.?@#&$]+)
""", re.X | re.S)


def tokenize(text):
    """(kind, text, glued): glued says no space came before (f( vs f ()"""
    out, i, glued = [], 0, False
    while i < len(text):
        m = TOKEN.match(text, i)
        if not m:
            raise SyntaxError(f"Unexpected {text[i:i + 20]!r}")
        kind = m.lastgroup
        if kind == 'space':
            glued = False
        else:
            word = m.group()
            if kind == 'quoted':
                word, kind = word[1:-1].replace("''", "'"), 'name'
            elif kind in ('num', 'sym', 'solo'):
                kind = 'num' if kind == 'num' else 'name'
            out.append((kind, word, glued))
            glued = True
        i = m.end()
    return out


class Reader:
    """Prolog terms by operator precedence; variables named per clause"""
    def __init__(self, text):
        self.toks, self.i = tokenize(text), 0

    def peek(self, k=0):
        return self.toks[self.i + k] if self.i + k < len(self.toks) else ('eof', '', False)

    def take(self, word=None):
        tok = self.peek()
        if word is not None and tok[1] != word:
            raise SyntaxError(f"Expected {word!r}, got {tok[1]!r}")
        self.i += 1
        return tok

    def clauses(self):
        while self.peek()[0] != 'eof':
            self.vars = {}
            term = self.term(1200)
            if self.take()[0] != 'end':
                raise SyntaxError(f"Expected '.' after {show(term)}")
            yield term, dict(self.vars)

    def var(self, name):
        if name == '_':
            return Var('_')
        return self.vars.setdefault(name, Var(name))

    def starts_term(self):
        kind, word, _ = self.peek()
        return kind in ('var', 'num') or (kind == 'name' and word not in INFIX) or word in '([' and word

    def term(self, maxp):
        left, lp = self.primary(maxp)
        while True:
            kind, word, _ = self.peek()
            if kind != 'name' and word not in (',', '|') or word not in INFIX:
                return left
            p, typ = INFIX[word]
            la = p - 1 if typ[0] == 'x' else p
            if p > maxp or lp > la:
                return left
            self.take()
            right = self.term(p - 1 if typ[2] == 'x' else p)
            left, lp = ((';' if word == '|' else word), (left, right)), p

    def primary(self, maxp):
        kind, word, _ = self.take()
        if kind == 'var':
            return self.var(word), 0
        if kind == 'num':
            return atom(canon(word)), 0
        if word == '(':
            t = self.term(1200)
            self.take(')')
            return t, 0
        if word == '[':
            if self.peek()[1] == ']':
                self.take()
                return self.after_name('[]', maxp)
            items = [self.term(999)]
            while self.peek()[1] == ',':
                self.take()
                items.append(self.term(999))
            tail = NIL
            if self.peek()[1] == '|':
                self.take()
                tail = self.term(999)
            self.take(']')
            for item in reversed(items):
                tail = cons(item, tail)
            return tail, 0
        if kind != 'name':
            raise SyntaxError(f"Unexpected {word!r}")
        return self.after_name(word, maxp)

    def after_name(self, name, maxp):
        nxt = self.peek()
        if nxt[1] == '(' and nxt[2]:            # f(...): a compound
            self.take()
            args = [self.term(999)]
            while self.peek()[1] == ',':
                self.take()
                args.append(self.term(999))
            self.take(')')
            return (name, tuple(args)), 0
        if name == '-' and nxt[0] == 'num' and nxt[2]:
            self.take()
            return atom(canon('-' + nxt[1])), 0
        if name in PREFIX and self.starts_term():
            p, typ = PREFIX[name]
            if p > maxp:
                p = 999
            return (name, (self.term(p - 1 if typ == 'fx' else p),)), p
        return atom(name), (1201 if name in INFIX or name in PREFIX else 0)


def show(t, names=None):
    """A term in Prolog syntax (lists as [a,b|T], operators infix); names
    {Var: text} names unbound variables, else their source names"""
    t = deref(t)
    if isinstance(t, Var):
        return (names or {}).get(t) or (t.name if t.name != '_' else '_')
    name, args = t
    if name == '[|]':
        items = []
        while isinstance(t, tuple) and t[0] == '[|]':
            items.append(show(t[1][0], names))
            t = deref(t[1][1])
        tail = '' if t == NIL else '|' + show(t, names)
        return '[' + ','.join(items) + tail + ']'
    if not args:
        if re.fullmatch(r'[a-z][A-Za-z0-9_]*|\[\]|[+\-*/\\^<>=~:.?@#&$]+|-?\d+(\.\d+)?|!|;', name):
            return name
        return "'" + name.replace("'", "''") + "'"
    if len(args) == 2 and name in INFIX:
        sep = ', ' if name == ',' else f' {name} '
        return show(args[0], names) + sep + show(args[1], names)
    return f"{show(atom(name))}({','.join(show(a, names) for a in args)})"


# ---------------------------------------------------------------- the engine

class Clause:
    def __init__(self, head, body, names):
        self.head, self.body, self.names = head, body, names
        self.index = arg_keys(head)


def arg_keys(t):
    """Each argument's functor (name, arity), None for a variable: a clause whose
    head clashes with the goal here can't unify, so it is skipped without renaming"""
    return tuple(None if isinstance(a, Var) else (a[0], len(a[1])) for a in map(deref, t[1]))


def clashes(index, keys):
    return any(c is not None and g is not None and c != g for c, g in zip(index, keys))


def conjuncts(t):
    t = deref(t)
    if isinstance(t, tuple) and t[0] == ',' and len(t[1]) == 2:
        return conjuncts(t[1][0]) + conjuncts(t[1][1])
    return [t]


def rename(t, fresh):
    t = deref(t)
    if isinstance(t, Var):
        if t not in fresh:
            fresh[t] = Var(t.name)
        return fresh[t]
    return (t[0], tuple(rename(a, fresh) for a in t[1])) if t[1] else t


def occurs(v, t):
    t = deref(t)
    if t is v:
        return True
    return isinstance(t, tuple) and any(occurs(v, a) for a in t[1])


def unify(a, b, trail):
    a, b = deref(a), deref(b)
    if a is b:
        return True
    if isinstance(a, Var) or isinstance(b, Var):
        v, t = (a, b) if isinstance(a, Var) else (b, a)
        if occurs(v, t):
            return False
        v.ref = t
        trail.append(v)
        return True
    if a[0] != b[0] or len(a[1]) != len(b[1]):
        return False
    return all(unify(x, y, trail) for x, y in zip(a[1], b[1]))


CONTROL = {('true', 0), ('!', 0), ('fail', 0), ('false', 0)}
UNSUPPORTED = {(';', 2), ('->', 2), ('\\+', 1), ('\\=', 2), ('==', 2), ('\\==', 2), ('=..', 2), ('call', 1),
               ('assert', 1), ('asserta', 1), ('assertz', 1), ('retract', 1), ('findall', 3),
               ('functor', 3), ('arg', 3), ('var', 1), ('nonvar', 1), ('atom', 1), ('number', 1),
               ('write', 1), ('nl', 0)}


def key(goal):
    return goal[0], len(goal[1])


class Engine:
    """Depth-first SLD resolution; a proof is (rule name, {variable: term}, children)"""
    def __init__(self, program, max_steps):
        self.program, self.steps, self.max_steps = program, 0, max_steps

    def solve(self, goal):
        goal = deref(goal)
        if isinstance(goal, Var):
            raise ValueError("A variable as a goal (call/1) is not supported")
        k = key(goal)
        if k == ('=', 2):
            trail = []
            if unify(goal[1][0], goal[1][1], trail):
                yield ('rEq', {'x': goal[1][0]}, [])
            undo(trail)
            return
        if k in ARITH:
            self.steps += 1
            yield from arith_goal(goal)
            return
        if k in UNSUPPORTED:
            raise ValueError(f"Not supported: {k[0]}/{k[1]}")
        if k not in self.program:
            raise ValueError(f"Unknown procedure: {k[0]}/{k[1]}")
        keys = arg_keys(goal)
        for rule, clause in self.program[k]:
            if clashes(clause.index, keys):
                continue
            self.steps += 1
            if self.steps > self.max_steps:
                raise RuntimeError(f"No answer within {self.max_steps} steps (--max-steps)")
            fresh = {}
            head, body = rename(clause.head, fresh), [rename(g, fresh) for g in clause.body]
            frame, trail = {'cut': False}, []
            if unify(head, goal, trail):
                for kids in self.conj(body, frame):
                    yield (rule, {name: fresh.get(v, v) for name, v in clause.names.items()}, kids)
            undo(trail)
            if frame['cut']:
                return

    def conj(self, goals, frame):
        """Proofs of the goals in turn; ! cuts the clause that frame belongs to"""
        if not goals:
            yield []
            return
        goal, rest = deref(goals[0]), goals[1:]
        k = key(goal) if isinstance(goal, tuple) else None
        if k in (('fail', 0), ('false', 0)):
            return
        if k in (('true', 0), ('!', 0)):
            yield from self.conj(rest, frame)
            if k == ('!', 0):
                frame['cut'] = True
            return
        for proof in self.solve(goal):
            for kids in self.conj(rest, frame):
                yield [proof] + kids
            if frame['cut']:
                return


def undo(trail):
    for v in trail:
        v.ref = None


# ---------------------------------------------------------------- arithmetic
#
# A number is an atom whose name is a numeral: 7, -12, 0.5, -0.0097. One type,
# PLACES decimals; sums are exact, and * / exp cut their results toward zero.
# The checked rules (prelude) work on digit strings: a numeral a stands for the
# integer a * 10^PLACES, its scaled form ($SC: 0.5 for 05000), and +, *, < on
# those are column by column from digit tables, carries passed up through the
# string. A quotient q = x / y is checked, not searched for: q y + r = x, r < y.
# exp(x) multiplies a table entry e^(d 10^j) for each digit d of x (|x| < 100),
# and e^-x is 1 / e^x. Those 60 constants (rounded) and the digit tables are
# the only facts. The proofs below are built directly; this code is not trusted.

PLACES = 4
SCALE = 10 ** PLACES
NUMERAL = re.compile(r'-?\d+(\.\d+)?')
ARITH = {('is', 2), ('<', 2), ('>', 2), ('=<', 2), ('>=', 2), ('=:=', 2), ('=\\=', 2)}
EXP_POSITIONS = range(-PLACES, 2)       # digit j of x stands for d 10^j


def scaled(text):
    """A numeral as an integer times SCALE, cut toward zero"""
    return int((Decimal(text) * SCALE).to_integral_value(rounding=ROUND_DOWN))


def numeral(v):
    """The canonical numeral of v / SCALE: 3, 0.5, -12.0097"""
    i, f = divmod(abs(v), SCALE)
    s = str(i) + (f'.{f:0{PLACES}d}'.rstrip('0') if f else '')
    return '-' + s if v < 0 else s


def canon(text):
    """A number literal as its numeral: 007 -> 7, 0.50 -> 0.5, 2.71828 -> 2.7182"""
    return numeral(scaled(text))


def exp_table():
    with localcontext() as ctx:
        ctx.prec = 80
        return {(d, j): numeral(int((Decimal(d * 10 ** (j + PLACES)) / SCALE).exp() * SCALE
                                    + Decimal('0.5')))
                for d in range(10) for j in EXP_POSITIONS}


EXP_TABLE = exp_table()


def pos(j):
    return f'm{-j}' if j < 0 else str(j)


def nd(rule, kids, **values):
    """A proof step; string values are numerals or digit strings (atoms)"""
    return (rule, {k: atom(v) if isinstance(v, str) else v for k, v in values.items()}, list(kids))


def mag(x):
    return x.startswith('-'), x.lstrip('-')


# Naturals: digit strings, leading zeros allowed

def f_sum(a, b, k):
    s = a + b + k
    return nd(f'rSum{a}{b}{k}', []), s % 10, s // 10


def f_prod(a, b):
    return nd(f'rProd{a}{b}', []), a * b // 10, a * b % 10


def f_dig(d):
    return nd(f'rDig{d}', [])


def addc(x, y, k):
    """$ADDC(x,y,k,z,j): x + y + k = z + j 10^n, all n digits; returns (proof, z, j)"""
    f, c, i = f_sum(int(x[-1]), int(y[-1]), k)
    if len(x) == 1:
        return nd('rAddc1', [f], a=x, b=y, k=str(k), c=str(c), j=str(i)), str(c), i
    p, z, j = addc(x[:-1], y[:-1], i)
    return (nd('rAddcS', [f, p], a=x[-1], b=y[-1], k=str(k), c=str(c), i=str(i),
               x=x[:-1], y=y[:-1], z=z, j=str(j)), z + str(c), j)


def fit(p, strip, pad, values, s, target):
    """Drop or add leading zeros of a result s until it reads target"""
    target = target if target is not None else s.lstrip('0') or '0'
    while len(s) > len(target):
        s = s[1:]
        p = nd(strip, [p], z=s, **values)
    while len(s) < len(target):
        p = nd(pad, [p], z=s, **values)
        s = '0' + s
    return p, s


def nadd(x, y, z=None):
    """$NADD(x,y,z): x + y = z; returns (proof, z)"""
    n = max(len(x), len(y))
    px, py = x.rjust(n, '0'), y.rjust(n, '0')
    p, s, j = addc(px, py, 0)
    p = nd('rNaddC' if j else 'rNadd', [p], x=px, y=py, z=s)
    s = '1' + s if j else s
    while px != x:
        px = px[1:]
        p = nd('rNaddL', [p], x=px, y=py, z=s)
    while py != y:
        py = py[1:]
        p = nd('rNaddR', [p], x=x, y=py, z=s)
    return fit(p, 'rNaddZ', 'rNaddP', {'x': x, 'y': y}, s, z)


def muld(x, d, k):
    """$MULD(x,d,k,z,j): x d + k = z + j 10^n; returns (proof, z, j)"""
    fp, h, l = f_prod(int(x[-1]), d)
    f1, c, i = f_sum(l, k, 0)
    f2, m, _ = f_sum(h, i, 0)
    v = dict(d=str(d), h=str(h), l=str(l), k=str(k), c=str(c), i=str(i))
    if len(x) == 1:
        return nd('rMuld1', [fp, f1, f2], a=x, j=str(m), **v), str(c), m
    p, z, j = muld(x[:-1], d, m)
    return nd('rMuldS', [fp, f1, f2, p], a=x[-1], m=str(m), x=x[:-1], z=z, j=str(j), **v), z + str(c), j


def nmul(x, y, z=None):
    """$NMUL(x,y,z): x y = z, one row per digit of y; returns (proof, z)"""
    def rows(y):
        d = int(y[-1])
        m, q, j = muld(x, d, 0)
        if len(y) == 1:
            return nd('rNmul1', [m], x=x, d=str(d), z=q, j=str(j)), str(j) + q
        p, s = rows(y[:-1])
        a, r = nadd(s + '0', str(j) + q)
        return nd('rNmulS', [p, m, a], x=x, y=y[:-1], p=s, d=str(d), q=q, j=str(j), z=r), r
    p, s = rows(y)
    return fit(p, 'rNmulZ', 'rNmulP', {'x': x, 'y': y}, s, z)


def nlt(x, y):
    """$NLT(x,y): x < y, as x + d + 1 = y"""
    d, c = str(int(y) - int(x) - 1), str(int(y) - 1)
    return nd('rNlt', [nadd(x, d, c)[0], nadd(c, '1', y)[0]], x=x, y=y, d=d, c=c)


def ndiv(x, y, q=None):
    """$NDIV(x,y,q,r): x = q y + r and r < y; returns (proof, r)"""
    qv, rv = divmod(int(x), int(y))
    q, r = q or str(qv), str(rv)
    m, p = nmul(q, y)
    return nd('rNdiv', [m, nadd(p, r, x)[0], nlt(r, y)], x=x, y=y, q=q, r=r, p=p), r


# Integers (scaled numerals): digit strings with an optional -

def iadd(x, y, z):
    """$IADD(x,y,z): x + y = z, z as wanted"""
    (nx, x), (ny, y), (nz, z) = mag(x), mag(y), mag(z)
    if nx == ny:
        return nd('rIaddNN' if nx else 'rIaddPP', [nadd(x, y, z)[0]], x=x, y=y, z=z)
    if ny:      # x - y
        rule, p = ('rIaddPN2', nadd(x, z, y)) if nz else ('rIaddPN', nadd(y, z, x))
    else:       # y - x
        rule, p = ('rIaddNP2', nadd(y, z, x)) if nz else ('rIaddNP', nadd(x, z, y))
    return nd(rule, [p[0]], x=x, y=y, z=z)


def ilt(x, y):
    """$ILT(x,y): x < y"""
    (nx, x), (ny, y) = mag(x), mag(y)
    if not nx and not ny:
        return nd('rIltPP', [nlt(x, y)], x=x, y=y)
    if nx and ny:
        return nd('rIltNN', [nlt(y, x)], x=x, y=y)
    s = str(int(x) + int(y))
    return nd('rIltNP', [nadd(x, y, s)[0], nlt('0', s)], x=x, y=y, s=s)


# Numerals

def sc(a):
    """$SC(a,s): numeral a is the integer s / SCALE; returns (proof, s)"""
    if a.startswith('-'):
        p, s = sc(a[1:])
        return nd('rScN', [p], t=a[1:], s=s), '-' + s
    if '.' not in a:
        return nd('rScI', [], x=a), a + '0' * PLACES
    x, f = a.split('.')
    return (nd(f'rScD{len(f)}', [f_dig(int(c)) for c in f], x=x, **dict(zip('abcd', f))),
            x + f + '0' * (PLACES - len(f)))


def nat(x):
    if len(x) == 1:
        return nd('rNat1', [f_dig(int(x))], a=x)
    return nd('rNatS', [nat(x[:-1]), f_dig(int(x[-1]))], x=x[:-1], a=x[-1])


def num(a):
    neg, m = mag(a)
    if '.' in m:
        x, f = m.split('.')
        return nd('rNumDN' if neg else 'rNumD', [nat(x), nat(f)], x=x, f=f)
    return nd('rNumIN' if neg else 'rNumI', [nat(m)], x=m)


def a_add(a, b):
    c = numeral(scaled(a) + scaled(b))
    (pa, x), (pb, y), (pc, z) = sc(a), sc(b), sc(c)
    return nd('rAdd', [pa, pb, iadd(x, y, z), pc], a=a, b=b, c=c, x=x, y=y, z=z), c


def a_sub(a, b):
    c = numeral(scaled(a) - scaled(b))
    return nd('rSub', [a_add(b, c)[0]], a=a, b=b, c=c), c


def signs(rule, op, a, b):
    """op on the magnitudes, then the sign: -0 is left for rEvZero"""
    (na, a), (nb, b) = mag(a), mag(b)
    p, c = op(a, b)
    if not na and not nb:
        return p, c
    return nd(rule + ('NN' if na and nb else 'NP' if na else 'PN'), [p], a=a, b=b, c=c), \
        c if na == nb else '-' + c


def mul(a, b):
    def unsigned(a, b):
        prod = scaled(a) * scaled(b)
        c = numeral(prod // SCALE)
        (pa, x), (pb, y), (pc, z) = sc(a), sc(b), sc(c)
        r = f'{prod % SCALE:0{PLACES}d}'
        return nd('rMul', [pa, pb, nmul(x, y, z + r)[0]] + [f_dig(int(ch)) for ch in r] + [pc],
                  a=a, b=b, c=c, x=x, y=y, z=z, **dict(zip('defg', r))), c
    return signs('rMul', unsigned, a, b)


def div(a, b):
    def unsigned(a, b):
        if scaled(b) == 0:
            raise ValueError('Arithmetic: division by zero')
        c = numeral(scaled(a) * SCALE // scaled(b))
        (pa, x), (pb, y), (pc, q) = sc(a), sc(b), sc(c)
        p, r = ndiv(x + '0' * PLACES, y, q)
        return nd('rDiv', [pa, pb, p, pc], a=a, b=b, c=c, x=x, y=y, q=q, r=r), c
    return signs('rDiv', unsigned, a, b)


def integers(a, b, op):
    if '.' in a or '.' in b:
        raise ValueError(f'Arithmetic: {op} needs integers, not {a} and {b}')
    if int(b) == 0:
        raise ValueError('Arithmetic: division by zero')


def idiv(a, b):
    integers(a, b, '//')

    def unsigned(a, b):
        p, r = ndiv(a, b)
        q = str(int(a) // int(b))
        return nd('rIdiv', [p], a=a, b=b, q=q, r=r), q
    return signs('rIdiv', unsigned, a, b)


def mod(a, b):
    """a mod b, with the sign of b (floored, as in Prolog)"""
    integers(a, b, 'mod')
    (na, ma), (nb, mb) = mag(a), mag(b)
    if nb:
        p, c = mod(ma if na else '-' + ma, mb)
        return nd('rModNN' if na else 'rModPN', [p], a=ma, b=mb, c=c), '-' + c
    p, r = ndiv(ma, mb)
    q = str(int(ma) // int(mb))
    if not na:
        return nd('rMod', [p], a=ma, b=mb, q=q, r=r), r
    if r == '0':
        return nd('rModNP0', [p], a=ma, b=mb, q=q), '0'
    c = str(int(mb) - int(r))
    return nd('rModNP', [p, nlt('0', r), nadd(r, c, mb)[0]], a=ma, b=mb, q=q, r=r, c=c), c


def expn(a):
    """e^a, digit by digit"""
    if a.startswith('-'):
        p, b = expn(a[1:])
        q, c = div('1', b)
        return nd('rExpN', [p, q], a=a[1:], b=b, c=c), c
    pa, s = sc(a)
    if len(s) > len(EXP_POSITIONS):
        raise ValueError(f'Arithmetic: exp({a}) is too large (only |x| < 100)')

    def digits(s, j):
        d = int(s[-1])
        et, q = nd(f'rEt{d}{pos(j)}', []), EXP_TABLE[d, j]
        if len(s) == 1:
            return nd('rExpJ1', [et], d=str(d), j=str(j), c=q), q
        p, v = digits(s[:-1], j + 1)
        m, c = mul(v, q)
        return (nd('rExpJS', [p, nd(f'rNext{pos(j)}', []), et, m], t=s[:-1], k=str(j + 1), p=v,
                   j=str(j), d=str(d), q=q, c=c), c)
    p, c = digits(s, -PLACES)
    return nd('rExp', [pa, p], a=a, s=s, c=c), c


def neg(a):
    return a_sub('0', a)


BINARY = {'+': ('rEvAdd', a_add), '-': ('rEvSub', a_sub), '*': ('rEvMul', mul),
          '/': ('rEvDiv', div), '//': ('rEvIdiv', idiv), 'mod': ('rEvMod', mod)}
UNARY = {'-': ('rEvNeg', neg), 'exp': ('rEvExp', expn)}


def evaluate(t):
    """$EVAL(t,a): the expression t has the value a; returns (proof, a)"""
    t = deref(t)
    if isinstance(t, Var):
        raise ValueError('Arithmetic: arguments are not sufficiently instantiated')
    name, args = t
    if not args:
        if not NUMERAL.fullmatch(name):
            raise ValueError(f'Arithmetic: {show(t)} is not a number')
        return nd('rEvNum', [num(name)], a=name), name
    if len(args) == 2 and name in BINARY:
        rule, op = BINARY[name]
        (pe, a), (pf, b) = evaluate(args[0]), evaluate(args[1])
        po, c = op(a, b)
        p = nd(rule, [pe, pf, po], e=args[0], f=args[1], a=a, b=b, c=c)
    elif len(args) == 1 and name in UNARY:
        rule, op = UNARY[name]
        pe, a = evaluate(args[0])
        po, c = op(a)
        p = nd(rule, [pe, po], e=args[0], a=a, b=c)
    else:
        raise ValueError(f'Arithmetic: unknown function {name}/{len(args)}')
    if c == '-0':
        p, c = nd('rEvZero', [p], e=t), '0'
    return p, c


def lt(a, b):
    (pa, x), (pb, y) = sc(a), sc(b)
    return nd('rLtN', [pa, pb, ilt(x, y)], a=a, b=b, x=x, y=y)


def le(a, b):
    return nd('rLeEq', [], a=a) if a == b else nd('rLeLt', [lt(a, b)], a=a, b=b)


def compare(name, l, r):
    """A proof of the comparison, or None when it is false"""
    (pl, a), (pr, b) = evaluate(l), evaluate(r)
    va, vb = scaled(a), scaled(b)
    v = dict(e=l, f=r, a=a, b=b)
    if name == '=:=':
        return nd('rEqA', [pl, pr], e=l, f=r, a=a) if va == vb else None
    if name == '=\\=':
        return None if va == vb else \
            nd('rNe1', [pl, pr, lt(a, b)], **v) if va < vb else nd('rNe2', [pl, pr, lt(b, a)], **v)
    holds, rule, fact = {'<': (va < vb, 'rLt', lambda: lt(a, b)), '>': (va > vb, 'rGt', lambda: lt(b, a)),
                         '=<': (va <= vb, 'rLe', lambda: le(a, b)),
                         '>=': (va >= vb, 'rGe', lambda: le(b, a))}[name]
    return nd(rule, [pl, pr, fact()], **v) if holds else None


ARITH_RELATIONS = ['$DIG', '$SUM', '$PROD', '$ADDC', '$NADD', '$MULD', '$NMUL', '$NLT', '$NDIV',
                   '$IADD', '$ILT', '$SC', '$NAT', '$NUM', '$ADD', '$SUB', '$MUL', '$DIV', '$IDIV',
                   '$MODN', '$ET', '$NEXT', '$EXPJ', '$EXPN', '$EVAL', '$LT', '$LE']


def prelude(w):
    """The arithmetic rules, with the program's own texts for is, +, <, ..."""
    op = {name: w.atom(name) for name in ['is', '+', '-', '*', '/', '//', 'mod', 'exp',
                                          '<', '>', '=<', '>=', '=:=', '=\\=']}
    dg = 'defg'[:PLACES]
    z = '0' * PLACES
    lines = ['# Arithmetic, built in: digit tables, then +, * and < column by column on digit strings,',
             f'# numerals as integers times 10^{PLACES} ($SC), and expressions ($EVAL). Facts: the',
             '# tables and e^(d 10^j) rounded; prolog2btp.py builds the proofs and is not trusted.']
    lines += [f'rDig{d} : $DIG({d})' for d in range(10)]
    lines += [f'rSum{a}{b}{k} : $SUM({a},{b},{k},{(a + b + k) % 10},{(a + b + k) // 10})'
              for k in (0, 1) for a in range(10) for b in range(10)]
    lines += [f'rProd{a}{b} : $PROD({a},{b},{a * b // 10},{a * b % 10})' for a in range(10) for b in range(10)]
    lines += [
        'rAddc1 : $SUM(a,b,k,c,j) -> $ADDC(a,b,k,c,j)',
        'rAddcS : $SUM(a,b,k,c,i) -> $ADDC(x,y,i,z,j) -> $ADDC(xa,yb,k,zc,j)',
        'rNadd : $ADDC(x,y,0,z,0) -> $NADD(x,y,z)',
        'rNaddC : $ADDC(x,y,0,z,1) -> $NADD(x,y,1z)',
        'rNaddL : $NADD(0x,y,z) -> $NADD(x,y,z)',
        'rNaddR : $NADD(x,0y,z) -> $NADD(x,y,z)',
        'rNaddZ : $NADD(x,y,0z) -> $NADD(x,y,z)',
        'rNaddP : $NADD(x,y,z) -> $NADD(x,y,0z)',
        'rMuld1 : $PROD(a,d,h,l) -> $SUM(l,k,0,c,i) -> $SUM(h,i,0,j,0) -> $MULD(a,d,k,c,j)',
        'rMuldS : $PROD(a,d,h,l) -> $SUM(l,k,0,c,i) -> $SUM(h,i,0,m,0) -> $MULD(x,d,m,z,j)'
        ' -> $MULD(xa,d,k,zc,j)',
        'rNmul1 : $MULD(x,d,0,z,j) -> $NMUL(x,d,jz)',
        'rNmulS : $NMUL(x,y,p) -> $MULD(x,d,0,q,j) -> $NADD(p0,jq,z) -> $NMUL(x,yd,z)',
        'rNmulZ : $NMUL(x,y,0z) -> $NMUL(x,y,z)',
        'rNmulP : $NMUL(x,y,z) -> $NMUL(x,y,0z)',
        'rNlt : $NADD(x,d,c) -> $NADD(c,1,y) -> $NLT(x,y)',
        'rNdiv : $NMUL(q,y,p) -> $NADD(p,r,x) -> $NLT(r,y) -> $NDIV(x,y,q,r)',
        'rIaddPP : $NADD(x,y,z) -> $IADD(x,y,z)',
        'rIaddNN : $NADD(x,y,z) -> $IADD(-x,-y,-z)',
        'rIaddPN : $NADD(y,z,x) -> $IADD(x,-y,z)',
        'rIaddPN2 : $NADD(x,z,y) -> $IADD(x,-y,-z)',
        'rIaddNP : $NADD(x,z,y) -> $IADD(-x,y,z)',
        'rIaddNP2 : $NADD(y,z,x) -> $IADD(-x,y,-z)',
        'rIltPP : $NLT(x,y) -> $ILT(x,y)',
        'rIltNP : $NADD(x,y,s) -> $NLT(0,s) -> $ILT(-x,y)',
        'rIltNN : $NLT(y,x) -> $ILT(-x,-y)',
        f'rScI : $SC(x,x{z})']
    for n in range(1, PLACES + 1):
        f = 'abcd'[:n]
        lines.append(f'rScD{n} : ' + ''.join(f'$DIG({c}) -> ' for c in f)
                     + f'$SC(x.{f},x{f}{"0" * (PLACES - n)})')
    lines += [
        'rScN : $SC(t,s) -> $SC(-t,-s)',
        'rNat1 : $DIG(a) -> $NAT(a)',
        'rNatS : $NAT(x) -> $DIG(a) -> $NAT(xa)',
        'rNumI : $NAT(x) -> $NUM(x)',
        'rNumIN : $NAT(x) -> $NUM(-x)',
        'rNumD : $NAT(x) -> $NAT(f) -> $NUM(x.f)',
        'rNumDN : $NAT(x) -> $NAT(f) -> $NUM(-x.f)',
        'rAdd : $SC(a,x) -> $SC(b,y) -> $IADD(x,y,z) -> $SC(c,z) -> $ADD(a,b,c)',
        'rSub : $ADD(b,c,a) -> $SUB(a,b,c)',
        'rMul : $SC(a,x) -> $SC(b,y) -> $NMUL(x,y,z' + dg + ') -> '
        + ''.join(f'$DIG({c}) -> ' for c in dg) + '$SC(c,z) -> $MUL(a,b,c)',
        f'rDiv : $SC(a,x) -> $SC(b,y) -> $NDIV(x{z},y,q,r) -> $SC(c,q) -> $DIV(a,b,c)',
        'rIdiv : $NDIV(a,b,q,r) -> $IDIV(a,b,q)']
    for rel, r in (('$MUL', 'rMul'), ('$DIV', 'rDiv'), ('$IDIV', 'rIdiv')):
        lines += [f'{r}NP : {rel}(a,b,c) -> {rel}(-a,b,-c)',
                  f'{r}PN : {rel}(a,b,c) -> {rel}(a,-b,-c)',
                  f'{r}NN : {rel}(a,b,c) -> {rel}(-a,-b,c)']
    lines += [
        'rMod : $NDIV(a,b,q,r) -> $MODN(a,b,r)',
        'rModNP : $NDIV(a,b,q,r) -> $NLT(0,r) -> $NADD(r,c,b) -> $MODN(-a,b,c)',
        'rModNP0 : $NDIV(a,b,q,0) -> $MODN(-a,b,0)',
        'rModPN : $MODN(-a,b,c) -> $MODN(a,-b,-c)',
        'rModNN : $MODN(a,b,c) -> $MODN(-a,-b,-c)']
    lines += [f'rEt{d}{pos(j)} : $ET({d},{j},{EXP_TABLE[d, j]})' for j in EXP_POSITIONS for d in range(10)]
    lines += [f'rNext{pos(j)} : $NEXT({j},{j + 1})' for j in EXP_POSITIONS[:-1]]
    lines += [
        'rExpJ1 : $ET(d,j,c) -> $EXPJ(d,j,c)',
        'rExpJS : $EXPJ(t,k,p) -> $NEXT(j,k) -> $ET(d,j,q) -> $MUL(p,q,c) -> $EXPJ(td,j,c)',
        f'rExp : $SC(a,s) -> $EXPJ(s,-{PLACES},c) -> $EXPN(a,c)',
        'rExpN : $EXPN(a,b) -> $DIV(1,b,c) -> $EXPN(-a,c)',
        'rEvNum : $NUM(a) -> $EVAL(a,a)',
        'rEvZero : $EVAL(e,-0) -> $EVAL(e,0)']
    for name, (rule, _) in BINARY.items():
        rel = {'+': '$ADD', '-': '$SUB', '*': '$MUL', '/': '$DIV', '//': '$IDIV', 'mod': '$MODN'}[name]
        lines.append(f'{rule} : $EVAL(e,a) -> $EVAL(f,b) -> {rel}(a,b,c) -> $EVAL({op[name]}(e,f),c)')
    lines += [f'rEvNeg : $EVAL(e,a) -> $SUB(0,a,b) -> $EVAL({op["-"]}(e),b)',
              f'rEvExp : $EVAL(e,a) -> $EXPN(a,b) -> $EVAL({op["exp"]}(e),b)',
              'rLtN : $SC(a,x) -> $SC(b,y) -> $ILT(x,y) -> $LT(a,b)',
              'rLeLt : $LT(a,b) -> $LE(a,b)',
              'rLeEq : $LE(a,a)',
              f'rIs : $EVAL(e,x) -> {op["is"]}(x,e)']
    two = '$EVAL(e,a) -> $EVAL(f,b) -> '
    ne = op['=\\=']     # named here: before Python 3.12 an f-string's braces can't hold a backslash
    lines += [f'rLt : {two}$LT(a,b) -> {op["<"]}(e,f)', f'rGt : {two}$LT(b,a) -> {op[">"]}(e,f)',
              f'rLe : {two}$LE(a,b) -> {op["=<"]}(e,f)', f'rGe : {two}$LE(b,a) -> {op[">="]}(e,f)',
              f'rEqA : $EVAL(e,a) -> $EVAL(f,a) -> {op["=:="]}(e,f)',
              f'rNe1 : {two}$LT(a,b) -> {ne}(e,f)', f'rNe2 : {two}$LT(b,a) -> {ne}(e,f)']
    return lines


def arith_goal(goal):
    """is/2 binds its result; a comparison has a proof or fails"""
    name, (l, r) = goal
    if name == 'is':
        p, a = evaluate(r)
        trail = []
        if unify(l, atom(a), trail):
            yield ('rIs', {'e': r, 'x': atom(a)}, [p])
        undo(trail)
        return
    p = compare(name, l, r)
    if p:
        yield p


# ---------------------------------------------------------------- writing

# Lowercase letters the same in every Python (see mm2btp.py); clause
# variables take ASCII first, answers' unbound variables Greek, so a value
# never contains a letter a rule substitutes.
RULE_LETTERS = 'abcdefghijklmnopqrstuvwxyz' + ''.join(
    chr(c) for c in range(0xdf, 0x250) if unicodedata.category(chr(c)) == 'Ll')
ANSWER_LETTERS = ''.join(chr(c) for a, b in ((0x3b1, 0x3ca), (0x430, 0x460), (0x1e00, 0x1f00))
                         for c in range(a, b) if unicodedata.category(chr(c)) == 'Ll')
RESERVED = {'[]'} | set(ARITH_RELATIONS)


class Writer:
    def __init__(self, out):
        self.out, self.atoms, self.taken = out, {}, set(RESERVED)
        self.terms, self.steps, self.n = {}, {}, 0

    def emit(self, line):
        print(line, file=self.out)

    def atom(self, name):
        """An atom as a token with no lowercase letter: append -> APPEND"""
        if name == '[]':
            return '[]'
        if name not in self.atoms:
            cand = name.upper()
            if (cand in self.taken or any(c.islower() or c.isspace() for c in cand)
                    or re.search(r"->|#|[()\[\],|']", cand) or not cand):
                cand = f'A{len(self.atoms)}'
                while cand in self.taken:
                    cand += "'"
                self.emit(f'# {cand} is the atom {show(atom(name))}')
            self.atoms[name] = cand
            self.taken.add(cand)
        return self.atoms[name]

    def text(self, t, letters):
        """A term in full: F(A,[x|[]]); variables by letters {Var: letter}"""
        t = deref(t)
        if isinstance(t, Var):
            if t not in letters:
                used = set(letters.values())
                letters[t] = next(c for c in ANSWER_LETTERS if c not in used)
            return letters[t]
        name, args = t
        if name == '[|]':
            return f'[{self.text(args[0], letters)}|{self.text(args[1], letters)}]'
        if not args:
            return self.atom(name)
        return f"{self.atom(name)}({','.join(self.text(a, letters) for a in args)})"

    def term(self, text):
        if text not in self.terms:
            k = len(self.terms)
            self.emit(f'rTm{k} : {text}')
            self.emit(f'tm{k}! : rTm{k}')
            self.terms[text] = f'tm{k}!'
        return self.terms[text]

    def step(self, body):
        if body not in self.steps:
            self.n += 1
            self.steps[body] = f't{self.n}!'
            self.emit(f'{self.steps[body]} : {body}')
        return self.steps[body]


def rule_letters(names):
    """Clause variable names -> letters: H -> h when free, else one nobody wants"""
    wanted = {n[0].lower() for n in names if n[0].isalpha()}
    out = {}
    for name in names:
        first = name[0].lower()
        if not (first.isascii() and first.isalpha()) or first in out.values():
            first = next(c for c in RULE_LETTERS if c not in out.values() and c not in wanted)
        out[name] = first
    return out


def clause_vars(terms):
    """The clause's variables in order, named; each _ gets its own name"""
    named = {}

    def walk(t):
        t = deref(t)
        if isinstance(t, Var):
            if t not in named.values():
                named[t.name if t.name != '_' else f'_{len(named)}'] = t
        else:
            for a in t[1]:
                walk(a)
    for t in terms:
        walk(t)
    return named


def translate(path, queries, all_answers, max_steps, out):
    with open(path, encoding='utf-8') as f:
        text = f.read()
    w = Writer(out)
    w.emit(f'# Translated from Prolog ({path.split("/")[-1]}) by prolog2btp.py: one rule per clause,')
    w.emit('# one theorem per resolution step of each answer. Atoms are uppercase, terms in full.')
    w.emit('rEq : =(x,x)')

    program, rules, letters_of, found = {}, {}, {}, []
    for term, names in Reader(text).clauses():
        term = deref(term)
        if term[0] == '?-' and len(term[1]) == 1:
            found.append((term[1][0], names))
            continue
        if term[0] == ':-' and len(term[1]) == 1:
            print(f'{path}: ignoring directive :- {show(term[1][0])}', file=sys.stderr)
            continue
        head, body = (term[1][0], conjuncts(term[1][1])) if term[0] == ':-' and len(term[1]) == 2 \
            else (term, [])
        head = deref(head)
        if isinstance(head, tuple) and head[0] == '-->' and len(head[1]) == 2:
            raise ValueError(f"DCG rules (-->) are not supported: {show(head)}")
        if isinstance(head, Var) or head[0] in (',', ';', '->', ':-', '?-'):
            raise ValueError(f"Not a clause head: {show(head)}")
        named = clause_vars([head] + body)
        k = key(head)
        if k in ARITH:
            raise ValueError(f"{k[0]}/{k[1]} is built in: {show(head)}")
        pred = re.sub(r'\W', '_', head[0]) or 'p'
        rule = f'r{pred}/{k[1]}_{len(program.get(k, [])) + 1}'
        while rule in rules:
            rule += "'"
        clause = Clause(head, body, named)
        program.setdefault(k, []).append((rule, clause))
        letters = rule_letters(list(named))
        lmap = {v: letters[n] for n, v in named.items()}
        hyps = [w.text(g, lmap) for g in body
                if not (isinstance(deref(g), tuple) and key(deref(g)) in CONTROL)]
        rules[rule] = ' -> '.join(hyps + [w.text(head, lmap)])
        letters_of[rule] = letters
        w.emit(f'{rule} : {rules[rule]}')

    if queries:
        found = []
        for q in queries:
            r = Reader(q.rstrip().rstrip('.') + ' .')
            found += list(r.clauses())
    if not found:
        print(f'{path}: no queries (?- Goal. in the file, or --query)', file=sys.stderr)

    goals = [g for _, c in sum(program.values(), []) for g in c.body] + \
        [g for q, _ in found for g in conjuncts(q)]
    if any(isinstance(deref(g), tuple) and key(deref(g)) in ARITH for g in goals):
        for line in prelude(w):
            w.emit(line)

    engine = Engine(program, max_steps)
    for qn, (query, qvars) in enumerate(found, 1):
        goals = conjuncts(query)
        w.emit(f'pQ{qn} : ?- {show(query)}.'.replace('#', '%23'))   # # would start a comment
        engine.steps = 0
        answers = 0
        for proofs in engine.conj(goals, {'cut': False}):
            answers += 1
            letters = {}
            for v in qvars.values():    # the query's variables take the first answer letters
                w.text(v, letters)
            for gn, proof in enumerate(proofs, 1):
                body = emit_proof(w, proof, letters_of, letters)
                suffix = f'_{gn}' if len(proofs) > 1 else ''
                w.emit(f'tQ{qn}{suffix}{"_" + str(answers) if all_answers else ""} : {body}')
            names = {v: f'_{c}' for v, c in letters.items()}     # unbound: _α, or as SWI does,
            for n, v in reversed(list(qvars.items())):            # the first query variable on it
                if isinstance(deref(v), Var) and not n.startswith('_'):
                    names[deref(v)] = n
            binding = ', '.join(f'{n} = {show(v, names)}' for n, v in qvars.items()
                                if not n.startswith('_') and not isinstance(deref(v), Var))
            w.emit(f'pA{qn}_{answers} : {binding or "true"}'.replace('#', '%23'))
            if not all_answers:
                break
        if not answers:
            w.emit(f'pA{qn}_0 : false (no proof, so nothing to check)')


def emit_proof(w, proof, letters_of, letters):
    """Theorems for the proof tree, children first; the body of its root step"""
    rule, values, kids = proof
    hyps = [w.step(emit_proof(w, kid, letters_of, letters)) for kid in kids]
    rl = letters_of.get(rule)     # a clause's own letters; built-in rules (rEq, arithmetic) name theirs
    reps = ';'.join(f"{rl[n] if rl else n}={w.term(w.text(v, letters))}" for n, v in values.items())
    if hyps and not reps:
        reps = ';'
    return f"{rule} {reps} {' '.join(hyps)}".strip()


def main():
    args = sys.argv[1:]
    usage = (f"Usage: python {sys.argv[0]} <program.pl> [--query GOAL]... [--all] "
             f"[--max-steps N] > <file.btp>")
    queries, all_answers, max_steps = [], False, 100000
    while '--query' in args:
        i = args.index('--query')
        if i + 1 >= len(args):
            sys.exit(usage)
        queries.append(args[i + 1])
        del args[i:i + 2]
    if '--all' in args:
        args.remove('--all')
        all_answers = True
    if '--max-steps' in args:
        i = args.index('--max-steps')
        if i + 1 >= len(args) or not args[i + 1].isdigit():
            sys.exit(usage)
        max_steps = int(args[i + 1])
        del args[i:i + 2]
    if len(args) != 1:
        sys.exit(usage)
    sys.setrecursionlimit(1000000)
    try:
        translate(args[0], queries, all_answers, max_steps, sys.stdout)
    except (SyntaxError, ValueError, RuntimeError) as error:
        sys.exit(f'{args[0]}: {error}')


if __name__ == '__main__':
    main()
