"""Tactics: Python for <?py ... ?> blocks over this library (logic, fol, peano, ...).

budge-tp.py runs a block with __file__ and env defined and checks what it
prints. A block over this library starts with

    import os, sys; sys.path.insert(0, <directory of this file>)
    from tactics import *
    use(env, __file__)

and then prints Budge code through the functions here. They use the rule and
theorem names of the library next to this file, so this is the Python half of
that library (in LCF terms, its tactics). They build proofs at a higher
level (terms by value, equation chains, natural deduction with Ctx,
quantifiers with de Bruijn indices) and print the individual rule
applications, which budge-tp.py then checks like any other code. Every rule
application is also simulated here as budge-tp.py does it, so a mistake is
reported at the step that makes it.

Everything above a block (rules, derived theorems, imports) is visible to it
(use), and identical facts and terms are reused rather than redeclared.
"""
import copy
import os

# ---------------------------------------------------------------- syntax trees
# Atoms are str; compound nodes are tuples (op, *args). THM is ⊢, NOT is ¬,
# and IMP, AND, OR are the parenthesised infix =>, ∧, ∨.
INFIX = {'IMP': '=>', 'AND': '∧', 'OR': '∨'}
# Program syntax and Hoare triples (lib/hoare.btp). Not parsed back.
PROGRAM = {
    'ASG': lambda x, e: f'{x} = {e};',
    'SEQ': lambda a, b: f'{a} {b}',
    'SKIP': lambda: ';',
    'IF': lambda b, c, d: f'IF ({b}) {{ {c} }} ELSE {{ {d} }}',
    'WHILE': lambda b, c: f'WHILE ({b}) {{ {c} }}',
    'TRIPLE': lambda p, c, q: f'{{{p}}} {c} {{{q}}}',
}


def r(t):
    if isinstance(t, str):
        return t
    op = t[0]
    if op == 'THM':
        return '⊢' + r(t[1])
    if op == 'NOT':
        return '¬' + r(t[1])
    if op in PROGRAM:
        return PROGRAM[op](*map(r, t[1:]))
    if op in INFIX:
        return '(' + r(t[1]) + INFIX[op] + r(t[2]) + ')'
    return op + '(' + ','.join(r(a) for a in t[1:]) + ')'


def parse(s):
    pos = 0

    def term():
        nonlocal pos
        if s.startswith('⊢', pos):
            pos += 1
            return ('THM', term())
        if s.startswith('¬', pos):
            pos += 1
            return ('NOT', term())
        if s.startswith('⊤', pos):
            pos += 1
            return '⊤'
        if s[pos] == '(':
            pos += 1
            a = term()
            for op, sym in INFIX.items():
                if s.startswith(sym, pos):
                    break
            else:
                raise AssertionError((s, pos))
            pos += len(sym)
            b = term()
            assert s[pos] == ')', (s, pos)
            pos += 1
            return (op, a, b)
        start = pos
        while pos < len(s) and (s[pos].isalnum() or s[pos] == '$'):
            pos += 1
        name = s[start:pos]
        assert name, (s, pos)
        if pos < len(s) and s[pos] == '(':
            pos += 1
            args = [term()]
            while s[pos] == ',':
                pos += 1
                args.append(term())
            assert s[pos] == ')', (s, pos)
            pos += 1
            return (name, *args)
        return name

    t = term()
    assert pos == len(s), (s, pos)
    return t


def S(x): return ('S', x)
def ADD(x, y): return ('ADD', x, y)
def MUL(x, y): return ('MUL', x, y)
def EQ(x, y): return ('EQ', x, y)
def IMP(x, y): return ('IMP', x, y)
def AND(x, y): return ('AND', x, y)
def OR(x, y): return ('OR', x, y)
def NOT(x): return ('NOT', x)
def ASG(x, e): return ('ASG', x, e)
def SEQ(a, b): return ('SEQ', a, b)
def IF(b, c, d): return ('IF', b, c, d)
def WHILE(b, c): return ('WHILE', b, c)


SKIP = ('SKIP',)
TOP = '⊤'
def V(n): return ('V', n)


Z = '0'
K_, M_, N_ = 'K', 'M', 'N'
PARAMS = ('K', 'M', 'N', 'U', 'W', 'X', 'Y', 'Z')   # in their PLT order
V0 = V(Z)


def num(n):
    t = Z
    for _ in range(n):
        t = S(t)
    return t


def subst(t, old, new):
    if t == old:
        return new
    if isinstance(t, str):
        return t
    return (t[0], *(subst(a, old, new) for a in t[1:]))


# ---------------------------------------------------------------- registries
# How each function symbol is built, checked closed, opened, abstracted and
# rewritten. Files that add a symbol (e.g. SUM) register it with add_symbol.
ATOM_RULES = {'0': 'rTm0', 'i': 'rTmi', 'j': 'rTmj', 'l': 'rTml',
              'a': 'rTma', 'b': 'rTmb', 'c': 'rTmc', '⊤': 'rTmTop'}
ATOM_RULES.update({w: 'rTm' + w for w in PARAMS})
CT_ATOMS = {}    # closed constants other than parameters, e.g. program variables
TERM_RULES = {'S': 'rTmS', 'V': 'rTmV', 'ADD': 'rTmAdd', 'MUL': 'rTmMul',
              'EQ': 'rTmEq', 'ALL': 'rTmAll', 'EX': 'rTmEx',
              'ASG': 'rTmAsg', 'SEQ': 'rTmSeq', 'SKIP': 'rTmSkip', 'IF': 'rTmIf',
              'WHILE': 'rTmWhile'}
TERM_KEYS = {'IF': 'bcd', 'WHILE': 'bc'}   # variables of a term rule, if not x, y
PROP_RULES = {'IMP': 'rTmImp', 'AND': 'rTmAnd', 'OR': 'rTmOr', 'NOT': 'rTmNeg'}
BINDERS = {'ALL': ('rOpenAll', 'rAbsAll'), 'EX': ('rOpenEx', 'rAbsEx')}
CT_RULES = {'S': 'rCtS', 'ADD': 'rCtAdd', 'MUL': 'rCtMul'}
OPEN_RULES = {'S': 'rOpenS', 'ADD': 'rOpenAdd', 'MUL': 'rOpenMul', 'EQ': 'rOpenEq',
              'IMP': 'rOpenImp', 'AND': 'rOpenAnd', 'OR': 'rOpenOr', 'NOT': 'rOpenNot'}
ABS_RULES = {'S': 'rAbsS', 'ADD': 'rAbsAdd', 'MUL': 'rAbsMul', 'EQ': 'rAbsEq',
             'IMP': 'rAbsImp', 'AND': 'rAbsAnd', 'OR': 'rAbsOr', 'NOT': 'rAbsNot'}
OPEN_ATOMS = {'0': 'rOpen0', '⊤': 'rOpenTop'}   # constants other than parameters
ABS_ATOMS = {'0': 'rAbs0', '⊤': 'rAbsTop'}
CONG = {('S', 0): 'rCongS', ('ADD', 0): 'rCongAddL', ('ADD', 1): 'rCongAddR',
        ('MUL', 0): 'rCongMulL', ('MUL', 1): 'rCongMulR'}


def add_symbol(op, term, ct, open_, abs_, cong):
    """Register rule names for a new function symbol; cong: {arg index: rule}."""
    TERM_RULES[op] = term
    CT_RULES[op] = ct
    OPEN_RULES[op] = open_
    ABS_RULES[op] = abs_
    for i, rule in cong.items():
        CONG[(op, i)] = rule


# ---------------------------------------------------------------- state
RULES = {}       # name -> (hyps[str], concl str)
THMS = {}        # name -> value string
TERM_NAMES = {}  # value string -> term theorem name
VALUES = {}      # value string -> theorem name, for reuse of identical facts
MEMO = {}        # judgement key -> theorem name
TERM_COUNT = {}  # file tag -> numbered terms emitted so far
SEC = {'prefix': 'x', 'count': 0}
FILE = {}

JUDGEMENTS = ('PAR', 'DIFF', 'PLT', 'LT', 'CT', 'OPEN', 'ABS')


def use(env, path):
    """Start a block: load what budge-tp.py has read and checked so far."""
    if FILE.get('env') is not env:              # a new run: forget the previous one
        for table in (RULES, THMS, VALUES, TERM_NAMES, MEMO, TERM_COUNT):
            table.clear()
        FILE['env'] = env
    stem = os.path.basename(path).split('.')[0]
    lib = os.path.basename(os.path.dirname(os.path.abspath(path))) == 'lib'
    FILE.update(path=path, tag=stem[:1].upper() + stem[1:3] + ('L' if lib else ''))
    TERM_COUNT.setdefault(FILE['tag'], 0)
    for name, rule in env['rules'].items():
        RULES[name] = (rule['hypotheses'], rule['conclusion'])
    for name, value in env['theorems'].items():
        if name in THMS:
            continue
        THMS[name] = value
        VALUES.setdefault(value, name)
        if name.startswith('tm'):
            TERM_NAMES.setdefault(value, name)
            continue
        try:
            t = parse(value)
        except (AssertionError, IndexError):
            continue
        if isinstance(t, tuple) and t[0] in JUDGEMENTS:
            MEMO.setdefault(judgement_key(t), name)


def judgement_key(t):
    if t[0] in ('OPEN', 'ABS'):
        return t[:4]
    return t


def emit_line(buf, name, rule, keys, hyps, comment=None):
    repl = ';'.join(f'{k}={v}' for k, v in keys)
    parts = [rule]
    if repl:
        parts.append(repl)
    elif hyps:
        parts.append(';')
    parts += hyps
    line = f'{name} : ' + ' '.join(parts)
    if comment:
        line += '   # ' + comment
    print(line)


def check_apply(name, rule, keys_vals, hyps):
    """Simulate budge-tp.py's apply_rule_or_theorem; return the conclusion."""
    if rule in RULES:
        ru_h = list(RULES[rule][0])
        ru_c = RULES[rule][1]
    else:
        ru_h = []
        ru_c = THMS[rule]
    th_h = [THMS[h] for h in hyps]
    for k, v in keys_vals:
        th_h = [x.replace(k, v) for x in th_h]
    for k, v in keys_vals:
        ru_h = [x.replace(k, v) for x in ru_h]
        ru_c = ru_c.replace(k, v)
    if ru_h != th_h:
        raise Exception(f'{name}: mismatch\n  rule: {ru_h}\n  thms: {th_h}')
    return ru_c


def T(t):
    """Name of a term theorem whose value is r(t); emits its construction."""
    s = r(t)
    if s in TERM_NAMES:
        return TERM_NAMES[s]
    if isinstance(t, str):
        rule, keys = ATOM_RULES[t], []
    elif t[0] in PROP_RULES:
        rule = PROP_RULES[t[0]]
        keys = [('pq'[i], T(a)) for i, a in enumerate(t[1:])]
    else:
        rule = TERM_RULES[t[0]]
        names = TERM_KEYS.get(t[0], 'xy')
        keys = [(names[i], T(a)) for i, a in enumerate(t[1:])]
    if len(s) <= 60 and not any(c in s for c in ' ;:#'):
        name, comment = f'tm{s}!', None
    else:
        TERM_COUNT[FILE['tag']] += 1
        name, comment = f"tm{FILE['tag']}{TERM_COUNT[FILE['tag']]}!", s
    assert name not in THMS, name
    v = check_apply(name, rule, [(k, THMS[n]) for k, n in keys], [])
    assert v == s, (v, s)
    THMS[name] = v
    TERM_NAMES[s] = name
    emit_line(None, name, rule, keys, [], comment)
    return name


def apply(rule, subst_list, hyps, name=None):
    """Apply a rule or theorem with [(key, tree)] and hypothesis names."""
    kv = [(k, r(v)) for k, v in subst_list]
    v = check_apply(name or '?', rule, kv, hyps)
    if name is None and v in VALUES:
        return VALUES[v]                 # already proved (here or in an import)
    keys = [(k, T(v)) for k, v in subst_list]
    if name is None:
        SEC['count'] += 1
        name = f"th{SEC['prefix']}{SEC['count']}!"
    assert name not in THMS, name
    THMS[name] = v
    VALUES.setdefault(v, name)
    c = v if (v.startswith('⊢') and name.endswith('!')) else None
    emit_line(None, name, rule, keys, hyps, c)
    return name


def val(name):
    return parse(THMS[name])


def section(title, prefix, intro=()):
    SEC.update(prefix=prefix, count=0)
    print()
    print(f'## {title} ##')
    for line in intro:
        print('# ' + line if line else '#')


def prose(name, text):
    print(f'{name} : {text}')


def visible(h, name):
    """Give theorem h a visible name, by restating it (a theorem used as a rule)."""
    print(f'{name} : {h}')
    THMS[name] = THMS[h]
    return name


# ---------------------------------------------------------------- logic
def mp(hp, himp):
    p = val(hp)[1]
    imp = val(himp)[1]
    assert imp[0] == 'IMP' and imp[1] == p, (THMS[hp], THMS[himp])
    return apply('rMp', [('p', p), ('q', imp[2])], [hp, himp])


def hs(hab, hbc):
    a, b = val(hab)[1][1:]
    b2, c = val(hbc)[1][1:]
    assert b == b2, (THMS[hab], THMS[hbc])
    t = apply('thHS', [('i', a), ('j', b), ('l', c)], [])
    return mp(hab, mp(hbc, t))


def weaken(h, G):
    return mp(h, apply('rK', [('p', val(h)[1]), ('q', G)], []))


# Equality proofs are either unconditional, ⊢EQ(a,b), or under an assumption
# G (the induction hypothesis), ⊢(G=>EQ(a,b)).
def is_cond(h):
    return val(h)[1][0] == 'IMP'


def sides(h):
    e = val(h)[1]
    if e[0] == 'IMP':
        e = e[2]
    assert e[0] == 'EQ', THMS[h]
    return e[1], e[2]


def through(h, imp):
    """h : EQ (maybe under G), imp : ⊢(EQ=>X). Gives X (same mode)."""
    e = val(h)[1]
    if e[0] == 'IMP' and e[1] == e[2]:
        return imp                       # h is ⊢(G=>G): imp already is G=>X
    return hs(h, imp) if is_cond(h) else mp(h, imp)


def sym(h):
    a, b = sides(h)
    return through(h, apply('rEqS', [('x', a), ('y', b)], []))


def trans(h1, h2, G=None):
    if is_cond(h1) != is_cond(h2):
        if is_cond(h1):
            h2 = weaken(h2, val(h1)[1][1])
        else:
            h1 = weaken(h1, val(h2)[1][1])
    a, b = sides(h1)
    b2, c = sides(h2)
    assert b == b2, (THMS[h1], THMS[h2])
    t = apply('rEqT', [('x', a), ('y', b), ('z', c)], [])
    if not is_cond(h1):
        return mp(h2, mp(h1, t))
    G = val(h1)[1][1]
    u = hs(h1, t)                        # ⊢(G=>(EQ(b,c)=>EQ(a,c)))
    s = apply('rS', [('p', G), ('q', EQ(b, c)), ('r', EQ(a, c))], [])
    return mp(h2, mp(u, s))


def rewrite(term, path, h):
    """Proof of EQ(term, term') rewriting the subterm at path with h."""
    if not path:
        a, _ = sides(h)
        assert a == term, (r(a), r(term))
        return h
    op, i = term[0], path[0]
    inner = rewrite(term[i + 1], path[1:], h)
    a, b = sides(inner)
    keys = [('x', a), ('y', b)]
    if len(term) == 3:
        keys.append(('z', term[2 - i]))
    return through(inner, apply(CONG[(op, i)], keys, []))


def at(term, path):
    for i in path:
        term = term[i + 1]
    return term


def chain(start, steps):
    """steps: [(path, proof or callable(subterm) -> proof)]. Proves EQ(start, end)."""
    acc, cur = None, start
    for path, h in steps:
        if callable(h):
            h = h(at(cur, path))
        step = rewrite(cur, path, h)
        _, cur = sides(step)
        acc = step if acc is None else trans(acc, step)
    return acc


# ---------------------------------------------------------------- judgements
def memo(key, f):
    if key not in MEMO:
        MEMO[key] = f()
    return MEMO[key]


def par(w):
    return memo(('PAR', w), lambda: apply('rPar' + w, [], []))


def plt(a, b):
    def go():
        i, j = PARAMS.index(a), PARAMS.index(b)
        assert i < j
        if j == i + 1:
            return apply(f'rPlt{a}{b}', [], [])
        m = PARAMS[i + 1]
        return apply('rPltT', [('a', a), ('b', m), ('c', b)], [plt(a, m), plt(m, b)])
    return memo(('PLT', a, b), go)


def diff(w, o):
    def go():
        if PARAMS.index(w) < PARAMS.index(o):
            return apply('rDiffL', [('w', w), ('o', o)], [plt(w, o)])
        return apply('rDiffG', [('w', w), ('o', o)], [plt(o, w)])
    return memo(('DIFF', w, o), go)


def ltj(n, k):
    def go():
        if n == Z:
            return apply('rLtZ', [('n', k[1])], [])
        return apply('rLtS', [('a', n[1]), ('b', k[1])], [ltj(n[1], k[1])])
    return memo(('LT', n, k), go)


def ct(t):
    def go():
        if t == Z:
            return apply('rCt0', [], [])
        if t in PARAMS:
            return apply('rCtPar', [('w', t)], [par(t)])
        if t in CT_ATOMS:
            return apply(CT_ATOMS[t], [], [])
        keys = [('xy'[i], a) for i, a in enumerate(t[1:])]
        return apply(CT_RULES[t[0]], keys, [ct(a) for a in t[1:]])
    return memo(('CT', t), go)


def open_(k, f, t):
    """Proof of OPEN(k,f,t,g); returns (name, g)."""
    def go():
        if isinstance(f, tuple) and f[0] == 'V':
            if f[1] == k:
                return apply('rOpenHit', [('k', k), ('t', t)], [ct(t)])
            return apply('rOpenBound', [('n', f[1]), ('k', k), ('t', t)], [ltj(f[1], k)])
        if f in OPEN_ATOMS:
            return apply(OPEN_ATOMS[f], [('k', k), ('t', t)], [])
        if f in PARAMS:
            return apply('rOpenPar', [('w', f), ('k', k), ('t', t)], [par(f)])
        if f[0] in BINDERS:
            inner, g = open_(S(k), f[1], t)
            return apply(BINDERS[f[0]][0], [('k', k), ('f', f[1]), ('t', t), ('g', g)], [inner])
        subs = [open_(k, a, t) for a in f[1:]]
        keys = [('k', k), ('x', f[1])] + ([('y', f[2])] if len(f) == 3 else [])
        keys += [('t', t), ('u', subs[0][1])] + ([('v', subs[1][1])] if len(f) == 3 else [])
        return apply(OPEN_RULES[f[0]], keys, [s[0] for s in subs])
    name = memo(('OPEN', k, f, t), go)
    return name, parse(THMS[name])[4]


def abs_(k, w, g):
    """Proof of ABS(k,w,g,f); returns (name, f)."""
    def go():
        if g == w:
            return apply('rAbsHit', [('k', k), ('w', w)], [par(w)])
        if isinstance(g, tuple) and g[0] == 'V':
            return apply('rAbsBound', [('n', g[1]), ('k', k), ('w', w)], [ltj(g[1], k)])
        if g in ABS_ATOMS:
            return apply(ABS_ATOMS[g], [('k', k), ('w', w)], [])
        if g in PARAMS:
            return apply('rAbsPar', [('k', k), ('w', w), ('o', g)], [diff(w, g)])
        if g[0] in BINDERS:
            inner, f = abs_(S(k), w, g[1])
            return apply(BINDERS[g[0]][1], [('k', k), ('w', w), ('f', g[1]), ('g', f)], [inner])
        subs = [abs_(k, w, a) for a in g[1:]]
        keys = [('k', k), ('w', w), ('x', g[1])] + ([('y', g[2])] if len(g) == 3 else [])
        keys += [('u', subs[0][1])] + ([('v', subs[1][1])] if len(g) == 3 else [])
        return apply(ABS_RULES[g[0]], keys, [s[0] for s in subs])
    name = memo(('ABS', k, w, g), go)
    return name, parse(THMS[name])[4]


# ---------------------------------------------------------------- quantifiers
def inst(h, *terms):
    """∀-eliminate h at the given closed terms, outermost quantifier first."""
    for t in terms:
        f = val(h)[1]
        assert f[0] == 'ALL', THMS[h]
        o, g = open_(Z, f[1], t)
        h = mp(h, apply('rAllE', [('f', f[1]), ('t', t), ('g', g)], [o]))
    return h


def gen(h, w, name=None):
    """Generalise parameter w: from ⊢g(w) to ⊢ALL(g(V(0)))."""
    g = val(h)[1]
    a, f = abs_(Z, w, g)
    return apply('rGen', [('w', w), ('g', g), ('f', f)], [a, h], name=name)


def ind_hyp(f):
    """Induction hypothesis f(N) and the proof ⊢(f(N)=>f(N)) to use it."""
    G = instantiate(f, N_)
    return G, apply('thId', [('i', G)], [])


def induction(f, base, step, name=None):
    """From ⊢f(0) and ⊢(f(N)=>f(S(N))) conclude ⊢ALL(f)."""
    b, g, h = instantiate(f, Z), instantiate(f, N_), instantiate(f, S(N_))
    o1, b2 = open_(Z, f, Z)
    a, f2 = abs_(Z, N_, g)
    o3, h2 = open_(Z, f, S(N_))
    assert (b2, f2, h2) == (b, f, h)
    return apply('rInd', [('f', f), ('b', b), ('g', g), ('h', h)],
                 [o1, a, o3, base, step], name=name)


# axiom instances
def aAZ(x): return apply('rAZ', [('x', x)], [])
def aAS(x, y): return apply('rAS', [('x', x), ('y', y)], [])
def aMZ(x): return apply('rMZ', [('x', x)], [])
def aMS(x, y): return apply('rMS', [('x', x), ('y', y)], [])


# ---------------------------------------------------------------- formulas with named parameters
def abstract(t, w, k=0):
    """Replace parameter w by the de Bruijn variable bound k binders out."""
    if t == w:
        return V(num(k))
    if isinstance(t, str):
        return t
    if t[0] in BINDERS:
        return (t[0], abstract(t[1], w, k + 1))
    return (t[0], *(abstract(a, w, k) for a in t[1:]))


def instantiate(f, t, k=0):
    """f with the variable bound k binders out replaced by the closed term t."""
    if f == V(num(k)):
        return t
    if isinstance(f, str):
        return f
    if f[0] in BINDERS:
        return (f[0], instantiate(f[1], t, k + 1))
    return (f[0], *(instantiate(a, t, k) for a in f[1:]))


def exists(w, body): return ('EX', abstract(body, w))
def mentions(t, w): return t == w or (isinstance(t, tuple) and any(mentions(a, w) for a in t[1:]))


# ---------------------------------------------------------------- natural deduction
def imp_mp(hxa, hxab):
    """⊢(X=>A), ⊢(X=>(A=>B)) give ⊢(X=>B), by axiom S."""
    x, a = val(hxa)[1][1:]
    x2, ab = val(hxab)[1][1:]
    assert x == x2 and ab[0] == 'IMP' and ab[1] == a, (THMS[hxa], THMS[hxab])
    s = apply('rS', [('p', x), ('q', a), ('r', ab[2])], [])
    return mp(hxa, mp(hxab, s))


class Ctx:
    """Reasoning under hypotheses. The context is a formula G, ⊤ at the root
    and (G∧H) after assuming H; a fact X proved here is the theorem ⊢(G=>X)."""

    def __init__(self, parent=None, hyp=None, reserved=()):
        self.parent, self.hyp = parent, hyp
        self.G = TOP if parent is None else AND(parent.G, hyp)
        self.params = set(reserved) if parent is None else set(parent.params)

    # -- facts and hypotheses
    def get(self, h):
        """A proof of X in this context, from one here, in an ancestor, or ⊢X."""
        f = val(h)[1]
        if f[0] == 'IMP' and f[1] == self.G:
            return h
        if self.parent is not None and f[0] == 'IMP' and self._ancestor(f[1]):
            return hs(apply('rAndL', [('p', self.parent.G), ('q', self.hyp)], []),
                      self.parent.get(h))
        return weaken(h, self.G)

    def _ancestor(self, g):
        c = self.parent
        while c is not None:
            if c.G == g:
                return True
            c = c.parent
        return False

    def concl(self, h):
        return val(self.get(h))[1][2]

    def hyp_(self, H=None):
        """The hypothesis H (default: the newest) as a fact."""
        c = self
        while H is not None and c.hyp != H:
            c = c.parent
        h = apply('rAndR', [('p', c.parent.G), ('q', c.hyp)], [])
        return self.get(h)

    def assume(self, H):
        return Ctx(self, H)

    def discharge(self, h):
        """Proof of X under (G∧H) gives (H=>X) in the parent context."""
        h = self.get(h)
        X = val(h)[1][2]
        cur = apply('thCurry', [('i', self.parent.G), ('j', self.hyp), ('l', X)], [])
        return mp(h, cur)

    def close(self, h):
        """At the root: from ⊢(⊤=>X) get ⊢X."""
        assert self.parent is None
        return mp(apply('rTop', [], []), self.get(h))

    # -- propositional steps
    def mp(self, ha, hab):
        return imp_mp(self.get(ha), self.get(hab))

    def thru(self, ha, imp):
        """X here and an unconditional ⊢(X=>Y) give Y."""
        return hs(self.get(ha), imp)

    def and_i(self, ha, hb):
        a, b = self.concl(ha), self.concl(hb)
        i = apply('rAndI', [('p', a), ('q', b)], [])
        return imp_mp(self.get(hb), self.thru(ha, i))

    def and_l(self, h):
        a, b = self.concl(h)[1:]
        return self.thru(h, apply('rAndL', [('p', a), ('q', b)], []))

    def and_r(self, h):
        a, b = self.concl(h)[1:]
        return self.thru(h, apply('rAndR', [('p', a), ('q', b)], []))

    def or_l(self, h, b):
        return self.thru(h, apply('rOrL', [('p', self.concl(h)), ('q', b)], []))

    def or_r(self, h, a):
        return self.thru(h, apply('rOrR', [('p', a), ('q', self.concl(h))], []))

    def cases(self, hor, case_a, case_b):
        """From A∨B, case_a(ctx with A) and case_b(ctx with B) proving the same C."""
        a, b = self.concl(hor)[1:]
        ca, cb = self.assume(a), self.assume(b)
        ha = ca.discharge(case_a(ca))
        hb = cb.discharge(case_b(cb))
        c = val(ha)[1][2][2]
        e = apply('rOrE', [('p', a), ('q', b), ('r', c)], [])
        return self.mp(hor, self.mp(self.get(hb), self.thru(ha, e)))

    def efq(self, ha, hna, b):
        a = self.concl(ha)
        e = apply('thEFQ', [('i', a), ('j', b)], [])
        return self.mp(ha, self.thru(hna, e))

    def absurd(self, a, prove):
        """¬A, from prove(ctx with A) returning proofs of some B and ¬B."""
        c = self.assume(a)
        hb, hnb = prove(c)
        h = c.discharge(c.efq(hb, hnb, NOT(a)))           # A => ¬A
        return self.thru(h, apply('thAbs', [('i', a)], []))

    def by_contra(self, a, prove):
        """A, from prove(ctx with ¬A) returning proofs of some B and ¬B."""
        h = self.absurd(NOT(a), prove)
        return self.thru(h, apply('thDNE', [('i', a)], []))

    def lem(self, a):
        return self.get(apply('thLEM', [('i', a)], []))

    # -- quantifiers
    def fresh(self, *avoid):
        for w in PARAMS:
            if w not in self.params and not any(mentions(t, w) for t in (self.G, *avoid)):
                return w
        raise Exception('out of parameters')

    def all_e(self, h, *terms):
        h = self.get(h)
        for t in terms:
            f = self.concl(h)[1]
            o, g = open_(Z, f, t)
            h = self.thru(h, apply('rAllE', [('f', f), ('t', t), ('g', g)], [o]))
        return h

    def ex_i(self, h, f, t):
        """f[t] here gives EX(f)."""
        o, g = open_(Z, f, t)
        assert g == self.concl(h), (r(g), r(self.concl(h)))
        return self.thru(h, apply('rExI', [('f', f), ('t', t), ('g', g)], [o]))

    def all_i(self, f, prove):
        """ALL(f), from prove(ctx, w) proving f[w] for a fresh parameter w."""
        w = self.fresh(f)
        c = copy.copy(self)
        c.params = self.params | {w}
        h = self.get(prove(c, w))                            # ⊢(G=>f[w])
        g = val(h)[1]
        a, f2 = abs_(Z, w, g)
        assert f2 == ('IMP', self.G, f), (r(f2), r(f))
        gen_ = apply('rGen', [('w', w), ('g', g), ('f', f2)], [a, h])
        o, _ = open_(Z, self.G, K_)
        ai = apply('rAllImp', [('q', self.G), ('f', f)], [o])
        return mp(gen_, ai)

    def ex_e(self, hex_, prove):
        """From EX(f) here and prove(ctx with f[w], w) proving X (w fresh, not in X)."""
        f = self.concl(hex_)[1]
        w = self.fresh(f)
        c = self.assume(instantiate(f, w))
        c.params = self.params | {w}
        hx = prove(c, w)
        X = c.concl(hx)
        assert not mentions(X, w), r(X)
        h1 = c.discharge(hx)                                  # ⊢(G=>(f[w]=>X))
        fw = instantiate(f, w)
        perm = apply('thC', [('i', self.G), ('j', fw), ('l', X)], [])
        h2 = mp(h1, perm)                                     # ⊢(f[w]=>(G=>X))
        g = val(h2)[1]
        a, f2 = abs_(Z, w, g)
        q = ('IMP', self.G, X)
        assert f2 == ('IMP', f, q), (r(f2),)
        gen_ = apply('rGen', [('w', w), ('g', g), ('f', f2)], [a, h2])
        o, _ = open_(Z, q, K_)
        ee = apply('rExE', [('q', q), ('f', f)], [o])
        h3 = mp(gen_, ee)                                     # ⊢(EX(f)=>(G=>X))
        h4 = self.thru(hex_, h3)                              # ⊢(G=>(G=>X))
        return mp(h4, apply('thW', [('i', self.G), ('j', X)], []))

    # -- equations
    def eq(self, h):
        """An equation: keep it unconditional if it is, else bring it here."""
        return self.get(h) if is_cond(h) else h

    def sym(self, h):
        return self.get(sym(self.eq(h)))

    def trans(self, h1, h2):
        return self.get(trans(self.eq(h1), self.eq(h2)))

    def chain(self, start, steps):
        acc, cur = None, start
        for path, h in steps:
            if callable(h):
                h = h(at(cur, path))
            step = rewrite(cur, path, self.eq(h))
            _, cur = sides(step)
            acc = step if acc is None else trans(self.eq(acc), self.eq(step))
        return self.get(acc)


# ---------------------------------------------------------------- shared proof helpers
ONE, TWO = S(Z), S(S(Z))


# ---------------------------------------------------------------- library symbols
# Defined by recursion in parity.btp (FLIP, MOD2, DIV2), sum.btp (SUM); each
# has a term rule and CT, OPEN, ABS and congruence rules.
def FLIP(x): return ('FLIP', x)
def MOD2(x): return ('MOD2', x)
def DIV2(x): return ('DIV2', x)
def SUM(x): return ('SUM', x)


for _op, _n in (('FLIP', 'Flip'), ('MOD2', 'Mod2'), ('DIV2', 'Div2'), ('SUM', 'Sum')):
    add_symbol(_op, f'rTm{_n}', f'rCt{_n}', f'rOpen{_n}', f'rAbs{_n}', {0: f'rCong{_n}'})


# ---------------------------------------------------------------- more axiom instances
def ax(rule, x=None):
    """An instance of a rule with at most one variable, x."""
    return apply(rule, [('x', x)] if x is not None else [], [])


def andl(p, q): return apply('rAndL', [('p', p), ('q', q)], [])   # ⊢((p∧q)=>p)
def andr(p, q): return apply('rAndR', [('p', p), ('q', q)], [])   # ⊢((p∧q)=>q)
def aSumZ(): return apply('rSumZ', [], [])
def aSumS(x): return apply('rSumS', [('x', x)], [])


def or_elim(h_p, h_q, r_):
    """From ⊢(P=>R) and ⊢(Q=>R) conclude ⊢((P∨Q)=>R)."""
    p, q = val(h_p)[1][1], val(h_q)[1][1]
    e = apply('rOrE', [('p', p), ('q', q), ('r', r_)], [])
    return mp(h_q, mp(h_p, e))


# ---------------------------------------------------------------- computation
def add_eval(a, b):
    """⊢EQ(ADD(a,b), numeral) for numerals a, b."""
    if b == Z:
        return aAZ(a)
    return chain(ADD(a, b), [
        ([], aAS(a, b[1])),
        ([0], lambda t: add_eval(a, b[1])),
    ])


def sum_eval(n):
    """⊢EQ(SUM(n), numeral) for a numeral n."""
    if n == Z:
        return aSumZ()
    h = chain(SUM(n), [
        ([], aSumS(n[1])),
        ([0], lambda t: sum_eval(n[1])),
    ])
    _, b = sides(h)
    return trans(h, add_eval(b[1], b[2]))
