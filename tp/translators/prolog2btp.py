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

Not supported (an error): negation (\\+), disjunction, if-then-else,
arithmetic and other built-ins, assert/retract, op/3, DCG (-->), strings.
"""
import re
import sys
import unicodedata

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
  | (?P<num>\d+)
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
            return atom(word), 0
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
            return atom('-' + nxt[1]), 0
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
        if re.fullmatch(r'[a-z][A-Za-z0-9_]*|\[\]|[+\-*/\\^<>=~:.?@#&$]+|-?\d+|!|;', name):
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
UNSUPPORTED = {(';', 2), ('->', 2), ('\\+', 1), ('is', 2), ('<', 2), ('>', 2), ('=<', 2), ('>=', 2),
               ('=:=', 2), ('=\\=', 2), ('\\=', 2), ('==', 2), ('\\==', 2), ('=..', 2), ('call', 1),
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
        if k in UNSUPPORTED:
            raise ValueError(f"Not supported: {k[0]}/{k[1]}")
        if k not in self.program:
            raise ValueError(f"Unknown procedure: {k[0]}/{k[1]}")
        for rule, clause in self.program[k]:
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


# ---------------------------------------------------------------- writing

# Lowercase letters the same in every Python (see mm2btp.py); clause
# variables take ASCII first, answers' unbound variables Greek, so a value
# never contains a letter a rule substitutes.
RULE_LETTERS = 'abcdefghijklmnopqrstuvwxyz' + ''.join(
    chr(c) for c in range(0xdf, 0x250) if unicodedata.category(chr(c)) == 'Ll')
ANSWER_LETTERS = ''.join(chr(c) for a, b in ((0x3b1, 0x3ca), (0x430, 0x460), (0x1e00, 0x1f00))
                         for c in range(a, b) if unicodedata.category(chr(c)) == 'Ll')
RESERVED = {'[]'}


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
    rl = letters_of.get(rule, {'x': 'x'})
    reps = ';'.join(f"{rl[n] if rule != 'rEq' else n}={w.term(w.text(v, letters))}" for n, v in values.items())
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
