"""Tactics: Python for <?py ... ?> blocks over this library (logic, fol, peano, ...).

budge-tp.py runs a block with __file__ and env defined and checks what it
prints. A block over this library starts with

    import os, sys; sys.path.insert(0, <directory of this file>)
    from tactics import *
    use(env, __file__)

and then prints Budge code through the functions here. They use the rule and
theorem names of the library next to this file, so this is the Python half of
that library (in LCF terms, its tactics). They build proofs at a higher
level (terms by value, equation chains, induction, quantifiers with de
Bruijn indices) and print the individual rule
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
def EQ(x, y): return ('EQ', x, y)
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


# ---------------------------------------------------------------- formulas with named parameters


def instantiate(f, t, k=0):
    """f with the variable bound k binders out replaced by the closed term t."""
    if f == V(num(k)):
        return t
    if isinstance(f, str):
        return f
    if f[0] in BINDERS:
        return (f[0], instantiate(f[1], t, k + 1))
    return (f[0], *(instantiate(a, t, k) for a in f[1:]))


# ---------------------------------------------------------------- shared proof helpers
ONE, TWO = S(Z), S(S(Z))


# ---------------------------------------------------------------- library symbols
# Defined by recursion in parity.btp (FLIP, MOD2, DIV2); each has a term rule
# and CT, OPEN, ABS and congruence rules.
def FLIP(x): return ('FLIP', x)
def MOD2(x): return ('MOD2', x)
def DIV2(x): return ('DIV2', x)


for _op, _n in (('FLIP', 'Flip'), ('MOD2', 'Mod2'), ('DIV2', 'Div2')):
    add_symbol(_op, f'rTm{_n}', f'rCt{_n}', f'rOpen{_n}', f'rAbs{_n}', {0: f'rCong{_n}'})


# ---------------------------------------------------------------- more axiom instances
def ax(rule, x=None):
    """An instance of a rule with at most one variable, x."""
    return apply(rule, [('x', x)] if x is not None else [], [])


def andl(p, q): return apply('rAndL', [('p', p), ('q', q)], [])   # ⊢((p∧q)=>p)
def andr(p, q): return apply('rAndR', [('p', p), ('q', q)], [])   # ⊢((p∧q)=>q)


def or_elim(h_p, h_q, r_):
    """From ⊢(P=>R) and ⊢(Q=>R) conclude ⊢((P∨Q)=>R)."""
    p, q = val(h_p)[1][1], val(h_q)[1][1]
    e = apply('rOrE', [('p', p), ('q', q), ('r', r_)], [])
    return mp(h_q, mp(h_p, e))
