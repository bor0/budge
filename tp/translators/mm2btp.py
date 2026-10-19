#!/usr/bin/env python3
"""Translate a Metamath database into Budge-TP.

    python3 mm2btp.py db.mm [--stop LABEL] > db.btp

Every assertion becomes a sequent  ⟦ H1 ⨾ … ⨾ Hn ⟧ ⟹ C : its mandatory
hypotheses ($f and $e, in database order) and its conclusion. $a statements
are rules. A $p proof is replayed step by step into theorems, each proving
⟦ Γ ⟧ ⟹ X under the theorem's own hypotheses Γ; the last one is the
theorem, which later proofs use as a rule (Budge substitutes its letters).
So typecodes and $e hypotheses are checked by Budge-TP itself; the
structural rules (rLeaf, rInL/rInR, rNode, rApply…, rWeaken, rFlat…, rDisj…)
are the only added axioms. Inside a proof Γ is a balanced tree ⟪ l ⨾ r ⟫, so
looking up a hypothesis takes log n short steps (rLeaf, then rInL/rInR);
rFlatN turns the last step back into the flat list of the statement.

Encoding: Metamath variables become single lowercase letters (ph → φ, x → x,
others from a pool of non-ASCII lowercase letters), constants become tokens
with no lowercase letters (wff → WFF, |- → ⊢), tokens are separated by single
spaces. Leftover lowercase letters name the structural rules' variables.

$d x y becomes a hypothesis DISJ ⟨ x ⟩ ⟨ y ⟩; using a lemma, Budge-TP proves
DISJ ⟨ E ⟩ ⟨ F ⟩ for the substituted expressions from the context's pairs (rDisjCat
splits a side, rDisjK… a constant has no variables, rDisjSym). A dummy variable
d of a proof becomes hypotheses too (its float, its DISJ pairs), so a theorem
reads "given fresh variables d…"; whoever uses it passes on its dummies (the
same letters, renamed when taken), there being no way in Budge to discharge
them (that needs "d does not occur in Γ"), so contexts carry them upward.

Not supported (the theorem and everything using it is skipped, with a note):
incomplete proofs, substituting the empty expression (miu.mm), $[ includes.
"""
import hashlib
import sys
import unicodedata

STRUCT_TOKENS = ('⟦', '⟧', '⨾', '⟹', '⟪', '⟫', 'DISJ', '⟨', '⟩')
PRETTY = {'|-': '⊢', '->': '→', '<->': '↔', '-.': '¬', '/\\': '∧', '\\/': '∨',
          'A.': '∀', 'E.': '∃', 'e.': '∈', 'T.': '⊤', 'F.': '⊥'}
GREEK = {'ph': 'φ', 'ps': 'ψ', 'ch': 'χ', 'th': 'θ', 'ta': 'τ', 'et': 'η', 'ze': 'ζ',
         'si': 'σ', 'rh': 'ρ', 'mu': 'μ', 'la': 'λ', 'ka': 'κ'}


class Unsupported(Exception):
    pass


# ---------------------------------------------------------------- parsing

def tokens(path):
    """Metamath tokens of a file, comments removed, read line by line"""
    comment = False
    with open(path, encoding='utf-8') as f:
        for line in f:
            for word in line.split():
                if comment:
                    comment = word != '$)'
                elif word == '$(':
                    comment = True
                elif word == '$[':
                    raise Exception("$[ includes are not supported")
                else:
                    yield word
    if comment:
        raise Exception(f"{path}: unterminated comment (a '$(' without '$)')")


def declarations(path, stop=None):
    """The $c and $v statements, in order (a first, cheap pass)"""
    toks, prev = tokens(path), None
    for t in toks:
        if t == stop and prev not in ('$c', '$v', '$d'):
            return
        if t in ('$c', '$v'):
            part = []
            for x in toks:
                if x == '$.':
                    break
                part.append(x)
            yield (t[1], part)
        prev = t


def parse(path, stop=None):
    """Assertions in order, as dicts, one at a time.

    An assertion records its mandatory hypotheses [(label, kind, toks)], and a
    $p its proof and the hypotheses ($f, $e) and $d pairs in scope."""
    toks = tokens(path)
    hyps = [[]]       # active $f/$e per scope: (label, kind, toks)
    dvs = [[]]        # active $d pairs per scope

    def upto(end):
        part = []
        for x in toks:
            if x == end:
                return part
            part.append(x)
        raise Exception(f"Missing '{end}'")

    for t in toks:
        if t == '${':
            hyps.append([])
            dvs.append([])
        elif t == '$}':
            hyps.pop()
            dvs.pop()
        elif t in ('$c', '$v'):
            upto('$.')
        elif t == '$d':
            vs = upto('$.')
            dvs[-1] += [frozenset((a, b)) for k, a in enumerate(vs) for b in vs[k + 1:]]
        else:
            label, kw = t, next(toks)
            if stop and label == stop:
                return
            if kw in ('$f', '$e'):
                hyps[-1].append((label, kw[1], upto('$.')))
            elif kw in ('$a', '$p'):
                stmt = upto('$=') if kw == '$p' else upto('$.')
                proof = upto('$.') if kw == '$p' else None
                active = [h for scope in hyps for h in scope]
                ess = [h for h in active if h[1] == 'e']
                mvars = {v for _, _, ts in ess for v in ts} | set(stmt)
                mand = [h for h in active if h[1] == 'e' or h[2][1] in mvars]
                fvars = {h[2][1] for h in mand if h[1] == 'f'}
                yield {'label': label, 'kind': kw[1], 'stmt': stmt, 'mand': mand,
                       'proof': proof, 'active': active,
                       'dv': {d for scope in dvs for d in scope if d <= fvars}}
            else:
                raise Exception(f"Unexpected '{label} {kw}'")


# ---------------------------------------------------------------- names

# Blocks whose lowercase letters are the same in every Python we know (the
# IPA block is not: U+0295 stopped being lowercase), Greek first
LETTER_BLOCKS = [(0x3b1, 0x3ca), (0xdf, 0x250), (0x370, 0x530), (0x561, 0x588),
                 (0x1e00, 0x2000), (0x1d41a, 0x1d800)]


def lowercase_pool(skip):
    """Single-code-point lowercase letters, non-ASCII, not in skip"""
    for a, b in LETTER_BLOCKS:
        for cp in range(a, b):
            ch = chr(cp)
            if unicodedata.category(ch) == 'Ll' and ch.islower() and ch not in skip:
                skip.add(ch)
                yield ch


def name_symbols(decls):
    decls = list(decls)
    consts = [c for kind, ts in decls if kind == 'c' for c in ts]
    vs = list(dict.fromkeys(v for kind, ts in decls if kind == 'v' for v in ts))

    enc, taken = {}, set(STRUCT_TOKENS)
    for n, c in enumerate(consts):
        cand = PRETTY.get(c, c.upper())
        if (cand in taken or '->' in cand or '#' in cand or '<?' in cand
                or any(ch.islower() for ch in cand)):
            cand = f'C{n}'
            while cand in taken:
                cand += "'"
        enc[c] = cand
        taken.add(cand)

    used = set()
    for v in vs:
        cand = GREEK.get(v) or (v.lower() if len(v) == 1 and v.lower().isascii() else None)
        if cand and cand.islower() and cand not in used:
            enc[v] = cand
            used.add(cand)
    pool = lowercase_pool(set(used))
    for v in vs:
        if v not in enc:
            enc[v] = next(pool)
            used.add(enc[v])
    fresh = [next(pool) for _ in range(128)]
    dummies = [next(pool) for _ in range(128)]
    struct = [ch for ch in 'abcdefghijklmnopqrstuvwxyz' if ch not in used]
    struct += list(pool)
    return enc, fresh, dummies, struct


# ---------------------------------------------------------------- output

def digest(text):
    return hashlib.blake2b(text.encode(), digest_size=16).digest()


class Writer:
    """Writes lines as they come; remembers terms and steps by digest"""
    def __init__(self, enc, fresh, dummies, struct, out):
        self.enc, self.fresh, self.dummies, self.out = enc, fresh, dummies, out
        self.G, self.C, self.A = struct[0], struct[1], struct[2:]
        self.terms, self.rules, self.memo, self.steps = {}, set(), {}, {}
        self.n = 0
        self.disj_consts, self.disj_rule = {}, {}

    def disj_const(self, tok):
        if tok not in self.disj_rule:
            rule = f'rDisjK{len(self.disj_rule)}'
            self.disj_rule[tok], self.disj_consts[rule] = rule, tok
        return self.structural(self.disj_rule[tok])

    def emit(self, line):
        print(line, file=self.out)

    def fresh_name(self, prefix):
        self.n += 1
        return f'{prefix}{self.n}!'

    def term(self, toks):
        """A theorem whose value is the token sequence: a literal term rule.
        Letters in it are left alone (nothing is substituted)."""
        text = ' '.join(toks)
        key = digest(text)
        if key not in self.terms:
            k = len(self.terms)
            self.emit(f'rTm{k} : {text}')
            self.emit(f'tm{k}! : rTm{k}')
            self.terms[key] = f'tm{k}!'
        return self.terms[key]

    def step(self, prefix, body):
        """A theorem line; equal bodies are shared (they name their context)"""
        key = digest(body)
        if key not in self.steps:
            self.steps[key] = self.fresh_name(prefix)
            self.emit(f'{self.steps[key]} : {body}')
        return self.steps[key]

    def ctx(self, hyps):
        return [t for k, h in enumerate(hyps) for t in (['⨾'] if k else []) + list(h)]

    def seq(self, hyps, concl):
        return ['⟦'] + self.ctx(hyps) + ['⟧', '⟹'] + list(concl)

    def structural(self, rule):
        """Declare a structural rule on first use"""
        if rule in self.rules:
            return rule
        self.rules.add(rule)
        G, C, A = self.G, self.C, self.A
        x, y, z = A[:3]
        if rule == 'rNode':
            self.emit(f'rNode : ⟪ {x} ⨾ {y} ⟫')
        elif rule == 'rLeaf':
            self.emit(f'rLeaf : ⟦ {x} ⟧ ⟹ {x}')
        elif rule == 'rInL':
            self.emit(f'rInL : ⟦ {x} ⟧ ⟹ {z} -> ⟦ ⟪ {x} ⨾ {y} ⟫ ⟧ ⟹ {z}')
        elif rule == 'rInR':
            self.emit(f'rInR : ⟦ {y} ⟧ ⟹ {z} -> ⟦ ⟪ {x} ⨾ {y} ⟫ ⟧ ⟹ {z}')
        elif rule.startswith('rFlat'):
            n = int(rule[5:])
            tree = self.tree_of(A[:n]) if n else ''
            self.emit(f"{rule} : ⟦ {tree} ⟧ ⟹ {C} -> {' '.join(self.seq(A[:n], C))}".replace('⟦  ⟧', '⟦ ⟧'))
        elif rule == 'rWeaken':
            self.emit(f'rWeaken : ⟦ ⟧ ⟹ {C} -> ⟦ {G} ⟧ ⟹ {C}')
        elif rule.startswith('rDisj'):
            d = lambda u, v: f'⟦ {G} ⟧ ⟹ DISJ ⟨ {u} ⟩ ⟨ {v} ⟩'
            if rule == 'rDisjCat':     # x y shares no variable with z if x and y don't
                self.emit(f"rDisjCat : {d(x, z)} -> {d(y, z)} -> {d(f'{x} {y}', z)}")
            elif rule == 'rDisjSym':
                self.emit(f'rDisjSym : {d(x, z)} -> {d(z, x)}')
            else:                      # a constant has no variables
                self.emit(f'{rule} : {d(self.disj_consts[rule], z)}')
        else:
            n, ctx = int(rule[6:].rstrip('E')), ('' if rule.endswith('E') else f' {G}')
            prem = ' -> '.join(f'⟦{ctx} ⟧ ⟹ {a}' for a in A[:n])
            self.emit(f"{rule} : {' '.join(self.seq(A[:n], C))} -> {prem} -> ⟦{ctx} ⟧ ⟹ {C}")
        return rule

    def tree_of(self, letters):
        if len(letters) == 1:
            return letters[0]
        h = len(letters) // 2
        return f'⟪ {self.tree_of(letters[:h])} ⨾ {self.tree_of(letters[h:])} ⟫'

    def instance(self, rule, subst):
        """rule with subst {var: toks}, applied simultaneously"""
        subst = {v: e for v, e in subst.items() if list(e) != [v]}
        key = digest(repr((rule, sorted((v, ' '.join(e)) for v, e in subst.items()))))
        if key in self.memo:
            return self.memo[key]
        order, left = [], dict(subst)
        while left:   # a key's value may only mention keys replaced before it
            ready = [v for v, e in left.items() if not any(w in e for w in left if w != v)]
            if not ready:
                break
            for v in ready:
                order.append(v)
                del left[v]
        if left:      # a cycle: rename every key to a fresh letter first
            ren = {v: self.fresh[k] for k, v in enumerate(subst)}
            rule = self.instance(rule, {v: [f] for v, f in ren.items()})
            subst = {ren[v]: e for v, e in subst.items()}
            order = list(subst)
        body = f"{rule} {';'.join(f'{v}={self.term(subst[v])}' for v in order)}".rstrip()
        self.memo[key] = self.step('tI', body)
        return self.memo[key]


def is_var(tok):
    return len(tok) == 1 and tok.islower()


def disj(u, v):
    return ['DISJ', '⟨', u, '⟩', '⟨', v, '⟩']


def translate(path, stop, out):
    enc, fresh, dummies, struct = name_symbols(declarations(path, stop))
    w = Writer(enc, fresh, dummies, struct, out)
    E = lambda ts: [enc[t] for t in ts]
    asserts, bad = {}, {}
    w.emit('# Translated from Metamath by mm2btp.py. Each theorem is a sequent')
    w.emit('# ⟦ hypotheses ⟧ ⟹ conclusion; letters stand for Metamath variables;')
    w.emit('# DISJ ⟨ x ⟩ ⟨ y ⟩ says x and y share no variable ($d).')

    for s in parse(path, stop):
        label = s['label']
        name = ('r' if s['kind'] == 'a' else 't') + label
        try:
            if s['kind'] == 'a':
                a = statement(s, E, [], set())
                w.emit(f"{name} : {' '.join(w.seq([e['toks'] for e in a['entries']], a['stmt']))}")
            else:
                a = prove(w, s, name, asserts, bad, E)
        except Unsupported as why:
            bad[label] = str(why)
            w.emit(f'# {label}: skipped ({why})')
            continue
        a['name'] = name
        asserts[label] = a
    return bad


def statement(s, E, dummy_floats, extra_dv):
    """An assertion's context: its $f/$e hypotheses, then floats of the dummy
    variables its proof (or the lemmas it uses) needs, then $d pairs as DISJ.
    Entries: {'kind': 'm' | 'df' | 'dv', 'toks': ..., and the letters}."""
    entries = []
    for _, kind, ts in s['mand']:
        entries.append({'kind': 'm', 'toks': E(ts), 'float': E(ts) if kind == 'f' else None})
    for tc, v in sorted(dummy_floats, key=lambda f: f[1]):
        entries.append({'kind': 'df', 'toks': [tc, v], 'var': v})
    pairs = {tuple(sorted(E(sorted(d)))) for d in s['dv']} | extra_dv
    for u, v in sorted(pairs):
        entries.append({'kind': 'dv', 'toks': disj(u, v), 'pair': (u, v)})
    return {'entries': entries, 'stmt': E(s['stmt']),
            'dummies': [(e['var'], e['toks'][0]) for e in entries if e['kind'] == 'df']}


def proof_steps(s):
    """The proof as ('label', L) / ('saved', k) / ('Z',) steps"""
    p = s['proof']
    if '?' in p:
        raise Unsupported('incomplete proof')
    if p[0] != '(':
        return [('label', t) for t in p]
    j = p.index(')')
    plist = [h[0] for h in s['mand']] + p[1:j]
    steps, n = [], 0
    for ch in ''.join(p[j + 1:]):
        if ch == 'Z':
            steps.append(('Z',))
        elif ch == '?':
            raise Unsupported('incomplete proof')
        elif 'U' <= ch <= 'Y':
            n = n * 5 + ord(ch) - ord('U') + 1
        else:
            n = n * 20 + ord(ch) - ord('A') + 1
            steps.append(('label', plist[n - 1]) if n <= len(plist) else ('saved', n - len(plist) - 1))
            n = 0
    return steps


def prove(w, s, name, asserts, bad, E0):
    mand = {h[0]: k for k, h in enumerate(s['mand'])}
    steps = proof_steps(s)
    # the proof's own dummies are renamed to the first letters of the dummy pool
    used = {h[0]: h[2] for h in s['active'] if h[1] == 'f'}
    used = [used[st[1]] for st in steps if st[0] == 'label' and st[1] not in mand and st[1] in used]
    own = {E0([ts[1]])[0]: w.dummies[k] for k, ts in enumerate(dict((t[1], t) for t in used).values())}
    E = lambda ts: [own.get(t, t) for t in E0(ts)]
    floats = {h[0]: E(h[2]) for h in s['active'] if h[1] == 'f'}
    mvars = {E(h[2])[1] for h in s['mand'] if h[1] == 'f'}
    own_tc = {own[E0([ts[1]])[0]]: E0([ts[0]])[0] for ts in used}
    mand_dv = {tuple(sorted(E(sorted(d)))) for d in s['dv']}

    def uses():
        """Replay the proof on statements only: yields (lemma, args, subst)"""
        stack, saved = [], []
        kinds.clear()
        kinds.update(own_tc)
        for step in steps:
            if step[0] == 'Z':
                saved.append(stack[-1])
                continue
            if step[0] == 'saved':
                stack.append(saved[step[1]])
                continue
            label = step[1]
            if label in mand or label in floats:
                toks = E(s['mand'][mand[label]][2]) if label in mand else floats[label]
                yield ('hyp', label, toks)
                stack.append(toks)
                continue
            if label in bad:
                raise Unsupported(f'uses {label}')
            a = asserts[label]
            ms = [e for e in a['entries'] if e['kind'] == 'm']
            args, stack = stack[len(stack) - len(ms):], stack[:len(stack) - len(ms)]
            subst = {}
            for e, val in zip(ms, args):
                if e['float']:
                    assert val[0] == e['float'][0], f'{s["label"]}: typecode mismatch at {label}'
                    if len(val) == 1:   # Budge values are never empty
                        raise Unsupported('empty expression')
                    subst[e['float'][1]] = val[1:]
            sub = lambda ts: [t for x in ts for t in subst.get(x, [x])]
            taken = set()
            for d, tc in a['dummies']:  # a lemma's dummy: the first pool letter its $d allow
                forbid = set(taken)
                for e in a['entries']:
                    if e['kind'] == 'dv' and d in e['pair']:
                        other = e['pair'][1 - e['pair'].index(d)]
                        if other in subst:
                            forbid |= set(filter(is_var, sub([other])))
                img = next(x for x in w.dummies if x not in forbid and kinds.get(x, tc) == tc)
                kinds[img] = tc
                taken.add(img)
                subst[d] = [img]
            for e, val in zip(ms, args):
                assert sub(e['toks']) == val, f'{s["label"]}: hypothesis mismatch at {label}'
            yield ('use', a, subst, sub)
            stack.append(sub(a['stmt']))
        assert len(stack) == 1 and stack[0] == E(s['stmt']), f"{s['label']}: wrong conclusion"

    # Pass 1: which dummy floats and $d pairs the proof needs
    kinds = {}    # dummy letter -> its typecode
    extra_dv = set()
    for u in uses():
        if u[0] != 'use':
            continue
        _, a, subst, sub = u
        for e in a['entries']:
            if e['kind'] == 'dv':
                for x in filter(is_var, sub([e['pair'][0]])):
                    for y in filter(is_var, sub([e['pair'][1]])):
                        if x == y:
                            raise Exception(f"{s['label']}: $d violated ({x}) at {a['name']}")
                        pair = tuple(sorted((x, y)))
                        if x in mvars and y in mvars and pair not in mand_dv:
                            raise Exception(f"{s['label']}: missing $d {x} {y} for {a['name']}")
                        if pair not in mand_dv:
                            extra_dv.add(pair)
    me = statement(s, E, {(tc, v) for v, tc in kinds.items()}, extra_dv)
    ctx = [e['toks'] for e in me['entries']]
    n = len(ctx)
    if n + 3 > len(w.A):
        raise Unsupported(f'{n} hypotheses, more than the letters available')
    index = {tuple(t): k for k, t in enumerate(ctx)}
    trees = {}

    def tree(lo, hi):
        """The term of the balanced tree of entries lo..hi"""
        if (lo, hi) not in trees:
            h = lo + (hi - lo) // 2
            trees[lo, hi] = (w.term(ctx[lo]) if hi - lo == 1 else
                             w.step('tT', f"{w.structural('rNode')} {w.A[0]}={tree(lo, h)};{w.A[1]}={tree(h, hi)}"))
        return trees[lo, hi]

    G = tree(0, n) if ctx else None

    def spec(prefix, rule, reps, hyps=()):
        return w.step(prefix, f"{rule} {reps} {' '.join(hyps)}".rstrip())

    def hyp(toks, lo=0, hi=None):
        """⟦ subtree of entries lo..hi ⟧ ⟹ toks, down the tree to its leaf"""
        hi = n if hi is None else hi
        k = index[tuple(toks)]
        x, y, z = w.A[:3]
        if hi - lo == 1:
            return spec('tH', w.structural('rLeaf'), f'{x}={w.term(toks)}')
        h = lo + (hi - lo) // 2
        side, inner = ('rInL', hyp(toks, lo, h)) if k < h else ('rInR', hyp(toks, h, hi))
        reps = f'{x}={tree(lo, h)};{y}={tree(h, hi)};{z}={w.term(toks)}'
        return spec('tH', w.structural(side), reps, [inner])

    def disjoint(e1, e2):
        """Prove DISJ ⟨ e1 ⟩ ⟨ e2 ⟩ from the context's DISJ pairs"""
        if not ctx:
            raise Unsupported('$d without hypotheses')
        x, y, z = w.A[:3]
        if len(e1) > 1:
            h = len(e1) // 2
            reps = f'{w.G}={G};{x}={w.term(e1[:h])};{y}={w.term(e1[h:])};{z}={w.term(e2)}'
            return spec('tD', w.structural('rDisjCat'), reps, [disjoint(e1[:h], e2), disjoint(e1[h:], e2)])
        if not is_var(e1[0]):
            return spec('tD', w.disj_const(e1[0]), f'{w.G}={G};{z}={w.term(e2)}')
        if len(e2) > 1 or not is_var(e2[0]) or tuple(disj(e1[0], e2[0])) not in index:
            if tuple(disj(e2[0], e1[0])) in index and len(e2) == 1:
                inner = hyp(disj(e2[0], e1[0]))
            else:
                inner = disjoint(e2, e1)
            return spec('tD', w.structural('rDisjSym'), f'{w.G}={G};{x}={w.term(e2)};{z}={w.term(e1)}', [inner])
        return hyp(disj(e1[0], e2[0]))

    # Pass 2: the proof
    stack, saved, proofs = [], [], iter(uses())
    for step in steps:
        if step[0] == 'Z':
            saved.append(stack[-1])
            continue
        if step[0] == 'saved':
            stack.append(saved[step[1]])
            continue
        u = next(proofs)
        if u[0] == 'hyp':
            stack.append(hyp(u[2]))
            continue
        _, a, subst, sub = u
        ms = [e for e in a['entries'] if e['kind'] == 'm']
        args, stack = stack[len(stack) - len(ms):], stack[:len(stack) - len(ms)]
        prems = iter(args)
        prem = [next(prems) if e['kind'] == 'm' else hyp(sub(e['toks'])) if e['kind'] == 'df'
                else disjoint(sub([e['pair'][0]]), sub([e['pair'][1]])) for e in a['entries']]
        hyps, concl = [sub(e['toks']) for e in a['entries']], sub(a['stmt'])
        inst = w.instance(a['name'], subst)
        m = len(hyps)
        if m == 0 and n == 0:
            result = inst
        elif m == 0:
            result = spec('tS', w.structural('rWeaken'), f'{w.G}={G};{w.C}={w.term(concl)}', [inst])
        else:
            rule = w.structural(f'rApply{m}' + ('' if n else 'E'))
            reps = [f'{w.G}={G}'] if n else []
            reps += [f'{w.C}={w.term(concl)}'] + [f'{x}={w.term(h)}' for x, h in zip(w.A, hyps)]
            result = spec('tS', rule, ';'.join(reps), [inst] + prem)
        stack.append(result)

    letters = w.A[:n]   # the statement: Γ as a flat list again
    reps = ';'.join([f'{w.C}={w.term(me["stmt"])}'] + [f'{x}={w.term(h)}' for x, h in zip(letters, ctx)])
    w.emit(f"{name} : {w.structural(f'rFlat{n}')} {reps} {stack[0]}")
    return me


def main():
    args = sys.argv[1:]
    usage = f"Usage: python {sys.argv[0]} [--stop LABEL] <filename.mm> > <filename.btp>"
    stop = None
    if '--stop' in args:
        i = args.index('--stop')
        if i + 1 >= len(args):
            sys.exit(usage)
        stop = args[i + 1]
        del args[i:i + 2]
    if len(args) != 1:
        sys.exit(usage)
    bad = translate(args[0], stop, sys.stdout)
    if bad:
        print(f'{len(bad)} assertions skipped', file=sys.stderr)


if __name__ == '__main__':
    main()
