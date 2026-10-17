#!/usr/bin/env python3
"""Budge-TP's rule application, as a Budge-PL program.

budge-tp checks a theorem `tFoo : rBar x=T1;y=T2 h1 h2` by substituting the values of T1,
T2 for the variables x, y (Python's .replace(), in order), requiring the rule's hypotheses
to equal h1, h2's values (substituted too), and returning the conclusion. Here that step is
a Budge-PL program, generated with budge_pl.py's macro assembler, one per shape (number of
replacements and hypotheses, alphabet size), and run by its interpreter. Everything else,
the parser, the theorem table and the output, is budge-tp.py's own, so the output can be
diffed against it.

Pure Budge-TP only: `<?py load('...') ?>` is an include; other Python blocks are errors.

Strings are numbers: bijective base B over the symbols of the application (digits 1..B),
first character least significant, so equal strings are equal numbers.

Usage: python3 budge-tp-pl.py [--dump] [--tp path/to/budge-tp.py] <file.btp>
"""
import importlib.util
import os
import re
import sys
import time

sys.dont_write_bytecode = True  # importing budge-tp.py would leave __pycache__ in tp/
from budge_pl import STEPS, Asm, build, pop_shape, show, size

def encode(s, alphabet):
    n, B = 0, len(alphabet)
    for c in reversed(s):
        n = n * B + alphabet.index(c) + 1
    return n

def decode(n, alphabet):
    s, B = '', len(alphabet)
    while n:
        d = n % B or B
        n = (n - d) // B
        s += alphabet[d - 1]
    return s

# The program for k replacements and h hypotheses. Inputs: the rule's hypotheses H, its
# conclusion C, the replacements V := X in order, the given theorems' values P. Each P is
# substituted too, as budge-tp does. Outputs: OUT, the conclusion; FAIL = 1 if some
# H ≠ P.

PROGRAMS = {}

def apply_program(k, h, B):
    if (k, h, B) in PROGRAMS:
        return PROGRAMS[(k, h, B)]
    a = Asm(B)
    C, OUT, FAIL = a.reg(), a.reg(), a.reg()
    H = [a.reg() for _ in range(h)]
    P = [a.reg() for _ in range(h)]
    VX = [(a.reg(), a.reg()) for _ in range(k)]
    code = []
    for p in P:
        for v, x in VX:
            code += a.subst(p, v, x)
    for v, x in VX:
        for s in H + [C]:
            code += a.subst(s, v, x)
    e = a.reg()
    for hr, p in zip(H, P):
        code += a.eq(hr, p, e) + a.if_else(e, lambda: [], lambda: [FAIL]) + a.zero(e)
    code += a.move(C, OUT)
    regs = dict(C=C, OUT=OUT, FAIL=FAIL, H=H, P=P, VX=VX)
    PROGRAMS[(k, h, B)] = (code, build(code, pop_shape(B)), regs, a.top)
    return PROGRAMS[(k, h, B)]

# budge-tp.py, with rule application replaced and Python blocks limited to load().

def budge_apply(env, theorem, name):
    reps = dict(theorem['replacements'])
    rule = theorem['rule']
    if rule in env['rules']:
        hyps, concl = env['rules'][rule]['hypotheses'], env['rules'][rule]['conclusion']
    elif rule in env['theorems']:
        hyps, concl = [], env['theorems'][rule]
    else:
        raise Exception(f"Invalid rule/theorem: '{rule}'")
    for key, value in reps.items():
        if not value or value not in env['theorems']:
            raise Exception(f"Invalid theorem: '{value}' in '{name}'")
        reps[key] = env['theorems'][value]
    given = []
    for hyp in theorem['hypotheses']:
        if hyp not in env['theorems']:
            raise Exception(f"Invalid theorem: '{hyp}' in '{name}'")
        given.append(env['theorems'][hyp])
    if len(hyps) != len(given):
        raise Exception(f"Hypotheses mismatch for '{name}': "
                        f"{len(hyps)} expected, {len(given)} given")

    texts = hyps + [concl] + given + list(reps) + list(reps.values())
    alphabet = sorted(set(''.join(texts)))
    _, run, regs, top = apply_program(len(reps), len(hyps), len(alphabet))
    R = [0] * (top + 1)
    R[regs['C']] = encode(concl, alphabet)
    for r, s in zip(regs['H'], hyps):
        R[r] = encode(s, alphabet)
    for r, s in zip(regs['P'], given):
        R[r] = encode(s, alphabet)
    for (v, x), (key, value) in zip(regs['VX'], reps.items()):
        R[v], R[x] = alphabet.index(key) + 1, encode(value, alphabet)
    run(R)
    if R[regs['FAIL']]:
        raise Exception(f"Hypotheses mismatch for '{name}'")
    return decode(R[regs['OUT']], alphabet)

def load_tp(path):
    spec = importlib.util.spec_from_file_location('budge_tp', path)
    tp = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(tp)

    def run_python(env, code, path, where, stack, loads):
        m = re.fullmatch(r"load\('([^']+)'\)", code.strip())
        if not m:
            raise Exception(f"{where}: Python blocks are not supported, only load('...')")
        full = os.path.join(os.path.dirname(path), m.group(1))
        if not os.path.isfile(full):
            raise Exception(f"File not found: '{m.group(1)}'")
        tp.load_file(env, full, False, stack)
        tp.check_pending(env)
        loads.append(m.group(1))
        return ''

    tp.apply_rule_or_theorem = budge_apply
    tp.run_python = run_python
    return tp

def main():
    args = sys.argv[1:]
    dump = '--dump' in args
    args = [a for a in args if a != '--dump']
    tp_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), '../../tp/budge-tp.py')
    if '--tp' in args:
        i = args.index('--tp')
        tp_path = args[i + 1]
        del args[i:i + 2]
    if len(args) != 1:
        sys.exit(__doc__.strip().splitlines()[-1])
    tp = load_tp(tp_path)
    sys.argv = [sys.argv[0], args[0]]
    start = time.time()
    try:
        tp.main()
    finally:
        print(f'[budge-pl] {len(PROGRAMS)} programs, {STEPS[0]} steps, '
              f'{time.time() - start:.1f}s', file=sys.stderr)
        if dump:
            for (k, h, B), p in sorted(PROGRAMS.items()):
                print(f'[budge-pl] {k} reps, {h} hyps, B={B}: {size(p[0])} instructions, '
                      f'{p[3]} registers\n{show(p[0])}', file=sys.stderr)

if __name__ == '__main__':
    main()
