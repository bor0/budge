"""Extraction: Python from a checked Hoare triple (lib/hoare.btp).

A <?py ... ?> block after the proof calls

    write_py(env, 'thProgram', 'count_odd_below', 'hoare.py', __file__)

which reads the *checked* value of the theorem from env (not the Python
terms the proof was built from), so the Python is the program Budge verified.
Program variables ($I, $N, ...) are Python variables without the $; the ones read
but never assigned are the function's parameters, the assigned ones the
postcondition mentions are its result. Pre- and postcondition become
asserts, or comments if they can't run (quantifiers).

Trusted, as in Coq's extraction: the table below, which reads library
symbols as Python on natural numbers (MOD2 as % 2, DIV2 as // 2, MOD as %,
LE as <=, which agree with the library's definitions where the program uses them), and
termination, which partial correctness does not give. A symbol not in the
table is an error, never passed through.
"""
import os

from tactics import parse

TERMS = {
    'S': lambda x: f'{x} + 1',
    'ADD': lambda x, y: f'{x} + {y}',
    'MUL': lambda x, y: f'{x} * {y}',
    'MOD': lambda x, y: f'{x} % {y}',
    'MOD2': lambda x: f'{x} % 2',
    'DIV2': lambda x: f'{x} // 2',
    'EQ': lambda x, y: f'{x} == {y}',
    'LE': lambda x, y: f'{x} <= {y}',
    'NOT': lambda x: f'not {x}',
    'AND': lambda x, y: f'{x} and {y}',
    'OR': lambda x, y: f'{x} or {y}',
    'IMP': lambda x, y: f'not {x} or {y}',
}


def numeral(t):
    """S(S(0)) -> 2, or None if t is not a closed numeral"""
    n = 0
    while isinstance(t, tuple) and t[0] == 'S':
        t, n = t[1], n + 1
    return n if t == '0' else None


def py_term(t):
    if numeral(t) is not None:
        return str(numeral(t))
    if t == '⊤':
        return 'True'
    if isinstance(t, str):
        if t.startswith('$') and t[1:].isalnum():
            return t[1:]
        raise ValueError(f"No Python for atom '{t}'")
    if t[0] not in TERMS:
        raise ValueError(f"No Python for symbol '{t[0]}'")

    def arg(a):
        s = py_term(a)
        return s if isinstance(a, str) or numeral(a) is not None else f'({s})'
    return TERMS[t[0]](*map(arg, t[1:]))


def expr(s):
    return py_term(parse(s))


def matching(s, i, open_, close):
    """Index just past the bracket closing the one at s[i]"""
    depth = 0
    for j in range(i, len(s)):
        depth += {open_: 1, close: -1}.get(s[j], 0)
        if depth == 0:
            return j + 1
    raise ValueError(f"Unbalanced '{open_}' in '{s}'")


def commands(s):
    """Parse the program text of lib/hoare.btp into a list of commands:
    ('ASG', x, e), ('SKIP',), ('IF', b, [..], [..]), ('WHILE', b, [..])"""
    out, i = [], 0

    def block(i):
        assert s.startswith('{ ', i), (s, i)
        end = matching(s, i, '{', '}')
        return commands(s[i + 2:end - 2]), end

    while i < len(s):
        if s[i] == ' ':
            i += 1
        elif s.startswith(';', i):
            out.append(('SKIP',))
            i += 1
        elif s.startswith('IF (', i) or s.startswith('WHILE (', i):
            kw = s[i:s.index(' ', i)]
            start = i + len(kw) + 1
            end = matching(s, start, '(', ')')
            cond = s[start + 1:end - 1]
            body, i = block(end + 1)
            if kw == 'IF':
                assert s.startswith(' ELSE ', i), (s, i)
                other, i = block(i + 6)
                out.append(('IF', cond, body, other))
            else:
                out.append(('WHILE', cond, body))
        else:
            end = s.index(';', i)
            x, e = s[i:end].split(' = ')
            out.append(('ASG', x, e))
            i = end + 1
    return out


def variables(t, acc):
    if isinstance(t, str):
        if t.startswith('$'):
            acc.add(t)
    else:
        for a in t[1:]:
            variables(a, acc)
    return acc


def scan(cmds, read, written):
    for c in cmds:
        if c[0] == 'ASG':
            written.add(c[1])
            variables(parse(c[2]), read)
        elif c[0] != 'SKIP':
            variables(parse(c[1]), read)
            for body in c[2:]:
                scan(body, read, written)


def emit(cmds, indent):
    pad = '    ' * indent
    lines = []
    for c in cmds:
        if c[0] == 'ASG':
            lines.append(f'{pad}{c[1][1:]} = {expr(c[2])}')
        elif c[0] == 'IF':
            lines.append(f'{pad}if {expr(c[1])}:')
            lines += emit(c[2], indent + 1) or [pad + '    pass']
            other = emit(c[3], indent + 1)
            if other:
                lines += [f'{pad}else:'] + other
        elif c[0] == 'WHILE':
            lines.append(f'{pad}while {expr(c[1])}:')
            lines += emit(c[2], indent + 1) or [pad + '    pass']
    return lines


def triple(value):
    """'{p} c {q}' -> (p, c, q); assertions contain no braces"""
    assert value.startswith('{'), value
    i = value.index('} ')
    j = value.rindex(' {')
    return value[1:i], value[i + 2:j], value[j + 2:-1]


def check(assertion, what):
    """An assert, or a comment if the assertion can't run"""
    try:
        return f'    assert {expr(assertion)}'
    except ValueError:
        return f'    # {what} (proved, not executable): {assertion}'


def to_py(name, function, value):
    pre, prog, post = triple(value)
    cmds = commands(prog)
    read, written = set(), set()
    scan(cmds, read, written)
    params = [p[1:] for p in sorted(read - written | variables(parse(pre), set()) - written)]
    results = [r[1:] for r in sorted(written & variables(parse(post), set()))]
    if not results:
        raise ValueError(f"'{name}': the postcondition mentions no assigned variable")

    lines = [f'# Extracted by budge-tp from the checked theorem {name}:',
             f'#   {value}',
             '# Partial correctness: if it returns, the postcondition holds.',
             '',
             '',
             f"def {function}({', '.join(p + ': int' for p in params)}):"]
    for p in params:        # the proof is about natural numbers
        lines.append(f"    if {p} < 0:\n        raise ValueError('{p} < 0')")
    if pre != '⊤':
        lines.append(check(pre, 'precondition'))
    lines += emit(cmds, 1)
    lines += [check(post, 'postcondition'), f"    return {', '.join(results)}", '']
    return '\n'.join(lines)


def write_py(env, name, function, target, here):
    """Write the Python for the checked Hoare triple `name` to `target`
    (relative to the file `here`)"""
    if name not in env['theorems']:
        raise ValueError(f"'{name}' is not a checked theorem")
    path = os.path.join(os.path.dirname(here), target)
    with open(path, 'w', encoding='utf-8') as file:
        file.write(to_py(name, function, env['theorems'][name]))
