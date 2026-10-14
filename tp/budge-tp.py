#!/usr/bin/python3
# -*- coding: utf-8 -*-

import contextlib
import io
import os
import sys
from os.path import dirname, exists, isfile, join, realpath


def parse_rule(expr):
    """Split a rule into its hypotheses and conclusion"""
    rule = list(map(str.strip, expr.split('->')))
    return {'hypotheses': rule[:-1], 'conclusion': rule[-1]}


def parse_replacements(theorem_name, replacements):
    """Parse all replacements for a theorem"""
    parsed_replacements = {}

    if replacements is None:
        return parsed_replacements

    replacements = list(filter(lambda x: x, replacements.split(';')))

    # Parses "x=X,y=Y,..." into a dictionary for easier substitution, checking
    # syntax on the way
    for expr in replacements:
        replacement = expr.split('=', 1)

        if len(replacement) < 2 or len(
                replacement[0]) != 1 or not replacement[0].islower():
            raise Exception(
                f"Invalid syntax for replacement '{expr}' in '{theorem_name}'")

        parsed_replacements[replacement[0]] = replacement[1]

    return parsed_replacements


def parse_theorem(name, expr):
    """Parse a theorem: the rule applied, its replacements and hypotheses"""
    arguments = list(filter(lambda x: x, expr.split(' ')))

    if len(arguments) < 1:
        raise Exception(f"Invalid syntax for theorem '{name}'")

    rule = arguments[0]
    replacements = arguments[1] if len(arguments) > 1 else None
    hypotheses = arguments[2:] if len(arguments) > 2 else []

    return {'rule': rule, 'replacements': parse_replacements(name, replacements),
            'hypotheses': hypotheses}


def new_environment():
    """An empty environment. Rules and theorems are parsed as they are read,
    and theorems are derived (checked) in source order: before a Python block
    runs, and at the end."""
    return {'rules': {}, 'theorems': {}, 'specs': {}, 'pending': [],
            'prose': {}, 'order': [], 'where': {}, 'loaded': set(),
            'expanded': {}, 'namespaces': {}}


def add_line(env, raw_line, where, visible):
    """Process one line of Budge code"""
    line = raw_line.split('#')[0].strip()  # strip comments and whitespace
    if not line:
        return

    types = {'r': 'rules', 't': 'theorems', 'p': 'prose'}
    parsed_line = list(filter(lambda x: x, map(str.strip, line.split(':', 1))))

    if len(parsed_line) != 2:
        raise Exception(f"{where}: Invalid syntax: '{line}'")

    [name, expr] = parsed_line

    if name[0] not in types:
        raise Exception(f"{where}: Invalid variable name: '{name}'")

    tip = types[name[0]]

    table = env['specs'] if tip == 'theorems' else env[tip]
    if name in table:
        raise Exception(f"{where}: Name redeclaration: '{name}' "
                        f"(first declared at {env['where'][name]})")
    env['where'][name] = where

    if tip == 'rules':
        env['rules'][name] = parse_rule(expr)
    elif tip == 'theorems':
        env['specs'][name] = parse_theorem(name, expr)
        env['pending'].append(name)
    else:
        env['prose'][name] = expr

    if tip in ('theorems', 'prose'):
        env['order'].append((tip, name, visible))


def check_pending(env):
    """Derive every theorem read so far, in source order"""
    for theorem_name in env['pending']:
        try:
            env['theorems'][theorem_name] = apply_rule_or_theorem(
                env, env['specs'][theorem_name], theorem_name)
        except Exception as error:
            raise Exception(
                f"{env['where'][theorem_name]}: {error}") from None
    env['pending'] = []


def run_python(env, code, path, where, stack, loads):
    """Run a <?py ... ?> block; what it prints is Budge code.

    The block runs with __file__ (this .btp file), env (what has been read
    and checked so far) and load(path) defined. load reads and checks another
    file (path relative to this one) once: its rules and theorems become
    available here, its theorems and prose are not printed. Blocks of one
    file share their namespace."""
    def load(target):
        full = join(dirname(path), target)
        if not isfile(full):
            raise Exception(f"File not found: '{target}'")
        load_file(env, full, False, stack)
        check_pending(env)
        loads.append(target)

    namespace = env['namespaces'].setdefault(realpath(path), {'__file__': path})
    namespace['env'], namespace['load'] = env, load
    output = io.StringIO()
    try:
        with contextlib.redirect_stdout(output):
            exec(compile(code, f"{path} (Python block at {where})", 'exec'), namespace)
    except Exception as error:
        raise Exception(f"{where}: Python block failed: "
                        f"{type(error).__name__}: {error}") from error
    return output.getvalue().rstrip('\n')


def load_file(env, path, visible=True, stack=None):
    """Read rules, theorems, prose and Python blocks from a file.

    Loaded files (load() in a block) share one namespace, are loaded once even
    if loaded more than once, and their theorems and prose are not printed.
    """
    stack = stack or []
    real = realpath(path)

    if real in stack:
        raise Exception(f"Load cycle: '{path}'")
    if real in env['loaded']:
        return

    env['loaded'].add(real)
    stack.append(real)

    with open(path, encoding='utf-8') as file:
        lines = file.read().split('\n')

    expanded = []

    def splice(code, where):
        """Run a block, check its output, and record what --expand writes."""
        check_pending(env)
        loads = []
        output = run_python(env, code, path, where, stack, loads)
        for k, out_line in enumerate(output.split('\n'), 1):
            add_line(env, out_line, f"{where} (generated line {k})", visible)
        for target in loads:        # loads stay in the expansion
            expanded.append(f"<?py load('{target}') ?>")
        if output:
            expanded.append(output)

    i = 0
    while i < len(lines):
        where = f"{path}:{i + 1}"
        stripped = lines[i].strip()
        if stripped.startswith('<?py') and stripped.endswith('?>') and len(stripped) > 6:
            splice(stripped[4:-2].strip(), where)        # one-line block
            i += 1
            continue
        if stripped == '<?py':
            end = i + 1
            while end < len(lines) and lines[end].strip() != '?>':
                end += 1
            if end == len(lines):
                raise Exception(f"{where}: Unterminated Python block")
            splice('\n'.join(lines[i + 1:end]), where)
            i = end + 1
            continue
        add_line(env, lines[i], where, visible)
        expanded.append(lines[i])
        i += 1

    env['expanded'][real] = (path, '\n'.join(expanded))
    stack.pop()


def check_environment(env):
    """Derive every remaining theorem"""
    check_pending(env)
    return env


def write_expanded(env, main_path, out_dir):
    """Write every loaded file, Python blocks replaced by their output, into
    out_dir (same layout relative to the main file), so the copies check
    without running any Python."""
    base = dirname(realpath(main_path))
    for real, (path, text) in env['expanded'].items():
        rel = os.path.relpath(real, base)
        if rel.startswith('..'):
            raise Exception(f"Cannot expand '{path}': outside '{base}'")
        target = join(out_dir, rel)
        os.makedirs(dirname(target), exist_ok=True)
        with open(target, 'w', encoding='utf-8') as file:
            file.write(text)


def apply_rule_or_theorem(env, theorem, theorem_name):
    """Main method used to apply a rule or a theorem"""
    replacements = dict(theorem['replacements'])
    th_hypotheses = list(theorem['hypotheses'])
    rule = theorem['rule']

    if rule in env['rules']:
        ru_hypotheses = env['rules'][rule]['hypotheses'].copy()
        ru_conclusion = env['rules'][rule]['conclusion']
    elif rule in env['theorems']:
        ru_hypotheses = []
        ru_conclusion = env['theorems'][rule]
    else:
        raise Exception(f"Invalid rule/theorem: '{rule}'")

    for key, value in replacements.items():
        if not value or value not in env['theorems']:
            raise Exception(f"Invalid theorem: '{value}' in '{theorem_name}'")

        replacements[key] = env['theorems'][value]

        if not isinstance(replacements[key], str):
            raise Exception(f"Invalid theorem: '{value}' in '{theorem_name}'")

    # Process theorem's hypotheses by substituting for other theorems
    for i, hypo in enumerate(th_hypotheses):
        if hypo not in env['theorems']:
            raise Exception(f"Invalid theorem: '{hypo}' in '{theorem_name}'")
        hypothesis = env['theorems'][hypo]

        for key, value in replacements.items():
            hypothesis = hypothesis.replace(key, value)

        th_hypotheses[i] = hypothesis

    for key, value in replacements.items():
        # Process rule's hypotheses by substituting the replacements
        for i, _ in enumerate(ru_hypotheses):
            ru_hypotheses[i] = ru_hypotheses[i].replace(key, value)

        # Process conclusion by substituting the replacements
        ru_conclusion = ru_conclusion.replace(key, value)

    if ru_hypotheses != th_hypotheses:
        raise Exception(
            f"Hypotheses mismatch for '{theorem_name}': cannot unify\n\t{str(ru_hypotheses)}\nand\n\t{str(th_hypotheses)}")

    return ru_conclusion


def main():
    """Entrypoint"""
    args = sys.argv[1:]
    out_dir = None
    if '--expand' in args:
        i = args.index('--expand')
        if i + 1 >= len(args):
            sys.exit("--expand needs a directory")
        out_dir = args[i + 1]
        del args[i:i + 2]

    if len(args) != 1:
        sys.exit(f"Usage: python {sys.argv[0]} [--expand DIR] <filename.btp>")

    if not exists(args[0]):
        sys.exit(f"Filename '{args[0]}' not found.")

    if not isfile(args[0]):
        sys.exit(f"Not a filename: '{args[0]}'.")

    env = new_environment()
    load_file(env, args[0])
    check_environment(env)

    if out_dir is not None:
        write_expanded(env, args[0], out_dir)

    for kind, name, visible in env['order']:
        if not visible or name[-1] == '!':
            continue
        if kind == 'prose':
            print(f"-- {env['prose'][name]}")
        else:
            print(f"{name} : {env['theorems'][name]}")


if __name__ == '__main__':
    sys.exit(main())
