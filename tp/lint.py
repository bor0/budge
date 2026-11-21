#!/usr/bin/env python3
"""Lint for Budge-TP files: what the checker accepts but is probably a mistake.

    python3 lint.py examples/*.btp examples/lib/*.btp

Each file is checked by budge-tp.py, in an environment of its own. Then, for
the rules and theorems written in the given files, it lists

  rules never applied   no file given applies the rule, so a mistake in it
                        would go unnoticed
  theorems never used   hidden theorems (name ending in !) that no file given
                        refers to
  letters not there     a replacement x=T whose letter is in none of the
                        texts it is applied to

A library's rules and terms are there for other files: give those files too,
as above. Lines that a Python block prints count as uses, but are not looked
at themselves (what a block prints depends on what was loaded before it).
This is advice, not checking: the exit status is 0 if the files check,
whatever is listed.
"""
import importlib.util
import os
import re
import sys
from collections import defaultdict

WHERE = re.compile(r'(.*):(\d+)( \(generated line \d+\))?')
KINDS = ('rules never applied', 'theorems never used', 'letters not there')


def checker():
    """budge-tp.py, next to this file, as a module"""
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'budge-tp.py')
    spec = importlib.util.spec_from_file_location('budge_tp', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(btp, path):
    """The environment of a file, checked. The modules its blocks brought in
    from the directories they added to sys.path (tactics.py) are forgotten
    again: they keep tables that a file adds to, so each file starts afresh."""
    modules, search = set(sys.modules), list(sys.path)
    env = btp.new_environment()
    try:
        btp.check(env, path)
    finally:
        added = {os.path.realpath(p) for p in sys.path if p not in search}
        for name, module in list(sys.modules.items()):
            file = getattr(module, '__file__', None)
            if name not in modules and file and os.path.dirname(os.path.realpath(file)) in added:
                del sys.modules[name]
        sys.path[:] = search
    return env


def key(env, name):
    """(file, line, name) of a rule or theorem written in a file; None if a
    block printed it"""
    path, line, generated = WHERE.fullmatch(env['where'][name]).groups()
    return None if generated else (os.path.realpath(path), int(line), name)


def references(spec):
    return [spec['rule'], *spec['replacements'].values(), *spec['hypotheses']]


def idle_letters(env, spec):
    """The replaced letters that are in no text when their turn comes: not in
    the rule, the hypotheses given, or a value put in before"""
    rule = env['rules'].get(spec['rule'])
    texts = rule['hypotheses'] + [rule['conclusion']] if rule else [env['theorems'][spec['rule']]]
    texts = texts + [env['theorems'][name] for name in spec['hypotheses']]
    idle = []
    for letter, name in spec['replacements'].items():
        if not any(letter in text for text in texts):
            idle.append(letter)
        texts = [text.replace(letter, env['theorems'][name]) for text in texts]
    return idle


def lint(btp, paths):
    """Findings as {file: {kind: [text]}}, for what is written in the files"""
    rules, theorems, used, idle = set(), set(), set(), {}
    for path in paths:
        env = check(btp, path)
        rules.update(key(env, name) for name in env['rules'])
        for name, spec in env['specs'].items():
            used.update(key(env, ref) for ref in references(spec))
            if key(env, name) not in theorems:
                theorems.add(key(env, name))
                idle[key(env, name)] = idle_letters(env, spec)
    found = defaultdict(lambda: defaultdict(list))
    for file, line, name in sorted((rules | theorems) - {None}):
        this = (file, line, name)
        if this not in used and this in rules:
            found[file][KINDS[0]].append(f'{name} ({line})')
        if this not in used and this in theorems and name.endswith('!'):
            found[file][KINDS[1]].append(f'{name} ({line})')
        if idle.get(this):
            letters = ' '.join(letter + '=' for letter in idle[this])
            found[file][KINDS[2]].append(f'{letters} in {name} ({line})')
    return found


def main():
    paths = sys.argv[1:]
    if not paths or paths[0] in ('-h', '--help'):
        sys.exit(__doc__.strip())
    try:
        found = lint(checker(), paths)
    except Exception as error:
        sys.exit(str(error))
    for file in sorted(found):
        here = os.path.relpath(file)
        print(file if here.startswith('..') else here)
        for kind in KINDS:
            if found[file][kind]:
                print(f"  {kind}: {', '.join(found[file][kind])}")
    counts = [sum(len(kinds[kind]) for kinds in found.values()) for kind in KINDS]
    files = f"{len(paths)} file{'' if len(paths) == 1 else 's'}"
    print(f'{files}: ' + ', '.join(f'{n} {kind}' for n, kind in zip(counts, KINDS)))


if __name__ == '__main__':
    main()
