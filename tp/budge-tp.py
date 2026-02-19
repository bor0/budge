#!/usr/bin/python3
# -*- coding: utf-8 -*-

import sys
from os.path import exists, isfile


def parse_rules(rules):
    """Given a list of rules, parse their hypotheses and conclusion"""
    parsed_rules = {}

    # Split rules into hypotheses and conclusion
    for name in rules:
        rule = list(map(str.strip, rules[name].split('->')))
        parsed_rules[name] = {'hypotheses': rule[:-1],
                              'conclusion': rule[-1]}

    return parsed_rules


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


def parse_theorems(theorems):
    """Parse all theorems"""
    parsed_theorems = {}

    # Process theorems, checking for valid syntax and process replacements on
    # the way
    for name in theorems:
        arguments = list(filter(lambda x: x, theorems[name].split(' ')))

        if len(arguments) < 1:
            raise Exception(f"Invalid syntax for theorem '{name}'")

        rule = arguments[0]
        replacements = arguments[1] if len(arguments) > 1 else None
        hypotheses = arguments[2:] if len(arguments) > 2 else []

        parsed_theorems[name] = {'rule': rule, 'replacements': parse_replacements(
            name, replacements), 'hypotheses': hypotheses}

    return parsed_theorems


def calculate_environment(code):
    """Calculate rules, theorems, prose"""
    env = {'rules': {}, 'theorems': {}, 'prose': {}, 'order': []}
    types = {'r': 'rules', 't': 'theorems', 'p': 'prose'}

    # Process every line in the code, checking for valid syntax and storing
    # the data for further parsing
    for lineno, raw_line in enumerate(code.split('\n'), 1):
        line = raw_line.split('#')[0].strip()  # strip comments and whitespace
        if not line:
            continue

        parsed_line = list(
            filter(lambda x: x, map(str.strip, line.split(':', 1))))

        if len(parsed_line) != 2:
            raise Exception(f"Line {lineno}: Invalid syntax: '{line}'")

        [name, expr] = parsed_line

        if name[0] not in types:
            raise Exception(f"Line {lineno}: Invalid variable name: '{name}'")

        tip = types[name[0]]

        if name in env[tip]:
            raise Exception(f"Line {lineno}: Name redeclaration: '{name}'")

        env[tip][name] = expr

        if tip in ('theorems', 'prose'):
            env['order'].append((tip, name))

    env['rules'] = parse_rules(env['rules'])
    env['theorems'] = parse_theorems(env['theorems'])

    return env


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
    if len(sys.argv) != 2:
        sys.exit(f"Usage: python {sys.argv[0]} <filename.btp>")

    if not exists(sys.argv[1]):
        sys.exit(f"Filename '{sys.argv[1]}' not found.")

    if not isfile(sys.argv[1]):
        sys.exit(f"Not a filename: '{sys.argv[1]}'.")

    with open(sys.argv[1], encoding='utf-8') as file:
        code = file.read()

    env = calculate_environment(code)

    for theorem_name in env['theorems']:
        theorem = env['theorems'][theorem_name]
        env['theorems'][theorem_name] = apply_rule_or_theorem(
            env, theorem, theorem_name)

    for kind, name in env['order']:
        if name[-1] == '!':
            continue
        if kind == 'prose':
            print(f"-- {env['prose'][name]}")
        else:
            print(f"{name} : {env['theorems'][name]}")


if __name__ == '__main__':
    sys.exit(main())
