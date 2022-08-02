#!/usr/bin/python3
# -*- coding: utf-8 -*-

import sys
from os.path import exists


def parse_rules(rules):
    parsed_rules = {}

    # Split rules into hypotheses and conclusion
    for name in rules:
        rule = list(map(str.strip, rules[name].split('->')))
        parsed_rules[name] = {'hypotheses': rule[:-1],
                              'conclusion': rule[-1]}

    return parsed_rules


def parse_replacements(theorem_name, replacements):
    parsed_replacements = {}

    if replacements == None:
        return parsed_replacements

    replacements = replacements.split(';')

    # Parses "x=X,y=Y,..." into a dictionary for easier substitution, checking syntax on the way
    for expr in replacements:
        replacement = expr.split('=', 1)

        if len(replacement) < 2 or len(replacement[0]) != 1 or not replacement[0].islower():
            raise Exception(
                "Invalid syntax for replacement '%s' in '%s'" % (expr, theorem_name))

        parsed_replacements[replacement[0]] = replacement[1]

    return parsed_replacements


def parse_theorems(theorems):
    parsed_theorems = {}

    # Process theorems, checking for valid syntax and process replacements on the way
    for name in theorems:
        arguments = list(filter(lambda x: x, theorems[name].split(' ')))

        if len(arguments) < 1:
            raise Exception("Invalid syntax for theorem '%s'" % name)

        rule = arguments[0]
        replacements = arguments[1] if len(arguments) > 1 else None
        hypotheses = arguments[2:] if len(arguments) > 2 else []

        parsed_theorems[name] = {'rule': rule, 'replacements': parse_replacements(
            name, replacements), 'hypotheses': hypotheses}

    return parsed_theorems


def calculate_environment(code):
    env = {'rules': {}, 'theorems': {}}
    types = {'r': 'rules', 't': 'theorems'}

    code = filter(lambda x: x, code.split('\n'))
    code = filter(lambda x: x, map(
        lambda line: line.split('#')[0], code))  # strip comments

    # Process every line in the code, checking for valid syntax and storing the data for further parsing
    for line in code:
        parsed_line = list(
            filter(lambda x: x, map(str.strip, line.split(':', 1))))

        if len(parsed_line) != 2:
            raise Exception("Invalid syntax: '%s'" % line)

        [name, expr] = parsed_line

        if name[0] not in types:
            raise Exception("Invalid variable name: '%s'" % name)

        ty = types[name[0]]

        if name in env[ty]:
            raise Exception("Name redeclaration: '%s'" % name)

        env[ty][name] = expr

    env['rules'] = parse_rules(env['rules'])
    env['theorems'] = parse_theorems(env['theorems'])

    return env


def apply_rule(env, theorem, theorem_name):
    replacements = theorem['replacements']
    th_hypotheses = theorem['hypotheses']
    rule = theorem['rule']

    if rule not in env['rules']:
        raise Exception("Invalid rule: '%s'" % rule)

    ru_hypotheses = env['rules'][rule]['hypotheses'].copy()
    ru_conclusion = env['rules'][rule]['conclusion']

    for k, v in replacements.items():
        if not v or v not in env['theorems']:
            raise Exception("Invalid theorem: '%s' in '%s'" %
                            (v, theorem_name))

        replacements[k] = env['theorems'][v]

        if not isinstance(replacements[k], str):
            raise Exception("Invalid theorem: '%s' in '%s'" %
                            (v, theorem_name))

    # Process theorem's hypotheses by substituting for other theorems
    for i, h in enumerate(th_hypotheses):
        if h not in env['theorems']:
            raise Exception("Invalid theorem: '%s' in '%s'" %
                            (h, theorem_name))
        hypothesis = env['theorems'][h]

        for k, v in replacements.items():
            hypothesis = hypothesis.replace(k, v)

        th_hypotheses[i] = hypothesis

    for k, v in replacements.items():
        # Process rule's hypotheses by substituting the replacements
        for i in range(0, len(ru_hypotheses)):
            ru_hypotheses[i] = ru_hypotheses[i].replace(k, v)

        # Process conclusion by substituting the replacements
        ru_conclusion = ru_conclusion.replace(k, v)

    if ru_hypotheses != th_hypotheses:
        raise Exception("Hypotheses mismatch for '%s': cannot unify\n\t%s\nand\n\t%s" % (
            theorem_name, str(ru_hypotheses), str(th_hypotheses)))

    return ru_conclusion


if len(sys.argv) != 2:
    exit('Usage: python %s <filename.arw>' % sys.argv[0])

if not exists(sys.argv[1]):
    exit("Filename '%s' not found." % sys.argv[1])

with open(sys.argv[1]) as f:
    code = f.read()

env = calculate_environment(code)

for theorem_name in env['theorems']:
    theorem = env['theorems'][theorem_name]
    env['theorems'][theorem_name] = apply_rule(env, theorem, theorem_name)

for name in env['theorems']:
    if name[-1] == '!':
        continue
    print('%s : %s' % (name, env['theorems'][name]))
