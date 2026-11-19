#!/usr/bin/env python3
"""Bind the accelerations of bootstrap/accelerations in Lean the bootstrap compiler emits.

Usage: scripts/accelerate.py [--table TABLE] FILE...

An acceleration is native code run in place of a definition written in Geb, bound to it by the
definition's name and proved equal to it (the manual's Bootstrap chapter, Speed and a second
host). Each line of TABLE, bootstrap/accelerations where none is given, that is not a comment
names a definition, the Lean function bound to it, the Lean function that runs that function
beside the definition's own code and compares the two, and the module declaring both. In each
FILE that defines NAME, the definition

    def «NAME» :=
      BODY

is rewritten in place to

    def «NAME$geb» :=
      BODY

    def «NAME$accel» : type_of% «NAME$geb» :=
      FUNCTION «NAME$geb»

    @[implemented_by «NAME$accel»]
    def «NAME» :=
      BODY

and the module is imported after the file's first import: the definition keeps the value the
compiler emits, which the loading of its program and the proofs about it read, and compiled code
runs FUNCTION, which is given the definition's own code. A FILE that defines none of the names
is left as it is.

The environment variable GEB_ACCELERATION selects what is bound: the function run in the
definition's place where it is unset or "bound", as the committed Lean has it; the function that
runs both and compares them where it is "shadow"; and nothing, each FILE left as the compiler
emits it, where it is "none".
"""
import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def accelerations(path):
    table = []
    for line in path.read_text().splitlines():
        fields = line.split()
        if not fields or fields[0].startswith('#'):
            continue
        if len(fields) != 4:
            raise SystemExit(f'accelerate: malformed line: {line}')
        table.append(tuple(fields))
    return table


def mode():
    selected = os.environ.get('GEB_ACCELERATION', 'bound')
    if selected not in ('bound', 'shadow', 'none'):
        raise SystemExit(f'accelerate: GEB_ACCELERATION is {selected}, not bound, shadow or none')
    return selected


def bind(text, name, function, module):
    pattern = re.compile(
        r'^def «' + re.escape(name) + r'» :=\n(.*?\n)(?=\n(?:def «|end ))', re.M | re.S)
    match = pattern.search(text)
    if match is None:
        return text
    body = match.group(1)
    bound = (f'def «{name}$geb» :=\n{body}\n'
             f'def «{name}$accel» : type_of% «{name}$geb» :=\n  {function} «{name}$geb»\n\n'
             f'@[implemented_by «{name}$accel»]\ndef «{name}» :=\n{body}')
    text = text[:match.start()] + bound + text[match.end():]
    line = f'public import {module}\n'
    if line not in text:
        first = re.search(r'^public import .*\n', text, re.M)
        if first is None:
            raise SystemExit(f'accelerate: no import to place {module} after')
        text = text[:first.end()] + line + text[first.end():]
    return text


def main():
    selected = mode()
    if selected == 'none':
        return
    args = sys.argv[1:]
    source = ROOT / 'bootstrap' / 'accelerations'
    if args[:1] == ['--table']:
        if len(args) < 2:
            raise SystemExit('usage: scripts/accelerate.py [--table TABLE] FILE...')
        source, args = Path(args[1]), args[2:]
    table = accelerations(source)
    for path in map(Path, args):
        text = path.read_text()
        bound = text
        for name, function, shadow, module in table:
            bound = bind(bound, name, shadow if selected == 'shadow' else function, module)
        if bound != text:
            path.write_text(bound)


if __name__ == '__main__':
    main()
