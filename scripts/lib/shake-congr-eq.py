#!/usr/bin/env python3
"""Pass a `lake shake --explain` report whose suggestions all stem from match congruence lemmas.

Usage: lake shake ... --explain MODULE... | scripts/lib/shake-congr-eq.py

Lean generates a matcher's congruence equation `M.match_n.congr_eq_k` on demand, in every module
that uses it, under a name core reserves (`Lean.Meta.Match.MatchEqs`). Lake's `lake shake` loads
modules without their environment extensions, so it does not recognise the name as reserved,
and it attributes the lemma to whichever module that also generated it is loaded first. It then
asks the module using the lemma to import that module, which is not among its imports.

A module compiles only against its transitive imports, so every module whose constants it uses
lies among them. An add of a project module outside them, explained by a reference to a
`congr_eq_k` lemma, is therefore such an attribution. A file's report is passed when it has one
and each other suggestion follows from it: a removal of an import the added module implies, and
an add of a module that removed import reached, public only when that import was public. Any
other report is printed and fails the check, as are output that holds no report and a module
outside the project, whose imports are not read.

The check is removed once `lake shake` recognises the reserved names.
"""

import re
import sys
import tomllib
from functools import cache
from pathlib import Path

repo = Path(__file__).resolve().parents[2]
with open(repo / 'lakefile.toml', 'rb') as lakefile:
    libraries = tomllib.load(lakefile).get('lean_lib', [])
roots = sorted({(repo / library.get('srcDir', '.')).resolve() for library in libraries},
               key=lambda root: len(root.parts), reverse=True)

IMPORT = re.compile(r'(?:public\s+)?(?:meta\s+)?import\s+(\S+)')
CONGR_EQ = re.compile(r'refers to `[^`]*\.congr_eq_\d+`')


def source(module):
    """The project file of `module`, or `None` for a module outside the project."""
    for root in roots:
        path = root / (module.replace('.', '/') + '.lean')
        if path.is_file():
            return path
    return None


def module_of(path):
    """The module name of a project file."""
    for root in roots:
        if path.is_relative_to(root):
            return '.'.join(path.relative_to(root).with_suffix('').parts)
    return None


@cache
def imports(module):
    """The modules the header of `module`'s file imports; none outside the project."""
    path = source(module)
    if path is None:
        return ()
    text = re.sub(r'\A\s*/-.*?-/', '', path.read_text(), flags=re.S)
    found = []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith('--') or line.split()[0] == 'module':
            continue
        match = IMPORT.match(line)
        if match is None:
            break
        found.append(match.group(1))
    return tuple(found)


@cache
def closure(module):
    """The project and external modules `module` imports transitively."""
    reached = set()
    for imported in imports(module):
        reached.add(imported)
        reached |= closure(imported)
    return frozenset(reached)


def entries(line):
    """The `(kind, module)` pairs of a suggestion line `  add #[public import A, import B]`."""
    items = line[line.index('#[') + 2:line.rindex(']')].split(', ')
    return [tuple(item.rsplit(' ', 1)) for item in items]


def reports(lines):
    """Each reported file with its adds, removes and the reason given for each requirement."""
    found, note = [], None
    for line in lines:
        if line.startswith('/') and line.endswith('.lean:'):
            found.append({'path': Path(line[:-1]), 'add': [], 'remove': [], 'reason': {},
                          'lines': [line]})
        elif found and line.startswith(('  add #[', '  remove #[')):
            found[-1]['add' if line.startswith('  add') else 'remove'] += entries(line)
            found[-1]['lines'].append(line)
        elif found and line.startswith('  note: `') and line.endswith('` required'):
            note = tuple(line[len('  note: `'):-len('` required')].rsplit(' ', 1))
        elif found and line.startswith('    because'):
            found[-1]['reason'][note] = line
    return [report for report in found if report['add'] or report['remove']]


def passes(report):
    """Whether every suggestion of `report` stems from a misattributed congruence lemma."""
    module = module_of(report['path'].resolve())
    if module is None:
        return False
    reached = closure(module)
    spurious = [(kind, added) for kind, added in report['add']
                if source(added) is not None and added not in reached and added != module
                and CONGR_EQ.search(report['reason'].get((kind, added), ''))]
    if not spurious:
        return False
    implied = set().union(*({added} | closure(added) for _, added in spurious))
    if any(removed not in implied for _, removed in report['remove']):
        return False
    return all((kind, added) in spurious
               or any(added in {removed} | closure(removed)
                      and ('public' not in kind.split() or 'public' in removed_kind.split())
                      for removed_kind, removed in report['remove'])
               for kind, added in report['add'])


def main():
    found = reports(sys.stdin.read().splitlines())
    if not found:
        print('shake-congr-eq: lake shake failed without a report', file=sys.stderr)
        return 1
    failing = [report for report in found if not passes(report)]
    for report in failing:
        print('\n'.join(report['lines']))
    if failing:
        return 1
    print(f'shake-congr-eq: passed {len(found)} report(s) from misattributed congr_eq lemmas:')
    for report in found:
        print(f"  {report['path'].relative_to(repo)}")
    return 0


if __name__ == '__main__':
    sys.exit(main())
