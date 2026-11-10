#!/usr/bin/env bash
# Exercise version 2 of the proof profile through the CLI: statements over the internal language,
# the tactics of trees and coproducts, rules at objects, imported documents, the diagnostics of a
# rejected development, and the development of bootstrap/proofs/, proved and replayed.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author
python3 - <<'PY'
from pathlib import Path
import shutil
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()
sample = Path('examples/authoring')
proofs_dir = Path('bootstrap/proofs')

def run(*args, ok=True, timeout=600):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=timeout)
    if result.returncode != (0 if ok else 1):
        raise AssertionError((args, result.returncode, result.stdout, result.stderr))
    return result.stderr.decode()

MORE = '''; Theorems of version 2 about the pair example.

(proofs 2 (import Pair.proofs.geb) (import lib/trees.proofs.geb)
  ; Appending the empty list after an appending, by generalizing the appending.
  (theorem append-append-nil
    (forall ((xs (List T)) (ys (List T)))
      (equal (Lists.append (Lists.append xs ys) (nil T)) (Lists.append xs ys)))
    (by (generalize (zs (List T)) (kernel (Lists.append xs ys)) (reduce weak append-nil))))
  ; The case analysis of a coproduct at its injections.
  (theorem case-inl
    (internal (X Y)
      (forall ((f (Arrow X Y)) (g (Arrow Unit Y)) (x X))
        (equal ((case X Unit Y (pair f g)) (inl X Unit x)) (f x))))
    (by (reduce weak)))
  (theorem case-inr
    (internal (X Y)
      (forall ((f (Arrow X Y)) (g (Arrow Unit Y)))
        (equal ((case X Unit Y (pair f g)) (inr X Unit unit)) (g unit))))
    (by (reduce weak)))
  ; A case analysis with one value at both bits is that value.
  (theorem bit-constant
    (internal (X)
      (forall ((x X) (b Bit))
        (equal ((case Unit Unit X (pair (lam ((u Unit)) x) (lam ((u Unit)) x))) b) x)))
    (by (sum-cases b (u) (reduce weak) (reduce weak))))
  ; A definition of the program beside a term of the kernel.
  (theorem first-internal
    (internal () (forall ((x T) (y T)) (equal (Pair.first x y) (kernel (Pair.left x y)))))
    (by (normalize 64)))
  ; A tree is the node of its label and children.
  (theorem node-label-children
    (internal () (forall ((t T)) (equal (node Bits (pair (lib lab t) (lib children t))) t)))
    (by (tree-cases t (l cs) lambek (reduce full map-id map-fusion lambek)))))
'''

def document(body, imports=''):
    return f'(proofs 2 {imports}\n  {body})\n'

with tempfile.TemporaryDirectory(prefix='geb-proof-scripts-test-') as directory:
    root = Path(directory)
    for name in ('Pair.geb', 'Lists.geb', 'Pair.proofs.geb', 'pair.manifest'):
        shutil.copyfile(sample / name, root / name)
    (root / 'lib').mkdir()
    shutil.copyfile(proofs_dir / 'trees.proofs.geb', root / 'lib/trees.proofs.geb')
    manifest = root / 'pair.manifest'
    more = root / 'More.proofs.geb'
    certificate = root / 'more.cert'
    more.write_text(MORE)

    # A document of version 2 imports documents of versions 1 and 2, and its certificate replays
    # from the documents alone.
    run('prove', manifest, more, certificate)
    run('replay', manifest, more, certificate)
    saved = certificate.read_bytes()

    # The certificate holds the imported theorems: a changed imported statement, or a changed
    # import, prevents its reuse, and a changed imported script does not.
    imported = root / 'Pair.proofs.geb'
    original = imported.read_text()
    imported.write_text(original.replace('(by (normalize 64 same))', '(by (normalize 65 same))'))
    run('replay', manifest, more, certificate)
    imported.write_text(original.replace('(equal (Pair.first x y) x)', '(equal (Pair.left x y) x)'))
    run('replay', manifest, more, certificate, ok=False)
    imported.write_text(original)
    more.write_text(MORE.replace(' (import lib/trees.proofs.geb)', '')
                    .replace('(tree-cases t (l cs) lambek (reduce full map-id map-fusion lambek))',
                             '(reduce full)'))
    run('replay', manifest, more, certificate, ok=False)
    more.write_text(MORE)
    assert certificate.read_bytes() == saved

    # A rejected development is reported at the theorem concerned, and leaves the output.
    def rejected(text, at, message, name='Bad.proofs.geb'):
        target = root / name
        target.write_text(text)
        error = run('prove', manifest, target, certificate, ok=False)
        expected = f'{target}:{at}: error: ' if at else f'{target}: '
        assert error.startswith(expected) and message in error, (text, error)
        assert certificate.read_bytes() == saved

    rejected(MORE.replace('(reduce weak append-nil))))', '(reduce weak))))'), '5:12',
             'the script of the theorem append-append-nil does not prove it')
    rejected(MORE.replace('(lib lab t)', '(lib label t)'), '31:12',
             'the theorem node-label-children is not')
    rejected(MORE.replace('(sum-cases b (u)', '(sum-cases c (u)'), '21:12',
             'the script of the theorem bit-constant does not read')
    rejected(MORE.replace('(theorem case-inr', '(theorem first-at'), '15:12',
             'the theorem first-at is declared before')
    # A term of the kernel mentions no variable without a kernel type; an equation's sides have
    # one type; an object variable is bound; a definition of the library takes its objects.
    for body in ('(theorem a (internal () (forall ((x Bits)) (equal (kernel x) x))) (by (normalize 4)))',
                 '(theorem a (internal () (forall ((x Bits) (t T)) (equal x t))) (by (normalize 4)))',
                 '(theorem a (internal (X) (forall ((x Y)) (equal x x))) (by (normalize 4)))',
                 '(theorem a (internal () (forall ((x Bits)) (equal (lib cond x x x) x)))'
                 ' (by (normalize 4)))'):
        rejected(document(body), '2:12', 'the theorem a is not')
    # A keyword of the internal language's terms names no variable of an internal statement.
    rejected(document('(theorem a (internal () (forall ((lib Bits)) (equal lib lib)))'
                      ' (by (normalize 4)))'), '2:12', 'the theorem a is not')

    # Versions 0 and 1 read neither internal statements, the tactics of version 2 nor imports.
    one = '(proofs 1\n  {})\n'
    rejected(one.format('(theorem a (internal () (forall ((x T)) (equal x x))) (by (normalize 4)))'),
             '2:12', 'the theorem a is not')
    rejected(one.format('(theorem a (forall ((b T)) (equal b b))'
                        ' (by (generalize (y T) b (normalize 4))))'),
             '2:12', 'the script of the theorem a does not read')
    rejected('(proofs 1 (import Pair.proofs.geb)\n'
             '  (theorem a (equal Pair.left Pair.left) (by (normalize 4))))\n', '',
             'a document of a version before 2 imports no document')

    # An import is a path below the document that reads, and imports return to no document.
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import ../Pair.proofs.geb)'), '', 'is not a relative path below')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Absent.proofs.geb)'), '', 'Absent.proofs.geb does not read')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Bad.proofs.geb)'), '', 'return to a document')

    # The development of the tree lemmas and of the case analysis of trees, about the type checker
    # and the expansion of the datatype language, is proved and replayed from its Geb sources.
    cases = root / 'tree-cases.cert'
    run('prove', 'bootstrap/expansion.manifest', proofs_dir / 'tree-cases.proofs.geb', cases)
    run('replay', 'bootstrap/expansion.manifest', proofs_dir / 'tree-cases.proofs.geb', cases)

print('test-proof-scripts: internal statements, tactics, imports, diagnostics and the tree-cases '
      'development passed')
PY
