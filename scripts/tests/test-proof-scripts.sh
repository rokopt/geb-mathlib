#!/usr/bin/env bash
# Exercise versions 2 and 3 of the proof profile through the CLI: statements over the internal
# language, the tactics of trees and coproducts, rules at objects, imported documents, the program
# a document names, the diagnostics of a rejected development, truth and implication, the tactics
# of the induction on trees with the hypothesis at each child, of the instances of a hypothesis
# and of implications, and the development of bootstrap/proofs/, proved and replayed.
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

def prune(t):
    return ('(rose-rec T (n) (node Bits (pair (fst n) (list-rec (nil T) (r acc) (cons T r (nil T))'
            f' (snd n)))) {t})')

HYP = f'''; Theorems of version 3 about the pair example.

(proofs 3 (import Pair.proofs.geb)
  ; The instance of a hypothesis that equates functions.
  (theorem instance
    (internal (X Y)
      (forall ((f (Arrow X Y)) (g (Arrow X Y)) (x X)) (implies (h (equal f g)) (equal (f x) (g x)))))
    (by (instances weak h ((hx x)) (reduce weak hx))))
  ; An implication is introduced, and eliminated by modus ponens.
  (theorem symmetry
    (internal (X) (forall ((x X) (y X)) (equal (implies (equal x y) (equal y x)) true)))
    (by (assume h (reduce weak h))))
  (theorem composition
    (internal (X)
      (forall ((a X) (b X) (c X) (d X))
        (implies (h (equal (implies (equal a b) (equal c d)) true))
          (equal (implies (equal a b) (equal d c)) true))))
    (by (assume ha (modus-ponens ha (h) (reduce weak h)))))
  ; The case analysis of a list that a hypothesis mentions.
  (theorem reverted
    (internal (X) (forall ((l (List X)) (m (List X))) (implies (h (equal l m)) (equal m l))))
    (by (revert-cases h l (y ys) (reduce weak h) (reduce weak h))))
  ; Keeping the first child alone at each node is idempotent, by induction on a tree with the
  ; hypothesis at the first child.
  (theorem prune-prune
    (internal () (forall ((t T)) (equal {prune(prune('t'))} {prune('t')})))
    (by
      (tree-induction t (l cs ih)
        (revert-cases ih cs (c ys) (reduce full)
          (child-hypotheses weak ih (((hc))) (reduce full hc))))))
  ; The children of a tree of the kernel have the kernel's type of lists of trees.
  (theorem kernel-children (forall ((t T)) (equal t t))
    (by (tree-induction t (l cs ih) (generalize (zs (List T)) (kernel cs) (reduce weak)))))
  ; A theorem of a document of an earlier version is cited after the connectives' rules.
  (theorem append-nil-again (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (reduce weak append-nil))))
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
             'a document of a version before 2 has no form (import')

    # Version 3 reads truth and implication and the tactics of hypotheses, its certificate begins
    # with the connectives' rules and replays, and it cites the theorems of earlier versions.
    hyp = root / 'Hyp.proofs.geb'
    hyp.write_text(HYP)
    hyp_cert = root / 'hyp.cert'
    run('prove', manifest, hyp, hyp_cert)
    run('replay', manifest, hyp, hyp_cert)
    # Version 2 reads none of them, and no document imports one of a later version.
    rejected(HYP.replace('(proofs 3', '(proofs 2'), '5:12',
             'the script of the theorem instance does not read')
    rejected(document('(theorem a (internal () (forall ((p Omega)) (equal (implies p p) true)))'
                      ' (by (normalize 4)))'), '2:12', 'the theorem a is not')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Hyp.proofs.geb)'), '', 'imports one of a later version')
    # The induction on a tree takes a goal without hypotheses; a keyword of the connectives names
    # no variable or hypothesis of a script; modus ponens cites hypotheses.
    three = '(proofs 3\n  {})\n'
    rejected(three.format('(theorem a (forall ((t T)) (implies (h (equal t t)) (equal t t)))'
                          ' (by (tree-induction t (l cs ih) (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')
    rejected(three.format('(theorem a (internal () (forall ((p Omega)) (equal (implies p p) true)))'
                          ' (by (assume implies (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')
    rejected(three.format('(theorem a (forall ((t T)) (implies (h (equal t t)) (equal t t)))'
                          ' (by (modus-ponens h (g) (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')
    # A script that does not prove its theorem is reported so: the antecedent is not cited.
    rejected(HYP.replace('(by (assume h (reduce weak h)))', '(by (assume h (reduce weak)))'),
             '10:12', 'the script of the theorem symmetry does not prove it')

    # An import is a path below the document that reads, and imports return to no document.
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import ../Pair.proofs.geb)'), '', 'is not a relative path below')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Absent.proofs.geb)'), '', 'Absent.proofs.geb does not read')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Bad.proofs.geb)'), '', 'return to a document')

    # A document that names its program is proved and replayed without a manifest, against the
    # manifest of that name in its directory or the nearest above; the documents it imports are
    # read against that program, whatever program they name.
    def named(header, body='(theorem again (forall ((xs (List T)))'
                           ' (equal (Lists.append xs (nil T)) xs)) (by (reduce weak append-nil)))'):
        return f'(proofs 2 {header}\n  {body})\n'
    below = root / 'below'
    below.mkdir()
    (below / 'Imported.proofs.geb').write_text(
        '(proofs 2 (program elsewhere)\n'
        '  (theorem append-nil (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))\n'
        '    (by (induction xs (y ys ih) (reduce weak)'
        ' (reduce-hypotheses weak (ih) (reduce weak ih))))))\n')
    here = below / 'Named.proofs.geb'
    here.write_text(named('(program pair) (import Imported.proofs.geb)'))
    own = root / 'named.cert'
    run('prove', here, own)
    run('replay', here, own)
    explicit = root / 'explicit.cert'
    run('prove', manifest, here, explicit)
    assert explicit.read_bytes() == own.read_bytes()

    # `check` proves a proof document and writes nothing, reports a failure at the theorem, and
    # compiles any other file as a source of a program.
    before = sorted(p.name for p in below.iterdir())
    assert run('check', here) == ''
    assert sorted(p.name for p in below.iterdir()) == before
    failing = below / 'Failing.proofs.geb'
    failing.write_text(named('(program pair)', '(theorem again (equal Pair.left Pair.first)'
                                               ' (by (normalize 0)))'))
    error = run('check', failing, ok=False)
    assert error.startswith(f'{failing}:2:12: error: the script of the theorem again'), error
    assert run('check', root / 'Pair.geb') == ''
    broken = below / 'Broken.geb'
    broken.write_text((root / 'Pair.geb').read_text().replace('T x))', 'T z))'))
    assert run('check', broken, ok=False).startswith(f'{broken}:9:9: error: Pair.left does not check')

    # A document proved without a manifest names one program, which a manifest in its directory
    # or above names once; a manifest given takes the place of the program named.
    def unnamed(text, message):
        target = below / 'Unnamed.proofs.geb'
        target.write_text(text)
        error = run('check', target, ok=False)
        assert error.startswith(f'{target}: ') and message in error, (text, error)
        return target
    plain = '(theorem again (equal Pair.left Pair.left) (by (normalize 4)))'
    target = unnamed(named('', plain), 'the document names no program')
    run('prove', manifest, target, root / 'unnamed.cert')
    target = unnamed(named('(program nowhere)', plain), 'no manifest of the program nowhere')
    run('prove', manifest, target, root / 'unnamed.cert')
    unnamed(named('(program pair) (program pair)', plain), 'names more than one program')
    unnamed('(proofs 1 (program pair)\n  ' + plain + ')\n',
            'a document of a version before 2 has no form (program')
    shutil.copyfile(manifest, root / 'second.manifest')
    unnamed(named('(program pair)', plain), 'several manifests')
    (root / 'second.manifest').unlink()

    # The development of the tree lemmas and of the case analysis of trees, about the type checker
    # and the expansion of the datatype language, is proved and replayed from its Geb sources, the
    # document of the case analysis naming its program.
    cases = root / 'tree-cases.cert'
    run('prove', proofs_dir / 'tree-cases.proofs.geb', cases)
    run('replay', proofs_dir / 'tree-cases.proofs.geb', cases)

print('test-proof-scripts: internal statements, tactics, imports, named programs, diagnostics, '
      'hypotheses and implications and the tree-cases development passed')
PY
