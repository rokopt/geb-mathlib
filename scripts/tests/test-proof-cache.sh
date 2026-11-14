#!/usr/bin/env bash
# Exercise the cache of a development through the CLI: a development proved with a cache is
# resumed from it, a theorem whose statement and script the cache has, proved, being searched
# for no more. The declarations of a theorem at an unchanged position after unchanged
# statements are taken as they stand; those of a theorem the cache has elsewhere, or under a
# changed program, are checked, the entries they cite renumbered and the definitions they name
# at their places in the present program; a theorem whose script or statement changed, whose
# derivation unfolds a definition defined otherwise, or that is not proved, is run. The
# certificate is that of a development proved without a cache, and a certificate of the program
# before a change is transported to the program after it where it still replays. A development
# of version 4 is resumed from a cache of the definitions it declares.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author
python3 - <<'PY'
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()
sample = Path('examples/authoring')

def run(*args, ok=True, timeout=600):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=timeout)
    if result.returncode != (0 if ok else 1):
        raise AssertionError((args, result.returncode, result.stdout, result.stderr))
    return result.stdout.decode(), result.stderr.decode()

def uses(out):
    found = re.search(r'cache: (\d+) taken, (\d+) checked, (\d+) proved, (\d+) not proved', out)
    assert found, out
    return tuple(int(n) for n in found.groups())

DOC = '''(proofs 3 (program pair)
  (theorem first-at (forall ((x T) (y T)) (equal (Pair.first x y) x)) (by (normalize 64)))
  (theorem append-nil (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (induction xs (y ys ih) (reduce weak) (reduce-hypotheses weak (ih) (reduce weak ih)))))
  (theorem append-nil-twice
    (forall ((xs (List T))) (equal (Lists.append (Lists.append xs (nil T)) (nil T)) xs))
    (by (reduce weak append-nil)))
  (theorem symmetry
    (internal (X) (forall ((x X) (y X)) (equal (implies (equal x y) (equal y x)) true)))
    (by (assume h (reduce weak h)))))
'''

with tempfile.TemporaryDirectory(prefix='geb-proof-cache-test-') as directory:
    root = Path(directory)
    for name in ('Pair.geb', 'Lists.geb', 'pair.manifest'):
        shutil.copyfile(sample / name, root / name)
    doc = root / 'Cached.proofs.geb'
    cache = root / 'caches'
    cert = root / 'cached.cert'
    plain = root / 'plain.cert'

    def prove(text, ok=True, output=cert):
        doc.write_text(text)
        return run('prove', '--cache', cache, doc, output, ok=ok)

    # The first run proves every theorem and leaves a cache; the second takes each from it. The
    # certificate is the one a run without a cache writes.
    out, _ = prove(DOC)
    assert uses(out) == (0, 0, 4, 0), out
    files = sorted(p.name for p in cache.iterdir())
    assert len(files) == 1 and files[0].startswith('Cached.proofs.geb.') and files[0].endswith('.cache'), files
    out, _ = prove(DOC)
    assert uses(out) == (4, 0, 0, 0), out
    run('prove', doc, plain)
    assert cert.read_bytes() == plain.read_bytes()
    run('replay', doc, cert)

    # A changed script is run again, and the theorems after it are taken: its statement is the
    # same, so the entries they were checked with are.
    out, _ = prove(DOC.replace('(by (normalize 64))', '(by (normalize 65))'))
    assert uses(out) == (3, 0, 1, 0), out

    # A theorem stated before the others moves their entries: the cache's derivations are
    # checked, the entries they cite renumbered, and none is searched for again. The theorem that
    # cites another by name is among them.
    lemma = '  (theorem first-again (forall ((x T) (y T)) (equal (Pair.first x y) x)) (by (normalize 64)))\n'
    moved = DOC.replace('(proofs 3 (program pair)\n', '(proofs 3 (program pair)\n' + lemma)
    out, _ = prove(moved.replace('(by (normalize 64)))\n  (theorem append-nil ', '(by (normalize 65)))\n  (theorem append-nil '))
    assert uses(out) == (0, 4, 1, 0), out
    out, _ = prove(moved.replace('(by (normalize 64)))\n  (theorem append-nil ', '(by (normalize 65)))\n  (theorem append-nil '))
    assert uses(out) == (5, 0, 0, 0), out
    out, _ = prove(DOC.replace('(by (normalize 64))', '(by (normalize 65))'))
    assert uses(out) == (0, 4, 0, 0), out

    # A changed statement is proved again, and the theorems after it are checked, not taken: the
    # entries they were checked with are no longer those before them.
    restated = DOC.replace('(equal (Pair.first x y) x)) (by (normalize 64))',
                           '(equal (Pair.left x y) x)) (by (normalize 65))')
    assert restated != DOC
    out, _ = prove(restated)
    assert uses(out) == (0, 3, 1, 0), out
    out, _ = prove(DOC)
    assert uses(out) == (0, 3, 1, 0), out
    out, _ = prove(DOC)
    assert uses(out) == (4, 0, 0, 0), out

    # A development that does not read leaves the cache as it is: here a script cites a theorem
    # under a name it no longer has.
    file = next(cache.iterdir())
    kept = file.read_bytes()
    out, err = prove(DOC.replace('(theorem append-nil ', '(theorem right-unit '), ok=False)
    assert 'the script of the theorem append-nil-twice does not read' in err, err
    assert file.read_bytes() == kept
    out, _ = prove(DOC)
    assert uses(out) == (4, 0, 0, 0), out

    # A development that fails keeps what it proves, and writes no certificate: the theorem that
    # is not proved is run at each run, and proved again alone once its script proves it.
    saved = cert.read_bytes()
    broken = DOC.replace('(by (assume h (reduce weak h)))', '(by (assume h (reduce weak)))')
    assert broken != DOC
    for _ in range(2):
        out, err = prove(broken, ok=False)
        assert uses(out) == (3, 0, 0, 1), out
        assert 'the script of the theorem symmetry does not prove it' in err, err
    assert cert.read_bytes() == saved
    out, _ = prove(DOC)
    assert uses(out) == (3, 0, 1, 0), out

    # A theorem with a hole is not proved and is reported at each run; the theorems after it,
    # proved under it as they were under its proof, are taken.
    holed = DOC.replace('(reduce-hypotheses weak (ih) (reduce weak ih))', '?step')
    assert holed != DOC
    for _ in range(2):
        out, err = prove(holed, ok=False)
        assert uses(out) == (3, 0, 0, 1), out
        assert 'leaves the hole ?step open' in err, err
    out, _ = prove(DOC)
    assert uses(out) == (3, 0, 1, 0), out
    assert cert.read_bytes() == saved

    # A changed program: the cache's items are read with the definitions they name at their
    # places in the present program, and their derivations are checked, none searched for again.
    # A definition added after the others moves the connectives, which the theorem stated with
    # them names.
    source = root / 'Lists.geb'
    original = source.read_text()
    source.write_text(original.replace("(module Lists (export append)", "(module Lists (export append twice)")
                      .rstrip()[:-1] + "\n  (defn twice ((xs (List T))) (List T) (append xs xs)))\n")
    manifest = root / 'pair.manifest'
    manifest.write_text(manifest.read_text().replace('Lists.append)', 'Lists.append Lists.twice)'))
    out, _ = prove(DOC)
    assert uses(out) == (0, 4, 0, 0), out
    out, _ = prove(DOC)
    assert uses(out) == (4, 0, 0, 0), out

    # The certificate of the program as it was does not replay against the changed program, and
    # is transported to it: the certificate written replays, and the one read is left as it is.
    earlier = root / 'earlier.cert'
    earlier.write_bytes(saved)
    moved = root / 'moved.cert'
    _, err = run('replay', doc, earlier, ok=False)
    assert 'compiled program differs' in err, err
    run('transport', doc, earlier, moved)
    run('replay', doc, moved)
    assert earlier.read_bytes() == saved
    run('transport', doc, moved, root / 'again.cert')
    assert (root / 'again.cert').read_bytes() == moved.read_bytes()

    # A definition stated before the others moves every definition of the program: the items
    # are checked, and the certificate of the program before it is transported.
    first = root / 'Pair.geb'
    paired = first.read_text()
    inserted = paired.replace('(module Pair (export first left)\n',
                              '(module Pair (export first left)\n  (defn second ((x T) (y T)) T y)\n')
    assert inserted != paired
    first.write_text(inserted)
    out, _ = prove(DOC)
    assert uses(out) == (0, 4, 0, 0), out
    out, _ = prove(DOC)
    assert uses(out) == (4, 0, 0, 0), out
    run('transport', doc, moved, root / 'inserted.cert')
    run('replay', doc, root / 'inserted.cert')

    # A definition defined otherwise: the theorem whose derivation unfolds it is proved again,
    # the others are checked, and the certificate of the program before it is not transported,
    # no output being written.
    redefined = inserted.replace('(defn first ((x T) (y T)) T (fst (pair x y)))',
                                 '(defn first ((x T) (y T)) T x)')
    assert redefined != inserted
    first.write_text(redefined)
    out, _ = prove(DOC)
    assert uses(out) == (0, 3, 1, 0), out
    refused = root / 'refused.cert'
    _, err = run('transport', doc, root / 'inserted.cert', refused, ok=False)
    assert 'does not prove these statements in this program' in err, err
    assert not refused.exists()
    out, _ = prove(DOC)
    assert uses(out) == (4, 0, 0, 0), out

    # `check` resumes from the cache and writes nothing but it; a cache that does not read, or
    # of another format, is no cache.
    before = sorted(p.name for p in root.iterdir())
    out, err = run('check', '--cache', cache, doc)
    assert uses(out) == (4, 0, 0, 0) and err == '', (out, err)
    assert sorted(p.name for p in root.iterdir()) == before
    out, err = run('check', doc)
    assert out == '' and err == '', (out, err)
    file.write_bytes(b'not a cache')
    out, _ = prove(DOC)
    assert uses(out) == (0, 0, 4, 0), out
    assert file.read_bytes() != b'not a cache'

    # A development of version 4 declares definitions, and its cache is of them: a definition
    # declared after the others, or defined otherwise, leaves no theorem taken, and a bound
    # variable's name is no part of a definition. Under a changed program its definitions move
    # with the connectives, in the cache's items and in its certificate.
    DEFS = '''(proofs 4 (program pair)
  (definition plus ((m Nat) (n Nat)) Nat
    ((nat-rec (lam ((a Nat)) a) (r) (lam ((a Nat)) (succ (r a))) n) m))
  (theorem plus-zero (internal () (forall ((n Nat)) (equal (plus n zero) n)))
    (by (reduce full (unfold plus))))
  (theorem zero-plus (internal () (forall ((n Nat)) (equal (plus zero n) n)))
    (by (nat-induction n 256 (unfold plus)))))
'''
    defined = root / 'Defined.proofs.geb'
    counted = root / 'defined.cert'

    def prove_defined(text):
        defined.write_text(text)
        out, _ = run('prove', '--cache', cache, defined, counted)
        return uses(out)

    assert prove_defined(DEFS) == (0, 0, 2, 0)
    assert prove_defined(DEFS) == (2, 0, 0, 0)
    renamed = DEFS.replace('(lam ((a Nat)) (succ (r a)))', '(lam ((b Nat)) (succ (r b)))')
    assert renamed != DEFS and prove_defined(renamed) == (2, 0, 0, 0)
    more = DEFS.replace('  (theorem plus-zero',
                        '  (definition one () Nat (succ zero))\n  (theorem plus-zero')
    assert more != DEFS and prove_defined(more) == (0, 2, 0, 0)
    assert prove_defined(more) == (2, 0, 0, 0)
    otherwise = more.replace(') n) m))', ') n) ((lam ((a Nat)) a) m)))')
    assert otherwise != more
    taken, _, _, unproved = prove_defined(otherwise)
    assert taken == 0 and unproved == 0
    assert prove_defined(otherwise) == (2, 0, 0, 0)
    before = counted.read_bytes()
    first.write_text(first.read_text().replace(
        '(module Pair (export first left)\n',
        '(module Pair (export first left)\n  (defn third ((x T) (y T)) T x)\n'))
    _, err = run('replay', defined, counted, ok=False)
    assert 'compiled program differs' in err, err
    run('transport', defined, counted, root / 'defined-moved.cert')
    run('replay', defined, root / 'defined-moved.cert')
    assert counted.read_bytes() == before
    assert prove_defined(otherwise) == (0, 2, 0, 0)
    assert prove_defined(otherwise) == (2, 0, 0, 0)

print('test-proof-cache: taken, checked and proved theorems, changed scripts, statements and '
      'programs, failures, holes, the certificate, its transport and declared definitions '
      'passed')
PY
