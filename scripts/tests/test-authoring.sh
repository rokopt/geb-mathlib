#!/usr/bin/env bash
# Exercise authoring, durable conversion, checked examples and certificate replay through the CLI.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-defs geb-compile
python3 - <<'PY'
import base64
from pathlib import Path
import shutil
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()
defs = Path('.lake/build/bin/geb-defs').resolve()
compiler = Path('.lake/build/bin/geb-compile').resolve()
sample = Path('examples/authoring')

def run(*args, ok=True):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=60)
    if result.returncode != (0 if ok else 1):
        raise AssertionError((args, result.returncode, result.stdout, result.stderr))
    return result

with tempfile.TemporaryDirectory(prefix='geb-author-test-') as directory:
    root = Path(directory)
    for name in ('Pair.geb', 'Lists.geb', 'Pair.proofs.geb', 'pair.manifest'):
        shutil.copyfile(sample / name, root / name)
    manifest = root / 'pair.manifest'
    source = root / 'Pair.geb'
    proofs = root / 'Pair.proofs.geb'
    original_source = source.read_text()
    original_proofs = proofs.read_text()
    original_manifest = manifest.read_text()
    certificate = root / 'proof.cert'
    image = root / 'program.img'
    run('prove', manifest, proofs, certificate)
    run('replay', manifest, proofs, certificate)
    run('compile', manifest, image)
    core = image.read_bytes()
    saved = certificate.read_bytes()
    native = root / 'native.img'
    subprocess.run([str(compiler), 'image', '--manifest', str(manifest), str(native)],
                   check=True, timeout=60)
    assert native.read_bytes() == core

    # More than one theorem is preserved in source order.
    proofs.write_text(original_proofs.rstrip()[:-1] +
                     ' (theorem left-self (equal Pair.left Pair.left) (by (normalize 64))))')
    run('prove', manifest, proofs, root / 'multiple.cert')
    run('replay', manifest, proofs, root / 'multiple.cert')
    proofs.write_text(original_proofs)

    # Canonical form is the comparison of the complete documents, including decorations.
    for document in (source, proofs):
        canonical = root / (document.name + '.canonical')
        advanced = root / (document.name + '.advanced')
        transport = root / (document.name + '.transport')
        again = root / (document.name + '.again')
        run('convert', 'canonical', manifest, document, canonical)
        run('convert', 'advanced', manifest, canonical, advanced)
        run('convert', 'canonical', manifest, advanced, again)
        assert again.read_bytes() == canonical.read_bytes(), document
        transport.write_bytes(b'{\n' + base64.b64encode(canonical.read_bytes()) + b'\n}')
        run('convert', 'canonical', manifest, transport, again)
        assert again.read_bytes() == canonical.read_bytes(), document
        run('convert', 'authoring', manifest, transport, document)
        run('convert', 'canonical', manifest, document, again)
        assert again.read_bytes() == canonical.read_bytes(), document
        for spelling in (canonical, advanced, transport):
            prior = document.read_bytes()
            document.write_bytes(spelling.read_bytes())
            run('compile', manifest, image)
            assert image.read_bytes() == core
            run('replay', manifest, proofs, certificate)
            document.write_bytes(prior)

    # Comments and note fields are durable metadata, independent of the compiled program.
    source.write_text(original_source.replace('Taking the first', 'Sélection of the first')
                      .replace('(note (example', '(note (future-field opaque) (example'))
    run('compile', manifest, image)
    assert image.read_bytes() == core
    run('replay', manifest, proofs, certificate)
    canonical = root / 'annotated.canonical'
    again = root / 'annotated.again'
    run('convert', 'canonical', manifest, source, canonical)
    run('convert', 'authoring', manifest, canonical, source)
    assert 'future-field' in source.read_text()
    run('convert', 'canonical', manifest, source, again)
    assert canonical.read_bytes() == again.read_bytes()
    source.write_text(original_source)

    # Replay uses the saved derivation even if the script now has insufficient search fuel.
    proofs.write_text(original_proofs.replace('normalize 64', 'normalize 0'))
    run('replay', manifest, proofs, certificate)
    run('prove', manifest, proofs, certificate, ok=False)
    assert certificate.read_bytes() == saved

    def reject_proof(text):
        proofs.write_text(text)
        run('prove', manifest, proofs, certificate, ok=False)
        assert certificate.read_bytes() == saved
        run('replay', manifest, proofs, certificate, ok=False)

    reject_proof(original_proofs.replace('Pair.left', 'Pair.missing'))
    reject_proof(original_proofs.replace('(proofs 1', '(proofs 2'))
    reject_proof(original_proofs.replace('(by (normalize 64))', '(by (unknown 64))'))
    reject_proof('(proofs 0)')
    reject_proof(original_proofs + '\n(proofs 0)')
    reject_proof('(proofs 0 (theorem dup (equal Pair.first Pair.left) (by (normalize 64)))'
                 ' (theorem dup (equal Pair.first Pair.left) (by (normalize 64))))')
    proofs.write_text(original_proofs.replace('first-pair', 'renamed'))
    run('replay', manifest, proofs, certificate, ok=False)

    # Version 0 documents keep their reading, and admit only its forms.
    version0 = '(proofs 0 (theorem first-pair (equal Pair.first Pair.left) (by (normalize 64))))'
    proofs.write_text(version0)
    run('prove', manifest, proofs, root / 'version0.cert')
    run('replay', manifest, proofs, root / 'version0.cert')
    for theorem in ('(theorem t (forall ((x T)) (equal x x)) (by (normalize 4)))',
                    '(theorem t (equal Pair.first Pair.left) (by (reduce weak)))',
                    '(theorem t (equal (Pair.first) Pair.left) (by (normalize 64)))'):
        reject_proof('(proofs 0 ' + theorem + ')')

    # Each script form proves a theorem after those of the example.
    def extended(*theorems):
        return original_proofs.rstrip()[:-1] + '\n  ' + '\n  '.join(theorems) + ')'
    accepted = extended(
        '(theorem first-ext (equal Pair.first Pair.left)'
        ' (by (extensionality x (extensionality y (normalize 64)))))',
        '(theorem nil-append (forall ((xs (List T))) (equal (Lists.append (nil T) xs) xs))'
        ' (by (auto weak 1)))',
        '(theorem twice-cases (forall ((xs (List T)) (z T))'
        ' (equal (Lists.append (Lists.append xs (nil T)) (nil T)) (Lists.append xs (nil T))))'
        ' (by (cases xs (y ys) (reduce weak) (reduce weak append-nil))))')
    proofs.write_text(accepted)
    run('prove', manifest, proofs, root / 'forms.cert')
    run('replay', manifest, proofs, root / 'forms.cert')

    # Names are resolved in their scopes, and a statement's sides have one type.
    for theorem in (
            '(theorem t (equal Pair.first Pair.left) (by (normalize 64 missing)))',
            '(theorem t (equal Pair.first Pair.left) (by (normalize 64 t)))',
            '(theorem t (equal Pair.first Pair.left) (by (normalize 64 later)))'
            ' (theorem later (equal Pair.left Pair.left) (by (normalize 64)))',
            '(theorem t (forall ((Pair.first T)) (equal Pair.first Pair.first)) (by (normalize 4)))',
            '(theorem t (forall ((x T) (x T)) (equal x x)) (by (normalize 4)))',
            '(theorem t (forall ((x T)) (implies (x (equal x x)) (equal x x))) (by (normalize 4)))',
            '(theorem t (forall ((lam T)) (equal lam lam)) (by (normalize 4)))',
            '(theorem t (forall ((x Missing)) (equal x x)) (by (normalize 4)))',
            '(theorem t (forall () (equal Pair.first Pair.first)) (by (normalize 4)))',
            '(theorem t (forall ((x T) (xs (List T))) (equal x xs)) (by (normalize 4)))',
            '(theorem t (forall ((x T) (xs (List T))) (equal xs xs))'
            ' (by (induction x (y ys ih) (normalize 4) (normalize 4))))',
            '(theorem t (forall ((xs (List T)) (z T)) (equal xs xs))'
            ' (by (induction xs (y ys ih) (normalize 4) (normalize 4))))',
            '(theorem t (forall ((xs (List T))) (equal xs xs))'
            ' (by (cases xs (xs ys) (normalize 4) (normalize 4))))',
            '(theorem t (equal Pair.first Pair.left) (by (extensionality first-pair (normalize 4))))',
            '(theorem t (forall ((x T)) (equal x x)) (by (reduce-hypotheses weak (h) (normalize 4))))',
            '(theorem t (equal Pair.first Pair.left) (by (reduce deep)))'):
        reject_proof(extended(theorem))

    # A certificate cannot be reassociated with a different statement, even a true one.
    proofs.write_text(original_proofs.replace('(equal Pair.first Pair.left)',
                                             '(equal Pair.left Pair.left)'))
    run('replay', manifest, proofs, certificate, ok=False)
    proofs.write_text(original_proofs)

    # A change to the computational program invalidates the old certificate.
    source.write_text(original_source.replace('(fst (pair x y))', '(snd (pair x y))'))
    run('replay', manifest, proofs, certificate, ok=False)
    run('prove', manifest, proofs, certificate, ok=False)
    assert certificate.read_bytes() == saved

    # A false equation with valid examples is rejected by the prover and checker.
    source.write_text(original_source.replace('T x))', 'T y))'))
    result = run('replay', manifest, proofs, certificate, ok=False)
    assert b'compiled program differs' in result.stderr
    run('prove', manifest, proofs, certificate, ok=False)
    assert certificate.read_bytes() == saved

    # Failed examples prevent both proof writing and compilation from replacing artifacts.
    source.write_text(original_source.replace('(quote (7))))', '(quote (8))))'))
    result = run('prove', manifest, proofs, certificate, ok=False)
    assert b'differs from its expected value' in result.stderr
    run('compile', manifest, image, ok=False)
    assert certificate.read_bytes() == saved and image.read_bytes() == core
    source.write_text(original_source)

    certificate.write_bytes(saved[:-1])
    run('replay', manifest, proofs, certificate, ok=False)
    certificate.write_bytes(saved)
    certificate.write_bytes(core)
    run('replay', manifest, proofs, certificate, ok=False)
    certificate.write_bytes(saved)

    # Quoted UTF-8 names in examples are bytes, just as they are in the program and proof.
    source.write_text(original_source.replace('(export first left)', '(export "pré" left)')
                      .replace('(defn first ', '(defn "pré" ')
                      .replace('Pair.first', '"Pair.pré"'))
    proofs.write_text(original_proofs.replace('Pair.first', '"Pair.pré"'))
    manifest.write_text(original_manifest.replace('Pair.first', '"Pair.pré"'))
    run('prove', manifest, proofs, root / 'unicode.cert')
    run('replay', manifest, proofs, root / 'unicode.cert')
    source.write_text(original_source)
    proofs.write_text(original_proofs)
    manifest.write_text(original_manifest)

    # Unsupported profile features fail; optional profile data survives conversion.
    manifest.write_text(original_manifest.replace('(schema 0)', '(schema 1)'))
    run('prove', manifest, proofs, certificate, ok=False)
    manifest.write_text(original_manifest.replace('(prose verso 0)',
                                                 '(prose verso 0) (crit future) (future opaque)'))
    run('prove', manifest, proofs, certificate, ok=False)
    manifest.write_text(original_manifest.replace('(prose verso 0)',
                                                 '(prose verso 0) (future opaque)'))
    run('convert', 'canonical', manifest, proofs, canonical)
    assert b'future' in canonical.read_bytes()
    run('convert', 'advanced', manifest, canonical, again)
    run('replay', manifest, again, certificate, ok=False)
    run('prove', manifest, again, certificate)
    run('replay', manifest, again, certificate)
    manifest.write_text(original_manifest)
    run('replay', manifest, again, certificate, ok=False)

    # The elaborated definition record is obtained from the same checked image.
    record = root / 'program.defs'
    subprocess.run([str(defs), str(image), str(record)], check=True, timeout=60)
    assert b'Pair.first\t' in record.read_bytes() and b'Pair.left\t' in record.read_bytes()

print('test-authoring: proof replay, conversions, metadata and rejection checks passed')
PY
