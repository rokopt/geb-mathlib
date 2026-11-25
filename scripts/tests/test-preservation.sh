#!/usr/bin/env bash
# Exercise immutable development records with the real compiler and proof runner.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-compile geb-defs geb-kernel
python3 - <<'PY'
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

repo = Path.cwd()
script = repo / 'scripts/preserve.py'
sample = repo / 'examples/roundtrip'

def run(*args, ok=True, cwd=None, env=None):
    result = subprocess.run([sys.executable, str(script), '--no-build', *map(str, args)],
                            capture_output=True, text=True, cwd=cwd, env=env, timeout=180)
    if result.returncode != (0 if ok else 1):
        raise AssertionError((args, result.returncode, result.stdout[-4000:], result.stderr[-4000:]))
    return result.stdout + result.stderr

def inventory(root):
    return {p.relative_to(root).as_posix(): p.read_bytes()
            for p in root.rglob('*') if p.is_file()}

with tempfile.TemporaryDirectory(prefix='geb-preservation-test-') as directory:
    root = Path(directory)
    project = root / 'project with spaces'
    shutil.copytree(sample, project, ignore=shutil.ignore_patterns('record'))
    manifest = project / 'roundtrip.manifest'
    proofs = project / 'Roundtrip.proofs.geb'
    source = project / 'Roundtrip.geb'
    original = source.read_text()
    original_proofs = proofs.read_text()
    record = root / 'records' / 'first'

    # A dependency manifest, quoted layer name and directory containing spaces survive relocation.
    dep = project / 'lib' / 'box.manifest'
    dep.write_text('(program box (edition 0) (document (syntax authoring 0) (schema 0) '
                   '(prose verso 0)) (sources Box.geb) (entries))\n')
    manifest.write_text(manifest.read_text().replace('lib/Box.geb', '(manifest lib/box.manifest)'))
    run('record', manifest, proofs, record, cwd=root)
    listing = subprocess.check_output([str(repo / '.lake/build/bin/geb-kernel'),
                                       'sources', str(manifest)], text=True)
    assert listing == 'lib/Box.geb\nRoundtrip.geb\n'
    info = json.loads((record / 'record.json').read_text())
    assert info['sources'] == ['lib/Box.geb', 'Roundtrip.geb']
    assert (record / 'project/lib/box.manifest').read_bytes() == dep.read_bytes()
    assert (record / 'documents/dependencies/lib/box.manifest.csexp').is_file()
    for name in info['sources']:
        assert (record / 'project' / name).read_bytes() == (project / name).read_bytes()
        assert (record / 'documents/sources' / (name + '.csexp')).is_file()
    assert (record / 'compiler.img').read_bytes() == (repo / 'bootstrap/compiler.img').read_bytes()
    assert (record / 'tooling/bootstrap/authoring.geb').read_bytes() == (
        repo / 'bootstrap/authoring.geb').read_bytes()
    before = inventory(record)

    # Integrity verification needs neither Lake nor the original sources.
    offline = dict(os.environ, PATH='/nonexistent')
    assert 'no semantic check performed' in run('verify', record, env=offline)
    assert 'documents unchanged' in run('check', record, cwd=root)
    assert 'record already exists' in run('record', manifest, proofs, record, ok=False)
    assert inventory(record) == before

    # A document-only edit preserves the core and replays the old proof.
    source.write_text(original.replace('Packing and then', 'Emballage: packing and then')
                      .replace('(note (example', '(note (extension opaque) (example'))
    assert 'documents changed' in run('compare', record, manifest, proofs)
    assert inventory(record) == before
    annotated = root / 'records' / 'annotated'
    run('record', manifest, proofs, annotated, '--certificate', record / 'proof.cert')
    assert 'extension' in (annotated / 'documents/sources/Roundtrip.geb.csexp').read_text()
    source.write_text(original)

    # A saved proof remains usable when the current script cannot find it.
    proofs.write_text(original_proofs.replace('normalize 64', 'normalize 0'))
    assert 'saved certificate replayed' in run('compare', record, manifest, proofs)
    cached = root / 'records' / 'cached'
    run('record', manifest, proofs, cached, '--certificate', record / 'proof.cert')
    run('check', cached)
    failed = root / 'records' / 'failed'
    run('record', manifest, proofs, failed, ok=False)
    assert not failed.exists()
    assert not list(failed.parent.glob('.geb-record-*'))
    proofs.write_text(original_proofs)

    # Changed meaning is reported without replacing a record or a saved certificate.
    source.write_text(original.replace('(unwrap (wrap x))', '(node 0 (cons x (nil T)))')
                      .replace('(quote (7 (8))))', '(quote (0 (7 (8)))))', 1))
    run('compare', record, manifest, proofs, ok=False)
    source.write_text(original + '\n(def unrelated (quote (42)))\n')
    assert 'program.img differs' in run('compare', record, manifest, proofs, ok=False)
    source.write_text(original)
    proofs.write_text(original_proofs.replace('Roundtrip.run Roundtrip.identity',
                                             'Roundtrip.identity Roundtrip.identity'))
    run('compare', record, manifest, proofs, ok=False)
    run('record', manifest, proofs, failed, '--certificate', record / 'proof.cert', ok=False)
    assert not failed.exists()
    proofs.write_text(original_proofs)
    assert inventory(record) == before

    # Records carry the sources they need and survive relocation without the original project.
    moved = root / 'relocated record'
    shutil.move(record, moved)
    shutil.rmtree(project)
    run('verify', moved, env=offline)
    run('check', moved, cwd=root)

    damaged = root / 'damaged'
    def reset():
        if damaged.exists():
            shutil.rmtree(damaged)
        shutil.copytree(moved, damaged)

    reset()
    (damaged / 'project/lib/Box.geb').write_text('corrupt')
    assert 'integrity differs' in run('verify', damaged, ok=False)
    reset()
    (damaged / 'extra').write_text('unlisted')
    assert 'integrity differs' in run('verify', damaged, ok=False)
    reset()
    (damaged / 'proof.cert').unlink()
    (damaged / 'proof.cert').symlink_to(moved / 'proof.cert')
    assert 'symbolic link' in run('verify', damaged, ok=False)
    reset()
    index = damaged / 'record.json'
    metadata = json.loads(index.read_text())
    metadata['format'] = 'geb-development/unsupported'
    index.write_text(json.dumps(metadata))
    assert 'unsupported' in run('verify', damaged, ok=False)
    metadata['format'] = 'geb-development/v1'
    metadata['manifest'] = '../outside'
    index.write_text(json.dumps(metadata))
    assert 'relative record path' in run('verify', damaged, ok=False)

    # Checksums alone do not establish semantics; replay checks even a rehashed certificate.
    reset()
    cert = damaged / 'proof.cert'
    cert.write_bytes(b'not a certificate')
    index = damaged / 'record.json'
    metadata = json.loads(index.read_text())
    metadata['files']['proof.cert'] = hashlib.sha256(cert.read_bytes()).hexdigest()
    index.write_text(json.dumps(metadata))
    run('verify', damaged, env=offline)
    run('check', damaged, ok=False)

    # A proof document's imports are archived with it, below the proof document, and the record
    # names them; the record of a development without imports keeps the earlier format.
    assert info['format'] == 'geb-development/v1' and 'imports' not in info
    authoring = repo / 'examples/authoring'
    development = root / 'development'
    development.mkdir()
    for name in ('Pair.geb', 'Lists.geb', 'Pair.proofs.geb', 'pair.manifest'):
        shutil.copyfile(authoring / name, development / name)
    (development / 'More.proofs.geb').write_text(
        '(proofs 2 (import Pair.proofs.geb)\n'
        '  (theorem append-nil-again\n'
        '    (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))\n'
        '    (by (reduce weak append-nil))))\n')
    imported = root / 'records' / 'imported'
    run('record', development / 'pair.manifest', development / 'More.proofs.geb', imported, cwd=root)
    info = json.loads((imported / 'record.json').read_text())
    assert info['format'] == 'geb-development/v2' and info['imports'] == ['Pair.proofs.geb']
    assert (imported / 'proofs/Pair.proofs.geb').read_bytes() == (
        authoring / 'Pair.proofs.geb').read_bytes()
    assert (imported / 'documents/imports/Pair.proofs.geb.csexp').is_file()
    (development / 'Pair.proofs.geb').unlink()
    run('verify', imported, env=offline)
    assert 'saved certificate replayed' in run('check', imported)
    (imported / 'proofs/Pair.proofs.geb').write_text('corrupt')
    assert 'integrity differs' in run('verify', imported, ok=False)

    # Code-only records keep the compiler, the original and canonical program, and checked core.
    requests = root / 'requests'
    shutil.copytree(repo / 'examples/requests', requests)
    manifest = requests / 'requests.manifest'
    code = root / 'records' / 'requests'
    run('record', manifest, code)
    info = json.loads((code / 'record.json').read_text())
    assert info['format'] == 'geb-program/v1' and 'proofs' not in info
    assert not (code / 'proof.cert').exists() and not (code / 'authoring.lean.txt').exists()
    assert (code / 'project/Index.geb').read_bytes() == (requests / 'Index.geb').read_bytes()
    assert 'documents unchanged' in run('compare', code, manifest)
    assert 'proof document' in run('compare', code, manifest, proofs, ok=False)
    assert 'proof document' in run('compare', moved, manifest, ok=False)
    assert 'proof document' in run('migrate-proof-v2', code, failed, ok=False)
    assert '--certificate requires' in run('record', manifest, failed,
                                           '--certificate', moved / 'proof.cert', ok=False)
    index = requests / 'Index.geb'
    original = index.read_text()
    index.write_text(original + '\n; A document-only edit.\n')
    assert 'documents changed' in run('compare', code, manifest)
    index.write_text(original.replace('(quote (1 (0 (0 (97))) (0 (0 (98)))))', '(quote (9))'))
    assert 'example' in run('record', manifest, failed, ok=False)
    assert 'example' in run('compare', code, manifest, ok=False)
    assert not failed.exists()
    index.write_text(original + '\n(def unrelated 42)\n')
    assert 'program.img differs' in run('compare', code, manifest, ok=False)
    shutil.rmtree(requests)
    moved_code = root / 'relocated requests'
    code.rename(moved_code)
    run('verify', moved_code, env=offline)
    assert 'documents unchanged' in run('check', moved_code, cwd=root)

# The committed corpus is replayed, never regenerated by this test.
before = inventory(sample / 'record')
run('check', sample / 'record')
run('compare', sample / 'record', sample / 'roundtrip.manifest', sample / 'Roundtrip.proofs.geb')
assert inventory(sample / 'record') == before
print('test-preservation: archived sources, replay, comparison, integrity and atomic creation passed')
PY
