#!/usr/bin/env bash
# Replay an archived development across proof-source versions without proof search.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-compile geb-defs geb-kernel
python3 - <<'PY'
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

repo = Path.cwd()
author = repo / '.lake/build/bin/geb-author'
preserve = repo / 'scripts/preserve.py'

def run(argv, ok=True):
    result = subprocess.run(list(map(str, argv)), capture_output=True, text=True, timeout=180)
    assert result.returncode == (0 if ok else 1), (argv, result.stdout[-4000:], result.stderr)
    return result.stdout + result.stderr

def archive(*args, ok=True):
    return run([sys.executable, preserve, '--no-build', *args], ok)

def inventory(root):
    return {p.relative_to(root).as_posix(): p.read_bytes()
            for p in root.rglob('*') if p.is_file()}

with tempfile.TemporaryDirectory(prefix='geb-migration-') as directory:
    root = Path(directory)
    project = root / 'source λ with spaces'
    project.mkdir()
    for name in ('Pair.geb', 'Lists.geb', 'Pair.proofs.geb', 'pair.manifest'):
        shutil.copyfile(repo / 'examples/authoring' / name, project / name)
    manifest, proofs = project / 'pair.manifest', project / 'Pair.proofs.geb'
    proofs.write_text(proofs.read_text().replace('(proofs 1',
        '; A retained reference: {geb}`Pair.first`, λ.\n(proofs\n; version\n1'),
        encoding='utf-8')
    source = project / 'Pair.geb'
    source.write_text(source.read_text().replace('(note (example',
        '(note (extension "opaque λ") (example'), encoding='utf-8')
    cert = root / 'saved.cert'
    run([author, 'prove', manifest, proofs, cert])
    proofs.write_text(proofs.read_text().replace('normalize 64', 'normalize 0'), encoding='utf-8')
    run([author, 'prove', manifest, proofs, root / 'unproved.cert'], ok=False)
    old = root / 'old'
    archive('record', manifest, proofs, old, '--certificate', cert)
    # Neither the original project nor its location is needed for migration.
    shutil.rmtree(project)
    moved = root / 'relocated old'
    old.rename(moved)
    old = moved
    before = inventory(old)
    archive('migrate-proof-v2', old, old / 'nested', ok=False)
    assert inventory(old) == before
    new = root / 'new'
    assert 'without proof search' in archive('migrate-proof-v2', old, new)
    assert inventory(old) == before
    archive('verify', new)
    archive('check', new)
    info = json.loads((new / 'record.json').read_text())
    new_manifest, new_proofs = new / info['manifest'], new / info['proofs']
    old_proofs = old / info['proofs']
    receipt = json.loads((new / 'migration.json').read_text())
    assert receipt == dict(format='geb-migration/v1', operation='proofs/1-to-2',
        previous_record_sha256=hashlib.sha256((old / 'record.json').read_bytes()).hexdigest())
    # All archived source files and the compiled meaning remain byte-identical.
    for name in info['sources']:
        assert (new / 'project' / name).read_bytes() == (old / 'project' / name).read_bytes()
    for name in ('program.img', 'program.defs', info['manifest']):
        assert (new / name).read_bytes() == (old / name).read_bytes()
    # Formatting may change; replacing only the version back reproduces the full
    # canonical decorated document, including comments on the version atom.
    restored = root / 'restored.geb'
    text, count = re.subn(r'(\(proofs\s*(?:;[^\n]*\n\s*)*)2\b', r'\g<1>1',
                         new_proofs.read_text(), count=1)
    assert count == 1
    restored.write_text(text, encoding='utf-8')
    canonical = root / 'restored.csexp'
    run([author, 'convert', 'canonical', new_manifest, restored, canonical])
    assert canonical.read_bytes() == (old / 'documents/proofs.csexp').read_bytes()
    # Strict durable encodings carry the same document and migrate to the same artifacts.
    for spelling in ('canonical', 'advanced'):
        encoded = root / (spelling + '.geb')
        run([author, 'convert', spelling, new_manifest, old_proofs, encoded])
        result = json.loads(run([author, 'migrate-proof-v2', new_manifest, encoded,
                                 old / 'proof.cert']))
        assert bytes(result['source']) == new_proofs.read_bytes()
        assert bytes(result['certificate']) == (new / 'proof.cert').read_bytes()
    # The certificate envelope changes; its payload is reused. The old envelope
    # must fail under the new source, while the migrated certificate replays.
    assert (new / 'proof.cert').read_bytes() != (old / 'proof.cert').read_bytes()
    run([author, 'replay', new_manifest, new_proofs, old / 'proof.cert'], ok=False)
    run([author, 'replay', new_manifest, new_proofs, new / 'proof.cert'])
    run([author, 'prove', new_manifest, new_proofs, root / 'still-unproved.cert'], ok=False)
    after = inventory(new)
    archive('migrate-proof-v2', old, new, ok=False)
    assert inventory(new) == after and inventory(old) == before
    failed = root / 'failed'
    archive('migrate-proof-v2', new, failed, ok=False)
    assert not failed.exists()
    damaged = root / 'damaged'
    shutil.copytree(old, damaged)
    (damaged / info['proofs']).write_text('corrupt')
    assert 'integrity differs' in archive('migrate-proof-v2', damaged, failed, ok=False)
    assert not failed.exists()
    # Even a rehashed invalid certificate must fail semantic replay before publication.
    shutil.rmtree(damaged)
    shutil.copytree(old, damaged)
    (damaged / 'proof.cert').write_bytes(b'not a certificate')
    metadata = json.loads((damaged / 'record.json').read_text())
    metadata['files']['proof.cert'] = hashlib.sha256(b'not a certificate').hexdigest()
    (damaged / 'record.json').write_text(json.dumps(metadata))
    archive('verify', damaged)
    archive('migrate-proof-v2', damaged, failed, ok=False)
    assert not failed.exists() and not list(root.glob('.geb-record-*'))
    assert inventory(old) == before and inventory(new) == after
print('test-proof-migration: relocated records, decorated source, replay and failure atomicity passed')
PY
