#!/usr/bin/env bash
# Run the saved-value fixture. Supply a new directory to retain both records and their files.
set -euo pipefail
if [ "$#" -eq 1 ]; then
  mkdir -- "$1"
  work=$(cd -- "$1" && pwd)
elif [ "$#" -eq 0 ]; then
  work=$(mktemp -d)
  trap 'rm -rf "$work"' EXIT
else
  echo "usage: $0 [NEW_DIRECTORY]" >&2
  exit 2
fi
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-compile geb-defs geb-kernel
python3 - "$work" <<'PY'
from pathlib import Path
import json
import shutil
import subprocess
import sys

repo = Path.cwd()
work = Path(sys.argv[1]).resolve()
fixture = repo / 'examples/value-migration'
author = repo / '.lake/build/bin/geb-author'
kernel = repo / '.lake/build/bin/geb-kernel'
preserve = [sys.executable, repo / 'scripts/preserve.py', '--no-build']

def run(*args, status=0):
    result = subprocess.run(args, cwd=work, capture_output=True, text=True, timeout=180)
    assert result.returncode == status, (args, result.returncode, result.stdout, result.stderr)

def definitions(record):
    return dict(line.split('\t') for line in (record / 'program.defs').read_text().splitlines())

old, new = work / 'v1', work / 'v2'
proof = fixture / 'Client.proofs.geb'
run(*preserve, 'record', fixture / 'v1.manifest', proof, old)
# Start from the recorded documents and install the upgrade's manifest and sources.
project = shutil.copytree(old / 'project', work / 'upgrade')
shutil.copytree(fixture / 'v2', project / 'v2')
for source in ('v2.manifest', 'Upgrade.geb'):
    shutil.copyfile(fixture / source, project / source)
manifest = project / 'v2.manifest'
proof = old / 'proofs' / proof.name
run(author, 'replay', manifest, proof, old / 'proof.cert', status=1)
run(author, 'transport', manifest, proof, old / 'proof.cert', work / 'transported.cert')
run(*preserve, 'record', manifest, proof, new, '--certificate', work / 'transported.cert')

# Both records archive the pinned revision of the dependency and check independently.
pins = fixture / 'SHA256SUMS'
shutil.copyfile(pins, work / pins.name)
revisions = dict(line.split()[::-1] for line in pins.read_text().splitlines())
for record in (old, new):
    source = record.name + '/Signal.geb'
    info = json.loads((record / 'record.json').read_text())
    assert source in info['sources'] and info['files']['project/' + source] == revisions[source]
    run(*preserve, 'check', record)

# Upgrading the manifest selects the new declaration and adds the migration. The shared
# documents and theorem are unchanged. The swapped declarations change references in select
# and clauses in display. The member predicate still recognizes the same two bare tags.
for name in ('sources/Files.geb.csexp', 'sources/Codec.geb.csexp', 'sources/Client.geb.csexp',
             'proofs.csexp'):
    assert (old / 'documents' / name).read_bytes() == (new / 'documents' / name).read_bytes()
before, after = definitions(old), definitions(new)
assert before.keys() <= after.keys()
assert {k for k in before if before[k] != after[k]} == {
    'Signal.red', 'Signal.green', 'Signal.version', 'Client.select', 'Client.display'}
assert before['Signal.red'] == after['Signal.green'] and before['Signal.green'] == after['Signal.red']
assert all(k.startswith('Upgrade.') for k in after.keys() - before.keys())

def interact(record, entry, src, dst, status=0):
    run(kernel, 'interact', record / 'program.img', entry, src, dst, status=status)

for color, name, old_tag in [('red', b'R', 0), ('green', b'G', 1)]:
    choice = work / (color + '.name')
    choice.write_bytes(name)
    saved = work / (color + '.v1')
    migrated = work / (color + '.v2')
    interact(old, 'Client.save', choice, saved)
    assert saved.read_bytes() == bytes([76, 1, old_tag])
    if color == 'red':
        assert saved.read_bytes() == (fixture / 'red.v1').read_bytes()
    interact(old, 'Client.observe', saved, 'old.output')
    interact(new, 'Client.observe', saved, 'refused', status=1)
    interact(new, 'Upgrade.migrate', saved, migrated)
    interact(new, 'Client.save', choice, 'new.save')
    assert migrated.read_bytes() == (work / 'new.save').read_bytes() == bytes([76, 2, 1 - old_tag])
    interact(new, 'Client.observe', migrated, 'new.output')
    assert (work / 'old.output').read_bytes() == (work / 'new.output').read_bytes() == name
    assert saved.read_bytes() == bytes([76, 1, old_tag])
assert not (work / 'refused').exists()

# Each entry accepts only its named datatype, version, arity and constructor tags.
refused = work / 'refused'
refused.write_bytes(b'keep')
for entry, version, other in [('Client.observe', 2, 1), ('Upgrade.migrate', 1, 2)]:
    for malformed in ([77, version, 0], [76, 99, 0], [76, other, 0], [76, version, 2],
                      [76, version], [76, version, 0, 0], []):
        (work / 'bad.input').write_bytes(bytes(malformed))
        interact(new, entry, 'bad.input', refused, status=1)
        assert refused.read_bytes() == b'keep'
print('test-value-migration: pinned records, transported proof, saved values and rejections passed')
PY
