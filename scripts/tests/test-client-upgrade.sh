#!/usr/bin/env bash
# Upgrade the client template's previous revision, examples/client-upgrade/client/ with the library
# at the revision it pins, to the template and the library of this checkout. Supply a new directory
# to retain both records, the saved inputs and the files the two clients write.
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
import hashlib
import json
import shutil
import subprocess
import sys

repo = Path.cwd()
work = Path(sys.argv[1]).resolve()
fixture = repo / 'examples/client-upgrade'
author = repo / '.lake/build/bin/geb-author'
kernel = repo / '.lake/build/bin/geb-kernel'
defs = repo / '.lake/build/bin/geb-defs'
preserve = [sys.executable, repo / 'scripts/preserve.py', '--no-build']

def run(*args, status=0):
    result = subprocess.run(args, cwd=work, capture_output=True, text=True, timeout=300)
    assert result.returncode == status, (args, result.returncode, result.stdout, result.stderr)

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def files(root):
    return {p.relative_to(root).as_posix() for p in root.rglob('*') if p.is_file()}

def identities(record):
    out = work / (record.name + '.identities')
    run(defs, '--identities', record / 'program.img', out)
    return dict(line.split('\t') for line in out.read_text().splitlines())

# The previous revision is the one its pins name, its library among them.
pins = {name.removeprefix('client/'): d for d, name in
        (line.split() for line in (fixture / 'SHA256SUMS').read_text().splitlines())}
previous = shutil.copytree(fixture / 'client', work / 'previous')
assert files(previous) == pins.keys()
assert all(digest(previous / name) == d for name, d in pins.items())
old, new = work / 'v1', work / 'v2'
run(*preserve, 'record', previous / 'client.manifest', previous / 'Client.proofs.geb', old)
info = json.loads((old / 'record.json').read_text())
for name, d in pins.items():
    kept = ('proofs/' if name.endswith('.proofs.geb') else 'project/') + name
    assert info['files'][kept] == d, name

# The upgrade checks out the template and pins the library of this checkout. The previous
# certificate names the previous program, so it is transported rather than replayed.
upgraded = shutil.copytree(repo / 'examples/client', work / 'upgraded', symlinks=True)
shutil.copytree(repo / 'library', upgraded / 'geb/library')
manifest, proof = upgraded / 'client.manifest', upgraded / 'Client.proofs.geb'
run(author, 'replay', manifest, proof, old / 'proof.cert', status=1)
run(author, 'transport', manifest, proof, old / 'proof.cert', work / 'transported.cert')
run(*preserve, 'record', manifest, proof, new, '--certificate', work / 'transported.cert')
for record in (old, new):
    run(*preserve, 'check', record)

# A document is unchanged where its source is, and the upgrade changes the document of Settings.
for name in files(old / 'documents') & files(new / 'documents'):
    if name.startswith(('sources/', 'imports/')):
        source = name.split('/', 1)[1].removesuffix('.csexp')
        if digest(previous / source) == digest(upgraded / source):
            assert (old / 'documents' / name).read_bytes() == (new / 'documents' / name).read_bytes()
assert digest(old / 'documents/proofs.csexp') == digest(new / 'documents/proofs.csexp')
settings = 'documents/sources/Settings.geb.csexp'
assert (old / settings).read_bytes() != (new / settings).read_bytes()

# The account of the elaborated definitions, by their content identifiers, which a definition
# inserted before others leaves unchanged. The constructor reversed, declared before mirrored,
# gives mirrored the tag that reversed takes from it, and changes the version, the recognizer of
# Settings.Order and the definitions that name a constructor, and so every definition referring
# to a changed one; the upgrade adds the migration. A later revision of the library that changes a
# definition the client uses adds that definition and those referring to it here.
before, after = identities(old), identities(new)
assert before.keys() <= after.keys()
assert {k for k in before if before[k] != after[k]} == {
    'Settings.mirrored', 'Settings.version', 'Settings.Order.member', 'Settings.named',
    'Settings.arrange', 'Settings.save', 'Settings.load', 'Settings.State.member',
    'Settings.after', 'Settings.step', 'Settings.choose', 'Settings.apply'}
assert before['Settings.mirrored'] == after['Settings.reversed']
assert after.keys() - before.keys() == {'Settings.reversed'} | {
    k for k in after if k.startswith('Upgrade.')}

def interact(record, entry, *paths, status=0):
    run(kernel, 'interact', record / 'program.img', entry, *paths, status=status)

(work / 'input').write_bytes(b'abc')
for letter, old_tag, new_tag in [('f', 0, 0), ('m', 1, 2)]:
    saved, migrated = work / (letter + '.v1'), work / (letter + '.v2')
    interact(old, 'Settings.choose', letter, saved)
    assert saved.read_bytes() == bytes([79, 1, old_tag])
    if letter == 'm':
        assert saved.read_bytes() == (fixture / 'mirrored.v1').read_bytes()
    interact(old, 'Settings.apply', saved, 'input', letter + '.old.output')
    # The upgraded client reads no setting of version 1, and the migration writes the order the
    # upgraded client saves for the same letter.
    interact(new, 'Settings.apply', saved, 'input', 'refused', status=1)
    interact(new, 'Upgrade.migrate', saved, migrated)
    interact(new, 'Settings.choose', letter, 'new.saved')
    assert migrated.read_bytes() == (work / 'new.saved').read_bytes() == bytes([79, 2, new_tag])
    interact(new, 'Settings.apply', migrated, 'input', letter + '.new.output')
    assert (work / (letter + '.old.output')).read_bytes() == \
        (work / (letter + '.new.output')).read_bytes()
    assert saved.read_bytes() == bytes([79, 1, old_tag])
assert not (work / 'refused').exists()
assert (work / 'm.new.output').read_bytes() == b'abccba'
# Changing the version byte alone would read the saved mirrored as reversed.
(work / 'relabelled').write_bytes(bytes([79, 2, 1]))
interact(new, 'Settings.apply', 'relabelled', 'input', 'relabelled.output')
assert (work / 'relabelled.output').read_bytes() == b'cba'

# The migration accepts only the datatype's identifier, version 1, one byte and the tags that
# version 1 declared, and writes nothing otherwise.
refused = work / 'refused'
refused.write_bytes(b'keep')
for malformed in ([79, 2, 1], [76, 1, 1], [79, 1, 2], [79, 1], [79, 1, 1, 1], []):
    (work / 'bad.input').write_bytes(bytes(malformed))
    interact(new, 'Upgrade.migrate', 'bad.input', refused, status=1)
    assert refused.read_bytes() == b'keep'
print('test-client-upgrade: pinned revision, transported proof, migrated settings and rejections '
      'passed')
PY
