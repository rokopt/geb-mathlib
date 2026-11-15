#!/usr/bin/env bash
# Check image profiles, migration and execution through the seed and the Geb compiler.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-kernel geb-compile geb-defs
python3 - <<'PY'
from pathlib import Path
import subprocess
import tempfile

repo = Path.cwd()
kernel = repo / '.lake/build/bin/geb-kernel'
compiler = repo / '.lake/build/bin/geb-compile'
defs = repo / '.lake/build/bin/geb-defs'

def run(tool, *args, ok=True):
    result = subprocess.run([str(tool), *map(str, args)], capture_output=True, timeout=60)
    assert (result.returncode == 0) == ok, (args, result.stdout, result.stderr)
    return result

with tempfile.TemporaryDirectory(prefix='geb-image-profile-') as directory:
    root = Path(directory)
    source = root / 'identity.geb'
    source.write_text('(def main (lam ((x T)) x))\n')
    seed, compiled = root / 'seed.img', root / 'compiled.img'
    run(kernel, 'build', source, seed)
    run(compiler, 'image', source, compiled)
    current = seed.read_bytes()
    assert current[:6] == b'GEBK\x02\x01'
    assert compiled.read_bytes() == current

    # Format 1 fixes the same kernel profile implicitly. Migration retains its bit count
    # and payload exactly, and applying migration again changes no byte.
    old, migrated, again = root / 'old.img', root / 'migrated.img', root / 'again.img'
    legacy = b'GEBK\x01' + current[6:]
    old.write_bytes(legacy)
    run(kernel, 'migrate-image', old, migrated)
    assert old.read_bytes() == legacy and migrated.read_bytes() == current
    run(kernel, 'migrate-image', migrated, again)
    assert again.read_bytes() == current

    # The same entry executes under either framing, including arbitrary input bytes.
    data, output = root / 'input', root / 'output'
    data.write_bytes(bytes(range(256)))
    for image in (old, seed, compiled, migrated):
        run(kernel, 'run', image, 'main', data, output)
        assert output.read_bytes() == data.read_bytes()
    run(defs, old, root / 'old.defs')
    run(defs, migrated, root / 'new.defs')
    assert (root / 'old.defs').read_bytes() == (root / 'new.defs').read_bytes()

    # Format and profile are checked independently. Rejection never replaces an output.
    invalid = root / 'invalid.img'
    malformed = [b'', current[:5], current[:6], current[:13], current[:-1], current + b'\x00',
                 b'BADK' + current[4:], b'GEBK\x03' + current[5:],
                 b'GEBK\x02\x00' + current[6:], b'GEBK\x02\x02' + current[6:],
                 b'GEBK\x02\xff' + current[6:], legacy[:-1], legacy + b'\x00',
                 # A leaf has two payload bits; its unused bits must be zero.
                 b'GEBK\x01' + (2).to_bytes(8, 'little') + b'\x06',
                 b'GEBK\x02\x01' + (2).to_bytes(8, 'little') + b'\x06']
    for bad in malformed:
        invalid.write_bytes(bad)
        for args in (('migrate-image', invalid, output),
                     ('run', invalid, 'main', data, output)):
            output.write_bytes(b'keep existing output')
            run(kernel, *args, ok=False)
            assert output.read_bytes() == b'keep existing output'
        run(defs, invalid, output, ok=False)
        assert output.read_bytes() == b'keep existing output'

print('test-image-profile: framing, profiles, migration, execution and rejection passed')
PY
