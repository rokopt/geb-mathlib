#!/usr/bin/env bash
# Retain and check kernel-source annotations through the native host.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-kernel
python3 - <<'PY'
from pathlib import Path
import subprocess
import tempfile

kernel = Path('.lake/build/bin/geb-kernel').resolve()

def run(*args, ok=True):
    result = subprocess.run([str(kernel), *map(str, args)], capture_output=True, timeout=30)
    if (result.returncode == 0) != ok:
        raise AssertionError((args, result.returncode, result.stdout, result.stderr))
    return result

with tempfile.TemporaryDirectory(prefix='geb-source-annotations-') as directory:
    root = Path(directory)
    source = root / 'source with spaces.geb'
    renamed = root / 'renamed.geb'
    record = root / 'source.csexp'
    source.write_text('; prose: λ\n(def f (lam ("λ" T) "λ"))\n; trailing\n', encoding='utf-8')
    renamed.write_text('; revised\n(def f (lam (other T) other))\n', encoding='utf-8')
    original = source.read_bytes()
    run('annotations', source, record)
    run('check-annotations', record)
    saved = record.read_bytes()
    assert b' trailing' in saved and 'λ'.encode() in saved
    assert source.read_bytes() == original

    # The ordinary compiler observes no change of meaning from names or comments.
    run('build', source, root / 'first.img')
    run('build', renamed, root / 'second.img')
    assert (root / 'first.img').read_bytes() == (root / 'second.img').read_bytes()
    run('annotations', renamed, root / 'second.csexp')
    assert (root / 'second.csexp').read_bytes() != saved

    # Records carry their source and remain checkable after it is removed.
    source.unlink()
    moved = root / 'relocated.csexp'
    record.rename(moved)
    run('check-annotations', moved)

    # Schema changes and source changes cannot silently reuse a saved correspondence.
    bad = root / 'bad.csexp'
    bad.write_bytes(saved.replace(b'geb-source-ann/v1', b'geb-source-ann/v2'))
    run('check-annotations', bad, ok=False)
    bad.write_bytes(saved.replace(b'lam', b'let'))
    run('check-annotations', bad, ok=False)
    bad.write_bytes(saved[:-1])
    run('check-annotations', bad, ok=False)

    # Rejection preserves an existing output, including when resolution succeeds but typing fails.
    for text in ('(def f missing)', '(def f (fst 7))', '(module M (def f 7))', '(def f'):
        source.write_text(text, encoding='utf-8')
        run('annotations', source, moved, ok=False)
        assert moved.read_bytes() == saved
    run('check-annotations', moved)

print('source annotation commands passed')
PY
