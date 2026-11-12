#!/usr/bin/env bash
# Exercise source navigation through the same reader and module elaborator as compilation.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author
python3 - <<'PY'
import json
from pathlib import Path
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()

def decoded(result):
    for symbol in result['symbols'] + [result['target']]:
        if symbol is not None:
            for field in ('name', 'signature', 'documentation'):
                symbol[field] = bytes(symbol[field]).decode('utf8')
    return result

with tempfile.TemporaryDirectory(prefix='geb-navigation-') as tmp:
    root = Path(tmp)
    lib = root / 'Library.geb'
    use = root / 'Use.geb'
    manifest = root / 'program.manifest'
    lib.write_text('''(module A (export identity)
  ; The documented identity.
  ;Without a space after the semicolon.
  (note (future opaque))
  (defn identity ((x T)) T x))
(module Generic (parameter X) (export ident)
  (defn ident ((x X)) X x))
(data Nat (zero) (succ Nat))
(deftype Tree T)
''')
    source = '''(module B (import A as X) (export forward)
  (defn forward ((x T)) T (X.identity x)))
(module C (import B) (import A) (import (Generic Tree) as G) (export run)
  (defn run ((x T)) T (forward (G.ident x)))
  (defn shadow ((identity T)) T identity)
  (defn chained ((x T)) T (let* ((identity T (identity x))) identity))
  (defn quoted ((x T)) T (quote identity)))
(def value (succ zero))
(def named (lam ((x T)) (B.forward x)))
(def branch (case value ((succ identity) identity) ((zero) zero)))
(def quoted-marker (quote ("%navigation" identity)))
'''
    use.write_text(source)
    manifest.write_text('(program nav (edition 0) '
        '(document (syntax authoring 0) (schema 0) (prose verso 0)) '
        '(sources Library.geb Use.geb) (entries named))')
    def query(fragment=None, text=source, snapshots=(), ok=True):
        offset = text.index(fragment) if fragment else 0
        prefix = text[:offset]
        request = dict(file=str(use), line=prefix.count('\n') + 1 if fragment else 0,
            column=len(prefix.rsplit('\n', 1)[-1].encode()) + 1 if fragment else 0,
            documents=list(snapshots))
        result = subprocess.run([runner, 'navigation', manifest], input=' \n' + json.dumps(request),
            capture_output=True, text=True, timeout=15)
        assert result.returncode == (0 if ok else 1), (result.stdout, result.stderr)
        return decoded(json.loads(result.stdout)) if ok else None
    result = query('X.identity x')
    assert result['target']['name'] == 'A.identity'
    assert result['target']['file'] == str(lib)
    assert result['target']['documentation'] == (
        'The documented identity.\nWithout a space after the semicolon.')
    assert query('forward (G')['target']['name'] == 'B.forward'
    assert query('G.ident x')['target']['name'] == 'Generic.ident'
    assert query('Generic Tree')['target']['name'] == 'Generic'
    assert query('Tree) as G')['target']['name'] == 'Tree'
    assert query('forward)\n  (defn')['target']['name'] == 'B.forward'
    assert query('run)\n  (defn')['target']['name'] == 'C.run'
    assert query('identity)\n  (defn chained')['target']['kind'] == 'variable'
    assert query('identity x')['target']['name'] == 'A.identity'
    assert query('identity))\n  (defn quoted')['target']['kind'] == 'variable'
    assert query('identity)))')['target'] is None
    assert query('succ zero')['target']['name'] == 'succ'
    assert query('B.forward x')['target']['name'] == 'B.forward'
    assert query('succ identity')['target']['name'] == 'succ'
    assert query('identity) identity')['target']['kind'] == 'variable'
    assert query('identity) ((zero')['target']['kind'] == 'variable'
    assert query('%navigation" identity')['target'] is None
    # UTF-8 byte columns, quoted names, CRLF, and snapshots never save a buffer.
    changed = source + '(def "λ😀" (lam ((x T)) (B.forward x)))\n(def last "λ😀")\n'
    changed = changed.replace('\n', '\r\n')
    offset = changed.rindex('"λ😀"')
    prefix = changed[:offset]
    req = dict(file=str(use), line=prefix.count('\n') + 1,
        column=len(prefix.rsplit('\n', 1)[-1].encode()) + 1,
        documents=[dict(path=str(use), text=changed)])
    result = subprocess.run([runner, 'navigation', manifest], input=json.dumps(req),
        capture_output=True, text=True, check=True, timeout=15)
    assert decoded(json.loads(result.stdout))['target']['name'] == 'λ😀'
    assert use.read_text() == source
    for invalid in (json.dumps(req) + '{}', '{"file":"a","file":"b"}'):
        rejected = subprocess.run([runner, 'navigation', manifest], input=invalid,
            capture_output=True, text=True, timeout=15)
        assert rejected.returncode == 1 and not rejected.stdout
        assert 'JSON' in rejected.stderr
    query(snapshots=[dict(path=str(use), text=source + '(')], ok=False)
    query(snapshots=[dict(path=str(use), text=source + '(def value 0)')], ok=False)
    # A private qualified declaration must not be found by spelling alone.
    lib.write_text(lib.read_text() + '(module Hidden (def secret 0))\n')
    changed = source + '(def attempt Hidden.secret)\n'
    assert query('Hidden.secret', changed, [dict(path=str(use), text=changed)])['target'] is None
print('test-navigation: scopes, aliases, templates, comments, snapshots and byte positions passed')
PY
