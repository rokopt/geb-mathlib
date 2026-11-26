#!/usr/bin/env bash
# Check statements over the datatype language, (typed ...) of version 7 of the proof-source
# profile: the library's documents proved and replayed, alone and in a program that names the
# library as a layer; hypotheses, membership and declarations with type parameters at types
# the program does not use them at; what the compiler and the reader reject; goals; the cache;
# the durable spellings; a record; and the transport of a certificate to a changed program.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-compile geb-defs geb-kernel
python3 - <<'PY'
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()

def run(*args, ok=True, timeout=600):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=timeout)
    assert result.returncode == (0 if ok else 1), (args, result.stdout, result.stderr)
    return result.stdout.decode(), result.stderr.decode()

# Hypotheses, a statement without variables, and declarations with type parameters at types the
# library uses them at nowhere: the lists of byte strings, and the optional values of trees.
MORE = '''(proofs 7 (program library) (import Datatypes.proofs.geb)
  (theorem length-of-equal
    (typed
      (forall ((xs (List T)) (ys (List T)))
        (implies (same (equal xs ys)) (equal (Lists.length T xs) (Lists.length T ys)))))
    (by (reduce full same)))
  (theorem closed (typed (equal (Optional.orElse T 7 (Optional.none T)) 7)) (by (reduce full)))
  (theorem one-byte-string
    (typed
      (forall ((b Bytes.Bytes))
        (equal (Lists.length Bytes.Bytes (cons b (nil Bytes.Bytes))) 1)))
    (by (reduce full)))
  (theorem cited
    (typed (forall ((x T)) (equal (Optional.orElse T 0 (Optional.some T x)) x)))
    (by (use or-else-some () ((kernel 0) x))))
  (theorem kernel-statement
    (forall ((x T)) (equal (Bytes.firstLine (cons 10 (cons x (nil T)))) (nil T)))
    (by (normalize 256))))
'''

def balanced(text, start):
    """The form that begins at a parenthesis of a text without comments inside the form."""
    depth = 0
    for i in range(start, len(text)):
        depth += (text[i] == '(') - (text[i] == ')')
        if depth == 0:
            return text[start:i + 1]
    raise AssertionError('unbalanced form')

def document(statement, script='?open', version=7, name='subject'):
    return (f'(proofs {version} (program library) (import Trees.proofs.geb)\n'
            f'  (theorem {name}\n    {statement}\n    (by {script})))\n')

with tempfile.TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    root = tmp / 'library'
    shutil.copytree('library', root)
    manifest = root / 'library.manifest'
    datatypes = root / 'Datatypes.proofs.geb'
    cert, plain = tmp / 'proof.cert', tmp / 'plain.cert'

    # The library's theorems over its datatypes, by the program the document names and by its
    # manifest given.
    run('prove', datatypes, cert)
    run('replay', datatypes, cert)
    run('replay', manifest, datatypes, cert)
    saved = cert.read_bytes()

    more = root / 'More.proofs.geb'
    more.write_text(MORE)
    run('prove', more, plain)
    run('replay', more, plain)

    # A certificate proves the statements it was found for: a changed term and a binder that no
    # longer states membership are each another statement, and a type the terms do not check
    # at leaves none.
    text = datatypes.read_text()
    for old, new in [('(Optional.none T)) d', '(Optional.none T)) 0'),
                     ('(b Bytes.Bytes member)', '(b Bytes.Bytes)'),
                     ('((d T) (x T))', '((d T) (x Bytes.Bytes))')]:
        assert old in text, old
        datatypes.write_text(text.replace(old, new))
        run('replay', datatypes, cert, ok=False)
    datatypes.write_text(text)
    run('replay', datatypes, cert)

    doc = root / 'Subject.proofs.geb'
    def rejected(statement, script, message, version=7, at='2:12'):
        doc.write_text(document(statement, script, version))
        _, err = run('prove', doc, plain, ok=False)
        assert message in err, err
        # The diagnostic is at the theorem's name in the document, or at the hole of its script.
        assert err.startswith(f'{doc}:{at}: error: '), err
        return err

    unchecked = 'the statement of the theorem subject does not check in the datatype language'
    unread = 'its statement does not read'
    # The compiler types the terms: the sides of an equation have one type of the datatype
    # language, a byte string being no tree; membership is stated of a datatype; a name is one
    # the program declares; and a case analysis names its datatype's constructors.
    err = rejected('(typed (forall ((b Bytes.Bytes)) (equal b 0)))', '(reduce full)', unchecked)
    assert '__geb_statement_' not in err, err
    rejected('(typed (forall ((x T member)) (equal x x)))', '(reduce full)', unchecked)
    rejected('(typed (forall ((x T)) (equal (Missing.name x) x)))', '(reduce full)', unchecked)
    rejected('(typed (forall ((b Bytes.Bytes)) (equal (case b ((Optional.none T) 0)) 0)))',
             '(reduce full)', unchecked)
    rejected('(typed (forall ((x T)) (implies (h (equal x (Bytes.bytes (nil T)))) (equal x x))))',
             '(reduce full)', unchecked)
    # The reader reads the form: an equation, binders and hypotheses of distinct names that a
    # variable may take, and no statement over the datatype language before version 7.
    rejected('(typed (forall ((x T)) x))', '(reduce full)', unread)
    rejected('(typed (forall ((x T) (x T)) (equal x x)))', '(reduce full)', unread)
    rejected('(typed (forall ((b Bytes.Bytes b)) (equal b b)))', '(reduce full)', unread)
    rejected('(typed (forall ((b Bytes.Bytes m)) (implies (m (equal b b)) (equal b b))))',
             '(reduce full)', unread)
    rejected('(typed (forall ((b Bytes.Bytes m extra)) (equal b b)))', '(reduce full)', unread)
    rejected('(typed (forall ((x T)) (equal x x)))', '(reduce full)', unread, version=6)
    rejected('(typed (forall ((x T)) (equal x x)) (equal 0 0))', '(reduce full)', unread)
    assert not plain.exists() or plain.read_bytes() != b''

    # A statement at a datatype is of its erasure at every tree unless a binder states
    # membership: the goal of a hole shows the hypothesis a binder names, and is the statement
    # over the internal language of the erasure, which a document reads back and the script of
    # the library's theorem proves.
    rebuilt = '(equal (case b ((Bytes.bytes & cs) (Bytes.bytes cs))) b)'
    err = rejected(f'(typed (forall ((b Bytes.Bytes)) {rebuilt}))', '?open',
                   'leaves the hole ?open open', at='4:9')
    assert 'assuming' not in err and 'Bytes.Bytes.member' not in err, err
    err = rejected(f'(typed (forall ((b Bytes.Bytes member)) {rebuilt}))', '?open',
                   'leaves the hole ?open open', at='4:9')
    assert '(assuming (member (equal ' in err and 'Bytes.Bytes.member' in err, err
    goal = err.split('at the goal ', 1)[1].splitlines()[0]
    script = balanced(text, text.index('(by', text.index('(theorem bytes-of-bytes')))[len('(by'):-1]
    doc.write_text(document(goal, script, version=6))
    run('prove', doc, plain)
    run('replay', doc, plain)

    # The cache of a development: its theorems are taken on a second run, and the certificate
    # found with the kept layers of the program is the one found without them.
    caches = tmp / 'caches'
    out, _ = run('check', '--cache', caches, datatypes)
    assert 'cache: 0 taken, 0 checked, 9 proved, 0 not proved' in out, out
    out, _ = run('check', '--cache', caches, datatypes)
    assert 'cache: 9 taken, 0 checked, 0 proved, 0 not proved' in out, out
    run('prove', '--cache', caches, datatypes, plain)
    assert plain.read_bytes() == saved
    run('replay', '--cache', caches, datatypes, plain)

    # The durable spellings hold the same statements: the certificate of the document as
    # written replays against its canonical encoding.
    canonical = root / 'Canonical.proofs.geb'
    run('convert', 'canonical', manifest, datatypes, canonical)
    for name in ('Trees.proofs.geb',):
        assert (root / name).exists()
    run('replay', manifest, canonical, cert)

    # A record keeps the development with its program and its certificate, and is checked from
    # what it keeps: the archived sources compiled again and the certificate replayed.
    preserve = [sys.executable, 'scripts/preserve.py', '--no-build']
    record = tmp / 'record'
    for action in (['record', manifest, datatypes, record], ['check', record]):
        result = subprocess.run([*preserve, *map(str, action)], capture_output=True, timeout=600)
        assert result.returncode == 0, (action, result.stdout, result.stderr)

    # A program that names the library as a layer proves the library's theorems against its own
    # definitions, the declarations with type parameters compiled at the statements' types
    # after them.
    client = tmp / 'client'
    client.mkdir()
    (client / 'library').symlink_to(root)
    (client / 'Use.geb').write_text('(module Use (export pick) (import Optional)\n'
        '  (defn pick ((m (Option T))) T (orElse T 3 m)))\n')
    (client / 'client.manifest').write_text(
        '(program client (edition 0) (document (syntax authoring 0) (schema 0) (prose verso 0))\n'
        '  (layers (library (manifest library/library.manifest)) (application Use.geb))\n'
        '  (entries))\n')
    (client / 'Use.proofs.geb').write_text(
        '(proofs 7 (program client) (import library/Datatypes.proofs.geb)\n'
        '  (theorem pick-some (typed (forall ((x T)) (equal (Use.pick (Optional.some T x)) x)))\n'
        '    (by (obtain h or-else-some () ((kernel 3) x)\n'
        '      (reduce-hypotheses full (h) (reduce full h))))))\n')
    used = tmp / 'client.cert'
    run('prove', client / 'Use.proofs.geb', used)
    run('replay', client / 'Use.proofs.geb', used)
    run('prove', '--cache', caches, client / 'Use.proofs.geb', plain)
    assert plain.read_bytes() == used.read_bytes()

    # A certificate is of one compiled program, the statements' definitions after the
    # manifest's: after a definition is added before them it does not replay, and its transport
    # to the changed program does.
    (client / 'Use.geb').write_text('(module Use (export pick other) (import Optional)\n'
        '  (def other 5)\n'
        '  (defn pick ((m (Option T))) T (orElse T 3 m)))\n')
    run('replay', client / 'Use.proofs.geb', used, ok=False)
    carried = tmp / 'carried.cert'
    run('transport', client / 'client.manifest', client / 'Use.proofs.geb', used, carried)
    run('replay', client / 'Use.proofs.geb', carried)

    # Navigation reads the statement's scopes: the hypothesis of membership that a binder names
    # is one of the script's hypotheses, beside the binder's variable; and a formula statement of
    # a document of version 7 keeps the scopes of its assumptions.
    def navigate(path, fragment):
        text = path.read_text()
        prefix = text[:text.index(fragment)]
        request = dict(file=str(path), line=prefix.count('\n') + 1,
            column=len(prefix.rsplit('\n', 1)[-1].encode()) + 1, proofs=str(path), documents=[])
        result = subprocess.run([runner, 'navigation', manifest], input=json.dumps(request),
            capture_output=True, text=True, timeout=30)
        assert result.returncode == 0, result.stderr
        return decoded(json.loads(result.stdout))
    # The host JSON encodes strings as arrays of codepoints.
    def decoded(value):
        if isinstance(value, list):
            if value and all(isinstance(x, int) for x in value):
                return ''.join(map(chr, value))
            return [decoded(x) for x in value]
        if isinstance(value, dict):
            return {k: decoded(v) for k, v in value.items()}
        return value
    nav = navigate(datatypes, 'member m1 full')
    assert nav['target']['kind'] == 'hypothesis', nav
    assert any(s['name'] == 'b' and s['kind'] == 'variable' for s in nav['completions']), nav
    doc.write_text('(proofs 7 (program library)\n'
        '  (theorem kept (internal () (forall ((P Omega)) (assuming (given P) P)))\n'
        '    (by (hypothesis given))))\n')
    run('prove', doc, plain)
    nav = navigate(doc, 'given))))')
    assert nav['target']['kind'] == 'hypothesis', nav

print('test-proof-typed: statements over the datatype language proved, rejected, cached, '
      'converted, recorded, transported and navigated')
PY
