#!/usr/bin/env bash
# Check formula statements, connective scripts, scopes, durable spellings and cached replay.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author
python3 - <<'PY'
from pathlib import Path
import json
import shutil
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()
sample = Path('examples/authoring')

def run(*args, ok=True, timeout=600):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=timeout)
    assert result.returncode == (0 if ok else 1), (args, result.stdout, result.stderr)
    return result.stdout.decode(), result.stderr.decode()

MORE = '''(proofs 5 (program pair) (import Logic.proofs.geb)
  (definition logical-not ((P Omega)) Omega (not P))
  (theorem declared-formula (internal () (logical-not false))
    (by (unfold-formula (unfold-formula (assume h (hypothesis h))))))
  (theorem truth (internal () true) (by (truth)))
  (theorem explosion
    (internal () (forall ((P Omega)) (assuming (h false) P)))
    (by (false-elim (hypothesis h))))
  (theorem not-false (internal () (not false))
    (by (unfold-formula (assume h (hypothesis h)))))
  (theorem contradiction
    (internal () (forall ((P Omega)) (assuming (h (not P)) (hp P) false)))
    (by (unfold-hypothesis h deny (imp-elim deny (hypothesis hp) bad (hypothesis bad)))))
  (theorem all-copy
    (internal (X) (forall ((P (Arrow X Omega))) (assuming (h (all X P)) (all X P))))
    (by (all-intro x (all-elim h x hx (hypothesis hx)))))
  (theorem exists-copy
    (internal (X)
      (forall ((P (Arrow X Omega)))
        (assuming (h (exists X (lam ((x X)) (P x)))) (exists X (lam ((x X)) (P x))))))
    (by (exists-elim h (x hx) (exists-intro x (hypothesis hx)))))
  (theorem unique-unit
    (internal () (exists-unique Unit (lam ((u Unit)) true)))
    (by (unfold-formula
      (and-intro (exists-intro unit (truth))
        (all-intro x (all-intro y (assume h (reduce weak))))))))
  (theorem predicate-implication
    (internal (X) (forall ((P (Arrow X Omega)) (x X)) (implies (P x) (P x))))
    (by (use identity () ((P x)))))
  (theorem rewrite-formula
    (internal () (forall ((P Omega)) (implies P P)))
    (by (reduce weak identity)))
  (theorem apply-with-premises
    (internal (X Y)
      (forall ((P (Arrow X Omega)) (Q (Arrow Y Omega)) (f (Arrow X Y)))
        (assuming (preserves (all X (lam ((x X)) (implies (P x) (Q (f x))))))
          (implies (exists X P) (exists Y Q)))))
    (by (use transport-witness (X Y) (P Q f) (hypothesis preserves))))
  (theorem imported-equation
    (forall ((x T) (y T)) (equal (Pair.first x y) x))
    (by (use first-at () ((kernel x) (kernel y)))))
  (theorem equality-to-truth
    (internal () (forall ((P Omega)) (equal (implies P P) true)))
    (by (assume h (hypothesis h))))
  (theorem explicit-equality-hypothesis
    (internal () (forall ((P Omega)) (assuming (h (equal P true)) (equal P true))))
    (by (hypothesis h)))
  (theorem explicit-equality-theorem
    (internal () (forall ((P Omega)) (assuming (h (equal P true)) (equal P true))))
    (by (use explicit-equality-hypothesis () (P) (hypothesis h)))))
'''

with tempfile.TemporaryDirectory(prefix='geb-proof-formulas-') as directory:
    root = Path(directory)
    for name in ('Pair.geb', 'Lists.geb', 'pair.manifest', 'Pair.proofs.geb', 'Logic.proofs.geb'):
        shutil.copyfile(sample / name, root / name)
    manifest = root / 'pair.manifest'
    doc = root / 'Formulas.proofs.geb'
    cert = root / 'formulas.cert'
    plain = root / 'plain.cert'
    cache = root / 'cache'
    doc.write_text(MORE)
    run('prove', '--cache', cache, doc, cert)
    out, _ = run('prove', '--cache', cache, doc, cert)
    assert '0 checked, 0 proved, 0 not proved' in out, out
    run('prove', doc, plain)
    assert cert.read_bytes() == plain.read_bytes()
    run('replay', doc, cert)

    # Every durable spelling replays against the original certificate; conversion is stable.
    canonical = root / 'formulas.csexp'
    advanced = root / 'formulas.advanced'
    again = root / 'again.csexp'
    run('convert', 'canonical', manifest, doc, canonical)
    run('convert', 'advanced', manifest, canonical, advanced)
    run('convert', 'canonical', manifest, advanced, again)
    assert canonical.read_bytes() == again.read_bytes()
    for spelling in (canonical, advanced):
        run('replay', manifest, spelling, cert)

    saved = cert.read_bytes()
    doc.write_text(MORE.replace('(theorem truth (internal () true)',
                                '(theorem truth (internal () false)'))
    run('replay', doc, cert, ok=False)
    run('prove', '--cache', cache, doc, cert, ok=False)
    assert cert.read_bytes() == saved

    def reject(statement, script, version=5):
        doc.write_text(f'(proofs {version} (program pair) '
                       f'(theorem rejected {statement} (by {script})))')
        run('prove', doc, cert, ok=False)
        assert cert.read_bytes() == saved

    reject('(internal () false)', '(truth)')
    reject('(internal () unit)', '(truth)')  # Formula statements must have type Omega.
    reject('(internal () (and true unit))', '(and-intro (truth) (truth))')
    reject('(internal () (all Unit true))', '(all-intro x (truth))')
    reject('(internal () (exists Unit (lam ((x Unit)) true)))',
           '(exists-intro zero (truth))')  # The checker validates the witness type.
    reject('(internal () (forall ((P Omega) (Q Omega)) (implies (or P Q) P)))',
           '(assume h (or-elim h (hp hq) (hypothesis hp) (hypothesis hp)))')
    reject('(internal () (forall ((P Omega)) (implies P P)))',
           '(assume P (hypothesis P))')  # No shadowing a variable with a hypothesis.
    reject('(internal () (implies true true))',
           '(assume Pair.first (truth))')  # Nor a program definition.
    reject('(internal () (all Unit (lam ((x Unit)) (equal x unit))))',
           '(and-intro (all-intro x (reduce weak)) (exists-intro x (truth)))')
    reject('(internal () true)', '(truth)', version=4)
    reject('(internal () (equal false false))', '(reduce weak)', version=4)
    reject('(internal () true)', '(truth)', version=6)

    # Quantifier elimination cannot let its witness escape to the outer conclusion.
    reject('(internal (X) (forall ((P (Arrow X Omega)) (y X)) '
           '(assuming (h (exists X P)) (P y))))',
           '(exists-elim h (x hx) (hypothesis hx))')

    # Equality-with-truth adaptation must not retry an elimination's whole continuation.
    # Otherwise this failed search doubles its work at every nesting level.
    script = '(truth)'
    for i in range(24):
        script = f'(and-elim h (p{i} q{i}) {script})'
    doc.write_text('(proofs 5 (program pair) (theorem deep '
        '(internal () (assuming (h (and true true)) false)) '
        f'(by {script})))')
    run('prove', doc, cert, ok=False, timeout=30)
    assert cert.read_bytes() == saved

    # Goals keep their formulas and names. The printed goal reads as a new v5 statement.
    doc.write_text('(proofs 5 (program pair) (theorem open '
        '(internal () (forall ((P Omega) (Q Omega)) (implies (and P Q) (or Q P)))) '
        '(by (assume h (and-elim h (hp hq) ?body)))))')
    _, err = run('prove', doc, cert, ok=False)
    assert '(assuming ' in err and '(hp P)' in err and '(hq Q)' in err, err
    assert '(or Q P)' in err and 'opaque' not in err, err
    goal = err.split('at the goal ', 1)[1].splitlines()[0]
    doc.write_text(f'(proofs 5 (program pair) (theorem filled {goal} '
                   '(by (or-left (hypothesis hq)))))')
    run('prove', doc, plain)
    run('replay', doc, plain)

    # Navigation uses the same scopes: no invented assumption at a predicate application,
    # and each disjunction branch sees only its own binder.
    text = (root / 'Logic.proofs.geb').read_text()
    def navigate(fragment):
        offset = text.index(fragment)
        prefix = text[:offset]
        request = dict(file=str(root / 'Logic.proofs.geb'),
            line=prefix.count('\n') + 1, column=len(prefix.rsplit('\n', 1)[-1].encode()) + 1,
            proofs=str(root / 'Logic.proofs.geb'), documents=[])
        result = subprocess.run([runner, 'navigation', manifest], input=json.dumps(request),
            capture_output=True, text=True, timeout=30)
        assert result.returncode == 0, result.stderr
        return json.loads(result.stdout)
    # The host JSON encodes strings as arrays of codepoints; normalize for comparisons.
    def decoded(value):
        if isinstance(value, list):
            if value and all(isinstance(x, int) for x in value):
                return ''.join(map(chr, value))
            return [decoded(x) for x in value]
        if isinstance(value, dict):
            return {k: decoded(v) for k, v in value.items()}
        return value
    nav = decoded(navigate('hp)) (or-left'))
    assert nav['target']['kind'] == 'hypothesis', nav
    assert not any(s['name'] == 'hq' for s in nav['completions']), nav
    nav = decoded(navigate('hx) image'))
    assert nav['target']['kind'] == 'hypothesis', nav
    assert any(s['name'] == 'x' and s['kind'] == 'variable' for s in nav['completions']), nav
    text = '''(proofs 5 (program pair)
      (theorem predicate (internal (X)
        (forall ((P (Arrow X Omega)) (x X)) (implies (P x) (P x))))
        (by (assume h (hypothesis h)))))'''
    (root / 'Logic.proofs.geb').write_text(text)
    nav = decoded(navigate('h)))))'))
    assert next(s for s in nav['completions'] if s['name'] == 'P')['kind'] == 'variable', nav

print('test-proof-formulas: formulas, checked scripts, scopes, conversion and replay passed')
PY
