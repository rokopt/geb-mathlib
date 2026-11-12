#!/usr/bin/env bash
# Exercise editor services against source snapshots through the real host.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author
python3 - <<'PY'
import json
from pathlib import Path
import subprocess
import tempfile

host = Path('.lake/build/bin/geb-author').resolve()

def call(args, request, ok=True):
    run = subprocess.run([host, *map(str, args)], input=json.dumps(request),
                         text=True, capture_output=True, timeout=30)
    assert run.returncode == (0 if ok else 1), (run.stdout, run.stderr)
    return json.loads(run.stdout) if ok else None

def text(value):
    return bytes(value).decode('utf8')

with tempfile.TemporaryDirectory(prefix='geb-editor-services-') as directory:
    root = Path(directory)
    source = root / 'Main.geb'
    library = root / 'Library.geb'
    manifest = root / 'main.manifest'
    proof = root / 'Main.proofs.geb'
    imported = root / 'Library.proofs.geb'
    library.write_text('(module Lib (export known "λ😀")\n'
                       '  (defn known ((x T)) T x)\n'
                       '  (defn "λ😀" ((x T)) T x))\n'
                       '(module Hidden (def secret 0))\n')
    program = '''(module Main (import Lib as L) (export f)
  (defn f ((x T)) T
    (let* ((x T x) (y T x)) (let x T y x)))
  (defn g ((x T)) T (L.known x))
  (def q (quote (L.known x))))
'''
    source.write_text(program)
    manifest.write_text('(program main (edition 0) '
        '(document (syntax authoring 0) (schema 0) (prose verso 0)) '
        '(sources Library.geb Main.geb) (entries Main.f))')
    imported.write_text('(proofs 2\n; Previous theorem documentation.\n'
                        '(theorem previous (forall ((a T)) (equal a a)) '
                        '(by (reduce weak))))\n')
    proofs = '''(proofs 3 (import Library.proofs.geb)
  (theorem example
    (internal (X) (forall ((x X)) (implies (h (equal x x)) (equal x x))))
    (by (extensionality y (reduce weak h previous))))
  (theorem branch (forall ((xs (List T))) (equal xs xs))
    (by (induction xs (y ys ih) (reduce weak previous) (reduce weak ih)))))
'''
    proof.write_text(proofs)

    def query(fragment, contents=program, file=source, offset=0, recover=False, extra=()):
        index = contents.index(fragment) + offset
        prefix = contents[:index]
        req = dict(file=str(file), line=prefix.count('\n') + 1,
                   column=len(prefix.rsplit('\n', 1)[-1].encode()) + 1,
                   proofs=str(proof), recover=recover,
                   documents=[dict(path=str(file), text=contents), *extra])
        return call(['navigation', manifest], req)

    def selected(result):
        s = result['target']
        assert s is not None, result
        return text(s['name']), s['selection']

    # A sequential binding's own initializer sees the preceding binding, not itself.
    first_query = query('((x T))', offset=2)
    first = selected(first_query)[1]
    assert text(first_query['target']['signature']).strip() == '(x T)'
    assert selected(query('(x T x)', offset=5))[1] == first
    second = selected(query('(x T x)', offset=1))[1]
    assert second != first
    assert selected(query('(y T x)', offset=5))[1] == second
    third = selected(query('(let x T y x)', offset=5))[1]
    assert selected(query('(let x T y x)', offset=11))[1] == third
    assert query('(quote (L.known', offset=8)['target'] is None
    assert query('(quote (L.known', offset=8)['completions'] == []
    choices = {text(s['name']): s for s in query('L.known x')['completions']}
    assert {'x', 'L.known', 'L.λ😀'} <= choices.keys(), choices.keys()
    assert 'Hidden.secret' not in choices and 'known' not in choices
    assert text(choices['L.λ😀']['insertText']) == '"L.λ😀"'
    unusual = program.replace('(export f)', '(export f) (def "line\\x0Aname" 0) (def "\\xFF" 0)')
    unusual_names = query('L.known x', unusual)['completions']
    assert any(bytes(s['name']) == b'line\nname' and
               text(s['insertText']) == '"line\\x0Aname"' for s in unusual_names)
    assert any(bytes(s['name']) == b'\xff' and
               text(s['insertText']) == '"\\xFF"' for s in unusual_names)
    assert selected(query('L.known x'))[0] == 'Lib.known'
    commented = program.replace('(L.known x)', '(L.known ; x is prose\n x)')
    assert query('x is prose', commented)['completions'] == []
    assert query('x is prose', commented)['target'] is None
    typed = program.replace('(export f)', '(export f) (deftype A T)')
    type_names = {text(s['name']) for s in query('((x T))', typed, offset=4)['completions']}
    assert type_names == {'A'}, type_names
    self_named = program.replace('defn f ((x T))', 'defn f ((f T))')
    assert selected(query('defn f', self_named, offset=5))[0] == 'Main.f'
    patterns = '''(data D (C T) (Nil))
(defn f ((C T) (x D)) T (case x ((C y) y) ((Nil) C)))
'''
    assert selected(query('((C y)', patterns, offset=2))[0] == 'C'
    assert query('((C y)', patterns, offset=2)['target']['kind'] == 'constructor'
    assert selected(query('y) y', patterns, offset=3))[0] == 'y'
    assert 'y' not in {text(s['name']) for s in query('((Nil) C)', patterns, offset=7)['completions']}
    data_types = query('(C T)', patterns, offset=3)['completions']
    assert [text(s['name']) for s in data_types] == ['D']
    for body in ['', '(lam ((y T)) )', '(let y T x )', '(let* ((y T x)) )']:
        empty = '(defn f ((x T)) T ' + body + ')'
        caret = len(empty) - (2 if body else 1)
        names = {text(s['name']) for s in query(empty, empty, offset=caret, recover=True)['completions']}
        assert 'x' in names and ('y' in names) == bool(body), (body, names)

    # Proof imports, quantified variables, hypotheses and script binders share one index.
    assert selected(query('weak h', proofs, proof, 5))[0] == 'h'
    assert selected(query('h previous', proofs, proof, 2))[0] == 'previous'
    assert 'Previous theorem documentation.' in text(
        query('h previous', proofs, proof, 2)['target']['documentation'])
    assert selected(query('((x X))', proofs, proof, 4))[0] == 'X'
    assert selected(query('extensionality y', proofs, proof, 15))[0] == 'y'
    base = query('weak previous', proofs, proof, 5)
    base_names = {text(s['name']) for s in base['completions']}
    assert not {'y', 'ys', 'ih', 'xs'} & base_names
    step = query('weak ih', proofs, proof, 5)
    assert selected(step)[0] == 'ih'
    assert {'y', 'ys', 'ih'} <= {text(s['name']) for s in step['completions']}
    changed = proofs.replace('h previous', 'h previous y')
    assert selected(query('previous y', changed, proof, 9))[0] == 'y'
    quoted = proofs.replace('(equal x x)', '(equal x (quote (previous)))')
    assert query('(previous)', quoted, proof, 1)['target'] is None
    assert query('(previous)', quoted, proof, 1)['completions'] == []
    kernel_binding = proofs.replace('(equal xs xs)', '(equal xs (let z T 0 z))')
    assert selected(query('0 z', kernel_binding, proof, 2))[0] == 'z'
    # An implication inside an internal term does not introduce named hypotheses.
    formula = '(implies (equal x x) (equal x x))'
    internal = proofs.replace('(equal x x)', '(equal ' + formula + ' x)', 1)
    result = query(formula, internal, proof, formula.rindex('equal'))
    assert result['target'] is None
    assert 'equal' not in {text(s['name']) for s in result['completions']}

    # Recovery keeps completed children of an open module, and other source files.
    unfinished = program[:-2] + '\n  (def unfinished "'
    partial = query('L.known x', unfinished, recover=True)
    assert str(source) in partial['incomplete']
    assert selected(partial)[0] == 'Lib.known'
    assert 'Main.g' in {text(s['name']) for s in partial['symbols']}
    partial = query('weak h', proofs + '(', proof, 5, recover=True)
    assert selected(partial)[0] == 'h'
    broken_import = proofs.replace('Library.proofs.geb', 'Missing.proofs.geb')
    partial = query('weak h', broken_import, proof, 5, recover=True)
    assert partial['errors'] and selected(partial)[0] == 'h'
    partial = query('L.known x', recover=True,
                    extra=[dict(path=str(proof), text=broken_import)])
    assert selected(partial)[0] == 'Lib.known'

    # Format unsaved bytes, retaining quoted atoms, comments and opaque notes; reject unfinished input.
    messy = '; retained λ😀\r\n(note (future opaque))\r\n(def "λ😀"   (quote (1 2)))\r\n'
    formatted = text(call(['format-buffer'], dict(text=messy))['text'])
    assert 'retained λ😀' in formatted and 'future opaque' in formatted and '"λ😀"' in formatted
    assert text(call(['format-buffer'], dict(text=formatted))['text']) == formatted
    call(['format-buffer'], dict(text=messy + '('), ok=False)
    multiline = '; preserved\r\n(def q   (quote (0 "first\r\nsecond")))\r\n'
    safe = text(call(['format-buffer'], dict(text=multiline, crlf=True))['text'])
    assert 'first\\x0D\\x0Asecond' in safe
    inserted = safe.replace('\r\n', '\n').replace('\n', '\r\n')
    assert call(['format-buffer'], dict(text=inserted)) == call(['format-buffer'], dict(text=multiline))
    arbitrary = '(def "λ😀"   (quote (0 "\\xFF")))\n'
    escaped = text(call(['format-buffer'], dict(text=arbitrary))['text'])
    assert '\\xFF' in escaped and '\ufffd' not in escaped
    assert text(call(['format-buffer'], dict(text=escaped))['text']) == escaped

    # Only actual holes, never annotation data, appear in the obligation's sites.
    holes = '(note (future (hole shared)))\n(def q (quote (0)))\n(def f (lam ((x T)) (add ?shared ?shared)))\n'
    source.write_text(holes)
    manifest.write_text(manifest.read_text().replace('Library.geb Main.geb', 'Main.geb')
                       .replace('Main.f', 'f'))
    req = dict(documents=[])
    report = call(['editor-holes', manifest], req)
    assert not report['complete'] and len(report['holes']) == 1
    hole = report['holes'][0]
    assert text(hole['name']) == 'shared' and text(hole['target']).strip() == 'T'
    assert [text(b['name']) for b in hole['context']] == ['x']
    assert len(hole['occurrences']) == 2
    req['documents'] = [dict(path=str(source), text=holes.replace('?shared', 'x'))]
    assert call(['editor-holes', manifest], req)['complete']
    req['documents'] = [dict(path=str(source), text=holes + '(')]
    call(['editor-holes', manifest], req, ok=False)
    assert source.read_text() == holes
print('test-editor-services: binding scopes, proof scopes, completion, recovery, formatting and holes passed')
PY
