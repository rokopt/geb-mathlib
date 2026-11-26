#!/usr/bin/env bash
# Check the case analysis of a member of a datatype, (member-cases ...) of version 8 of the
# proof-source profile: the library's document proved and replayed, alone and in a program that
# names the library as a layer; the cases a datatype's constructors do not have; a hypothesis
# that is not one of membership; the names a case may not take; the goal at a hole of a case;
# and the versions before 8, which do not read the script.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author geb-compile geb-defs geb-kernel
python3 - <<'PY'
from pathlib import Path
import shutil
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()

def run(*args, ok=True, timeout=900):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=timeout)
    assert result.returncode == (0 if ok else 1), (args, result.stdout, result.stderr)
    return result.stdout.decode(), result.stderr.decode()

OPTION = ('(typed (forall ((m (Optional.Option T) member)) (equal (case m ((Optional.none T) '
          '(Optional.none T)) ((Optional.some T x) (Optional.some T x))) m)))')
BYTES = ('(typed (forall ((b Bytes.Bytes member)) '
         '(equal (case b ((Bytes.bytes & cs) (Bytes.bytes cs))) b)))')
# A statement of a datatype whose first constructor has a field before the remaining children and
# whose second has two fields.
EVENT = ('(typed (forall ((e Requests.Event member)) '
         '(equal (case e ((Requests.start v & as) 0) ((Requests.resume s r) 0)) 0)))')

def document(statement, script, version=8):
    return (f'(proofs {version} (program library) (import Trees.proofs.geb)\n'
            f'  (theorem subject\n    {statement}\n    (by {script})))\n')

with tempfile.TemporaryDirectory() as tmp:
    tmp = Path(tmp)
    root = tmp / 'library'
    shutil.copytree('library', root)
    manifest = root / 'library.manifest'
    members = root / 'Members.proofs.geb'
    cert, plain = tmp / 'proof.cert', tmp / 'plain.cert'

    # The library's theorems about the members of its datatypes, by the program the document
    # names and by its manifest given.
    run('prove', members, cert)
    run('replay', members, cert)
    run('replay', manifest, members, cert)

    # A client that names the library as a layer proves the library's document against its own
    # program, and its own theorem by cases on a member of the library's datatype.
    client = tmp / 'client'
    client.mkdir()
    (client / 'library').symlink_to(root)
    (client / 'Use.geb').write_text(
        '(module Use (export first) (import Optional)\n'
        '  (defn first ((m (Option T))) T (case m ((none T) 0) ((some T x) x))))\n')
    (client / 'client.manifest').write_text(
        '(program client (edition 0) (document (syntax authoring 0) (schema 0) (prose verso 0))\n'
        '  (layers (library (manifest library/library.manifest)) (application Use.geb))\n'
        '  (entries))\n')
    own = client / 'Use.proofs.geb'
    own.write_text(
        '(proofs 8 (program client) (import library/Members.proofs.geb)\n'
        '  (theorem first-or-zero\n'
        '    (typed (forall ((m (Optional.Option T) member))\n'
        '      (equal (Use.first m) (Optional.orElse T 0 m))))\n'
        '    (by (member-cases member m lambek () (reduce full) (x) (reduce full)))))\n')
    run('prove', own, plain)
    run('replay', own, plain)

    doc = root / 'Subject.proofs.geb'
    def unproved(statement, script, message='does not prove', version=8):
        doc.write_text(document(statement, script, version))
        _, err = run('prove', doc, plain, ok=False)
        assert message in err, err
        return err

    # The cases are those of the datatype's constructors, in their order: a case missing, a
    # constructor at another number of fields, a constructor taking the remaining children that
    # the datatype does not have, and a case too many each prove nothing.
    unproved(OPTION, '(member-cases member m lambek () (reduce full))')
    unproved(OPTION, '(member-cases member m lambek () (reduce full) (x y) (reduce full))')
    unproved(OPTION, '(member-cases member m lambek (x) (reduce full) () (reduce full))')
    unproved(OPTION, '(member-cases member m lambek () (reduce full) (& xs) (reduce full))')
    unproved(OPTION, '(member-cases member m lambek () (reduce full) (x) (reduce full) () '
             '(reduce full))')
    unproved(BYTES, '(member-cases member b lambek () (reduce full))')
    # The hypothesis named is one that fails at every tree but the members: an equation that
    # holds of every tree refutes no case.
    unproved('(typed (forall ((x T)) (implies (h (equal x x)) (equal x 0))))',
             '(member-cases h x lambek () (reduce full))')

    # The script names a hypothesis and a variable of its goal and a theorem, and each case
    # names its fields by distinct names that a variable may take, the last after & where it
    # takes the remaining children.
    unread = 'the script of the theorem subject does not read'
    for script in ['(member-cases missing m lambek () (reduce full) (x) (reduce full))',
                   '(member-cases member missing lambek () (reduce full) (x) (reduce full))',
                   '(member-cases member m missing () (reduce full) (x) (reduce full))',
                   '(member-cases member m lambek)',
                   '(member-cases member m lambek () (reduce full) (x))',
                   '(member-cases member m lambek () (reduce full) (m) (reduce full))',
                   '(member-cases member m lambek () (reduce full) (member) (reduce full))',
                   '(member-cases member m lambek () (reduce full) (x x) (reduce full))',
                   '(member-cases member m lambek () (reduce full) (& x y) (reduce full))',
                   '(member-cases member m lambek () (reduce full) (x &) (reduce full))',
                   '(member-cases member m lambek () (reduce full) (7) (reduce full))']:
        unproved(OPTION, script, unread)
    # No version before 8 reads the script.
    unproved(OPTION, '(member-cases member m lambek () (reduce full) (x) (reduce full))', unread,
             version=7)

    # The goal at a hole of a case is that of the constructor's tree, in the variable of its
    # field and under the hypothesis, which the case's script names again.
    err = unproved(OPTION, '(member-cases member m lambek () (reduce full) (x) ?some)',
                   'leaves the hole ?some open')
    assert '(x T)' in err and '(member' in err, err

    # A constructor's fields before a last field that takes the remaining children: the case is
    # read at the fields and at the list of the remaining children, and a constructor of two
    # fields at both.
    doc.write_text(document(EVENT, '(member-cases member e lambek (v & as) (reduce full) (s r) '
                            '(reduce full))'))
    run('prove', doc, plain)
    run('replay', doc, plain)
    err = unproved(EVENT, '(member-cases member e lambek (v & as) ?start (s r) (reduce full))',
                   'leaves the hole ?start open')
    assert '(v T)' in err and '(as (List T))' in err, err
    unproved(EVENT, '(member-cases member e lambek (v) (reduce full) (s r) (reduce full))')

print('test-proof-members: the case analysis of a member of a datatype proved, replayed and '
      'rejected')
PY
