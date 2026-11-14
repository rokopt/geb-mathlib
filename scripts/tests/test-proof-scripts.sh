#!/usr/bin/env bash
# Exercise versions 2 to 4 of the proof profile through the CLI: statements over the internal
# language, the tactics of trees and coproducts, rules at objects, imported documents, the program
# a document names, the diagnostics of a rejected development, truth and implication, the tactics
# of the induction on trees with the hypothesis at each child, of the instances of a hypothesis
# and of implications, the alternative of two scripts and the case analysis of a bitstring to a
# number of bits and by the scripts of its labels, abbreviations, the normal form of a theorem's
# companion, rules that keep definitions folded, the uniqueness of folds with premises that
# scripts prove, instances of theorems and hypotheses cut in from them, the searches that split
# the values of tests and rewrite under masks, holes and the goals reported of them and of the
# steps that fail, the natural numbers and the definitions a development declares, and the
# development of
# bootstrap/proofs/tree-cases.proofs.geb, proved and replayed. scripts/proofs.sh proves the
# developments of bootstrap/proofs/ whose searches take longer.
set -euo pipefail
cd "$(dirname "$0")/../.."
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
lake build geb-author
python3 - <<'PY'
from pathlib import Path
import shutil
import subprocess
import tempfile

runner = Path('.lake/build/bin/geb-author').resolve()
sample = Path('examples/authoring')
proofs_dir = Path('bootstrap/proofs')

def run(*args, ok=True, timeout=600):
    result = subprocess.run([str(runner), *map(str, args)], capture_output=True, timeout=timeout)
    if result.returncode != (0 if ok else 1):
        raise AssertionError((args, result.returncode, result.stdout, result.stderr))
    return result.stderr.decode()

MORE = '''; Theorems of version 2 about the pair example.

(proofs 2 (import Pair.proofs.geb) (import lib/trees.proofs.geb)
  ; Appending the empty list after an appending, by generalizing the appending.
  (theorem append-append-nil
    (forall ((xs (List T)) (ys (List T)))
      (equal (Lists.append (Lists.append xs ys) (nil T)) (Lists.append xs ys)))
    (by (generalize (zs (List T)) (kernel (Lists.append xs ys)) (reduce weak append-nil))))
  ; The case analysis of a coproduct at its injections.
  (theorem case-inl
    (internal (X Y)
      (forall ((f (Arrow X Y)) (g (Arrow Unit Y)) (x X))
        (equal ((case X Unit Y (pair f g)) (inl X Unit x)) (f x))))
    (by (reduce weak)))
  (theorem case-inr
    (internal (X Y)
      (forall ((f (Arrow X Y)) (g (Arrow Unit Y)))
        (equal ((case X Unit Y (pair f g)) (inr X Unit unit)) (g unit))))
    (by (reduce weak)))
  ; A case analysis with one value at both bits is that value.
  (theorem bit-constant
    (internal (X)
      (forall ((x X) (b Bit))
        (equal ((case Unit Unit X (pair (lam ((u Unit)) x) (lam ((u Unit)) x))) b) x)))
    (by (sum-cases b (u) (reduce weak) (reduce weak))))
  ; A definition of the program beside a term of the kernel.
  (theorem first-internal
    (internal () (forall ((x T) (y T)) (equal (Pair.first x y) (kernel (Pair.left x y)))))
    (by (normalize 64)))
  ; A tree is the node of its label and children.
  (theorem node-label-children
    (internal () (forall ((t T)) (equal (node Bits (pair (lib lab t) (lib children t))) t)))
    (by (tree-cases t (l cs) lambek (reduce full map-id map-fusion lambek)))))
'''

def prune(t):
    return ('(rose-rec T (n) (node Bits (pair (fst n) (list-rec (nil T) (r acc) (cons T r (nil T))'
            f' (snd n)))) {t})')

def same(t):
    return ('((case Unit Unit Bit (pair (lam ((u Unit)) (inl Unit Unit u))'
            f' (lam ((u Unit)) (inr Unit Unit u)))) {t})')

HYP = f'''; Theorems of version 3 about the pair example.

(proofs 3 (import Pair.proofs.geb)
  ; The instance of a hypothesis that equates functions.
  (theorem instance
    (internal (X Y)
      (forall ((f (Arrow X Y)) (g (Arrow X Y)) (x X)) (implies (h (equal f g)) (equal (f x) (g x)))))
    (by (instances weak h ((hx x)) (reduce weak hx))))
  ; An implication is introduced, and eliminated by modus ponens.
  (theorem symmetry
    (internal (X) (forall ((x X) (y X)) (equal (implies (equal x y) (equal y x)) true)))
    (by (assume h (reduce weak h))))
  (theorem composition
    (internal (X)
      (forall ((a X) (b X) (c X) (d X))
        (implies (h (equal (implies (equal a b) (equal c d)) true))
          (equal (implies (equal a b) (equal d c)) true))))
    (by (assume ha (modus-ponens ha (h) (reduce weak h)))))
  ; The case analysis of a list that a hypothesis mentions.
  (theorem reverted
    (internal (X) (forall ((l (List X)) (m (List X))) (implies (h (equal l m)) (equal m l))))
    (by (revert-cases h l (y ys) (reduce weak h) (reduce weak h))))
  ; Keeping the first child alone at each node is idempotent, by induction on a tree with the
  ; hypothesis at the first child.
  (theorem prune-prune
    (internal () (forall ((t T)) (equal {prune(prune('t'))} {prune('t')})))
    (by
      (tree-induction t (l cs ih)
        (revert-cases ih cs (c ys) (reduce full)
          (child-hypotheses weak ih (((hc))) (reduce full hc))))))
  ; The children of a tree of the kernel have the kernel's type of lists of trees.
  (theorem kernel-children (forall ((t T)) (equal t t))
    (by (tree-induction t (l cs ih) (generalize (zs (List T)) (kernel cs) (reduce weak)))))
  ; A theorem of a document of an earlier version is cited after the connectives' rules.
  (theorem append-nil-again (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (reduce weak append-nil)))
  ; An alternative proves by its second script where its first does not.
  (theorem append-nil-first (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (first (reduce weak) (reduce weak append-nil))))
  ; The head of a bitstring or else a bit, the head taken through the case analysis that
  ; returns a bit, is the head or else an equal bit: at each bitstring of fewer than two bits
  ; and of two bits before a bitstring, and for a second bitstring at each of none and of one
  ; before a bitstring, the script being read in the variables and hypotheses of each case.
  (theorem head-bits
    (internal ()
      (forall ((d Bit) (e Bit) (b Bits) (c Bits))
        (equal
          (implies (equal d e)
            (equal (pair (list-rec d (y r) {same('y')} b) (list-rec d (y r) {same('y')} c))
              (pair (list-rec e (y r) y b) (list-rec e (y r) y c))))
          true)))
    (by (bits-cases b 2 (bits-cases c 1 (assume h (reduce weak h)))))))
'''

FORMS = '''; Theorems of version 3 about the pair example: abbreviations, the uniqueness of folds with
; premises that scripts prove, instances of theorems, hypotheses cut in, normal forms and rules.

(proofs 3 (import Pair.proofs.geb) (import lib/trees.proofs.geb)
  ; A type, a term in the variable ts, several rules and a script.
  (abbreviation Ts (List T))
  (abbreviation rebuilt (list-rec (nil T) (t r) (cons T t r) ts))
  (abbreviation append-rules append-nil append-nil-twice)
  (abbreviation by-append (with-rules (append-rules) (reduce weak)))
  ; The uniqueness of a list's fold, its premises by scripts.
  (theorem rebuild-again (internal () (forall ((ts Ts)) (equal rebuilt ts)))
    (by (fold-uniqueness ts (y ys r) (cons T y r) (reduce weak) (reduce weak))))
  ; The uniqueness of a tree's fold, its premise by a script.
  (theorem lambek-again
    (internal ()
      (forall ((t T))
        (equal
          (node Bits
            (rose-rec (Prod Bits Ts) (n)
              (pair (fst n) (list-rec (nil T) (c s) (cons T (node Bits c) s) (snd n)))
              t))
          t)))
    (by
      (tree-fold-uniqueness t (l cs rs) (node Bits (pair l rs))
        (normalize 64 map-id map-fusion))))
  ; A theorem that equates functions, and its instance at a term, applied to an argument.
  (theorem first-fn
    (internal (X) (forall ((x X)) (equal (lam ((y X)) (fst (pair y x))) (lam ((y X)) y))))
    (by (extensionality z (reduce weak))))
  (theorem first-at-pair (internal (X) (forall ((x X) (z X)) (equal (fst (pair z x)) z)))
    (by (instance (first-fn X) (x) (z) weak)))
  ; The rules of a script, and a theorem's instance cut in as a hypothesis.
  (theorem append-nil-rules (forall ((xs Ts)) (equal (Lists.append xs (nil T)) xs)) (by by-append))
  (theorem append-nil-have (forall ((xs Ts)) (equal (Lists.append xs (nil T)) xs))
    (by (have h append-nil (xs) () (reduce-hypotheses weak (h) (reduce weak h)))))
  ; The congruence of a hypothesis, and a formula that a hypothesis equates with a truth.
  (theorem first-equal
    (internal (X)
      (forall ((p (Prod X X)) (q (Prod X X))) (implies (h (equal p q)) (equal (fst p) (fst q)))))
    (by (congruence h (g (z (Prod X X)) (fst z)) (reduce-hypotheses weak (g) (reduce weak g)))))
  (theorem holds-equal
    (internal (X)
      (forall ((x X) (y X)) (implies (h (equal (equal x y) (equal unit unit))) (equal x y))))
    (by (holds h (g) (reduce weak g))))
  ; A definition kept folded in a theorem's normal form, by which a rule rewrites where a script
  ; keeps it folded.
  (theorem first-folded (forall ((x T) (y T)) (equal (Pair.first x y) x)) (by (normalize 64))
    (normal weak (folded Pair.first)))
  (theorem first-twice (forall ((x T) (y T)) (equal (Pair.first (Pair.first x y) y) x))
    (by (with-rules ((folded Pair.first) first-folded) (reduced weak (reduce weak)))))
  ; The case analysis of a test's value, found among the sides' subterms.
  (theorem test-either (forall ((x T) (y T)) (equal (if (Pair.left x y) 1 1) 1))
    (by
      (with-rules ((folded Pair.left))
        (test-cases (Pair.left any any) 1 lambek (reduce weak) (reduce weak)))))
  ; The search that splits the variable a conditional is stuck on.
  (theorem cond-same-again (internal (X) (forall ((x X) (c Bits)) (equal (lib cond X c x x) x)))
    (by (auto-conditions 4 lambek)))
  ; The cases of a bitstring by the scripts of their labels: the empty bitstring, and the bit zero
  ; before it.
  (theorem label-scripts
    (internal () (forall ((b Bits)) (equal (lib cond Bits b (lib bnil) (lib bnil)) (lib bnil))))
    (by (bits-cases b 2 (reduce weak) (0 1) (reduce head))))
  ; The argument of two applications rewritten to the left side of a theorem at the two innermost
  ; variables.
  (theorem cons-again
    (internal ()
      (forall ((bs Bits) (b Bit)) (equal ((lam ((x Bits)) x) (cons Bit b bs)) (cons Bit b bs))))
    (by (reduce weak)))
  (theorem at-cons
    (internal ()
      (forall ((f (Arrow Bits Bits)) (b Bit) (bs Bits))
        (equal (f (cons Bit b bs)) (f (cons Bit b bs)))))
    (by (succ-pred cons-again (reduce weak))))
  ; A term rewritten under the mask of a conditional's test by a hypothesis, the conditional kept
  ; folded.
  (theorem absorb
    (internal (X Y)
      (forall ((f (Arrow Y X)) (y Y) (z Y) (x X) (c Bits))
        (equal (lib cond X c (f (lib cond Y c z y)) x) (lib cond X c (f z) x))))
    (by (induction c (b bs ih) (reduce weak) (sum-cases b (w) (reduce weak) (reduce weak)))))
  (theorem under-mask
    (internal ()
      (forall ((t T) (m Bits) (n Bits) (c Bits))
        (implies (h (equal (lib cond Bits c m n) (lib cond Bits c n n)))
          (equal (lib cond T c (node Bits (pair m (nil T))) t)
            (lib cond T c (node Bits (pair n (nil T))) t)))))
    (by
      (with-rules ((folded (lib cond)))
        (mask-hypotheses absorb cond-same-again 1 (reduce weak))))))
'''

def document(body, imports=''):
    return f'(proofs 2 {imports}\n  {body})\n'

with tempfile.TemporaryDirectory(prefix='geb-proof-scripts-test-') as directory:
    root = Path(directory)
    for name in ('Pair.geb', 'Lists.geb', 'Pair.proofs.geb', 'pair.manifest'):
        shutil.copyfile(sample / name, root / name)
    (root / 'lib').mkdir()
    shutil.copyfile(proofs_dir / 'trees.proofs.geb', root / 'lib/trees.proofs.geb')
    manifest = root / 'pair.manifest'
    more = root / 'More.proofs.geb'
    certificate = root / 'more.cert'
    more.write_text(MORE)

    # A document of version 2 imports documents of versions 1 and 2, and its certificate replays
    # from the documents alone.
    run('prove', manifest, more, certificate)
    run('replay', manifest, more, certificate)
    saved = certificate.read_bytes()

    # The certificate holds the imported theorems: a changed imported statement, or a changed
    # import, prevents its reuse, and a changed imported script does not.
    imported = root / 'Pair.proofs.geb'
    original = imported.read_text()
    imported.write_text(original.replace('(by (normalize 64 same))', '(by (normalize 65 same))'))
    run('replay', manifest, more, certificate)
    imported.write_text(original.replace('(equal (Pair.first x y) x)', '(equal (Pair.left x y) x)'))
    run('replay', manifest, more, certificate, ok=False)
    imported.write_text(original)
    more.write_text(MORE.replace(' (import lib/trees.proofs.geb)', '')
                    .replace('(tree-cases t (l cs) lambek (reduce full map-id map-fusion lambek))',
                             '(reduce full)'))
    run('replay', manifest, more, certificate, ok=False)
    more.write_text(MORE)
    assert certificate.read_bytes() == saved

    # The line and column at which an occurrence of a snippet of a text begins.
    def where(text, snippet, nth=0):
        index = -1
        for _ in range(nth + 1):
            index = text.index(snippet, index + 1)
        return f"{text.count(chr(10), 0, index) + 1}:{index - text.rfind(chr(10), 0, index)}"

    # A rejected development is reported at the theorem concerned, or at the step of its script
    # that fails, and leaves the output.
    def rejected(text, at, message, name='Bad.proofs.geb'):
        target = root / name
        target.write_text(text)
        error = run('prove', manifest, target, certificate, ok=False)
        expected = f'{target}:{at}: error: ' if at else f'{target}: '
        assert error.startswith(expected) and message in error, (text, error)
        assert certificate.read_bytes() == saved
        return error

    # A script that does not prove its theorem is reported at its innermost step that fails, with
    # the goal that step is given: here the goal the generalization gives, which applies the
    # abstractions over the term generalized to the new variable, reported reduced.
    text = MORE.replace('(reduce weak append-nil))))', '(reduce weak))))')
    error = rejected(text, where(text, '(reduce weak))))'),
                     'the script of the theorem append-append-nil does not prove it: this step '
                     'does not prove the goal (internal () (forall ((xs (List T)) (ys (List T)) '
                     '(zs (List T))) (equal (Lists.append zs (nil T)) zs)))')
    assert error.count(': error: ') == 1, error
    rejected(MORE.replace('(lib lab t)', '(lib label t)'), '31:12',
             'the theorem node-label-children is not')
    rejected(MORE.replace('(sum-cases b (u)', '(sum-cases c (u)'), '21:12',
             'the script of the theorem bit-constant does not read')
    rejected(MORE.replace('(theorem case-inr', '(theorem first-at'), '15:12',
             'the name first-at is declared before')
    # A term of the kernel mentions no variable without a kernel type; an equation's sides have
    # one type; an object variable is bound; a definition of the library takes its objects.
    for body in ('(theorem a (internal () (forall ((x Bits)) (equal (kernel x) x))) (by (normalize 4)))',
                 '(theorem a (internal () (forall ((x Bits) (t T)) (equal x t))) (by (normalize 4)))',
                 '(theorem a (internal (X) (forall ((x Y)) (equal x x))) (by (normalize 4)))',
                 '(theorem a (internal () (forall ((x Bits)) (equal (lib cond x x x) x)))'
                 ' (by (normalize 4)))'):
        rejected(document(body), '2:12', 'the theorem a is not')
    # A keyword of the internal language's terms names no variable of an internal statement.
    rejected(document('(theorem a (internal () (forall ((lib Bits)) (equal lib lib)))'
                      ' (by (normalize 4)))'), '2:12', 'the theorem a is not')

    # Versions 0 and 1 read neither internal statements, the tactics of version 2 nor imports.
    one = '(proofs 1\n  {})\n'
    rejected(one.format('(theorem a (internal () (forall ((x T)) (equal x x))) (by (normalize 4)))'),
             '2:12', 'the theorem a is not')
    rejected(one.format('(theorem a (forall ((b T)) (equal b b))'
                        ' (by (generalize (y T) b (normalize 4))))'),
             '2:12', 'the script of the theorem a does not read')
    rejected('(proofs 1 (import Pair.proofs.geb)\n'
             '  (theorem a (equal Pair.left Pair.left) (by (normalize 4))))\n', '',
             'a document of a version before 2 has no form (import')

    # Version 3 reads truth and implication and the tactics of hypotheses, its certificate begins
    # with the connectives' rules and replays, and it cites the theorems of earlier versions.
    hyp = root / 'Hyp.proofs.geb'
    hyp.write_text(HYP)
    hyp_cert = root / 'hyp.cert'
    run('prove', manifest, hyp, hyp_cert)
    run('replay', manifest, hyp, hyp_cert)
    # Version 2 reads none of them, and no document imports one of a later version.
    rejected(HYP.replace('(proofs 3', '(proofs 2'), '5:12',
             'the script of the theorem instance does not read')
    rejected(document('(theorem a (internal () (forall ((p Omega)) (equal (implies p p) true)))'
                      ' (by (normalize 4)))'), '2:12', 'the theorem a is not')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Hyp.proofs.geb)'), '', 'imports one of a later version')
    # The induction on a tree takes a goal without hypotheses; a keyword of the connectives names
    # no variable or hypothesis of a script; modus ponens cites hypotheses.
    three = '(proofs 3\n  {})\n'
    rejected(three.format('(theorem a (forall ((t T)) (implies (h (equal t t)) (equal t t)))'
                          ' (by (tree-induction t (l cs ih) (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')
    rejected(three.format('(theorem a (internal () (forall ((p Omega)) (equal (implies p p) true)))'
                          ' (by (assume implies (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')
    rejected(three.format('(theorem a (forall ((t T)) (implies (h (equal t t)) (equal t t)))'
                          ' (by (modus-ponens h (g) (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')
    # A script that does not prove its theorem is reported so: the antecedent is not cited.
    text = HYP.replace('(by (assume h (reduce weak h)))', '(by (assume h (reduce weak)))')
    rejected(text, where(text, '(reduce weak))))\n  (theorem composition'),
             'the script of the theorem symmetry does not prove it')
    # An alternative has two scripts, and proves by neither where neither proves; a case analysis
    # of a bitstring names a variable and a number of bits, and proves nothing the bits decide
    # where it takes fewer of them; version 2 reads neither.
    rejected(HYP.replace('(first (reduce weak) (reduce weak append-nil))', '(first (reduce weak))'),
             '38:12', 'the script of the theorem append-nil-first does not read')
    # The failure of an alternative is that of its second script; a script read at several cases
    # is reported at each case at which it fails.
    text = HYP.replace('(first (reduce weak) (reduce weak append-nil))',
                       '(first (reduce weak) (reduce head))')
    error = rejected(text, where(text, '(reduce head)'),
                     'the script of the theorem append-nil-first does not prove it')
    assert error.count(': error: ') == 1, error
    for old, new in (('(bits-cases b 2', '(bits-cases a 2'), ('(bits-cases b 2', '(bits-cases b weak')):
        rejected(HYP.replace(old, new), '44:12', 'the script of the theorem head-bits does not read')
    text = HYP.replace('(bits-cases c 1', '(bits-cases c 0')
    step = where(text, '(reduce weak h))))))')
    error = rejected(text, step, 'the script of the theorem head-bits does not prove it')
    reports = [line for line in error.splitlines() if ': error: ' in line]
    assert len(reports) > 1 and all(f':{step}: error: ' in line for line in reports), error
    rejected(document('(theorem a (forall ((t T)) (equal t t))'
                      ' (by (first (reduce weak) (reduce weak))))'),
             '2:12', 'the script of the theorem a does not read')

    # Version 3 abbreviates, proves the uniqueness of a fold with premises that scripts prove,
    # cites the instances of theorems, cuts in hypotheses, states the normal form of a theorem's
    # companion, keeps definitions folded, chooses a script by a bitstring's label, splits the
    # values of tests and rewrites under masks and in arguments.
    forms = root / 'Forms.proofs.geb'
    forms.write_text(FORMS)
    forms_cert = root / 'forms.cert'
    run('prove', manifest, forms, forms_cert)
    run('replay', manifest, forms, forms_cert)
    def at(text, name):
        for number, line in enumerate(text.splitlines(), 1):
            column = line.find(f'(theorem {name}')
            if column >= 0:
                return f'{number}:{column + len("(theorem ") + 1}'
        raise AssertionError(name)
    def forms_rejected(old, new, name, message, step=None):
        text = FORMS.replace(old, new)
        assert text != FORMS, old
        rejected(text, where(text, step) if step else at(text, name), message)
    # A definition kept folded is not unfolded: without the rule the script proves nothing.
    forms_rejected('(with-rules ((folded Pair.first) first-folded)', '(with-rules ((folded Pair.first))',
                   'first-twice', 'the script of the theorem first-twice does not prove it',
                   step='(reduce weak)))))\n  ; The case analysis of a test')
    # A rule keeps folded definitions of the program and of the library; a normal form names a
    # depth and rules; an abbreviation is expanded where it stands, and names what is bound there.
    forms_rejected('(normal weak (folded Pair.first))', '(normal weak (folded Pair.second))',
                   'first-folded', 'the script of the theorem first-folded does not read')
    forms_rejected('(normal weak (folded Pair.first))', '(normal (folded Pair.first))',
                   'first-folded', 'the script of the theorem first-folded does not read')
    forms_rejected('(forall ((ts Ts)) (equal rebuilt ts))', '(forall ((us Ts)) (equal rebuilt us))',
                   'rebuild-again', 'the theorem rebuild-again is not')
    # The script of a label proves at its bitstring, and a label has fewer bits than the cases.
    forms_rejected('(0 1) (reduce head)', '(0 1) (normalize 0)', 'label-scripts',
                   'the script of the theorem label-scripts does not prove it',
                   step='(normalize 0)')
    forms_rejected('(0 1) (reduce head)', '(0 4) (reduce head)', 'label-scripts',
                   'the script of the theorem label-scripts does not read')
    forms_rejected('(0 1) (reduce head)', '(0 1)', 'label-scripts',
                   'the script of the theorem label-scripts does not read')
    # An instance is of the terms given; a formula holds where its hypothesis equates it with the
    # equation of a term with itself, which the checker decides.
    forms_rejected('(instance (first-fn X) (x) (z) weak)', '(instance (first-fn X) (z) (x) weak)',
                   'first-at-pair', 'the script of the theorem first-at-pair does not prove it',
                   step='(instance (first-fn X) (z) (x) weak)')
    forms_rejected('(equal (equal x y) (equal unit unit))', '(equal (equal x y) (equal x unit))',
                   'holds-equal', 'the theorem holds-equal is not')
    text = FORMS.replace('(implies (h (equal (equal x y) (equal unit unit))) (equal x y))',
                         '(implies (h (equal x y)) (equal x x))')
    assert text != FORMS
    target = root / 'Bad.proofs.geb'
    target.write_text(text)
    assert 'the derivations of the development do not check' in run(
        'prove', manifest, target, certificate, ok=False)
    # Rewriting under a mask takes its rounds, and finds the conditional where it is kept folded;
    # an argument is rewritten to the left side of a theorem whose right side it is, which the
    # checker decides.
    forms_rejected('(mask-hypotheses absorb cond-same-again 1', '(mask-hypotheses absorb cond-same-again 0',
                   'under-mask', 'the script of the theorem under-mask does not prove it',
                   step='(reduce weak))))))\n')
    forms_rejected('(with-rules ((folded (lib cond)))\n        (mask-hypotheses',
                   '(with-rules ()\n        (mask-hypotheses',
                   'under-mask', 'the script of the theorem under-mask does not prove it',
                   step='(reduce weak))))))\n')
    target.write_text(FORMS.replace('(succ-pred cons-again (reduce weak))',
                                    '(succ-pred append-nil (reduce weak))'))
    assert 'the derivations of the development do not check' in run(
        'prove', manifest, target, certificate, ok=False)
    # Version 2 reads none of them.
    target.write_text(FORMS.replace('(proofs 3', '(proofs 2'))
    assert 'the theorem Ts is not' in run('prove', manifest, target, certificate, ok=False)
    assert certificate.read_bytes() == saved

    # A hole stands where a script stands, in version 3. Its development is not proved and writes
    # nothing: the hole is reported where it is written, with its goal as a statement of the
    # internal language in the names the script has there. The theorems after it are proved
    # under it, so that a later failure is reported beside it and a theorem that cites it is not.
    holes = """(proofs 3 (program pair) (import Pair.proofs.geb)
  (theorem right-unit (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (induction xs (y ys ih) (reduce weak) ?step)))
  (theorem right-unit-twice
    (forall ((xs (List T))) (equal (Lists.append (Lists.append xs (nil T)) (nil T)) xs))
    (by (reduce weak right-unit)))
  (theorem left-first (equal Pair.left Pair.first) (by (normalize 0))))
"""
    goal = ('(internal () (forall ((y T) (ys (List T))) '
            '(implies (ih (equal (Lists.append ys (nil T)) ys)) '
            '(equal (Lists.append (cons T y ys) (nil T)) (cons T y ys)))))')
    error = rejected(holes, where(holes, '?step'),
                     f'the script of the theorem right-unit leaves the hole ?step open, at the goal {goal}')
    reports = [line for line in error.splitlines() if ': error: ' in line]
    assert len(reports) == 2, error
    assert (f":{where(holes, '(normalize 0)')}: error: the script of the theorem left-first does "
            'not prove it') in reports[1], error
    # A goal longer than a line of the report is also laid out on the lines after it.
    assert error.splitlines()[1] == '  (internal ()', error
    # `check` reports the same obligations.
    target = root / 'Bad.proofs.geb'
    assert run('check', target, ok=False) == error
    # The goal reported is a statement the document reads: stated as a theorem, the script that
    # fills the hole proves it, and the development with the hole filled is proved and replayed.
    fill = '(reduce-hypotheses weak (ih) (reduce weak ih))'
    filled = (holes.replace('?step', fill).replace('(normalize 0)', '(normalize 64)')
              .replace('(import Pair.proofs.geb)',
                       f'(import Pair.proofs.geb)\n  (theorem step {goal}\n    (by {fill}))'))
    target.write_text(filled)
    run('prove', manifest, target, root / 'filled.cert')
    run('replay', manifest, target, root / 'filled.cert')
    # A step that fails and a hole of one script are both reported, each where it is written.
    text = holes.replace('(reduce weak) ?step', '(normalize 0) ?step')
    error = rejected(text, where(text, '(normalize 0) ?step'),
                     'the script of the theorem right-unit does not prove it: this step does not '
                     'prove the goal (internal () (equal (Lists.append (nil T) (nil T)) (nil T)))')
    assert f":{where(text, '?step')}: error: the script of the theorem right-unit leaves the hole" in error, error
    # A hole that no proof reaches states no obligation; version 2 reads no hole.
    target.write_text(holes.replace('(induction xs (y ys ih) (reduce weak) ?step)',
                                    '(first (reduce weak append-nil) ?unreached)')
                      .replace('(normalize 0)', '(normalize 64)'))
    run('prove', manifest, target, root / 'filled.cert')
    run('replay', manifest, target, root / 'filled.cert')
    rejected(document('(theorem a (forall ((t T)) (equal t t)) (by ?h))'), '2:12',
             'the script of the theorem a does not read')
    # A hole of a script read at several cases is reported at each, here the empty bitstring and
    # each bit before a bitstring, the variables and hypotheses the cases add named by their
    # positions; a hole an abbreviation holds is reported where the abbreviation stands.
    text = FORMS.replace('(bits-cases b 2 (reduce weak) (0 1) (reduce head))', '(bits-cases b 1 ?bit)')
    error = rejected(text, where(text, '?bit'),
                     'the script of the theorem label-scripts leaves the hole ?bit open, at the goal '
                     '(internal () (forall ((b Bits)) '
                     '(equal (lib cond Bits (nil Bit) (lib bnil) (lib bnil)) (lib bnil))))')
    reports = [line for line in error.splitlines() if ': error: ' in line]
    assert len(reports) == 3, error
    assert all(f":{where(text, '?bit')}: error: " in line for line in reports), error
    for line, bit in zip(reports[1:], ('inl', 'inr')):
        assert ('(forall ((b Bits) (_1 Bit) (_2 Bits) (_3 Unit)) (implies (_h0 (equal (lib cond '
                'Bits _2 (lib bnil) (lib bnil)) (lib bnil))) (equal (lib cond Bits '
                f'(cons Bit ({bit} Unit Unit _3) _2) (lib bnil) (lib bnil)) (lib bnil)))))') in line, error
    # The goal of a hole that is a theorem's whole script is the theorem's statement, as the
    # document reads the forms of types and of terms: written with the names the report gives the
    # variables that terms bind, the statement is reported as it is written.
    part = ('(pair (list-rec (nil Y) (_8 _9) (cons Y (f _8) _9) (snd p)) '
            '(pair ((case X Unit Y (pair f (lam ((_8 Unit)) (f (fst p))))) s) '
            '(pair (rose-rec Bits (_8) (fst _8) t) '
            '(pair (implies o true) '
            '(pair (inr Unit Unit unit) '
            '(pair (lib cond Y bs (f (fst p)) (f (fst p))) '
            '(pair (node Bits (pair bs (nil T))) '
            '(pair (equal r r) (pair (Pair.first t t) (lam ((_8 X)) (pair _8 b)))))))))))')
    statement = ('(internal (X Y) (forall ((f (Arrow X Y)) (p (Prod X (List X))) (s (Sum X Unit)) '
                 '(t T) (r (Rose X)) (o Omega) (b Bit) (bs Bits)) '
                 f'(implies (h (equal (f (fst p)) (f (fst p)))) (equal {part} {part}))))')
    text = three.format(f'(theorem shapes {statement}\n    (by ?whole))')
    rejected(text, where(text, '?whole'),
             f'the script of the theorem shapes leaves the hole ?whole open, at the goal {statement}')
    text = FORMS.replace('(abbreviation by-append (with-rules (append-rules) (reduce weak)))',
                         '(abbreviation by-append (with-rules (append-rules) ?rules))')
    rejected(text, where(text, 'by-append))'),
             'the script of the theorem append-nil-rules leaves the hole ?rules open, at the goal '
             '(internal () (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs)))')

    # An import is a path below the document that reads, and imports return to no document.
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import ../Pair.proofs.geb)'), '', 'is not a relative path below')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Absent.proofs.geb)'), '', 'Absent.proofs.geb does not read')
    rejected(document('(theorem a (equal Pair.left Pair.left) (by (normalize 4)))',
                      '(import Bad.proofs.geb)'), '', 'return to a document')

    # A document that names its program is proved and replayed without a manifest, against the
    # manifest of that name in its directory or the nearest above; the documents it imports are
    # read against that program, whatever program they name.
    def named(header, body='(theorem again (forall ((xs (List T)))'
                           ' (equal (Lists.append xs (nil T)) xs)) (by (reduce weak append-nil)))'):
        return f'(proofs 2 {header}\n  {body})\n'
    below = root / 'below'
    below.mkdir()
    (below / 'Imported.proofs.geb').write_text(
        '(proofs 2 (program elsewhere)\n'
        '  (theorem append-nil (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))\n'
        '    (by (induction xs (y ys ih) (reduce weak)'
        ' (reduce-hypotheses weak (ih) (reduce weak ih))))))\n')
    here = below / 'Named.proofs.geb'
    here.write_text(named('(program pair) (import Imported.proofs.geb)'))
    own = root / 'named.cert'
    run('prove', here, own)
    run('replay', here, own)
    explicit = root / 'explicit.cert'
    run('prove', manifest, here, explicit)
    assert explicit.read_bytes() == own.read_bytes()

    # `check` proves a proof document and writes nothing, reports a failure at the theorem, and
    # compiles any other file as a source of a program.
    before = sorted(p.name for p in below.iterdir())
    assert run('check', here) == ''
    assert sorted(p.name for p in below.iterdir()) == before
    failing = below / 'Failing.proofs.geb'
    failing.write_text(named('(program pair)', '(theorem again (equal Pair.left Pair.first)'
                                               ' (by (normalize 0)))'))
    error = run('check', failing, ok=False)
    assert error.startswith(f'{failing}:2:51: error: the script of the theorem again does not '
                            'prove it: this step does not prove the goal '
                            '(internal () (equal Pair.left Pair.first))'), error
    assert run('check', root / 'Pair.geb') == ''
    broken = below / 'Broken.geb'
    broken.write_text((root / 'Pair.geb').read_text().replace('T x))', 'T z))'))
    assert run('check', broken, ok=False).startswith(f'{broken}:9:9: error: Pair.left does not check')

    # A document proved without a manifest names one program, which a manifest in its directory
    # or above names once; a manifest given takes the place of the program named.
    def unnamed(text, message):
        target = below / 'Unnamed.proofs.geb'
        target.write_text(text)
        error = run('check', target, ok=False)
        assert error.startswith(f'{target}: ') and message in error, (text, error)
        return target
    plain = '(theorem again (equal Pair.left Pair.left) (by (normalize 4)))'
    target = unnamed(named('', plain), 'the document names no program')
    run('prove', manifest, target, root / 'unnamed.cert')
    target = unnamed(named('(program nowhere)', plain), 'no manifest of the program nowhere')
    run('prove', manifest, target, root / 'unnamed.cert')
    unnamed(named('(program pair) (program pair)', plain), 'names more than one program')
    unnamed('(proofs 1 (program pair)\n  ' + plain + ')\n',
            'a document of a version before 2 has no form (program')
    shutil.copyfile(manifest, root / 'second.manifest')
    unnamed(named('(program pair)', plain), 'several manifests')
    (root / 'second.manifest').unlink()

    # Version 4: the natural numbers, the definitions a development declares, the rule that
    # unfolds one and the induction on a natural number. The certificate replays; a document of
    # version 3 reads none of it; a definition that does not check, a name declared twice and a
    # declared name taken by a variable are rejected; and a hole's goal is reported in the names
    # of the definitions.
    NATURALS = '''(proofs 4 (program pair)
  (definition plus ((m Nat) (n Nat)) Nat
    ((nat-rec (lam ((a Nat)) a) (r) (lam ((a Nat)) (succ (r a))) n) m))
  (definition two () Nat (succ (succ zero)))
  (theorem plus-zero (internal () (forall ((n Nat)) (equal (plus n zero) n)))
    (by (reduce full (unfold plus))))
  (theorem zero-plus (internal () (forall ((n Nat)) (equal (plus zero n) n)))
    (by (nat-induction n 256 (unfold plus))))
  (theorem succ-plus
    (internal () (forall ((m Nat) (n Nat)) (equal (plus (succ m) n) (succ (plus m n)))))
    (by (nat-induction n 256 (unfold plus))))
  (theorem plus-comm (internal () (forall ((m Nat) (n Nat)) (equal (plus m n) (plus n m))))
    (by (nat-induction n 256 zero-plus succ-plus (unfold plus))))
  (theorem two-twice (internal () (equal (plus two two) (succ (succ two))))
    (by (reduce full (unfold plus) (unfold two))))
  (theorem append-nil-again (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (induction xs (y ys ih) (reduce weak) (reduce-hypotheses weak (ih) (reduce weak ih))))))
'''
    naturals = root / 'Naturals.proofs.geb'
    naturals.write_text(NATURALS)
    counted = root / 'naturals.cert'
    run('prove', naturals, counted)
    run('replay', naturals, counted)

    def naturals_rejected(old, new, message):
        text = NATURALS.replace(old, new)
        assert text != NATURALS, old
        target = root / 'BadNaturals.proofs.geb'
        target.write_text(text)
        error = run('check', target, ok=False)
        assert message in error, (new, error)
        return error

    naturals_rejected('(proofs 4 ', '(proofs 3 ', 'does not read')
    naturals_rejected('(definition two () Nat (succ (succ zero)))',
                      '(definition two () Nat (pair zero zero))',
                      'the definition two is not (definition NAME')
    naturals_rejected('(definition two () Nat', '(definition plus () Nat',
                      'the name plus is declared before')
    naturals_rejected('(theorem plus-zero ', '(theorem two ', 'the name two is declared before')
    naturals_rejected('(theorem plus-zero ', '(theorem Nat ', 'the name Nat is declared before')
    naturals_rejected('(forall ((n Nat)) (equal (plus n zero) n))',
                      '(forall ((two Nat)) (equal (plus two zero) two))',
                      'the theorem plus-zero is not (theorem NAME STATEMENT (by SCRIPT))')
    naturals_rejected('(equal (plus two two) (succ (succ two)))', '(equal (plus two) two)',
                      'the theorem two-twice is not (theorem NAME STATEMENT (by SCRIPT))')
    error = naturals_rejected('(by (nat-induction n 256 (unfold plus))))\n  (theorem succ-plus',
                              '(by ?base))\n  (theorem succ-plus',
                              'the script of the theorem zero-plus leaves the hole ?base open')
    assert 'at the goal (internal () (forall ((n Nat)) (equal (plus zero n) n)))' in error, error
    error = naturals_rejected('(by (reduce full (unfold plus) (unfold two))))',
                              '(by (reduce full (unfold plus))))',
                              'the script of the theorem two-twice does not prove it')

    # The development of the tree lemmas and of the case analysis of trees, about the type checker
    # and the expansion of the datatype language, is proved and replayed from its Geb sources, the
    # document of the case analysis naming its program.
    cases = root / 'tree-cases.cert'
    run('prove', proofs_dir / 'tree-cases.proofs.geb', cases)
    run('replay', proofs_dir / 'tree-cases.proofs.geb', cases)

print('test-proof-scripts: internal statements, tactics, imports, named programs, diagnostics, '
      'hypotheses and implications, alternatives, the cases of bitstrings, abbreviations, the '
      'uniqueness of folds, instances, normal forms, folded definitions, rewriting under masks, '
      'holes and goals, natural numbers and definitions, and the tree-cases development passed')
PY
