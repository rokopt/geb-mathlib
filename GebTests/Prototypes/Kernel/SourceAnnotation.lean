/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.SourceAnnotation
public meta import Geb.Prototypes.Kernel.SourceAnnotation -- shake: keep

set_option doc.verso true in
/-!
# Source annotations of kernel programs

The fixtures distinguish source occurrences of equal terms, shadowed and unused binders,
curried applications and let expansion. Canonical records retain comments before forms,
inside binders, inside quoted data and after the last form. Malformed and stale records are
rejected. The core and its identifiers are unaffected by changes of bound names or comments.

## Main definitions

* {lit}`readSource` — read a fixture as source bytes.
* {lit}`binderNames` — the binder spellings and their kernel vertices.
* {lit}`nested`, {lit}`forms` — binding and term-form fixtures.

## Tags

kernel, annotation, binder, comment, serialization, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.SourceAnnotation.Tests

open scoped FinEnum
open Document

/-- Read an ASCII or UTF-8 fixture as bytes, as the host reads source. -/
def readSource (s : String) : Option Annotated :=
  (readDoc (s.toUTF8.data.toList.map fun b ↦ Char.ofNat b.toNat)).bind annotate

/-- The binder spellings at their full kernel addresses, in source order. -/
def binderNames (a : Annotated) : List (List ℕ × List Char) :=
  a.correspondence.filterMap fun o ↦ do
    guard (o.role == .binder)
    let note ← noteOf a.source o
    return (o.core, ← note.spelling)

/-- Nested and unused binders with comments at the declaration, binder and body. -/
def nested : String :=
  "; before the definition\n\n(def f\n  (lam ((x T)\n    ; unused\n    (unused T))\n" ++
    "    ; body\n    (let x T x\n      (lam (x T) x))))\n; trailing\n"

#guard (readSource nested).map binderNames ==
  some [([0], ['x']), ([0, 1], ['u', 'n', 'u', 's', 'e', 'd']),
    ([0, 1, 1, 0], ['x']), ([0, 1, 1, 0, 1], ['x'])]

-- A use in a let value resolves outside the binding; the body resolves inside it.
#guard (readSource nested).bind (fun a ↦ atForest (a.definitions.map Prod.snd) [0, 1, 1, 1]) ==
  some (mk Label.var [leaf 1])
#guard (readSource nested).bind
    (fun a ↦ atForest (a.definitions.map Prod.snd) [0, 1, 1, 0, 1, 1]) ==
  some (mk Label.var [leaf 0])

-- The unused binder's comment is attached to its lambda, not to a use of its name.
#guard (readSource nested).any fun a ↦
  (a.notesAt [0, 1]).any fun n ↦
    n.trivia.lead.map (·.text) == [" unused".toList]
#guard (readSource nested).any fun a ↦
  (a.notesAt [0]).any fun n ↦ n.trivia.lead.map (·.text) == [" before the definition".toList]
#guard (readSource nested).any fun a ↦ a.source.trail.map (·.text) == [" trailing".toList]

-- Numeral expansion may change a binder's resolved name; its original spelling is retained.
#guard (readSource "(defnum named 7) (def f (lam (named T) named))").map binderNames ==
  some [([0], "named".toList)]

-- A quoted list whose contents spell a lambda supplies no binder annotation.
#guard (readSource "(def q (quote (0 lam (0 x T) x)))").map binderNames == some []

-- Equal subexpressions retain distinct comments and distinct source vertices.
#guard (readSource "(def p (pair\n; left\n7\n; right\n7))").any fun a ↦
  (a.notesAt [0, 0]).any (fun n ↦ n.trivia.lead.map (·.text) == [" left".toList]) &&
  (a.notesAt [0, 1]).any (fun n ↦ n.trivia.lead.map (·.text) == [" right".toList])

-- Arguments of curried applications have different paths from their source argument indices.
#guard (readSource "(def apply (lam ((f (Arrow T (Arrow T T))) (x T) (y T)) (f x y)))").any
  fun a ↦ (a.notesAt [0, 1, 1, 1, 0, 1]).any (·.spelling == some ['x']) &&
    (a.notesAt [0, 1, 1, 1, 1]).any (·.spelling == some ['y'])

/-- Syntax forms whose keyword and type arguments have kernel vertices. -/
def forms : List String :=
  ["(def f unit)", "(def f (pair 1 2))", "(def f (fst (pair 1 2)))",
    "(def f (snd (pair 1 2)))", "(def f (if 1 2 3))", "(def f (nil T))",
    "(def f (cons 1 (nil T)))", "(def f (fold T))", "(def f (para T))",
    "(def f (iter T))", "(def f (foldr T T))", "(def f (lcase T T))",
    "(def f (iter T 1 (lam (x T) x) 3))",
    "(deftype X T) (def f (lam (x X) x))", "(def f ((lam (x T) x) 1))"]

#guard forms.all (readSource · |>.isSome)

-- Trivia without a direct core address is retained explicitly, including inside quoted data.
#guard (readSource "; alias\n(deftype X T)\n(def q (quote (0\n; inside data\n1)))").any
  fun a ↦ a.unattached.any (fun (_, tr) ↦ tr.lead.map (·.text) == [" alias".toList]) &&
    a.unattached.any (fun (_, tr) ↦ tr.lead.map (·.text) == [" inside data".toList])

-- Closing comments and blank lines survive the existing strict document representation.
#guard (readSource "(def f (lam (x T) x\n\n; close\n))\n\n; end\n").any fun a ↦
  (read a.write).any fun b ↦ b.source.items == a.source.items &&
    b.source.trail == a.source.trail && b.correspondence == a.correspondence &&
    b.definitions == a.definitions

#guard (readSource "(def f (lam (\"λ\" T) \"λ\"))\n; prose: λ\n").any fun a ↦
  (read a.write).any fun b ↦ b.source.items == a.source.items && b.source.trail == a.source.trail

-- Renaming binders or editing prose changes the document, but not the core or its CIDs.
#guard (do
  let a ← readSource "(def f (lam (x T) x))"
  let b ← readSource "; changed\n(def f (lam (y T) y))"
  return a.definitions == b.definitions &&
    a.rekeyed.map Prod.fst == b.rekeyed.map Prod.fst && a.write != b.write) == some true

-- Equal definitions share CIDs but do not merge their source occurrences or binder names.
#guard (readSource "(def f (lam (x T) x)) (def g (lam (y T) y))").any fun a ↦
  let ns := a.rekeyed.filter (·.2.2 == .binder)
  ns.length == 2 && (ns[0]?.map (·.1)) == (ns[1]?.map (·.1)) &&
    (ns[0]?.map (·.2.1)) != (ns[1]?.map (·.2.1))

-- References change their representation during migration; the annotation keeps its vertex.
#guard (readSource "(def f (lam (x T) x)) (def g (lam (z T) (f z)))").any fun a ↦
  a.rekeyed.all fun ((cid, v), _) ↦
    (Identity.migrate (a.definitions.map Prod.snd)).any fun p ↦
      p.cid == cid && (Identity.subtree? p.body v).isSome

-- A changed header cannot assign old source annotations to a new core or a wrong vertex.
#guard (readSource nested).any fun a ↦
  (read (printCanonDoc ({a with definitions := []}.header) a.source)).isNone &&
  (read (printCanonDoc ({a with correspondence := []}.header) a.source)).isNone &&
  (read (printCanonDoc (atomOf ['?', '?']) a.source)).isNone

#guard (readSource "(def f (lam (x T) missing))").isNone
#guard (readSource "(def f 1) (def f 2)").isNone
#guard (readSource "(module M (def f 1))").isNone
#guard (readSource "(data N (zero))").isNone

end Geb.Kernel.SourceAnnotation.Tests

end
