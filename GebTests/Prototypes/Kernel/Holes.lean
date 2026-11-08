/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Holes -- shake: keep
public meta import Geb.Prototypes.Kernel.Holes -- shake: keep

set_option doc.verso true in
/-!
# Programs with holes

The check of programs with holes, at examples: a hole's context and expected type, read from
the hole's position and from the definitions after it; a type that no equation determines,
displayed with a metavariable; one obligation for every occurrence of a name, an occurrence under
a further binder substituting by name; and the rejections, of an ill-typed program, of an
occurrence outside its hole's context, of a binder that would capture a lifted hole, and of a
budget too small. A program without holes is reported as complete, and every accepted program's
completion loads. A hole filled by a term written in its context is accepted when the term has
the hole's type, and its occurrences compute the term's value though a binder around one shadows
a name the term refers to.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`,
as in the kernel's examples.

## Main definitions

* {lit}`shown` — the display of a program's check, or its failure.
* {lit}`filled`, {lit}`shownFilled` — the check of a program after one hole is filled, and its
  display.

## Tags

typed hole, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Holes.Tests

/-- The display of a program's check within a budget of a thousand steps, or its failure. -/
def shown (text : String) : String :=
  match check 1000 text.toList with
  | .ok r => String.ofList r.render
  | .error e => e

-- a hole's context and expected type, from its position
#guard shown "(def f (lam (x T) (add ?a x)))" = "(?a T)\n  (x T)\n"
-- the expected type of a function's body, from a later definition's use of the function
#guard shown "(def f (lam (x T) ?b)) (def g (lam (y T) (add (f y) 1)))" = "(?b T)\n  (x T)\n"
-- the binders of a binding and of several abstractions, the outermost first
#guard shown "(def f (lam ((x T) (y (List T))) (let z Unit unit ?c)))" =
  "(?c (meta 0))\n  (x T)\n  (y (List T))\n  (z Unit)\n"
-- a type no equation determines, displayed with its metavariables
#guard shown "(def f (lam (p (Prod T T)) (fst ?q)))" =
  "(?q (Prod (meta 0) (meta 1)))\n  (p (Prod T T))\n"
-- every occurrence of a name is one obligation; an occurrence under a further binder applies the
-- hole to the variable of the same name
#guard shown "(def f (lam (x T) (pair ?a (lam (y Unit) (add ?a x)))))" = "(?a T)\n  (x T)\n"
-- an atom of a quotation is data, whatever its characters
#guard shown "(def f (quote (0 \"?x\")))" = "complete\n"
-- a program without holes is complete
#guard shown "(def f (lam (x T) x)) (def main f)" = "complete\n"
-- the rejections: an ill-typed program, an occurrence where a variable of the hole's context is
-- not in scope, a binder that would capture a lifted hole, and a budget too small
#guard shown "(def f (lam (x T) (add ?a unit)))" = "f is ill-typed: it equates T and Unit"
#guard shown "(def f (pair (lam (x T) ?a) ?a))" = "f does not resolve"
#guard (match check 1000 "(def f (lam (\"?a\" T) ?a))".toList with
  | .error _ => true | .ok _ => false)
#guard (match check 0 "(def f (lam (x T) (add ?a x)))".toList with
  | .error e => e == "f: the budget of unification is spent" | .ok _ => false)
-- the completion of an accepted program loads, and is the program when it has no holes
#guard (match check 1000 "(def f (lam (x T) (add ?a x))) (def g (f 3))".toList with
  | .ok r => (load r.completion).isSome && !r.complete | .error _ => false)
#guard (match check 1000 "(def f (lam (x T) x)) (def g (f 3))".toList,
    readProgram "(def f (lam (x T) x)) (def g (f 3))".toList with
  | .ok r, some ds => r.completion == ds.map Prod.snd && r.complete | _, _ => false)

/-- The check of a program after one hole is filled by a term's text. -/
def filled (text name filling : String) : Except String Report := do
  let L ← liftProgram text.toList
  let some [e] := readSExps filling.toList | .error "the filling does not read"
  obligationsOf 1000 (← fill L name.toList e) >>= validate

/-- The display of {lit}`filled`, or its failure. -/
def shownFilled (text name filling : String) : String :=
  match filled text name filling with
  | .ok r => String.ofList r.render
  | .error e => e

-- a filling refers to its own context: the second occurrence, under a binder that shadows the
-- definition the filling names, still adds the definition, so that the program computes 1 + 5
#guard (match filled "(def g 5) (def f (lam (x T) (pair ?a (lam (g T) ?a)))) \
      (def main (lam (t T) ((snd (f 1)) 0)))" "a" "(add x g)" with
  | .ok r => r.complete && ((load r.completion).bind fun G ↦ G.getLast?.bind (·.apply (leaf 0))) ==
      some (leaf 6)
  | .error _ => false)
-- filling one hole leaves the others
#guard shownFilled "(def f (lam (x T) (pair ?a ?b)))" "a" "x" = "(?b (meta 0))\n  (x T)\n"
-- a filling of another type, one naming a variable outside the hole's context, one with a hole
-- of its own, and the filling of a hole the program does not have, are rejected
#guard shownFilled "(def f (lam (x T) (add ?a x)))" "a" "unit" =
  "f is ill-typed: it equates Unit and T"
#guard shownFilled "(def f (lam (x T) (add ?a x)))" "a" "y" =
  "the filling of a does not resolve in its context"
#guard shownFilled "(def f (lam (x T) (add ?a x)))" "a" "?c" =
  "the filling of a does not resolve in its context"
#guard shownFilled "(def f (lam (x T) (add ?a x)))" "b" "x" = "no hole is named b"

end Geb.Kernel.Holes.Tests

end
