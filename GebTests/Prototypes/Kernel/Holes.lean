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
completion loads.

The texts are string constants, converted to lists of characters inside each {lit}`#guard`,
as in the kernel's examples.

## Main definitions

* {lit}`shown` — the display of a program's check, or its failure.

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
#guard shown "(def f (lam (x T) (add ?a unit)))" =
  "the program is ill-typed: two types it equates differ"
#guard shown "(def f (pair (lam (x T) ?a) ?a))" = "f does not resolve"
#guard (match check 1000 "(def f (lam (\"?a\" T) ?a))".toList with
  | .error _ => true | .ok _ => false)
#guard (match check 0 "(def f (lam (x T) (add ?a x)))".toList with
  | .error e => e == "the budget of unification is spent" | .ok _ => false)
-- the completion of an accepted program loads, and is the program when it has no holes
#guard (match check 1000 "(def f (lam (x T) (add ?a x))) (def g (f 3))".toList with
  | .ok r => (load r.completion).isSome && !r.complete | .error _ => false)
#guard (match check 1000 "(def f (lam (x T) x)) (def g (f 3))".toList,
    readProgram "(def f (lam (x T) x)) (def g (f 3))".toList with
  | .ok r, some ds => r.completion == ds.map Prod.snd && r.complete | _, _ => false)

end Geb.Kernel.Holes.Tests

end
