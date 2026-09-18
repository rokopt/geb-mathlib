/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Correct
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Main
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The Elias-length tree recognizer in logarithmic space

The recognizer of the Elias-length tree encoding is computable in polynomial
time and logarithmic space by the soundness theorem of the successor-free
subalgebra alone: it is the meaning of the expression
{name}`Geb.SizeBounded.Logspace.EliasTree.isEliasTree`, and
{name}`Geb.SizeBounded.Logspace.Machine.computableInTimeAndSpace_sem` compiles
every unary expression to such a machine. The bounds are the generic ones of
the compiled machine rather than those of the hand-written binary-counter
machine {lit}`Geb.BitTree.EliasBinary.machine`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statement mentions {name}`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`,
which depends on {lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`computableInTimeAndSpace_isEliasTree` — the recognizer is computable
  in polynomial time and logarithmic space.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, Elias delta code, binary tree, recognizer, Turing machine
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.EliasTree

open Turing MultiTapeTM

public section

/-- The Elias-length tree recognizer, returning {lit}`[true]` on an encoding
and the empty word on every other word, is computable in polynomial time and
space linear in the input's binary size. -/
theorem computableInTimeAndSpace_isEliasTree :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ if Geb.BitTree.Elias.validBool w then [true] else []) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) := by
  have h := Machine.computableInTimeAndSpace_sem isEliasTree
  rwa [show (fun w ↦ isEliasTree.sem ![w]) =
    fun w ↦ if Geb.BitTree.Elias.validBool w then [true] else [] from
    funext fun w ↦ isEliasTreeSem_eq_validBool w] at h

end

end Geb.SizeBounded.Logspace.EliasTree
