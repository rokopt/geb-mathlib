/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Kristiansen.Basic
public import Geb.Prototypes.Computability.SizeBounded.Machine.Main
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Polynomial-time machine soundness

The inclusion in the size-bounded algebra supplies a CSLib machine computing
every unary expression in polynomial time and linear space.

## Main statements

* {lit}`computableInTimeAndSpace_sem` transfers the containing algebra's theorem.

## Implementation notes

This machine stores complete words on work tapes. Its linear space bound does
not establish the logarithmic space bound of {cite}`Kristiansen2005` Theorem 4.7,
which requires a machine evaluating suffix references. This module is allowed
classical choice because CSLib's machine predicates depend on it.

## References

* {cite}`Kristiansen2005`

## Tags

function algebra, Turing machine, polynomial time
-/

set_option doc.verso true

namespace Geb.Kristiansen

public section

/-- Every unary expression is computable in polynomial time and linear space.
The time bound is a machine bound, including input and output. -/
theorem computableInTimeAndSpace_sem (e : LOf 1) :
    ∃ c d : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength
      (fun w ↦ e.sem ![w]) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (n + 1)) :=
  SizeBounded.Machine.computableInTimeAndSpace_sem e.1

end

end Geb.Kristiansen
