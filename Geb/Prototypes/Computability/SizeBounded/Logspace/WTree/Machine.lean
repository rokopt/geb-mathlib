/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.RecognizeExpr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Main
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The W-tree recognizer's machine

The recognizer of the W-trees of a coded signature, as the successor-free
expression {name}`Geb.SizeBounded.Logspace.WTree.recognizeExpr` with
parameters computing the signature's label and edge conditions, is
computable by a multi-tape machine in polynomial time and logarithmic space:
{name}`Geb.SizeBounded.Logspace.Machine.computableInTimeAndSpace_sem`
compiles every unary expression to such a machine.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statement mentions {name}`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`,
which depends on {lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main statements

* {lit}`CodedSig.computableInTimeAndSpace_recognize` — the recognizer is
  computable in polynomial time and logarithmic space.

# References

* {cite}`Kristiansen2005`

# Tags

logspace, W-type, recognizer, Turing machine
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.CodedSig

open Turing MultiTapeTM

public section

variable {I : Type} [DecidableEq I] (C : CodedSig I)

/-- The recognizer of the signature's admissible W-trees, returning
{lit}`[true]` on a spelling and the empty word on every other word, is
computable in polynomial time and space linear in the input's binary size,
given expressions computing the signature's label and edge conditions on
every word. -/
theorem computableInTimeAndSpace_recognize (label : LOf 4) (edge : LOf 6)
    (hl : ∀ y, C.ComputesLabel label y) (he : ∀ y, C.ComputesEdge edge y) :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ if C.recognize w then [true] else []) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) := by
  have h := Machine.computableInTimeAndSpace_sem (recognizeExpr label edge)
  rwa [show (fun w ↦ (recognizeExpr label edge).sem ![w]) =
    fun w ↦ if C.recognize w then [true] else [] from
    funext fun w ↦ C.recognizeExprSem_eq label edge w (hl w) (he w)] at h

end

end Geb.SizeBounded.Logspace.WTree.CodedSig
