/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Recognize
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Main
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The machine recognizing Oitavem-coded bitstreams

The recognizer of the words coding the streams of expressions,
{name}`Geb.BitStream.Oitavem.recognizer`, is an expression of the
successor-free subalgebra, so the subalgebra's soundness theorem compiles it
to a multi-tape machine running in polynomial time and space logarithmic in
the input's length.

The module is admitted to {lit}`GebMeta.classicalAllowedModules` for the
reason {lit}`Geb.SizeBounded.Logspace.WTree.CodedSig.computableInTimeAndSpace_recognize`
is: its statement mentions
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`.

# Main statements

* {lit}`computableInTimeAndSpace_recognizer` — the recognizer's value is
  computed by a machine in polynomial time and logarithmic space.
* {lit}`computableInTimeAndSpace_recognize` — that machine decides whether
  a word codes the stream of an expression.

# References

* {cite}`Kristiansen2005`
* {cite}`Oitavem2010`

# Tags

bitstream, logspace, recognizer, Turing machine
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Turing MultiTapeTM
open Geb.SizeBounded.Logspace.WTree (boolWord)

public section

/-- The recognizer, being an expression of the subalgebra, is computed by a
machine in polynomial time and space linear in the input's binary size. -/
theorem computableInTimeAndSpace_recognizer :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ recognizer.sem ![w]) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) :=
  Geb.SizeBounded.Logspace.Machine.computableInTimeAndSpace_sem recognizer

/-- That machine decides whether a word codes the stream of an expression, in
polynomial time and space linear in the input's binary size. -/
theorem computableInTimeAndSpace_recognize :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ boolWord (recognize w)) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) := by
  have h := computableInTimeAndSpace_recognizer
  rwa [show (fun w ↦ recognizer.sem ![w]) = fun w ↦ boolWord (recognize w) from
    funext recognizerSem_eq] at h

end

end Geb.BitStream.Oitavem
