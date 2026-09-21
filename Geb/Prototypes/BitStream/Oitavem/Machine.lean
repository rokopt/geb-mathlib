/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Recognize
public import Geb.Prototypes.BitStream.Oitavem.Plain
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Machine
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The machine recognizing Oitavem-coded bitstreams

The recognizer of the words coding the streams of expressions,
{name}`Geb.BitStream.Oitavem.recognizer`, is an expression of the
successor-free subalgebra, so the subalgebra's soundness theorem compiles it
to a multi-tape machine running in polynomial time and space logarithmic in
the input's length. The recognizer of the spellings of expressions of Logs
at every arity, {name}`Geb.BitStream.Oitavem.recognizerPlain`, compiles the
same way.

The module is admitted to {lit}`GebMeta.classicalAllowedModules` for the
reason {lit}`Geb.SizeBounded.Logspace.WTree.CodedSig.computableInTimeAndSpace_recognize`
is: its statement mentions
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`.

# Main statements

* {lit}`computableInTimeAndSpace_recognizer` — the recognizer's value is
  computed by a machine in polynomial time and logarithmic space.
* {lit}`computableInTimeAndSpace_recognize` — that machine decides whether
  a word codes the stream of an expression.
* {lit}`computableInTimeAndSpace_recognizePlain` — a machine in the same
  bounds decides whether a word spells an expression of Logs at any arity.

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

/-- A machine in polynomial time and space linear in the input's binary size
decides whether a word spells an expression of Logs at any arity. -/
theorem computableInTimeAndSpace_recognizePlain :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ boolWord (codedPlain.recognize w)) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) :=
  codedPlain.computableInTimeAndSpace_recognize labelOkPlain EdgeExpr.edgeOk computesLabelPlain
    computesEdgePlain

end

end Geb.BitStream.Oitavem
