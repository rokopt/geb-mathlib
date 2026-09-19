/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.SigCheck
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Machine
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The machine recognizing the algebra's own expressions

The recognizer of the spellings of the size-bounded algebra's expressions,
{name}`Geb.SizeBounded.Logspace.WTree.SigCheck.sigRecognizer`, is an
expression of the successor-free subalgebra, so the subalgebra's soundness
theorem compiles it to a multi-tape machine running in polynomial time and
space logarithmic in the input's length.

The module is admitted to {lit}`GebMeta.classicalAllowedModules` for the
reason {name}`Geb.SizeBounded.Logspace.WTree.CodedSig.computableInTimeAndSpace_recognize`
is: its statement mentions
{name}`Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength`.

# Main statements

* {lit}`computableInTimeAndSpace_sigRecognizer` — the recognizer's value is
  computed by a machine in polynomial time and logarithmic space.
* {lit}`computableInTimeAndSpace_sigRecognize` — that machine decides
  whether a word spells an expression of the algebra.

# References

* {cite}`Kristiansen2005`
* {cite}`Mazzanti2016`

# Tags

logspace, size-bounded algebra, recognizer, Turing machine
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.SigCheck

open Turing MultiTapeTM Sig SigLabel SigEdge

public section

/-- The recognizer, being an expression of the subalgebra, is computed by a
machine in polynomial time and space linear in the input's binary size. -/
theorem computableInTimeAndSpace_sigRecognizer :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ sigRecognizer.sem ![w]) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) :=
  Machine.computableInTimeAndSpace_sem sigRecognizer

/-- That machine decides whether a word spells an expression of the algebra,
in polynomial time and space linear in the input's binary size. -/
theorem computableInTimeAndSpace_sigRecognize :
    ∃ c d : ℕ, ComputableInTimeAndSpaceOfLength
      (fun w ↦ if sigCoded.recognize w then [true] else []) (.refl _) (.refl _)
      (fun n ↦ c * (n + 1) ^ d) (fun n ↦ c * (Nat.size n + 1)) :=
  sigCoded.computableInTimeAndSpace_recognize labelOk edgeOk computesLabel computesEdge

end

end Geb.SizeBounded.Logspace.WTree.SigCheck
