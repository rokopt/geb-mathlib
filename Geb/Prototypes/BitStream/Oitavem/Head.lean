/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Tail
public import Geb.Prototypes.Computability.Oitavem.Size
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The head of a coded bitstream

The head of the stream a word codes is the head of the value at depth zero
of the expression the word spells: a bit, or termination when that value is
empty, or nothing when the word codes no stream. With the tail on words, the
head makes the coding words the carrier of a coalgebra of the bitstream
functor, whose step at a code is termination when the head is, and otherwise
the head over the tail word; the stream a code denotes is the corecursion of
that coalgebra from the code. The head is the universal evaluator of Logs at
the empty word, restricted to its first bit.

The value at depth {lit}`n` of an expression of {lit}`s` nodes has length at
most {lit}`(n + 2) ^ 2 ^ s`, by the bound
{name}`Geb.Oitavem.Expr.length_le_pow` uniform in the expression, and the
tail's code has two nodes more than the expression's. An evaluator that
recomputes intermediate words bit by bit, holding one counter per node of a
position in an intermediate word, therefore runs in space exponential in the
code's size, not polynomial: the bound's exponent is attained up to a
constant factor by iterated squaring, and the logarithm of the largest
intermediate word is then linear in {lit}`2 ^ s`. The machine form of that
bound is not proved here.

# Main definitions

* {lit}`headCode`, {lit}`stepCode` — the head of a coded stream, and the
  coalgebra on codes.

# Main statements

* {lit}`headCode_spellExpr`, {lit}`headCode_eq_decodeStream` — the head of a
  coding word is the head of the expression's value at depth zero, and the
  head agrees with the decoded stream's first entry on every word.
* {lit}`toStream_eq_corec`, {lit}`decodeStream_eq_corec` — the stream an
  expression codes is the corecursion of the coalgebra from its code, and
  the stream a recognized word codes is the corecursion from the word.
* {lit}`length_valueAt_le`, {lit}`size_tailExpr` — the length of the value
  at a depth, and the size of the tail's code.

# References

* {cite}`Oitavem2010`, Definition 3.1.

# Tags

bitstream, M-type, corecursion, evaluator, expression size
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.Oitavem (Expr size)

public section

/-- The head of the stream a word codes: the head of the value at depth zero
of the expression the word spells, termination when that value is empty,
nothing when the word spells no expression. -/
@[expose] def headCode (w : List Bool) : Option (Option Bool) :=
  (decodeExpr w).map fun e ↦ (valueAt e 0).head?

/-- The head of a coding word is the head of the expression's value at depth
zero. -/
theorem headCode_spellExpr (e : Expr 1 0) : headCode (spellExpr e) = some (valueAt e 0).head? := by
  rw [headCode, decodeExpr_spellExpr]
  rfl

/-- The head agrees with the first entry of the decoded stream. -/
theorem headCode_eq_decodeStream (w : List Bool) :
    headCode w = (decodeStream w).map fun s ↦ (WConstruction.seqEquiv s).get? 0 := by
  rw [headCode, decodeStream, Option.map_map]
  cases decodeExpr w with
  | none => rfl
  | some e =>
    refine congrArg some ?_
    change (valueAt e 0).head? = (WConstruction.seqEquiv (toStream e)).get? 0
    rw [get?_seq_toStream]
    cases hv : valueAt e 0 with
    | nil => exact (ite_eq_right fun h ↦ h 0 (Nat.le_refl 0) hv).symm
    | cons b v =>
      exact (ite_eq_left fun m hm ↦ by
        obtain rfl : m = 0 := Nat.le_zero.mp hm
        rw [hv]
        exact List.cons_ne_nil b v).symm

/-- The coalgebra on codes: termination when the head is, and otherwise the
head over the tail word. -/
@[expose] def stepCode (w : List Bool) : Layer (List Bool) :=
  (headCode w).bind fun h ↦ h.map fun b ↦ (b, tailWord w)

/-- The coalgebra's step at a coding word: termination when the value at depth
zero is empty, and otherwise its head over the code of the tail. -/
theorem stepCode_spellExpr (e : Expr 1 0) :
    stepCode (spellExpr e) =
      match valueAt e 0 with
      | [] => none
      | b :: _ => some (b, spellExpr (tailExpr e)) := by
  rw [stepCode, headCode_spellExpr, Option.bind_some, tailWord_spellExpr]
  cases valueAt e 0 <;> rfl

/-- The finite unfoldings of the transition from depth zero are those of the
coalgebra on codes from the code. -/
theorem corecApprox_step_eq_stepCode : ∀ (n : WConstruction.Depth) (e : Expr 1 0),
    WConstruction.corecApprox (step e) n 0 = WConstruction.corecApprox stepCode n (spellExpr e) :=
  WConstruction.depthInduction
    (fun _ ↦ (WConstruction.eq_cutoff _).trans (WConstruction.eq_cutoff _).symm)
    fun n ih e ↦ by
      apply (WConstruction.succEquiv n).injective
      rw [WConstruction.corecApprox_succ, WConstruction.corecApprox_succ, stepCode_spellExpr]
      simp only [step]
      cases valueAt e 0 with
      | nil => rfl
      | cons b v =>
        exact congrArg (fun t ↦ some (b, t))
          ((corecApprox_step_succ e n 0).trans (ih (tailExpr e)))

/-- The stream an expression codes is the corecursion of the coalgebra on
codes from its code. -/
theorem toStream_eq_corec (e : Expr 1 0) :
    toStream e = WConstruction.corec stepCode (spellExpr e) :=
  WConstruction.stream_ext _ _ fun n ↦ corecApprox_step_eq_stepCode n e

/-- The stream a recognized word codes is the corecursion of the coalgebra on
codes from the word. -/
theorem decodeStream_eq_corec (w : List Bool) (h : recognize w = true) :
    decodeStream w = some (WConstruction.corec stepCode w) := by
  obtain ⟨e, rfl⟩ := (recognize_iff_spellExpr w).mp h
  rw [decodeStream_spellExpr, toStream_eq_corec]

/-- The value at a depth of an expression of {lit}`s` nodes has length at most
{lit}`(n + 2) ^ 2 ^ s`. -/
theorem length_valueAt_le (e : Expr 1 0) (n : ℕ) :
    (valueAt e n).length ≤ (n + 2) ^ 2 ^ size e.1.1 :=
  Expr.length_le_pow e ![depthWord n] Fin.elim0 n fun j ↦ match j with
    | ⟨0, _⟩ => (List.length_replicate (n := n) (a := false)).le

/-- The code of the tail has two nodes more than the code of the expression. -/
theorem size_tailExpr (e : Expr 1 0) : size (tailExpr e).1.1 = size e.1.1 + 2 := by
  change 1 + size e.1.1 + Geb.SizeBounded.finSum 1 (fun _ ↦ 1) = size e.1.1 + 2
  change 1 + size e.1.1 + (0 + 1) = size e.1.1 + 2
  omega

end

end Geb.BitStream.Oitavem
