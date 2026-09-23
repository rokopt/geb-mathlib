/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.BitStream.Oitavem.Recognize
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The tail of a coded bitstream

The tail of the stream an expression codes is coded by the composite of the
expression with the successor by a clear bit: the value of the composite at
a depth is the value of the expression at the next depth. The coded stream
is thereby the corecursion of a generator on codes: its first layer is
termination when the value at depth zero is empty, and otherwise the head
of that value over the stream the composite codes. The composite codes the
tail of the stream exactly when the stream does not terminate at once,
since the stream terminates at the first empty value and a later empty
value is not observed.

On words, the code of the composite is the code of the expression between
a constant prefix, the root's prefix followed by the spine and label of the
composition node, and a constant suffix, the label of the successor. The
tail on words is that rewrite, computable in constant space; it is stated
as a function on words rather than as an expression of the successor-free
subalgebra, whose values are no longer than its inputs.

# Main definitions

* {lit}`tailExpr` — the composite coding the tail.
* {lit}`compHeader`, {lit}`succLeaf`, {lit}`tailWord` — the constant
  words around the code of the expression, and the tail on words.

# Main statements

* {lit}`valueAt_tailExpr` — the composite's value at a depth is the
  expression's at the next.
* {lit}`dest_toStream` — the generator law: the first layer of the coded
  stream.
* {lit}`tail_toStream` — the composite codes the tail of the stream when
  the value at depth zero is not empty.
* {lit}`spellExpr_tailExpr`, {lit}`tailWord_spellExpr` — the code of the
  composite, and the tail on words.

# References

* {cite}`Oitavem2010`, Definition 3.1.

# Tags

bitstream, M-type, corecursion, tail, logspace
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.Oitavem (Expr)
open Geb.SizeBounded.Logspace.WTree (spine)
open Geb.BitTree (leaf)
open Geb.BitTree.Elias (encode)

public section

/-- The composite coding the tail: the expression at the successor of the
depth by a clear bit. -/
@[expose] def tailExpr (e : Expr 1 0) : Expr 1 0 :=
  Expr.comp (safe := false) e ![Expr.initial (.succ false)]

/-- The composite's value at a depth is the expression's at the next. -/
theorem valueAt_tailExpr (e : Expr 1 0) (n : ℕ) :
    valueAt (tailExpr e) n = valueAt e (n + 1) :=
  congrArg (fun x ↦ e.eval x Fin.elim0) (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The finite unfoldings of the transition from a successor depth are those
of the composite's transition from the depth. -/
theorem corecApprox_step_succ (e : Expr 1 0) : ∀ (n : Geb.MType.Depth) (k : ℕ),
    WConstruction.corecApprox (step e) n (k + 1) =
      WConstruction.corecApprox (step (tailExpr e)) n k :=
  Geb.MType.Depth.induction (fun _ ↦ Subsingleton.elim _ _)
    fun n ih k ↦ by
      apply (WConstruction.succEquiv n).injective
      rw [WConstruction.corecApprox_succ, WConstruction.corecApprox_succ]
      simp only [step, valueAt_tailExpr]
      cases valueAt e (k + 1) with
      | nil => rfl
      | cons b v => exact congrArg (fun t ↦ some (b, t)) (ih (k + 1))

/-- The corecursion from a successor depth is the corecursion of the
composite's transition from the depth. -/
theorem corec_step_succ (e : Expr 1 0) (k : ℕ) :
    WConstruction.corec (step e) (k + 1) = WConstruction.corec (step (tailExpr e)) k :=
  Geb.MType.M.ext fun n ↦ corecApprox_step_succ e n k

/-- The generator law: the first layer of the coded stream is termination
when the value at depth zero is empty, and otherwise the head of that value
over the stream the composite codes. -/
theorem dest_toStream (e : Expr 1 0) :
    WConstruction.dest (toStream e) =
      match valueAt e 0 with
      | [] => none
      | b :: _ => some (b, toStream (tailExpr e)) := by
  change WConstruction.dest (WConstruction.corec (step e) 0) = _
  rw [WConstruction.dest_corec]
  simp only [step]
  cases valueAt e 0 with
  | nil => rfl
  | cons b v => exact congrArg (fun t ↦ some (b, t)) (corec_step_succ e 0)

/-- The composite codes the tail of the coded stream when the value at depth
zero is not empty. -/
theorem tail_toStream (e : Expr 1 0) (h : valueAt e 0 ≠ []) :
    toStream (tailExpr e) = WConstruction.tail (toStream e) := by
  cases hv : valueAt e 0 with
  | nil => exact absurd hv h
  | cons b v =>
    rw [WConstruction.tail, dest_toStream, hv]
    rfl

/-- The word between the root's prefix and the code of the expression in the
code of its composite: the two forks of the composition node's spine, and
its label as a leaf. -/
@[expose] def compHeader : List Bool :=
  true :: true :: encode (leaf (code (some (.comp 1 1 false))))

/-- The word after the code of the expression in the code of its composite:
the label of the successor by a clear bit, as a leaf. -/
@[expose] def succLeaf : List Bool := encode (leaf (code (some (.initial (.succ false)))))

/-- The code of the composite: the root's prefix, the composition node's
header, the code of the expression, and the successor's leaf. -/
theorem spellExpr_tailExpr (e : Expr 1 0) :
    spellExpr (tailExpr e) =
      rootPrefix ++ (compHeader ++ (coded.spell (embed e.1.1) ++ succLeaf)) := by
  rw [spellExpr, spell_wrap]
  refine congrArg (rootPrefix ++ ·) ?_
  change encode (spine (leaf (code (some (.comp 1 1 false))))
    (List.ofFn fun i : Fin 2 ↦ coded.toTree
      (embed ((Fin.cases (Sum.inl ()) (fun j ↦ Sum.inr j) i : Unit ⊕ Fin 1).elim (fun _ ↦ e)
        (fun j ↦ ![Expr.initial (.succ false)] j)).1.1))) = _
  rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
  rfl

/-- The tail on words: the root's prefix, the composition node's header, the
word after the root's prefix, and the successor's leaf. -/
@[expose] def tailWord (w : List Bool) : List Bool :=
  rootPrefix ++ (compHeader ++ (w.drop rootPrefix.length ++ succLeaf))

/-- The tail of the code of an expression is the code of its composite. -/
theorem tailWord_spellExpr (e : Expr 1 0) : tailWord (spellExpr e) = spellExpr (tailExpr e) := by
  rw [tailWord, spellExpr_tailExpr, spellExpr, spell_wrap, List.drop_left]

end

end Geb.BitStream.Oitavem
