/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Syntax
public import Geb.Prototypes.BitStream.WConstruction
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The stream an expression codes

An expression of Logs with one normal and no safe argument codes a bitstream:
its value at a depth, the all-zero word of that length, is read as a bit,
the head of the value, or as termination, when the value is empty. The
stream is the corecursion from depth zero on the transition reading the
value at the current depth and moving to the next. Every expression codes a
stream; compatibility of the observations at successive depths is supplied by
the corecursion rather than checked. The stream terminates at the first depth
whose value is empty, and a later empty value is not observed.

# Main definitions

* {lit}`depthWord`, {lit}`valueAt` — a depth as a word, and the value of an
  expression at it.
* {lit}`step`, {lit}`toStream` — the transition and the coded stream.

# Main statements

* {lit}`seqEquiv_toStream`, {lit}`get?_seq_toStream` — the coded stream as a
  sequence, and its entry at a depth: the head of the value there when no
  earlier value is empty.

# References

* {cite}`Oitavem2010`, Definition 3.1.

# Tags

bitstream, M-type, corecursion, logspace
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.Oitavem (Expr)

public section

/-- A depth as a word: the all-zero word of that length. -/
@[expose] def depthWord (n : ℕ) : List Bool := List.replicate n false

/-- The value of an expression at a depth. -/
@[expose] def valueAt (e : Expr 1 0) (n : ℕ) : List Bool := e.eval ![depthWord n] Fin.elim0

/-- The transition: the head of the value at the depth and the next depth, or
termination when the value is empty. -/
@[expose] def step (e : Expr 1 0) (n : ℕ) : Layer ℕ :=
  match valueAt e n with
  | [] => none
  | b :: _ => some (b, n + 1)

/-- The stream an expression codes: the corecursion from depth zero. -/
@[expose] def toStream (e : Expr 1 0) : WConstruction.Stream := WConstruction.corec (step e) 0

/-- The coded stream as a sequence. -/
theorem seqEquiv_toStream (e : Expr 1 0) :
    WConstruction.seqEquiv (toStream e) = Stream'.Seq.corec (step e) 0 :=
  WConstruction.seqEquiv_corec (step e) 0

/-- The entry of the corecursion from a depth: the head of the value at the
depth reached when no value on the way is empty. -/
theorem get?_corec_step (e : Expr 1 0) : ∀ n k : ℕ,
    (Stream'.Seq.corec (step e) k).get? n =
      if ∀ m ≤ n, valueAt e (k + m) ≠ [] then (valueAt e (k + n)).head? else none := by
  intro n
  induction n with
  | zero =>
    intro k
    cases hv : valueAt e k with
    | nil =>
      rw [Stream'.Seq.corec_nil _ _ (by simp only [step, hv]), Stream'.Seq.get?_nil,
        ite_eq_right fun h ↦ h 0 (Nat.le_refl 0) (by rw [Nat.add_zero, hv])]
    | cons b v =>
      rw [Stream'.Seq.corec_cons (show step e k = some (b, k + 1) by simp only [step, hv]),
        Stream'.Seq.get?_cons_zero,
        ite_eq_left fun m hm ↦ by
          obtain rfl : m = 0 := Nat.le_zero.mp hm
          rw [Nat.add_zero, hv]
          exact List.cons_ne_nil b v]
      rfl
  | succ n ih =>
    intro k
    cases hv : valueAt e k with
    | nil =>
      rw [Stream'.Seq.corec_nil _ _ (by simp only [step, hv]), Stream'.Seq.get?_nil,
        ite_eq_right fun h ↦ h 0 (Nat.zero_le _) (by rw [Nat.add_zero, hv])]
    | cons b v =>
      rw [Stream'.Seq.corec_cons (show step e k = some (b, k + 1) by simp only [step, hv]),
        Stream'.Seq.get?_cons_succ, ih (k + 1)]
      have hiff : (∀ m ≤ n, valueAt e (k + 1 + m) ≠ []) ↔ ∀ m ≤ n + 1, valueAt e (k + m) ≠ [] := by
        constructor
        · intro h m hm
          cases m with
          | zero =>
            rw [Nat.add_zero, hv]
            exact List.cons_ne_nil b v
          | succ m =>
            rw [show k + (m + 1) = k + 1 + m by omega]
            exact h m (by omega)
        · intro h m hm
          rw [show k + 1 + m = k + (m + 1) by omega]
          exact h (m + 1) (by omega)
      rw [show k + 1 + n = k + (n + 1) by omega]
      by_cases h : ∀ m ≤ n + 1, valueAt e (k + m) ≠ []
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right fun h' ↦ h (hiff.mp h'), ite_eq_right h]

/-- The entry of the coded stream at a depth: the head of the value there
when no value at a depth up to it is empty. -/
theorem get?_seq_toStream (e : Expr 1 0) (n : ℕ) :
    (WConstruction.seqEquiv (toStream e)).get? n =
      if ∀ m ≤ n, valueAt e m ≠ [] then (valueAt e n).head? else none := by
  rw [seqEquiv_toStream, get?_corec_step]
  simp only [Nat.zero_add]

end

end Geb.BitStream.Oitavem
