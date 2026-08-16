/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto.Initial
public import Geb.Mathlib.Data.W.Basic

/-!
# The term algebra's destructor in the fold's language

The inverse of the initial algebra's structure map, as expressions of
Cobham's class, at the representation `RankedAlphabet.spell` fixes.

`codeOf` and `dropCodeOf` read a word's leading block and what follows it,
through a constant unary prefix that makes the word a self-delimiting entry
whose payload is that block, so no dispatch over the block is needed.

`algPara` is the paramorphism as a fold, at a carrier pairing a subterm's
spelling with the step's value, the value delimited so the two are separable.
The delimiting does not nest: each level reads only the spelling half of a
child's value, so a subterm's boundary is reached by a fold rather than at
the cost a nested encoding would carry. `WType.para` already exists, so no
recursion scheme is introduced here; `algPara` is the encoding at which it is
computed, and `algPara_eq_para` identifies the two.

## Main definitions

* `Geb.CobhamFold.codeOf`, `Geb.CobhamFold.dropCodeOf` — the block reader and
  its complement.
* `Geb.CobhamFold.ParaStep`, `Geb.CobhamFold.algPara` — the paramorphism's
  step, and the paramorphism as a fold.
* `Geb.CobhamFold.algCh` — the delimited-children algebra, one instance of
  the paramorphism.

## Main statements

* `Geb.CobhamFold.stepWord_codeOf`, `Geb.CobhamFold.stepWord_dropCodeOf` —
  what those two compute at an arbitrary word.
* `Geb.CobhamFold.stepWord_codeOf_spell_mk`,
  `Geb.CobhamFold.stepWord_dropCodeOf_spell_mk` — what they recover from a
  spelling.
* `Geb.CobhamFold.dropEntry_algPara` — the value's second half is the
  spelling, whatever the step.
* `Geb.CobhamFold.takeEntry_algPara` — the paramorphism's defining equation.
* `Geb.CobhamFold.algPara_eq_para` — it is `WType.para` at the step that sees
  each child's spelling in place of the subtree.
* `Geb.CobhamFold.sum_ofFn_length_eq_length_flatten`,
  `Geb.CobhamFold.growth_algPara` — a family's total length, and the
  per-symbol growth a bounded step gives.
* `Geb.CobhamFold.dropEntry_algCh`, `Geb.CobhamFold.takeEntry_algCh` — the
  paramorphism's two laws at `Geb.CobhamFold.algCh`.
* `Geb.CobhamFold.length_algCh`,
  `Geb.CobhamFold.five_mul_length_dropEntrySem_algCh_le` — its length at
  arbitrary arguments, and the bound its outputs satisfy.

## References

* [Cobham1965]
* [Meertens1992]
* [Strahm2003]

## Tags

Cobham, ranked tree, destructor, self-delimiting, subterm, paramorphism
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

/-- The leading block of a word, as an expression of arity one: a constant
unary prefix of the alphabet's width makes the word a self-delimiting entry
whose payload is that block. -/
def codeOf (R : RankedAlphabet) : COf 1 :=
  comp1Of takeEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)

/-- The word past its leading block, by the same prefix. -/
def dropCodeOf (R : RankedAlphabet) : COf 1 :=
  comp1Of dropEntryOf (prependOf (List.replicate R.width true ++ [false]) idOf)

/-- The prefixed word, in the shape the payload primitives read. -/
private theorem stepWord_prefix (R : RankedAlphabet) (w : List Bool) :
    stepWord (prependOf (List.replicate R.width true ++ [false]) idOf) w =
      List.replicate R.width true ++ false :: w := by
  rw [stepWord_prependOf, stepWord_idOf, List.append_assoc]
  rfl

/-- The block reader truncates to the alphabet's width. -/
theorem stepWord_codeOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (codeOf R) w = w.take R.width := by
  rw [codeOf, stepWord_comp1Of, stepWord_prefix, stepWord_takeEntryOf,
    takeEntrySem_replicate]

/-- Its complement drops the alphabet's width. -/
theorem stepWord_dropCodeOf (R : RankedAlphabet) (w : List Bool) :
    stepWord (dropCodeOf R) w = w.drop R.width := by
  rw [dropCodeOf, stepWord_comp1Of, stepWord_prefix, stepWord_dropEntryOf,
    dropEntrySem_replicate]

/-- At a spelling the block reader recovers the head symbol's block. -/
theorem stepWord_codeOf_spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    stepWord (codeOf R) (R.spell (Term.mk R i ch)) = R.code i := by
  rw [stepWord_codeOf, spell_mk, List.take_left' (R.length_code i)]

/-- And its complement recovers the children's spellings. -/
theorem stepWord_dropCodeOf_spell_mk (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    stepWord (dropCodeOf R) (R.spell (Term.mk R i ch)) =
      (List.ofFn fun d ↦ R.spell (ch d)).flatten := by
  rw [stepWord_dropCodeOf, spell_mk, List.drop_left' (R.length_code i)]

/-- A paramorphism's step: it receives each child's spelling beside its value.
Distinct from `WType.paraStep`, which pairs a subtree with its value; here the
subtree is replaced by its spelling, so the step is a function on
bitstrings. -/
abbrev ParaStep (R : RankedAlphabet) :=
  (i : Fin R.card) → (Fin (R.arity i) → List Bool × List Bool) → List Bool

/-- The paramorphism as a fold, at a carrier pairing a subterm's spelling with
its value, the value delimited so the two are separable. -/
def algPara (R : RankedAlphabet) (phi : ParaStep R) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) : List Bool :=
  entryWord (phi i fun d ↦ (dropEntrySem ![f d], takeEntrySem ![f d])) ++
    (R.code i ++ (List.ofFn fun d ↦ dropEntrySem ![f d]).flatten)

/-- The value's second half is the spelling, whatever the step, so the
delimiting does not nest: each level reads only this half of a child's
value. -/
theorem dropEntry_algPara (R : RankedAlphabet) (phi : ParaStep R) (t : R.Term) :
    dropEntrySem ![Term.fold R (algPara R phi) t] = R.spell t :=
  Term.induction (motive := fun t ↦
      dropEntrySem ![Term.fold R (algPara R phi) t] = R.spell t)
    (fun i ch ih ↦ by
      rw [Term.fold_mk, algPara, dropEntrySem_entryWord, spell_mk]
      exact congrArg (fun g ↦ R.code i ++ (List.ofFn g).flatten) (funext ih)) t

/-- The step is applied to each child's spelling and value, which is the
paramorphism's defining equation. -/
theorem takeEntry_algPara (R : RankedAlphabet) (phi : ParaStep R)
    (i : Fin R.card) (ch : Fin (R.arity i) → R.Term) :
    takeEntrySem ![Term.fold R (algPara R phi) (Term.mk R i ch)] =
      phi i fun d ↦ (R.spell (ch d),
        takeEntrySem ![Term.fold R (algPara R phi) (ch d)]) := by
  rw [Term.fold_mk, algPara, takeEntrySem_entryWord]
  exact congrArg (phi i) (funext fun d ↦
    congrArg (·, _) (dropEntry_algPara R phi (ch d)))

/-- Read through its take-half, the fold at `algPara` is `WType.para` at the
step that sees each child's spelling in place of the subtree: the recursion
scheme is [Meertens1992]'s, computed at the bitstring representation. -/
theorem algPara_eq_para (R : RankedAlphabet) (phi : ParaStep R) (t : R.Term) :
    takeEntrySem ![Term.fold R (algPara R phi) t] =
      WType.para (α := Fin R.card) (β := fun i ↦ Fin (R.arity i)) (List Bool)
        (fun x ↦ phi x.1 fun d ↦ (R.spell (x.2 d).1, (x.2 d).2)) t :=
  Term.induction (motive := fun t ↦
      takeEntrySem ![Term.fold R (algPara R phi) t] =
        WType.para (α := Fin R.card) (β := fun i ↦ Fin (R.arity i)) (List Bool)
          (fun x ↦ phi x.1 fun d ↦ (R.spell (x.2 d).1, (x.2 d).2)) t)
    (fun i ch ih ↦ by
      have h := WType.para_mk (α := Fin R.card) (β := fun i ↦ Fin (R.arity i))
        (γ := List Bool)
        (fun x ↦ phi x.1 fun d ↦ (R.spell (x.2 d).1, (x.2 d).2)) i ch
      exact ((takeEntry_algPara R phi i ch).trans
        (congrArg (phi i) (funext fun d ↦ congrArg (_, ·) (ih d)))).trans h.symm) t

/-- A family's lengths sum to the length of its flattening. -/
theorem sum_ofFn_length_eq_length_flatten {n : ℕ} (g : Fin n → List Bool) :
    (List.ofFn fun d ↦ (g d).length).sum = ((List.ofFn g).flatten).length := by
  rw [List.length_flatten, List.map_ofFn]
  rfl

/-- The weighted length bound, over a list rather than a family: the payloads
counted twice and the remainders together fit inside the words. -/
private theorem two_mul_length_flatten_take_add_drop_le : ∀ l : List (List Bool),
    2 * ((l.map fun x ↦ takeEntrySem ![x]).flatten).length +
        ((l.map fun x ↦ dropEntrySem ![x]).flatten).length ≤ l.flatten.length :=
  List.rec (Nat.le_refl 0) fun a t ih ↦ by
    have h := two_mul_length_takeEntrySem_add_length_dropEntrySem_le a
    simp only [List.map_cons, List.flatten_cons, List.length_append]
    omega

/-- A paramorphism whose step is bounded by its children's values, plus a
constant, meets the per-symbol growth condition at `2 * cphi + R.width + 1`,
attained at a nullary symbol. The constant is unconditional because the
weighted bound holds at an arbitrary word rather than only at a fold's
value. -/
theorem growth_algPara (R : RankedAlphabet) (phi : ParaStep R) (cphi : ℕ)
    (hphi : ∀ (i : Fin R.card) (g : Fin (R.arity i) → List Bool × List Bool),
      (phi i g).length ≤ (List.ofFn fun d ↦ (g d).2.length).sum + cphi)
    (i : Fin R.card) (f : Fin (R.arity i) → List Bool) :
    (algPara R phi i f).length ≤
      (List.ofFn fun d ↦ (f d).length).sum + (2 * cphi + R.width + 1) := by
  have hstep := hphi i fun d ↦ (dropEntrySem ![f d], takeEntrySem ![f d])
  have hw := two_mul_length_flatten_take_add_drop_le (List.ofFn f)
  rw [algPara, List.length_append, length_entryWord, List.length_append,
    R.length_code, sum_ofFn_length_eq_length_flatten]
  simp only [List.map_ofFn, Function.comp_def, sum_ofFn_length_eq_length_flatten] at hstep hw ⊢
  omega

/-- The delimited-children algebra: the paramorphism whose step returns its
children's spellings, each delimited. -/
def algCh (R : RankedAlphabet) : (i : Fin R.card) →
    (Fin (R.arity i) → List Bool) → List Bool :=
  algPara R fun _ g ↦ (List.ofFn fun d ↦ entryWord (g d).1).flatten

/-- Its value's second half is the spelling. -/
theorem dropEntry_algCh (R : RankedAlphabet) (t : R.Term) :
    dropEntrySem ![Term.fold R (algCh R) t] = R.spell t :=
  dropEntry_algPara R _ t

/-- Its first half is the children's spellings, each delimited, so the `j`-th
child is `Geb.CobhamFold.entryOf j` of it. -/
theorem takeEntry_algCh (R : RankedAlphabet) (i : Fin R.card)
    (ch : Fin (R.arity i) → R.Term) :
    takeEntrySem ![Term.fold R (algCh R) (Term.mk R i ch)] =
      (List.ofFn fun d ↦ entryWord (R.spell (ch d))).flatten :=
  takeEntry_algPara R _ i ch

/-- A family's delimited spelling is the stack layout at the list it names. -/
theorem stackWordV_ofFn {n : ℕ} (g : Fin n → List Bool) :
    stackWordV (List.ofFn g) = (List.ofFn fun d ↦ entryWord (g d)).flatten := by
  rw [stackWordV, List.flatMap_def, List.map_ofFn]
  rfl

/-- The value's second half is the symbol's block followed by the children's
own second halves, whatever the arguments. -/
theorem dropEntrySem_algCh (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    dropEntrySem ![algCh R i f] =
      R.code i ++ (List.ofFn fun d ↦ dropEntrySem ![f d]).flatten := by
  rw [algCh, algPara, dropEntrySem_entryWord]

/-- Its length, at arbitrary arguments: five times the children's second
halves, two bits per child, the sentinel and the block. -/
theorem length_algCh (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algCh R i f).length =
      5 * ((List.ofFn fun d ↦ dropEntrySem ![f d]).flatten).length +
        2 * R.arity i + 1 + R.width := by
  have hlen := length_stackWordV (List.ofFn fun d ↦ dropEntrySem ![f d])
  rw [stackWordV_ofFn, stackSize] at hlen
  rw [algCh, algPara, List.length_append, length_entryWord, List.length_append,
    R.length_code]
  simp only [List.length_ofFn] at hlen ⊢
  omega

/-- Every value the delimited-children algebra produces carries its second
half within a fixed multiple of its own length. It needs no induction
hypothesis, holding at arbitrary arguments, and holds with equality at a
nullary symbol. This is what a potential argument runs over where the
per-symbol growth condition fails: `algCh` duplicates its children's
payloads, delimited and plain, so `|algCh R i f|` is bounded by a multiple of
the children's total rather than by that total plus a constant. -/
theorem five_mul_length_dropEntrySem_algCh_le (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    5 * (dropEntrySem ![algCh R i f]).length + 1 ≤
      (algCh R i f).length + 4 * R.width := by
  rw [dropEntrySem_algCh, List.length_append, R.length_code, length_algCh]
  omega

end Geb.CobhamFold

end
