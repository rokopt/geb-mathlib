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
* `Geb.CobhamFold.chGrowth` — the per-symbol growth the delimited-children
  algebra meets under its own invariant.
* `Geb.CobhamFold.algChOf` — that algebra as an expression of the class.

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
* `Geb.CobhamFold.growth_algCh_of_dropEntrySem_le`,
  `Geb.CobhamFold.stackSize_algCh_le` — the per-symbol growth condition at
  `Geb.CobhamFold.algCh`, and the linearity hypothesis it discharges.
* `Geb.CobhamFold.semAt_algChOf`, `Geb.CobhamFold.smashFreeBool_algChOf` —
  what `Geb.CobhamFold.algChOf` computes, and that it carries no `smash`.

## Implementation notes

`algCh` does not meet the per-symbol growth condition
`Geb.CobhamFold.stackSize_le_of_growth` consumes, and not because
`dropEntrySem` fails to shrink — `length_dropEntrySem_le` bounds its result
by its argument. It duplicates its children's payloads, delimited and plain,
so its length is bounded by a multiple of the children's total rather than by
that total plus a constant. A multiplicative condition alone would not give
the linearity hypothesis either, a fold whose values multiply at every level
being exponential in depth. The route taken instead is
`five_mul_length_dropEntrySem_algCh_le`, a property of the algebra's own
outputs that needs no induction hypothesis,
carried along the scan by `mem_stack_foldScanFinal` and consumed by a
potential argument in the shape
`Geb.CobhamFold.potential_foldScanStep_le`'s.

`Variable.lean` states the potential chain at a growth condition restricted
to values satisfying a predicate the scan's stack carries, and derives the
unrestricted forms from it at the trivial predicate. The restriction is what
`algCh` needs and what the unrestricted condition does not give.

## References

* [Cobham1965]
* [Meertens1992]
* [Strahm2003]

## Tags

Cobham, ranked tree, destructor, self-delimiting, subterm, paramorphism,
smash-free
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

/-- The per-symbol growth the delimited-children algebra meets under its own
invariant, attained at a symbol of maximum arity whose children are all
nullary. -/
def chGrowth (R : RankedAlphabet) : ℕ :=
  4 * R.maxArity * R.width + R.maxArity + R.width + 1

/-- The children's second halves, bounded by their own lengths under the
invariant, over a list rather than a family. -/
private theorem five_mul_length_flatten_dropEntrySem_le (R : RankedAlphabet) :
    ∀ l : List (List Bool),
      (∀ x ∈ l, 5 * (dropEntrySem ![x]).length + 1 ≤ x.length + 4 * R.width) →
      5 * ((l.map fun x ↦ dropEntrySem ![x]).flatten).length + l.length ≤
        l.flatten.length + 4 * R.width * l.length :=
  List.rec (fun _ ↦ Nat.le_refl 0) fun a t ih h ↦ by
    have ha := h a List.mem_cons_self
    have ht := ih fun x hx ↦ h x (List.mem_cons_of_mem a hx)
    -- `omega` atomises `4 * R.width * (t.length + 1)` and
    -- `4 * R.width * t.length` separately, so the step is supplied by hand.
    have hd : 4 * R.width * (t.length + 1) = 4 * R.width * t.length + 4 * R.width := by
      rw [Nat.mul_add, Nat.mul_one]
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons]
    omega

/-- The delimited-children algebra lengthens by at most `chGrowth R` per
symbol, at arguments satisfying the invariant its own outputs satisfy. It
does not meet the condition at arbitrary arguments: it duplicates its
children's payloads, delimited and plain. -/
theorem growth_algCh_of_dropEntrySem_le (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool)
    (hf : ∀ d, 5 * (dropEntrySem ![f d]).length + 1 ≤
      (f d).length + 4 * R.width) :
    (algCh R i f).length ≤
      (List.ofFn fun d ↦ (f d).length).sum + chGrowth R := by
  have hlist := five_mul_length_flatten_dropEntrySem_le R (List.ofFn f)
    (fun x hx ↦ by
      obtain ⟨d, hd⟩ := List.mem_ofFn.mp hx
      exact hd ▸ hf d)
  have harity : R.arity i ≤ R.maxArity := R.arity_le_maxArity i
  -- `omega` is linear: it atomises `4 * R.width * R.arity i` and
  -- `4 * R.maxArity * R.width` separately and has no rule taking
  -- `R.arity i ≤ R.maxArity` from one to the other, so the monotonicity and
  -- the commutation are supplied by hand.
  have hmono : 4 * R.width * R.arity i ≤ 4 * R.width * R.maxArity :=
    Nat.mul_le_mul_left _ harity
  have hcomm : 4 * R.width * R.maxArity = 4 * R.maxArity * R.width := by
    rw [Nat.mul_assoc, Nat.mul_comm R.width, ← Nat.mul_assoc]
  rw [length_algCh, chGrowth, sum_ofFn_length_eq_length_flatten]
  simp only [List.map_ofFn, Function.comp_def, List.length_ofFn] at hlist ⊢
  omega

/-- The pending values stay linear in the input at the delimited-children
algebra, which is the hypothesis `Geb.CobhamFold.foldOutOfV` takes. The
per-symbol growth condition does not apply, so the bound runs through the
invariant `five_mul_length_dropEntrySem_algCh_le` and a potential argument
over it, which charges each input bit at most `chGrowth R` and so needs no
assumption about how the pending subterms are laid out. -/
theorem stackSize_algCh_le (R : RankedAlphabet) (w : List Bool) :
    stackSize (foldScanFinal R (algCh R) w).stack ≤ chGrowth R * w.length :=
  stackSize_le_of_growth_of_invariant R (algCh R)
    (fun v ↦ 5 * (dropEntrySem ![v]).length + 1 ≤ v.length + 4 * R.width)
    (chGrowth R) (five_mul_length_dropEntrySem_algCh_le R) (growth_algCh_of_dropEntrySem_le R) w

/-- The delimited-children algebra as an expression of Cobham's class. Each
slot contributes its own second half, plain in the first argument and
delimited in the second; `Geb.CobhamFold.flattenOf` concatenates a family
through `Geb.CobhamFold.compOf`, so no new combinator is introduced. -/
def algChOf (R : RankedAlphabet) (i : Fin R.card) : COf (R.arity i) :=
  concatCompOf (R.arity i)
    (prependOf (R.code i)
      (compOf (flattenOf (R.arity i)) fun d ↦
        comp1Of dropEntryOf (projOf (R.arity i) d)))
    (comp1Of entryWordOf
      (compOf (flattenOf (R.arity i)) fun d ↦
        comp1Of entryWordOf (comp1Of dropEntryOf (projOf (R.arity i) d))))

/-- The expression computes the algebra. -/
theorem semAt_algChOf (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    semAt (R.arity i) (algChOf R i).1.1 (algChOf R i).2 f = algCh R i f := by
  rw [algChOf, semAt_concatCompOf, semAt_prependOf, semAt_comp1Of,
    semAt_compOf, semAt_compOf, semAt_flattenOf, semAt_flattenOf, algCh,
    algPara]
  simp only [semAt_comp1Of, semAt_projOf, stepWord_dropEntryOf,
    stepWord_entryWordOf]

/-- The expression carries no `smash`, which is
`Geb.CobhamFold.smashFree_foldOutExprV`'s hypothesis at this algebra. -/
theorem smashFreeBool_algChOf (R : RankedAlphabet) (i : Fin R.card) :
    smashFreeBool (algChOf R i).1.1.1 = true :=
  smashFreeBool_concatCompOf (R.arity i) _ _
    (smashFreeBool_prependOf _ _
      (smashFreeBool_compOf _ _ (smashFreeBool_flattenOf (R.arity i))
        fun d ↦ smashFreeBool_comp1Of _ _ smashFreeBool_dropEntryOf
          (smashFreeBool_projOf (R.arity i) d)))
    (smashFreeBool_comp1Of _ _ smashFreeBool_entryWordOf
      (smashFreeBool_compOf _ _ (smashFreeBool_flattenOf (R.arity i))
        fun d ↦ smashFreeBool_comp1Of _ _ smashFreeBool_entryWordOf
          (smashFreeBool_comp1Of _ _ smashFreeBool_dropEntryOf
            (smashFreeBool_projOf (R.arity i) d))))

end Geb.CobhamFold

end
