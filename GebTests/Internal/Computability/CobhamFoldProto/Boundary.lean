/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.Computability.CobhamFoldProto
public import Geb.Mathlib.Data.W.Basic
public meta import Geb.Internal.Computability.CobhamFoldProto  -- shake: keep; #guard needs it

/-!
# The term algebra's operations, at the semantic layer

The initial algebra's structure map transported along `RankedAlphabet.spell`,
and the algebra from which a subterm's spelling is recovered.

`algMk` is that structure map at the carrier `List Bool`: `Term.fold` at it is
`RankedAlphabet.spell` itself, so the preorder encoding is the unique morphism
from the term algebra into `algMk` rather than a construction beside it.

`algPara` carries a subterm's spelling beside the step's value, the value
delimited so the two are separable. The delimiting does not nest: each level
reads only the spelling half of a child's value, so a subterm's boundary is
reached by a fold. `algCh` is the instance whose step returns the children's
spellings, each delimited. Read through its take-half the fold is
`WType.para`, so the recursion scheme is [Meertens1992]'s, computed at the
bitstring representation rather than introduced here.

## Main definitions

* `GebTests.CobhamFold.algMk` — the initial algebra's structure map.
* `GebTests.CobhamFold.ParaStep`, `GebTests.CobhamFold.algPara` — the
  paramorphism's step, and the paramorphism as a fold.
* `GebTests.CobhamFold.algCh` — the delimited-children algebra, one of its
  instances.
* `GebTests.CobhamFold.childSem` — a child's spelling, from a fold's value.
* `GebTests.CobhamFold.destSample`, `GebTests.CobhamFold.valueBounded` — the
  sample term whose children differ, and the length bound read at it.

## Main statements

* `GebTests.CobhamFold.fold_algMk` — the fold at `algMk` is the spelling.
* `GebTests.CobhamFold.length_algMk` — it lengthens by the alphabet's width.
* `GebTests.CobhamFold.foldOut_algMk` — the fold at `algMk` is the identity on
  the recognized language.
* `GebTests.CobhamFold.dropEntry_algPara` — the value's second half is the
  spelling, whatever the step.
* `GebTests.CobhamFold.takeEntry_algPara` — the paramorphism's defining
  equation.
* `GebTests.CobhamFold.algPara_eq_para` — it is `WType.para` at the step that
  sees each child's spelling.
* `GebTests.CobhamFold.two_mul_length_takeEntrySem_add_length_dropEntrySem_le`
  — the payload counted twice and the remainder fit inside the word.
* `GebTests.CobhamFold.dropEntry_algCh`, `GebTests.CobhamFold.takeEntry_algCh`
  — those two at the delimited-children instance.

## References

* [GambinoHyland2004]
* [Meertens1992]

## Tags

Cobham, ranked tree, initial algebra, subterm, paramorphism, self-delimiting
-/

@[expose] public section

namespace GebTests.CobhamFold

open Cobham Geb.CobhamFold RankedAlphabet RankedAlphabet.Binary

/-- The initial algebra's structure map, at the carrier `List Bool`: a
symbol's block followed by its children's spellings. -/
def algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) : List Bool :=
  R.code i ++ (List.ofFn f).flatten

/-- The fold at that map is the preorder encoding, so `RankedAlphabet.spell`
is the unique morphism from the term algebra into it, by the initiality
`Geb.CobhamFold.Term.fold_unique` carries [GambinoHyland2004]. -/
theorem fold_algMk (R : RankedAlphabet) : Term.fold R (algMk R) = R.spell := rfl

/-- It lengthens its arguments' total by exactly the alphabet's width. -/
theorem length_algMk (R : RankedAlphabet) (i : Fin R.card)
    (f : Fin (R.arity i) → List Bool) :
    (algMk R i f).length = (List.ofFn fun d ↦ (f d).length).sum + R.width := by
  rw [algMk, List.length_append, R.length_code, List.length_flatten,
    List.map_ofFn]
  exact Nat.add_comm _ _

/-- The fold at that map is the identity on the recognized language. -/
theorem foldOut_algMk (R : RankedAlphabet) (w : List Bool) :
    foldOut R (algMk R) w = (R.parse w).map (fun _ ↦ w) := by
  rw [foldOut_eq]
  cases h : R.parse w with
  | none => rfl
  | some t => exact congrArg some (R.parse_eq_some_iff.mp h)

/-- The payload and the remainder together fit inside the word, the payload
counted twice: a `true` lengthens the payload by at most one bit while the
remainder loses one, so the weighted total does not grow. This is what bounds
a general paramorphism step's contribution; `Geb.CobhamFold.SelfDelim` has the
two halves separately. -/
theorem two_mul_length_takeEntrySem_add_length_dropEntrySem_le :
    ∀ w : List Bool,
      2 * (takeEntrySem ![w]).length + (dropEntrySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [takeEntrySem_cons, dropEntrySem_cons, List.length_cons]
    cases b
    · rw [ite_eq_right (by simp), ite_eq_right (by simp), List.length_nil]
      omega
    · rw [ite_eq_left rfl, ite_eq_left rfl, List.length_append, List.length_tail,
        firstBitSem_eq]
      match hd : dropEntrySem ![v] with
      | [] =>
        rw [hd] at ih
        simp only [List.length_nil]
        omega
      | c :: t =>
        rw [hd, List.length_cons] at ih
        simp only [List.length_cons, List.length_nil]
        omega

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
scheme is the existing one, computed at the bitstring representation. -/
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

/-- The `j`-th child's spelling, read from a term's fold value. -/
def childSem (R : RankedAlphabet) (j : ℕ) (t : R.Term) : List Bool :=
  stepWord (entryOf j) (takeEntrySem ![Term.fold R (algCh R) t])

/-- A sample term whose two children differ. -/
def destSample : binRanked.Term := node leaf (node leaf leaf)

#guard binRanked.spell destSample = [true, false, true, false, false]
#guard childSem binRanked 0 destSample = [false]
#guard childSem binRanked 1 destSample = [true, false, false]

/-- At `binRanked`, the fold's value stays within six times the term's node
count. The factor is this alphabet's; no general bound is proved here. -/
def valueBounded (t : binRanked.Term) : Bool :=
  (Term.fold binRanked (algCh binRanked) t).length ≤ 6 * t.size

#guard valueBounded leaf
#guard valueBounded (node leaf leaf)
#guard valueBounded destSample
#guard valueBounded (node (node leaf leaf) (node leaf leaf))

end GebTests.CobhamFold
