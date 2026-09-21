/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Primitives.Copy
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Inc
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.While
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Inv

set_option doc.verso true in
/-!
# Arithmetic on word indices

Word indices are binary counters bounded by virtual word lengths. Addition can
consume one counter while incrementing another, reusing the existing increment,
decrement, and loop programs. All intermediate sums are bounded by the final sum.

## Main definitions

* {lit}`addCounter` adds and consumes a binary counter.
* {lit}`subCounter` subtracts and consumes a binary counter, saturating at zero.
* {lit}`minCounter` clamps a counter to a saved bound using two saturated subtractions.

## Main statements

* {lit}`addCounter_transformsIn` proves addition, termination, caller preservation,
  and a bound throughout the loop.
* {lit}`subCounter_transformsIn` proves saturating subtraction at the original bound.

## Implementation notes

The loop uses one iteration per unit of the consumed counter. Its termination
bound is sufficient for the configuration-counting time theorem. The contracts
inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, binary counter, addition
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Add the second counter to the first, consuming the second counter. -/
@[expose] def addCounter {k : ℕ} (A C : Fin k) :=
  whileNonblank (some C) (seq (inc A) (dec C))

/-- Addition uses only the final sum's binary size and leaves its second counter blank. -/
theorem addCounter_transformsIn {k : ℕ} (A C : Fin k) (hAC : A ≠ C) (N B : ℕ → ℕ) :
    TransformsIn (addCounter A C)
      (fun input σ ↦ ∃ a c, σ A = counterWord a ∧ σ C = counterWord c ∧
        c ≤ N input.length ∧ (a + c).size ≤ B input.length)
      (fun _ σ ↦ Function.update (Function.update σ A
        (counterWord (counterValue (σ A) + counterValue (σ C)))) C [])
      (fun n ↦ N n * (4 * B n + 11) + 1) B := by
  intro input cfg σ hq hpark _ hσ hpre hB
  obtain ⟨a, c, hA, hC, hcN, hac⟩ := hpre
  let v (j : ℕ) := Function.update (Function.update σ A (counterWord (a + j)))
    C (counterWord (c - j))
  let f (j : ℕ) : Cfg k Bool (StateOf (seq (inc A) (dec C))) input :=
    { cfg with state := none, workTapes := fun i ↦ tapeOf (v j i) }
  have hb (j : ℕ) (hj : j ≤ c) : Bounded (v j) (B input.length) :=
    (hB.update (by
      rw [length_counterWord]
      exact (size_le_size (by omega : a + j ≤ a + c)).trans hac)).update
      ((length_counterWord_le_of_le (Nat.sub_le c j)).trans (hC ▸ hB C))
  have hvA (j : ℕ) : v j A = counterWord (a + j) := by
    simp [v, Function.update_of_ne hAC]
  have hvC (j : ℕ) : v j C = counterWord (c - j) := Function.update_self ..
  have hprobe (j : ℕ) : probeOf (some C) (f j) = tapeOf (counterWord (c - j)) 0 := by
    change tapeOf (v j C) (cfg.workTapePos C) = _
    rw [hvC, hpark C]
  have hheads (i : Fin k) :
      -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    rw [hpark i]
    constructor <;> omega
  obtain ⟨t, ht, hr⟩ := RunsTo.whileNonblank (some C) (seq (inc A) (dec C))
    (B input.length) (4 * B input.length + 10) c f
    (by
      intro j hj hz
      rw [hprobe] at hz
      have := (counterWord_eq_nil_iff _).mp ((tapeOf_zero_eq_none_iff _).mp hz)
      omega)
    (by rw [hprobe, Nat.sub_self]; rfl)
    (by
      intro j hj
      let u := Function.update (v j) A (counterWord (a + j + 1))
      have huB : Bounded u (B input.length) := (hb j (by omega)).update (by
        rw [length_counterWord]
        exact (size_le_size (by omega : a + j + 1 ≤ a + c)).trans hac)
      obtain ⟨s, hs, ri⟩ := inc_transforms A (B input.length)
        { f j with state := some (inc A).q₀ } (v j) rfl hpark (fun _ ↦ rfl)
        (hb j (by omega)) (by dsimp only; rw [hvA, incL_counterWord]; exact huB)
      dsimp only at ri
      rw [hvA, incL_counterWord] at ri
      have huC : u C = counterWord (c - j) := by
        simp only [u, Function.update_of_ne hAC.symm, hvC]
      have hv : Function.update u C (decL (u C).reverse).reverse = v (j + 1) := by
        rw [huC, show c - j = (c - (j + 1)) + 1 from by omega, decL_counterWord_succ]
        dsimp only [u, v]
        rw [Function.update_comm hAC, Function.update_idem, Function.update_comm hAC.symm,
          Function.update_idem, Nat.add_assoc]
      obtain ⟨s', hs', rd⟩ := dec_transforms C (B input.length)
        { after (f j) u with state := some (dec C).q₀ } u rfl hpark (fun _ ↦ rfl)
        huB (by dsimp only; rw [hv]; exact hb (j + 1) (by omega))
      dsimp only at rd
      rw [hv] at rd
      have r := RunsTo.seqStart
        (cfg := { f j with state := some (seq (inc A) (dec C)).q₀ }) rfl ri rd
      refine ⟨s + s', by omega, r.congr_target ?_⟩
      rfl)
    hheads
  have hv0 : v 0 = σ := by
    dsimp only [v]
    rw [Nat.add_zero, Nat.sub_zero, ← hA, Function.update_eq_self,
      ← hC, Function.update_eq_self]
  have hstart : { f 0 with state := some (.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      change tapeOf (v 0 i) = cfg.workTapes i
      rw [hv0, hσ i]
    · rfl
    · rfl
  rw [hstart] at hr
  dsimp only
  rw [hA, hC, counterValue_counterWord, counterValue_counterWord]
  have hend : v c = Function.update (Function.update σ A (counterWord (a + c))) C [] := by
    simp only [v, Nat.sub_self, show counterWord 0 = [] from rfl]
  refine ⟨hend ▸ hb c le_rfl, t, ht.trans ?_, ?_⟩
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hcN) 1
  · simpa only [addCounter, f, after, hend] using hr

/-- Decrementing a canonical counter saturates at zero. -/
theorem decL_counterWord (n : ℕ) :
    (decL (counterWord n).reverse).reverse = counterWord (n - 1) := by
  cases n with
  | zero => rfl
  | succ n => simpa only [Nat.add_sub_cancel] using decL_counterWord_succ n

/-- Subtract the second counter from the first, saturating at zero and consuming the second. -/
@[expose] def subCounter {k : ℕ} (A C : Fin k) :=
  whileNonblank (some C) (seq (dec A) (dec C))

/-- Saturating subtraction preserves the original register bound throughout the loop. -/
theorem subCounter_transformsIn {k : ℕ} (A C : Fin k) (hAC : A ≠ C) (N B : ℕ → ℕ) :
    TransformsIn (subCounter A C)
      (fun input σ ↦ ∃ a c, σ A = counterWord a ∧ σ C = counterWord c ∧ c ≤ N input.length)
      (fun _ σ ↦ Function.update (Function.update σ A
        (counterWord (counterValue (σ A) - counterValue (σ C)))) C [])
      (fun n ↦ N n * (4 * B n + 13) + 1) B := by
  let F := fun (σ : Fin k → List Bool) ↦
    Function.update (Function.update σ A (decL (σ A).reverse).reverse)
      C (decL (σ C).reverse).reverse
  have hd (i : Fin k) := Transforms.toIn_of (fun n ↦ dec_transforms i (B n))
    (fun _ _ ↦ True) (fun _ σ hB _ ↦ hB.update (by
      rw [List.length_reverse]
      exact (length_decL_le _).trans (by simpa only [List.length_reverse] using hB i)))
  have hp : TransformsIn (seq (dec A) (dec C)) (fun _ _ ↦ True) (fun _ ↦ F)
      (fun n ↦ 4 * B n + 12) B := by
    refine ((((hd A).seq (hd C)).mono_pre
      (fun _ _ _ _ ↦ ⟨trivial, trivial⟩)).mono_time ?_).congr ?_
    · intro n
      omega
    · intro input σ _
      dsimp only [F]
      rw [Function.update_of_ne hAC.symm]
  have hiter (σ : Fin k → List Bool) (a c : ℕ) (hA : σ A = counterWord a)
      (hC : σ C = counterWord c) (j : ℕ) :
      F^[j] σ = Function.update (Function.update σ A (counterWord (a - j)))
        C (counterWord (c - j)) := by
    refine Nat.rec ?_ (fun j ih ↦ ?_) j
    · simp only [Function.iterate_zero_apply, Nat.sub_zero, ← hA, Function.update_eq_self,
        ← hC]
    · rw [Function.iterate_succ_apply', ih]
      dsimp only [F]
      rw [Function.update_of_ne hAC, Function.update_self, Function.update_self,
        decL_counterWord, decL_counterWord, Nat.sub_sub, Nat.sub_sub,
        Function.update_comm hAC, Function.update_idem, Function.update_comm hAC.symm,
        Function.update_idem]
  have hw := TransformsIn.whileReg C hp
    (fun input σ ↦ ∃ a c, σ A = counterWord a ∧ σ C = counterWord c ∧ c ≤ N input.length)
    (fun _ σ ↦ counterValue (σ C)) N
    (by intro input σ ⟨a, c, hA, hC, hc⟩; simpa only [hC, counterValue_counterWord] using hc)
    (by
      intro input σ ⟨a, c, hA, hC, hc⟩ j hj
      simp only [hC, counterValue_counterWord] at hj
      refine ⟨?_, trivial⟩
      rw [hiter σ a c hA hC, Function.update_self]
      exact fun hz ↦ (by omega : c - j ≠ 0) ((counterWord_eq_nil_iff _).mp hz))
    (by
      intro input σ ⟨a, c, hA, hC, _⟩
      rw [hC, counterValue_counterWord, hiter σ a c hA hC, Function.update_self, Nat.sub_self]
      rfl)
  refine hw.congr ?_
  intro input σ ⟨a, c, hA, hC, _⟩
  rw [hC, counterValue_counterWord, hiter σ a c hA hC, hA, counterValue_counterWord,
    Nat.sub_self]
  rfl

/-- Clamp a counter to a saved upper bound, using one temporary register.
The bound survives and the temporary register is cleared. -/
@[expose] def minCounter {k : ℕ} (A L D : Fin k) :=
  seq (seq (copy L D) (subCounter D A)) (seq (copy L A) (subCounter A D))

/-- Two saturated subtractions compute a minimum without growing either counter. -/
theorem minCounter_transformsIn {k : ℕ} (A L D : Fin k)
    (hAL : A ≠ L) (hAD : A ≠ D) (hLD : L ≠ D) (N B : ℕ → ℕ) :
    TransformsIn (minCounter A L D)
      (fun input σ ↦ ∃ a l, σ A = counterWord a ∧ σ L = counterWord l ∧
        a ≤ N input.length ∧ l ≤ N input.length)
      (fun _ σ ↦ Function.update (Function.update σ A
        (counterWord (min (counterValue (σ A)) (counterValue (σ L))))) D [])
      (fun n ↦ 2 * ((5 * B n + 12) + (N n * (4 * B n + 13) + 1))) B := by
  have hc (R : Fin k) (hLR : L ≠ R) :=
    Transforms.toIn_of (fun n ↦ copy_transforms L R hLR (B n))
      (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (hB L))
  have h := ((hc D hLD).seq (subCounter_transformsIn D A hAD.symm N B)).seq
    ((hc A hAL.symm).seq (subCounter_transformsIn A D hAD N B))
  have hs := h.mono_pre (Pre' := fun input σ ↦
    ∃ a l, σ A = counterWord a ∧ σ L = counterWord l ∧
      a ≤ N input.length ∧ l ≤ N input.length) (by
    intro input σ _ hp
    obtain ⟨a, l, ha, hl, han, hln⟩ := hp
    refine ⟨⟨trivial, l, a, ?_, ?_, han⟩, trivial, l, l - a, ?_, ?_, ?_⟩
    · simp [hl]
    · simp [hAD, ha]
    · simp [hAL.symm, hLD, hl]
    · simp [hAD, hAD.symm, ha, hl, counterValue_counterWord]
    · omega)
  refine (hs.congr ?_).mono_time (fun n ↦ by omega)
  intro input σ hp
  obtain ⟨a, l, ha, hl, _⟩ := hp
  have he : l - (l - a) = min a l := by omega
  funext i
  by_cases hiA : i = A
  · subst i
    simp [hAD, hAD.symm, hAL.symm, hLD, ha, hl, counterValue_counterWord, he]
  · by_cases hiD : i = D
    · subst i
      simp
    · simp [Function.update_of_ne hiA, Function.update_of_ne hiD]

end

end Geb.Oitavem.Machine
