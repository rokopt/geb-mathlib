/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Steps
public import Geb.Prototypes.Computability.BitTree.Counter

set_option doc.verso true

/-!
# Binary carry execution

An initial sequence of one-bits is reset while both binary heads advance. The first zero-bit
ends the carry after being set to one. The statements here follow the actual machine steps.

## Main statements

* {lit}`configs_carry_prefix` describes every intermediate carry configuration.
* {lit}`configs_carry_bits` identifies the terminal counter with binary-list increment.
* {lit}`configs_carry_bits_pos` gives both binary head positions throughout the carry.

## Implementation notes

The module relates list-level increment to CSLib's configuration sequence. Its machine
statements inherit the axioms of CSLib's input-symbol access through the step function.

## Tags

Turing machine, binary counter, carry propagation
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- Resetting an initial sequence of ones preserves the carry state and advances both heads. -/
theorem configs_carry_prefix {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (p k : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = p) (hp1 : cfg.workTapePos 1 = p)
    (hones : ∀ j < k, digits cfg (if leaf then 1 else 0) (p + j) = true)
    (t : ℕ) (ht : t ≤ k) :
    let now := machine.configs cfg t
    now.state = some (if leaf then stCarryLeaf else stCarryFork) ∧
    now.workTapePos 0 = (p + t : ℕ) ∧ now.workTapePos 1 = (p + t : ℕ) ∧
    now.inputPos = cfg.inputPos ∧
    digits now (if leaf then 1 else 0) =
      (fun j ↦ if p ≤ j ∧ j < p + t then false else digits cfg (if leaf then 1 else 0) j) ∧
    digits now (if leaf then 0 else 1) = digits cfg (if leaf then 0 else 1) := by
  revert ht
  apply Nat.rec (motive := fun t ↦ t ≤ k →
    let now := machine.configs cfg t
    now.state = some (if leaf then stCarryLeaf else stCarryFork) ∧
    now.workTapePos 0 = (p + t : ℕ) ∧ now.workTapePos 1 = (p + t : ℕ) ∧
    now.inputPos = cfg.inputPos ∧
    digits now (if leaf then 1 else 0) =
      (fun j ↦ if p ≤ j ∧ j < p + t then false else digits cfg (if leaf then 1 else 0) j) ∧
    digits now (if leaf then 0 else 1) = digits cfg (if leaf then 0 else 1)) ?_ ?_ t
  · intro _
    refine ⟨hq, hp0, hp1, rfl, ?_, rfl⟩
    funext j
    have hj : ¬(p ≤ j ∧ j < p + 0) := by omega
    simp only [configs_zero, hj, ↓reduceIte]
  · intro t ih ht
    obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother⟩ := ih (by omega)
    let now := machine.configs cfg t
    have hp : now.workTapePos (if leaf then 1 else 0) = (p + t : ℕ) := by
      cases leaf
      · exact hpos0
      · exact hpos1
    have hone := hones t (by omega)
    have hd : digit (now.workTapeSymbols (if leaf then 1 else 0)) = true := by
      change digit (now.workTapes (if leaf then 1 else 0)
        (now.workTapePos (if leaf then 1 else 0))) = true
      rw [hp]
      change digits now (if leaf then 1 else 0) (p + t) = true
      rw [hselected]
      simp only [Nat.lt_irrefl, and_false, ↓reduceIte]
      exact hone
    rw [configs_succ_eq_step']
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [step_carry_state now leaf hstate, hd]
      rfl
    · rw [step_carry_binaryPos now leaf 0 (by decide) hstate, hpos0]
      simp [Int.add_assoc]
    · rw [step_carry_binaryPos now leaf 1 (by decide) hstate, hpos1]
      simp [Int.add_assoc]
    · rw [step_carry_inputPos now leaf hstate, hin]
    · rw [step_carry_digits now leaf (p + t) hstate hp, hselected]
      funext j
      by_cases hj : j = p + t
      · subst j
        simp [Function.update_self, hone]
      · rw [Function.update_of_ne hj]
        have he : (p ≤ j ∧ j < p + t) ↔ (p ≤ j ∧ j < p + (t + 1)) := by omega
        simp only [he]
    · rw [step_carry_other_digits now leaf hstate, hother]

/-- The first zero ends carry propagation after being changed to one. -/
theorem configs_carry_terminal {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (p k : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = p) (hp1 : cfg.workTapePos 1 = p)
    (hones : ∀ j < k, digits cfg (if leaf then 1 else 0) (p + j) = true)
    (hzero : digits cfg (if leaf then 1 else 0) (p + k) = false) :
    let now := machine.configs cfg (k + 1)
    now.state = some stReturn ∧
    now.workTapePos 0 = (p + (k + 1) : ℕ) ∧
    now.workTapePos 1 = (p + (k + 1) : ℕ) ∧ now.inputPos = cfg.inputPos ∧
    digits now (if leaf then 1 else 0) =
      (fun j ↦ if j = p + k then true else
        if p ≤ j ∧ j < p + k then false else digits cfg (if leaf then 1 else 0) j) ∧
    digits now (if leaf then 0 else 1) = digits cfg (if leaf then 0 else 1) := by
  obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother⟩ :=
    configs_carry_prefix cfg leaf p k hq hp0 hp1 hones k (Nat.le_refl _)
  let now := machine.configs cfg k
  have hp : now.workTapePos (if leaf then 1 else 0) = (p + k : ℕ) := by
    cases leaf
    · exact hpos0
    · exact hpos1
  have hd : digit (now.workTapeSymbols (if leaf then 1 else 0)) = false := by
    change digit (now.workTapes (if leaf then 1 else 0)
      (now.workTapePos (if leaf then 1 else 0))) = false
    rw [hp]
    change digits now (if leaf then 1 else 0) (p + k) = false
    rw [hselected]
    simp only [Nat.lt_irrefl, and_false, ↓reduceIte]
    exact hzero
  rw [configs_succ_eq_step']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [step_carry_state now leaf hstate, hd]
    rfl
  · rw [step_carry_binaryPos now leaf 0 (by decide) hstate, hpos0]
    simp [Int.add_assoc]
  · rw [step_carry_binaryPos now leaf 1 (by decide) hstate, hpos1]
    simp [Int.add_assoc]
  · rw [step_carry_inputPos now leaf hstate, hin]
  · rw [step_carry_digits now leaf (p + k) hstate hp, hselected]
    funext j
    by_cases hj : j = p + k
    · subst j
      simp [Function.update_self, hzero]
    · simp only [Function.update_of_ne hj, hj, ↓reduceIte]
  · rw [step_carry_other_digits now leaf hstate, hother]

/-- Carry propagation emits nothing, including the step that ends the carry. -/
theorem outputString_carry {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (p k : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = p) (hp1 : cfg.workTapePos 1 = p)
    (hones : ∀ j < k, digits cfg (if leaf then 1 else 0) (p + j) = true) :
    machine.outputString cfg (k + 1) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro t ht
  have hq' := (configs_carry_prefix cfg leaf p k hq hp0 hp1 hones t
    (by have h := List.mem_range.mp ht; omega)).1
  rw [outputSymbol_carry _ leaf hq']
  rfl

/-- Carry from the origin implements binary-list increment in exactly its bit-change count. -/
theorem configs_carry_bits {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (bs : List Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = 0) (hp1 : cfg.workTapePos 1 = 0)
    (hbits : ∀ j, digits cfg (if leaf then 1 else 0) j = bs[j]?.getD false) :
    let now := machine.configs cfg (Counter.flips bs)
    now.state = some stReturn ∧
    now.workTapePos 0 = Counter.flips bs ∧ now.workTapePos 1 = Counter.flips bs ∧
    now.inputPos = cfg.inputPos ∧
    digits now (if leaf then 1 else 0) = (fun j ↦ (Counter.increment bs)[j]?.getD false) ∧
    digits now (if leaf then 0 else 1) = digits cfg (if leaf then 0 else 1) ∧
    machine.outputString cfg (Counter.flips bs) = [] := by
  have hf := Counter.flips_pos bs
  have he : Counter.flips bs - 1 + 1 = Counter.flips bs := by omega
  have hones : ∀ j < Counter.flips bs - 1,
      digits cfg (if leaf then 1 else 0) (0 + j) = true := by
    intro j hj
    rw [Nat.zero_add, hbits]
    exact Counter.getD_eq_true_of_lt_flips bs j (by omega)
  have hzero : digits cfg (if leaf then 1 else 0) (0 + (Counter.flips bs - 1)) = false := by
    rw [Nat.zero_add, hbits]
    exact Counter.getD_last_flip bs
  have hterm := configs_carry_terminal cfg leaf 0 (Counter.flips bs - 1)
    hq hp0 hp1 hones hzero
  simp only [he, Nat.zero_add, Nat.zero_le, true_and] at hterm
  obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother⟩ := hterm
  refine ⟨hstate, hpos0, hpos1, hin, ?_, hother, ?_⟩
  · funext j
    rw [hselected, Counter.getD_increment]
    dsimp only
    rw [hbits]
    split_ifs <;> first | rfl | omega
  · have hout := outputString_carry cfg leaf 0 (Counter.flips bs - 1) hq hp0 hp1 hones
    simpa only [he] using hout

/-- Every configuration before the final carry step remains in the carry state. -/
theorem configs_carry_bits_state {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (bs : List Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = 0) (hp1 : cfg.workTapePos 1 = 0)
    (hbits : ∀ j, digits cfg (if leaf then 1 else 0) j = bs[j]?.getD false)
    (t : ℕ) (ht : t < Counter.flips bs) :
    (machine.configs cfg t).state = some (if leaf then stCarryLeaf else stCarryFork) ∧
    (machine.configs cfg t).workTapePos 0 = t ∧
    (machine.configs cfg t).workTapePos 1 = t := by
  have hones : ∀ j < Counter.flips bs - 1,
      digits cfg (if leaf then 1 else 0) (0 + j) = true := by
    intro j hj
    rw [Nat.zero_add, hbits]
    exact Counter.getD_eq_true_of_lt_flips bs j (by omega)
  have h := configs_carry_prefix cfg leaf 0 (Counter.flips bs - 1) hq hp0 hp1 hones t
    (by omega)
  exact ⟨h.1, by simpa only [Nat.zero_add] using h.2.1,
    by simpa only [Nat.zero_add] using h.2.2.1⟩

/-- The binary heads equal elapsed time throughout a carry, including its terminal state. -/
theorem configs_carry_bits_pos {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (bs : List Bool)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = 0) (hp1 : cfg.workTapePos 1 = 0)
    (hbits : ∀ j, digits cfg (if leaf then 1 else 0) j = bs[j]?.getD false)
    (t : ℕ) (ht : t ≤ Counter.flips bs) :
    (machine.configs cfg t).workTapePos 0 = t ∧
    (machine.configs cfg t).workTapePos 1 = t := by
  by_cases he : t = Counter.flips bs
  · subst t
    have h := configs_carry_bits cfg leaf bs hq hp0 hp1 hbits
    exact ⟨h.2.1, h.2.2.1⟩
  · exact (configs_carry_bits_state cfg leaf bs hq hp0 hp1 hbits t (by omega)).2

end Geb.BitTree.BinaryMachine
