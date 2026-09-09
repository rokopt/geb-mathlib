/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Carry
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Return
public import Geb.Prototypes.Computability.BitTree.BinaryMachine.Representation

set_option doc.verso true

/-!
# Complete counter increments

A carry followed by the return is one counter increment. The marker and
mismatch invariants connect its final state to equality of the represented
counter values.

## Main statements

* {lit}`configs_carry_invariants` maintains marker and mismatch invariants.
* {lit}`configs_increment` implements one increment in twice its bit-change count plus one step.
* {lit}`configs_increment_head_bounds` bounds every visited work-tape position.

## Tags

Turing machine, simulation, binary counter
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- The marker and mismatch invariants survive every carry prefix, including its last step. -/
theorem configs_carry_invariants {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (p k width : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = p) (hp1 : cfg.workTapePos 1 = p)
    (hones : ∀ j < k, digits cfg (if leaf then 1 else 0) (p + j) = true)
    (hw : p + k < width)
    (hm : cfg.workTapePos 2 = (mismatchCount width (digits cfg 0) (digits cfg 1) : ℤ))
    (t : ℕ) (ht : t ≤ k + 1) :
    let now := machine.configs cfg t
    (∀ z, origin (now.workTapes 0 z) = origin (cfg.workTapes 0 z)) ∧
    now.workTapes 2 = cfg.workTapes 2 ∧
    now.workTapePos 2 = (mismatchCount width (digits now 0) (digits now 1) : ℤ) := by
  revert ht
  apply Nat.rec (motive := fun t ↦ t ≤ k + 1 →
    let now := machine.configs cfg t
    (∀ z, origin (now.workTapes 0 z) = origin (cfg.workTapes 0 z)) ∧
    now.workTapes 2 = cfg.workTapes 2 ∧
    now.workTapePos 2 = (mismatchCount width (digits now 0) (digits now 1) : ℤ)) ?_ ?_ t
  · intro _
    exact ⟨fun _ ↦ rfl, rfl, hm⟩
  · intro t ih ht
    obtain ⟨ho, hmark, hmismatch⟩ := ih (by omega)
    obtain ⟨hstate, hpos0, hpos1, _⟩ :=
      configs_carry_prefix cfg leaf p k hq hp0 hp1 hones t (by omega)
    rw [configs_succ_eq_step']
    refine ⟨?_, ?_, ?_⟩
    · intro z
      rw [step_carry_origin _ leaf z hstate, ho]
    · rw [step_carry_marker _ leaf hstate, hmark]
    · exact step_carry_mismatch _ leaf width (p + t) hstate hpos0 hpos1 (by omega) hmismatch

/-- Marker and mismatch invariants throughout the carry of a represented bit list. -/
theorem configs_carry_bits_invariants {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (bs : List Bool) (width : ℕ)
    (hq : cfg.state = some (if leaf then stCarryLeaf else stCarryFork))
    (hp0 : cfg.workTapePos 0 = 0) (hp1 : cfg.workTapePos 1 = 0)
    (hbits : ∀ j, digits cfg (if leaf then 1 else 0) j = bs[j]?.getD false)
    (hw : Counter.flips bs ≤ width)
    (hm : cfg.workTapePos 2 = (mismatchCount width (digits cfg 0) (digits cfg 1) : ℤ))
    (t : ℕ) (ht : t ≤ Counter.flips bs) :
    let now := machine.configs cfg t
    (∀ z, origin (now.workTapes 0 z) = origin (cfg.workTapes 0 z)) ∧
    now.workTapes 2 = cfg.workTapes 2 ∧
    now.workTapePos 2 = (mismatchCount width (digits now 0) (digits now 1) : ℤ) := by
  have hpos := Counter.flips_pos bs
  apply configs_carry_invariants cfg leaf 0 (Counter.flips bs - 1) width
    hq hp0 hp1 ?_ (by omega) hm t (by omega)
  intro j hj
  rw [Nat.zero_add, hbits]
  exact Counter.getD_eq_true_of_lt_flips bs j (by omega)

/-- A complete carry and return implements one increment and tests equality. -/
theorem configs_increment {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (width a b : ℕ)
    (h : Represents width cfg (if leaf then stCarryLeaf else stCarryFork) a b)
    (hnext : ((if leaf then b else a) + 1).size ≤ width) :
    let f := Counter.flips (if leaf then b else a).bits
    let a' := if leaf then a else a + 1
    let b' := if leaf then b + 1 else b
    let now := machine.configs cfg (2 * f + 1)
    Represents width now (if a' = b' then stDone else stTree) a' b' ∧
      now.inputPos = cfg.inputPos ∧ machine.outputString cfg (2 * f + 1) = [] := by
  let n := if leaf then b else a
  let f := Counter.flips n.bits
  let a' := if leaf then a else a + 1
  let b' := if leaf then b + 1 else b
  let after := machine.configs cfg f
  have hbits : ∀ j, digits cfg (if leaf then 1 else 0) j = n.bits[j]?.getD false := by
    intro j
    cases leaf
    · exact congrFun h.forkDigits j
    · exact congrFun h.leafDigits j
  obtain ⟨hstate, hpos0, hpos1, hin, hselected, hother, hout⟩ :=
    configs_carry_bits cfg leaf n.bits h.state h.forkPos h.leafPos hbits
  have hw : f ≤ width := (Counter.flips_bits_le_succ_size n).trans hnext
  have hm : cfg.workTapePos 2 = (mismatchCount width (digits cfg 0) (digits cfg 1) : ℤ) := by
    rw [h.forkDigits, h.leafDigits]
    exact h.mismatchPos
  obtain ⟨horigin, hmarker, hmismatch⟩ := configs_carry_bits_invariants cfg leaf n.bits
    width h.state h.forkPos h.leafPos hbits hw hm f (Nat.le_refl _)
  have hd0 : digits after 0 = bitsAt a' := by
    cases leaf
    · funext j
      simpa [Counter.increment_bits, n, a', after, f, bitsAt] using congrFun hselected j
    · exact hother.trans h.forkDigits
  have hd1 : digits after 1 = bitsAt b' := by
    cases leaf
    · exact hother.trans h.leafDigits
    · funext j
      simpa [Counter.increment_bits, n, b', after, f, bitsAt] using congrFun hselected j
  have ho : ∀ z, origin (after.workTapes 0 z) = decide (z = 0) :=
    fun z ↦ (horigin z).trans (h.originTag z)
  have hmark : ∀ z, after.workTapes 2 z = if z = 0 then some 0 else none := by
    intro z
    rw [hmarker, h.marker]
  have hm' : after.workTapePos 2 = (mismatchCount width (bitsAt a') (bitsAt b') : ℤ) := by
    rw [← hd0, ← hd1]
    exact hmismatch
  have ha' : a'.size ≤ width := by cases leaf <;> first | exact hnext | exact h.forkSize
  have hb' : b'.size ≤ width := by cases leaf <;> first | exact hnext | exact h.leafSize
  have hr := returnedCfg_represents after width a' b' hd0 hd1 ho hmark hm' ha' hb'
  have he := returnCfg_self after f hstate hpos0 hpos1
  obtain ⟨hc, ho'⟩ := configs_return_done after ho f
  rw [he] at hc ho'
  have hfinal : machine.configs cfg (2 * f + 1) = returnedCfg after := by
    rw [show 2 * f + 1 = f + (f + 1) by omega, configs_add]
    exact hc
  change Represents width _ _ a' b' ∧ _ ∧ _
  rw [hfinal]
  refine ⟨hr, hin, ?_⟩
  rw [show 2 * f + 1 = f + (f + 1) by omega, outputString_add_eq_append, hout, ho']
  rfl

/-- Every work head stays within the fixed width during a complete increment. -/
theorem configs_increment_head_bounds {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (leaf : Bool) (width a b : ℕ)
    (h : Represents width cfg (if leaf then stCarryLeaf else stCarryFork) a b)
    (hnext : ((if leaf then b else a) + 1).size ≤ width)
    (t : ℕ) (ht : t ≤ 2 * Counter.flips (if leaf then b else a).bits + 1) (i : Fin 3) :
    0 ≤ (machine.configs cfg t).workTapePos i ∧
      (machine.configs cfg t).workTapePos i ≤ width := by
  let n := if leaf then b else a
  let f := Counter.flips n.bits
  have hw : f ≤ width := (Counter.flips_bits_le_succ_size n).trans hnext
  have hbits : ∀ j, digits cfg (if leaf then 1 else 0) j = n.bits[j]?.getD false := by
    intro j
    cases leaf
    · exact congrFun h.forkDigits j
    · exact congrFun h.leafDigits j
  have hm : cfg.workTapePos 2 = (mismatchCount width (digits cfg 0) (digits cfg 1) : ℤ) := by
    rw [h.forkDigits, h.leafDigits]
    exact h.mismatchPos
  by_cases htf : t ≤ f
  · obtain ⟨hp0, hp1⟩ :=
      configs_carry_bits_pos cfg leaf n.bits h.state h.forkPos h.leafPos hbits t htf
    have hm' := (configs_carry_bits_invariants cfg leaf n.bits width h.state
      h.forkPos h.leafPos hbits hw hm t htf).2.2
    have hcount := mismatchCount_le width (digits (machine.configs cfg t) 0)
      (digits (machine.configs cfg t) 1)
    fin_cases i
    · change 0 ≤ (machine.configs cfg t).workTapePos 0 ∧
        (machine.configs cfg t).workTapePos 0 ≤ width
      rw [hp0]
      omega
    · change 0 ≤ (machine.configs cfg t).workTapePos 1 ∧
        (machine.configs cfg t).workTapePos 1 ≤ width
      rw [hp1]
      omega
    · change 0 ≤ (machine.configs cfg t).workTapePos 2 ∧
        (machine.configs cfg t).workTapePos 2 ≤ width
      rw [hm']
      omega
  · let after := machine.configs cfg f
    obtain ⟨hq, hp0, hp1, _⟩ :=
      configs_carry_bits cfg leaf n.bits h.state h.forkPos h.leafPos hbits
    obtain ⟨horigin, _, hm'⟩ := configs_carry_bits_invariants cfg leaf n.bits width
      h.state h.forkPos h.leafPos hbits hw hm f (Nat.le_refl _)
    have ho : ∀ z, origin (after.workTapes 0 z) = decide (z = 0) :=
      fun z ↦ (horigin z).trans (h.originTag z)
    have he := returnCfg_self after f hq hp0 hp1
    have hcount := mismatchCount_le width (digits after 0) (digits after 1)
    dsimp only [after] at hcount
    have hb := configs_return_head_bounds after ho f width hw
      (by rw [hm']; omega) (by rw [hm']; omega) (t - f) (by dsimp [f, n]; omega) i
    rw [he] at hb
    rw [show t = f + (t - f) by omega, configs_add]
    exact hb

end Geb.BitTree.BinaryMachine
