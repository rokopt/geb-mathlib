/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Recursion
public import Cslib.Computability.Machines.Turing.MultiTape.ConfigBound
public import Geb.Prototypes.Computability.MultiTape.RunFrom
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Time from work space

A halting deterministic transducer cannot repeat a configuration after forgetting
its write-only output. CSLib's bound on the number of configuration cores therefore
bounds its halting time by an exponential in the work space, for the same machine
that satisfies the space bound. At logarithmic space this bound is polynomial in
the input length; at space exponential in the input length it is doubly
exponential.

## Main statements

* {lit}`core_runFrom_eq_of_core_eq` lifts equality of cores through a run.
* {lit}`exists_halt_le_of_space` bounds the first halt by the configuration count.
* {lit}`computes_of_space` gives simultaneous bounds for a halting transducer
  under any work space bound, the time exponential in the space.
* {lit}`computes_polytime_logspace` is its instance at logarithmic space, and
  {lit}`computes_expspace` its instance at exponential space.

## Implementation notes

This module concerns CSLib machines. Its statements inherit
{lit}`Classical.choice` from CSLib's configuration and counting interfaces, so the
module belongs to {lit}`GebMeta.classicalAllowedModules`.

## References

* {cite}`Oitavem2010`, Theorem 3.4: the intended application to Logs requires
  a separate construction of a machine with the asserted space bound.

## Tags

Turing machine, logarithmic space, polynomial time, configuration counting
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded (IsPolyBounded isPolyBounded_mul isPolyBounded_add
  isPolyBounded_id isPolyBounded_const)

public section

/-- Configurations agreeing outside their output tapes keep agreeing there. -/
theorem core_runFrom_eq_of_core_eq {k : ℕ} {Symbol State : Type*}
    (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    {c₁ c₂ : Cfg k Symbol State input} (hc : c₁.core = c₂.core) (t : ℕ) :
    (tm.runFrom c₁ t).core = (tm.runFrom c₂ t).core := by
  apply Nat.rec (motive := fun t ↦ (tm.runFrom c₁ t).core = (tm.runFrom c₂ t).core) ?_ ?_ t
  · exact hc
  · intro t ih
    rw [runFrom_succ_eq_step', runFrom_succ_eq_step']
    exact core_step_eq_of_core_eq ih

/-- Repeating a core before the first halt would give an earlier halt. -/
theorem core_ne_of_lt {k : ℕ} {Symbol State : Type*}
    (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (cfg : Cfg k Symbol State input) {i j T : ℕ} (hij : i < j) (hj : j ≤ T)
    (hhalt : (tm.runFrom cfg T).state = none)
    (hlive : ∀ t < T, (tm.runFrom cfg t).state ≠ none) :
    (tm.runFrom cfg i).core ≠ (tm.runFrom cfg j).core := by
  intro hc
  have he := core_runFrom_eq_of_core_eq tm hc (T - j)
  rw [← runFrom_add, ← runFrom_add, Nat.add_sub_of_le hj] at he
  have hs := congrArg (fun c ↦ c.2.state) he
  exact hlive (i + (T - j)) (by omega) (hs.trans hhalt)

/-- Every time up to the first halt has a distinct configuration core. -/
theorem core_injective_before_halt {k : ℕ} {Symbol State : Type*}
    (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (cfg : Cfg k Symbol State input) (T : ℕ)
    (hhalt : (tm.runFrom cfg T).state = none)
    (hlive : ∀ t < T, (tm.runFrom cfg t).state ≠ none) :
    Function.Injective (fun t : Fin (T + 1) ↦ (tm.runFrom cfg t).core) := by
  intro i j hc
  apply Fin.ext
  by_cases h : i.val < j.val
  · exact False.elim (core_ne_of_lt tm cfg h (by omega) hhalt hlive hc)
  · by_cases h' : j.val < i.val
    · exact False.elim (core_ne_of_lt tm cfg h' (by omega) hhalt hlive hc.symm)
    · omega

/-- The first halt is bounded by the number of cores allowed by the space budget. -/
theorem exists_halt_le_of_space {k : ℕ} {Symbol State : Type*}
    [Finite Symbol] [Finite State] (tm : MultiTapeTM k Symbol State) :
    ∃ a b : ℕ, ∀ (input : List Symbol) (s : ℕ),
      (∀ t, tm.spaceUsed (tm.initCfg input) t ≤ s) →
      (∃ t, (tm.runFrom (tm.initCfg input) t).state = none) →
      ∃ T ≤ (input.length + 2) * a * 2 ^ (b * s),
        (tm.runFrom (tm.initCfg input) T).state = none ∧
        ∀ t < T, (tm.runFrom (tm.initCfg input) t).state ≠ none := by
  obtain ⟨a, b, hab⟩ := tm.encard_cores_le_pow
  refine ⟨a, b, fun input s hs hhalt ↦ ?_⟩
  let T := Nat.find hhalt
  have hT : (tm.runFrom (tm.initCfg input) T).state = none := Nat.find_spec hhalt
  have hlive : ∀ t < T, (tm.runFrom (tm.initCfg input) t).state ≠ none :=
    fun t ht ↦ Nat.find_min hhalt ht
  have hinj := core_injective_before_halt tm (tm.initCfg input) T hT hlive
  have hc : ((T + 1 : ℕ) : ℕ∞) ≤
      (Set.range fun t ↦ (tm.runFrom (tm.initCfg input) t).core).encard := by
    have he := hinj.encard_range
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin] at he
    rw [← he]
    apply Set.encard_le_encard
    rintro _ ⟨t, rfl⟩
    exact ⟨t.val, rfl⟩
  have hb : T + 1 ≤ (input.length + 2) * a * 2 ^ (b * s) := by
    exact_mod_cast hc.trans (hab input s hs)
  exact ⟨T, by omega, hT, hlive⟩

/-- A halting transducer computes its function in time exponential in its work space,
using the very same machine: the first halt is bounded by the number of configuration cores
the space budget allows. -/
theorem computes_of_space {k : ℕ} {State : Type*} [Finite State]
    (tm : MultiTapeTM k Bool State) (f : List Bool → List Bool) (s : ℕ → ℕ)
    (hcorrect : ∀ w, ∃ t, (tm.runFrom (tm.initCfg w) t).state = none ∧
      (tm.runFrom (tm.initCfg w) t).output = f w)
    (hspace : ∀ w t, tm.spaceUsed (tm.initCfg w) t ≤ s w.length) :
    ∃ a b : ℕ, ComputesFunInTimeAndSpace tm (.refl _) (.refl _) f
      (fun w ↦ (w.length + 2) * a * 2 ^ (b * s w.length)) (fun w ↦ s w.length) := by
  obtain ⟨a, b, hab⟩ := exists_halt_le_of_space tm
  refine ⟨a, b, fun w ↦ ?_⟩
  obtain ⟨u, hu, hout⟩ := hcorrect w
  obtain ⟨T, hTb, hT, hlive⟩ := hab w (s w.length) (hspace w) ⟨u, hu⟩
  have hTu : T ≤ u := by
    by_cases h : T ≤ u
    · exact h
    · exact False.elim (hlive u (by omega) hu)
  refine ⟨T, hTb, tm.spaceUsed (tm.initCfg w) T, hspace w T, hT, ?_, rfl⟩
  exact (tm.runFrom_output_eq_of_halt (tm.initCfg w) hTu hT).symm.trans hout

/-- A halting logarithmic-space transducer computes its function in simultaneous
polynomial time and logarithmic space, using the very same machine. -/
theorem computes_polytime_logspace {k : ℕ} {State : Type*} [Finite State]
    (tm : MultiTapeTM k Bool State) (f : List Bool → List Bool) (c : ℕ)
    (hcorrect : ∀ w, ∃ t, (tm.runFrom (tm.initCfg w) t).state = none ∧
      (tm.runFrom (tm.initCfg w) t).output = f w)
    (hspace : ∀ w t, tm.spaceUsed (tm.initCfg w) t ≤ c * (w.length.size + 1)) :
    ∃ C d : ℕ, ComputesFunInTimeAndSpace tm (.refl _) (.refl _) f
      (fun w ↦ C * (w.length + 1) ^ d) (fun w ↦ C * (w.length.size + 1)) := by
  obtain ⟨a, b, h⟩ := computes_of_space tm f (fun n ↦ c * (n.size + 1)) hcorrect hspace
  have hp : IsPolyBounded (fun n ↦ (n + 2) * a * 2 ^ (b * (c * (n.size + 1)))) := by
    simpa only [Nat.mul_assoc] using isPolyBounded_mul
      (isPolyBounded_mul (isPolyBounded_add isPolyBounded_id (isPolyBounded_const 2))
        (isPolyBounded_const a)) (isPolyBounded_pow_size (b * c))
  obtain ⟨C, d, hpoly⟩ := hp
  exact ⟨max C c, d, h.mono
    (fun w ↦ (hpoly w.length).trans (Nat.mul_le_mul_right _ (Nat.le_max_left _ _)))
    (fun w ↦ Nat.mul_le_mul_right _ (Nat.le_max_right _ _))⟩

/-- The exponent of the configuration count of an exponential-space machine, a linear term
plus a constant multiple of the space bound, is within a constant of the exponent of the
next exponential level. -/
theorem exists_add_le_two_pow (a K d : ℕ) :
    ∃ M, ∀ n, n + 1 + a + K * 2 ^ ((n + 1) ^ d) ≤ M + 2 ^ ((n + 1) ^ (d + 1)) := by
  refine ⟨K + a + 1 + 1 + a + K * 2 ^ ((K + a + 1) ^ d), fun n ↦ ?_⟩
  rcases Nat.lt_or_ge n (K + a + 1) with hn | hn
  · have h : K * 2 ^ ((n + 1) ^ d) ≤ K * 2 ^ ((K + a + 1) ^ d) :=
      Nat.mul_le_mul_left K (Nat.pow_le_pow_right Nat.two_pos
        (Nat.pow_le_pow_left (show n + 1 ≤ K + a + 1 by omega) d))
    exact (show n + 1 + a + K * 2 ^ ((n + 1) ^ d) ≤
      K + a + 1 + 1 + a + K * 2 ^ ((K + a + 1) ^ d) by omega).trans (Nat.le_add_right _ _)
  · have hP : 1 ≤ (n + 1) ^ d := Nat.one_le_pow _ _ (by omega)
    have h2n : K + a + n + 1 ≤ 2 ^ n := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := Nat.lt_two_pow_self (n := m)
      rw [Nat.pow_succ]
      omega
    have hmul : (K + a + n + 1) * 2 ^ ((n + 1) ^ d) ≤ 2 ^ ((n + 1) ^ (d + 1)) := by
      rw [Nat.pow_succ, Nat.mul_succ, Nat.pow_add]
      exact Nat.mul_le_mul_right _ (h2n.trans (Nat.pow_le_pow_right (by omega)
        (Nat.le_mul_of_pos_left n hP)))
    have hle : n + 1 + a + K * 2 ^ ((n + 1) ^ d) ≤ (K + a + n + 1) * 2 ^ ((n + 1) ^ d) := by
      have h1 : a + n + 1 ≤ (a + n + 1) * 2 ^ ((n + 1) ^ d) :=
        Nat.le_mul_of_pos_right _ (Nat.pow_pos Nat.two_pos)
      have h2 : (K + a + n + 1) * 2 ^ ((n + 1) ^ d) =
          K * 2 ^ ((n + 1) ^ d) + (a + n + 1) * 2 ^ ((n + 1) ^ d) := by ring
      omega
    omega

/-- A halting transducer whose work space is exponential in the input's length computes
its function in simultaneous doubly exponential time and exponential space, using the
very same machine. -/
theorem computes_expspace {k : ℕ} {State : Type*} [Finite State]
    (tm : MultiTapeTM k Bool State) (f : List Bool → List Bool) (c d : ℕ)
    (hcorrect : ∀ w, ∃ t, (tm.runFrom (tm.initCfg w) t).state = none ∧
      (tm.runFrom (tm.initCfg w) t).output = f w)
    (hspace : ∀ w t, tm.spaceUsed (tm.initCfg w) t ≤ c * 2 ^ ((w.length + 1) ^ d)) :
    ∃ C D : ℕ, ComputesFunInTimeAndSpace tm (.refl _) (.refl _) f
      (fun w ↦ C * 2 ^ 2 ^ ((w.length + 1) ^ D)) (fun w ↦ C * 2 ^ ((w.length + 1) ^ D)) := by
  obtain ⟨a, b, h⟩ := computes_of_space tm f (fun n ↦ c * 2 ^ ((n + 1) ^ d)) hcorrect hspace
  obtain ⟨M, hM⟩ := exists_add_le_two_pow a (b * c) d
  refine ⟨c + 2 ^ M, d + 1, h.mono (fun w ↦ ?_) (fun w ↦ ?_)⟩
  · calc (w.length + 2) * a * 2 ^ (b * (c * 2 ^ ((w.length + 1) ^ d)))
        ≤ 2 ^ (w.length + 1) * 2 ^ a * 2 ^ (b * c * 2 ^ ((w.length + 1) ^ d)) := by
          rw [Nat.mul_assoc b]
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul
            (Nat.lt_two_pow_self (n := w.length + 1)) (Nat.lt_two_pow_self (n := a)).le)
      _ = 2 ^ (w.length + 1 + a + b * c * 2 ^ ((w.length + 1) ^ d)) := by
          rw [← Nat.pow_add, ← Nat.pow_add]
      _ ≤ 2 ^ (M + 2 ^ ((w.length + 1) ^ (d + 1))) :=
          Nat.pow_le_pow_right Nat.two_pos (hM w.length)
      _ = 2 ^ M * 2 ^ 2 ^ ((w.length + 1) ^ (d + 1)) := Nat.pow_add _ _ _
      _ ≤ (c + 2 ^ M) * 2 ^ 2 ^ ((w.length + 1) ^ (d + 1)) :=
          Nat.mul_le_mul_right _ (Nat.le_add_left _ _)
  · exact Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.pow_le_pow_right Nat.two_pos
      (Nat.pow_le_pow_right (by omega) (by omega)))

end

end Geb.Oitavem.Machine
