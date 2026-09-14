/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Loop.Basic
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The loop's control phases

Between two runs of a body, {name}`Geb.SizeBounded.Machine.caseLoop` passes
through three phases of its control automaton. The seek phase walks the head
of the register right to the blank after its word and steps back onto the
word's last cell; the back phase blanks that cell, so that the register holds
the word's tail, and enters the return state for the bit it read; the return
phase walks the head back to cell {lit}`0` and enters the body for that bit.
From a parked empty register the seek phase finds the blank at cell
{lit}`0` instead, and two steps halt the machine.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`caseSeekCfg`, {lit}`caseRetCfg` — the closed forms of the seek and
  return phases' configurations.

# Main statements

* {lit}`caseLoop_seek`, {lit}`caseLoop_back`, {lit}`caseLoop_ret` — the reach
  of each phase, naming the configuration it ends in and the step count.
* {lit}`caseLoop_exit` — the run from a parked empty register.

# Tags

Turing machine, loop, recursion, register
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- The configuration of {name}`caseLoop` in its seek state after {lit}`s`
steps from a parked start. -/
@[expose] def caseSeekCfg {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (s : ℕ) :
    Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input :=
  { cfg with
    state := some (.inl 0)
    workTapePos := Function.update cfg.workTapePos R (s : ℤ) }

/-- The configuration of {name}`caseLoop` in the return state for {lit}`c`
after {lit}`s` steps from a start whose head on {lit}`R` is at cell
{lit}`p`. -/
@[expose] def caseRetCfg {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (c : Bool) (p : ℤ) (s : ℕ) :
    Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input :=
  { cfg with
    state := some (.inl (if c then 3 else 2))
    workTapePos := Function.update cfg.workTapePos R (p - s) }

/-- The seek phase: from the seek state with {lit}`R` holding {lit}`c :: r`
and parked, {lit}`r.length + 2` steps reach the back state with {lit}`R`'s
head at cell {lit}`r.length`. -/
theorem caseLoop_seek {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 0))
    (c : Bool) (r : List Bool) (hR : cfg.workTapes R = tapeOf (c :: r))
    (hp : cfg.workTapePos R = 0) (B : ℕ) (hB : r.length + 1 ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Reaches (caseLoop R bodyF bodyT) cfg
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (r.length : ℤ) }
      (r.length + 2) B := by
  have hsym : ∀ s : ℕ, (caseSeekCfg (SF := SF) (ST := ST) R cfg s).workTapeSymbols R =
      tapeOf (c :: r) (s : ℤ) := by
    intro s
    change cfg.workTapes R (Function.update cfg.workTapePos R (s : ℤ) R) = _
    rw [Function.update_self, hR]
  have hstep : ∀ s : ℕ, s ≤ r.length →
      (caseLoop R bodyF bodyT).step (caseSeekCfg R cfg s) = caseSeekCfg R cfg (s + 1) := by
    intro s hs
    have hsome : ((caseSeekCfg (SF := SF) (ST := ST) R cfg s).workTapeSymbols R).isSome = true := by
      rw [hsym s, tapeOf_of_lt _ _ (by omega) (by rw [List.length_cons]; omega)]
      rfl
    rw [step_of_state _ _ (.inl 0) rfl]
    apply Cfg.ext
    · change some (Sum.inl (if ((caseSeekCfg R cfg s).workTapeSymbols R).isSome = true
        then 0 else 1)) = some (Sum.inl 0)
      rw [hsome, ite_eq_left rfl]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos R (s : ℤ) j +
          ((if j = R then (if ((caseSeekCfg R cfg s).workTapeSymbols R).isSome then 1 else -1)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos R ((s + 1 : ℕ) : ℤ) j
      rw [hsome]
      by_cases hj : j = R
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, ite_eq_left rfl,
          SignType.coe_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
  have hhalt : (caseLoop R bodyF bodyT).step (caseSeekCfg R cfg (r.length + 1)) =
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (r.length : ℤ) } := by
    have hnone : ((caseSeekCfg (SF := SF) (ST := ST) R cfg (r.length + 1)).workTapeSymbols
        R).isSome = false := by
      rw [hsym _, tapeOf_of_le _ _ (by rw [List.length_cons])]
      rfl
    rw [step_of_state _ _ (.inl 0) rfl]
    apply Cfg.ext
    · change some (Sum.inl (if ((caseSeekCfg R cfg (r.length + 1)).workTapeSymbols R).isSome = true
        then 0 else 1)) = some (Sum.inl 1)
      rw [hnone, ite_eq_right (by simp)]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos R ((r.length + 1 : ℕ) : ℤ) j +
          ((if j = R
            then (if ((caseSeekCfg R cfg (r.length + 1)).workTapeSymbols R).isSome then 1 else -1)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos R (r.length : ℤ) j
      rw [hnone]
      by_cases hj : j = R
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, ite_eq_right (by simp),
          SignType.coe_neg_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ,
      (caseLoop R bodyF bodyT).outputSymbol (caseSeekCfg R cfg s) = none := fun _ ↦ rfl
  have hzero : caseSeekCfg (SF := SF) (ST := ST) R cfg 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · change Function.update cfg.workTapePos R (((0 : ℕ) : ℤ)) = cfg.workTapePos
      rw [show (((0 : ℕ) : ℤ)) = cfg.workTapePos R by omega, Function.update_eq_self]
  have key : ∀ s : ℕ, s ≤ r.length + 1 →
      (caseLoop R bodyF bodyT).configs cfg s = caseSeekCfg R cfg s ∧
        (caseLoop R bodyF bodyT).outputString cfg s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨by rw [configs_zero, hzero], rfl⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s]
        rfl
  obtain ⟨hcn, hon⟩ := key (r.length + 1) (le_refl _)
  have ht : r.length + 2 = (r.length + 1) + 1 := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact Option.some_ne_none _
  · rw [ht, configs_succ_eq_step', hcn, hhalt]
  · rw [ht, outputString_succ, hon, hcn, hout _]
    rfl
  · intro t' ht' j
    by_cases hlt : t' ≤ r.length + 1
    · rw [(key t' hlt).1]
      exact update_workTapePos_bounds R hpos _ (by omega) (by omega) j
    · rw [show t' = (r.length + 1) + 1 by omega, configs_succ_eq_step', hcn, hhalt]
      exact update_workTapePos_bounds R hpos _ (by omega) (by omega) j

/-- The back phase: from the back state with {lit}`R` holding {lit}`c :: r`
and its head at cell {lit}`r.length`, one step blanks that cell, so that
{lit}`R` holds {lit}`r`, moves left, and enters the return state for
{lit}`c`. -/
theorem caseLoop_back {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 1))
    (c : Bool) (r : List Bool) (hR : cfg.workTapes R = tapeOf (c :: r))
    (hp : cfg.workTapePos R = (r.length : ℤ)) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Reaches (caseLoop R bodyF bodyT) cfg
      { cfg with
        state := some (.inl (if c then 3 else 2))
        workTapes := Function.update cfg.workTapes R (tapeOf r)
        workTapePos := Function.update cfg.workTapePos R ((r.length : ℤ) - 1) }
      1 B := by
  have hsym : cfg.workTapeSymbols R = some c := by
    change cfg.workTapes R (cfg.workTapePos R) = some c
    rw [hR, hp, tapeOf_cons, Function.update_self]
  have htr : (caseLoop R bodyF bodyT).tr (.inl 1) cfg.inputSymbol cfg.workTapeSymbols =
      { inputMove := 0
        workActions := fun j ↦ if j = R then (some none, -1) else (none, 0)
        outS := none
        q' := some (.inl (if c then 3 else 2)) } := by
    unfold caseLoop
    dsimp only
    rw [hsym]
  have hstep : (caseLoop R bodyF bodyT).step cfg =
      { cfg with
        state := some (.inl (if c then 3 else 2))
        workTapes := Function.update cfg.workTapes R (tapeOf r)
        workTapePos := Function.update cfg.workTapePos R ((r.length : ℤ) - 1) } := by
    have hact : ∀ j : Fin k, ((caseLoop R bodyF bodyT).tr (.inl 1) cfg.inputSymbol
        cfg.workTapeSymbols).workActions j =
        if j = R then ((some none : Option (Option Bool)), (-1 : SignType)) else (none, 0) := by
      intro j
      rw [htr]
    rw [step_of_state _ _ (.inl 1) hq]
    apply Cfg.ext
    · rw [htr]
    · rw [htr]
      change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      simp only [hact j]
      by_cases hj : j = R
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update (cfg.workTapes j) (cfg.workTapePos j) none =
          Function.update cfg.workTapes j (tapeOf r) j
        rw [hR, hp, tapeOf_update_none, Function.update_self]
      · rw [ite_eq_right hj]
        change cfg.workTapes j = Function.update cfg.workTapes R (tapeOf r) j
        rw [Function.update_of_ne hj]
    · funext j
      simp only [hact j]
      by_cases hj : j = R
      · subst hj
        rw [ite_eq_left rfl]
        change cfg.workTapePos j + ((-1 : SignType) : ℤ) =
          Function.update cfg.workTapePos j ((r.length : ℤ) - 1) j
        rw [Function.update_self, SignType.coe_neg_one, hp, ← sub_eq_add_neg]
      · rw [ite_eq_right hj]
        change cfg.workTapePos j + ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos R ((r.length : ℤ) - 1) j
        rw [Function.update_of_ne hj, SignType.coe_zero, add_zero]
  have hout : (caseLoop R bodyF bodyT).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    dsimp only
    rw [htr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t' ht'
    rw [show t' = 0 by omega, configs_zero, hq]
    exact Option.some_ne_none _
  · rw [configs_succ_eq_step' (t := 0), configs_zero, hstep]
  · rw [outputString_succ, configs_zero, hout]
    rfl
  · intro t' ht' j
    rcases show t' = 0 ∨ t' = 1 by omega with h0 | h1
    · rw [h0, configs_zero]
      exact hpos j
    · rw [h1, configs_succ_eq_step' (t := 0), configs_zero, hstep]
      have hB := (hpos R).2
      exact update_workTapePos_bounds R hpos _ (by omega) (by omega) j

/-- The return phase: from the return state for {lit}`c` with {lit}`R`
holding {lit}`r` and its head at cell {lit}`r.length - 1`,
{lit}`r.length + 1` steps park the head and enter the body for {lit}`c` in
its initial state. -/
theorem caseLoop_ret {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (c : Bool)
    (hq : cfg.state = some (.inl (if c then 3 else 2)))
    (r : List Bool) (hR : cfg.workTapes R = tapeOf r)
    (hp : cfg.workTapePos R = (r.length : ℤ) - 1) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Reaches (caseLoop R bodyF bodyT) cfg
      { cfg with
        state := some (if c then .inr (.inr bodyT.q₀) else .inr (.inl bodyF.q₀))
        workTapePos := Function.update cfg.workTapePos R 0 }
      (r.length + 1) B := by
  have htr : ∀ (inp : Option Bool) (work : Fin k → Option Bool),
      (caseLoop R bodyF bodyT).tr (.inl (if c then 3 else 2)) inp work =
        { inputMove := 0
          workActions := fun j ↦ (none, if j = R
            then (if (work R).isSome then -1 else 1) else 0)
          outS := none
          q' := some (if (work R).isSome then .inl (if c then 3 else 2)
            else if c then .inr (.inr bodyT.q₀) else .inr (.inl bodyF.q₀)) } := by
    intro inp work
    cases c <;> rfl
  have hsym : ∀ s : ℕ,
      (caseRetCfg (SF := SF) (ST := ST) R cfg c ((r.length : ℤ) - 1) s).workTapeSymbols R =
        tapeOf r ((r.length : ℤ) - 1 - s) := by
    intro s
    change cfg.workTapes R
      (Function.update cfg.workTapePos R ((r.length : ℤ) - 1 - s) R) = _
    rw [Function.update_self, hR]
  have hstep : ∀ s : ℕ, s < r.length →
      (caseLoop R bodyF bodyT).step (caseRetCfg R cfg c ((r.length : ℤ) - 1) s) =
        caseRetCfg R cfg c ((r.length : ℤ) - 1) (s + 1) := by
    intro s hs
    have hsome : ((caseRetCfg (SF := SF) (ST := ST) R cfg c ((r.length : ℤ) - 1)
        s).workTapeSymbols R).isSome = true := by
      rw [hsym s, tapeOf_of_lt _ _ (by omega) (by omega)]
      rfl
    rw [step_of_state _ _ (.inl (if c then 3 else 2)) rfl, htr]
    apply Cfg.ext
    · dsimp only
      rw [hsome, ite_eq_left rfl]
      rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos R ((r.length : ℤ) - 1 - s) j +
          ((if j = R
            then (if ((caseRetCfg R cfg c ((r.length : ℤ) - 1) s).workTapeSymbols R).isSome
              then -1 else 1)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos R ((r.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ)) j
      rw [hsome]
      by_cases hj : j = R
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, ite_eq_left rfl,
          SignType.coe_neg_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
  have hhalt : (caseLoop R bodyF bodyT).step (caseRetCfg R cfg c ((r.length : ℤ) - 1) r.length) =
      { cfg with
        state := some (if c then .inr (.inr bodyT.q₀) else .inr (.inl bodyF.q₀))
        workTapePos := Function.update cfg.workTapePos R 0 } := by
    have hnone : ((caseRetCfg (SF := SF) (ST := ST) R cfg c ((r.length : ℤ) - 1)
        r.length).workTapeSymbols R).isSome = false := by
      rw [hsym _, tapeOf_neg _ _ (by omega)]
      rfl
    rw [step_of_state _ _ (.inl (if c then 3 else 2)) rfl, htr]
    apply Cfg.ext
    · dsimp only
      rw [hnone, ite_eq_right (by simp)]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos R ((r.length : ℤ) - 1 - ((r.length : ℕ) : ℤ)) j +
          ((if j = R
            then (if ((caseRetCfg R cfg c ((r.length : ℤ) - 1) r.length).workTapeSymbols
              R).isSome then -1 else 1)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos R 0 j
      rw [hnone]
      by_cases hj : j = R
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, ite_eq_right (by simp),
          SignType.coe_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ, (caseLoop R bodyF bodyT).outputSymbol
      (caseRetCfg R cfg c ((r.length : ℤ) - 1) s) = none := by
    intro s
    unfold outputSymbol
    change ((caseLoop R bodyF bodyT).tr (.inl (if c then 3 else 2)) _ _).outS = none
    rw [htr]
  have hzero : caseRetCfg (SF := SF) (ST := ST) R cfg c ((r.length : ℤ) - 1) 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · change Function.update cfg.workTapePos R ((r.length : ℤ) - 1 - ((0 : ℕ) : ℤ)) =
        cfg.workTapePos
      rw [show ((r.length : ℤ) - 1 - ((0 : ℕ) : ℤ)) = cfg.workTapePos R by omega,
        Function.update_eq_self]
  have key : ∀ s : ℕ, s ≤ r.length →
      (caseLoop R bodyF bodyT).configs cfg s = caseRetCfg R cfg c ((r.length : ℤ) - 1) s ∧
        (caseLoop R bodyF bodyT).outputString cfg s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨by rw [configs_zero, hzero], rfl⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s]
        rfl
  obtain ⟨hcn, hon⟩ := key r.length (le_refl _)
  have hpB : (r.length : ℤ) - 1 ≤ B := hp ▸ (hpos R).2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact Option.some_ne_none _
  · rw [configs_succ_eq_step', hcn, hhalt]
  · rw [outputString_succ, hon, hcn, hout _]
    rfl
  · intro t' ht' j
    by_cases hlt : t' ≤ r.length
    · rw [(key t' hlt).1]
      exact update_workTapePos_bounds R hpos _ (by omega) (by omega) j
    · rw [show t' = r.length + 1 by omega, configs_succ_eq_step', hcn, hhalt]
      exact update_workTapePos_bounds R hpos _ (by omega) (by omega) j

/-- The exit: from the seek state with {lit}`R` empty and parked, two steps
halt with every head where it was. -/
theorem caseLoop_exit {k : ℕ} {SF ST : Type} {input : List Bool} (R : Fin k)
    (bodyF : MultiTapeTM k Bool SF) (bodyT : MultiTapeTM k Bool ST)
    (cfg : Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input) (hq : cfg.state = some (.inl 0))
    (hR : cfg.workTapes R = tapeOf []) (hp : cfg.workTapePos R = 0) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (caseLoop R bodyF bodyT) cfg { cfg with state := none } 2 B := by
  have hblank : ∀ z : ℤ, cfg.workTapes R z = none := by
    intro z
    rw [hR, tapeOf_nil]
  have hsym : (cfg.workTapeSymbols R).isSome = false := by
    change (cfg.workTapes R (cfg.workTapePos R)).isSome = false
    rw [hblank]
    rfl
  have hstep₁ : (caseLoop R bodyF bodyT).step cfg =
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (-1) } := by
    rw [step_of_state _ _ (.inl 0) hq]
    apply Cfg.ext
    · change some (Sum.inl (if (cfg.workTapeSymbols R).isSome = true then 0 else 1)) =
        some (Sum.inl 1)
      rw [hsym, ite_eq_right (by simp)]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change cfg.workTapePos j +
          ((if j = R then (if (cfg.workTapeSymbols R).isSome then 1 else -1)
            else 0 : SignType) : ℤ) = Function.update cfg.workTapePos R (-1) j
      rw [hsym]
      by_cases hj : j = R
      · subst hj
        rw [Function.update_self, ite_eq_left rfl, ite_eq_right (by simp), SignType.coe_neg_one,
          hp]
        omega
      · rw [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
  have hsym₁ : (({ cfg with
      state := some (.inl 1)
      workTapePos := Function.update cfg.workTapePos R (-1 : ℤ) } :
        Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input).workTapeSymbols R) = none := by
    change cfg.workTapes R (Function.update cfg.workTapePos R (-1 : ℤ) R) = none
    rw [hblank]
  have htr₁ : (caseLoop R bodyF bodyT).tr (.inl 1)
      ({ cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (-1 : ℤ) } :
          Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input).inputSymbol
      ({ cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (-1 : ℤ) } :
          Cfg k Bool (Fin 4 ⊕ (SF ⊕ ST)) input).workTapeSymbols =
      { inputMove := 0
        workActions := fun j ↦ (none, if j = R then 1 else 0)
        outS := none
        q' := none } := by
    unfold caseLoop
    dsimp only
    rw [hsym₁]
  have hstep₂ : (caseLoop R bodyF bodyT).step
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (-1 : ℤ) } =
      { cfg with state := none } := by
    rw [step_of_state _ _ (.inl 1) rfl, htr₁]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos R (-1 : ℤ) j +
          ((if j = R then (1 : SignType) else 0 : SignType) : ℤ) = cfg.workTapePos j
      by_cases hj : j = R
      · subst hj
        rw [Function.update_self, ite_eq_left rfl, SignType.coe_one, hp]
        omega
      · rw [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
  have hout₀ : (caseLoop R bodyF bodyT).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  have hout₁ : (caseLoop R bodyF bodyT).outputSymbol
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (-1 : ℤ) } = none := by
    unfold outputSymbol
    change ((caseLoop R bodyF bodyT).tr (.inl 1) _ _).outS = none
    rw [htr₁]
  have hc₁ : (caseLoop R bodyF bodyT).configs cfg 1 =
      { cfg with
        state := some (.inl 1)
        workTapePos := Function.update cfg.workTapePos R (-1 : ℤ) } := by
    rw [configs_succ_eq_step' (t := 0), configs_zero, hstep₁]
  have hc₂ : (caseLoop R bodyF bodyT).configs cfg 2 = { cfg with state := none } := by
    rw [show (2 : ℕ) = 1 + 1 by omega, configs_succ_eq_step', hc₁, hstep₂]
  refine ⟨⟨?_, hc₂, ?_, ?_⟩, rfl⟩
  · intro t' ht'
    rcases show t' = 0 ∨ t' = 1 by omega with h0 | h1
    · rw [h0, configs_zero, hq]
      exact Option.some_ne_none _
    · rw [h1, hc₁]
      exact Option.some_ne_none _
  · rw [show (2 : ℕ) = 1 + 1 by omega, outputString_succ, outputString_succ, configs_zero,
      hout₀, hc₁, hout₁]
    rfl
  · intro t' ht' j
    rcases show t' = 0 ∨ t' = 1 ∨ t' = 2 by omega with h0 | h1 | h2
    · rw [h0, configs_zero]
      exact hpos j
    · rw [h1, hc₁]
      exact update_workTapePos_bounds R hpos _ (by omega) (by omega) j
    · rw [h2, hc₂]
      exact hpos j

end

end Geb.SizeBounded.Machine
