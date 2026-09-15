/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The clearing phases

Emptying a register from a parked head takes two sweeps: {lit}`walkEnd`
moves the head right while it reads a bit, stopping on the blank after the
word, and {lit}`blankLeft` moves it left while it reads a bit, blanking each
cell it reads, stopping on the blank before the word. {lit}`clear` sequences
the two through a {name}`Geb.SizeBounded.Machine.moveLeft` that steps from
the blank after the word onto the word's last cell.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`walkEnd` — move one head right to the blank after the word.
* {lit}`blankLeft` — blank the word leftwards and park the head.
* {lit}`clear` — empty one register from a parked head.
* {lit}`walkCfg`, {lit}`blankCfg` — the closed forms of the two sweeps'
  configurations.

# Main statements

* {lit}`walkEnd_runsTo`, {lit}`blankLeft_runsTo`, {lit}`clear_runsTo` — the
  run of each machine, naming the halted configuration and the step count.

# Tags

Turing machine, register, head position
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Move the head of tape {lit}`i` right while it reads a bit; halt on the
first blank, without moving. -/
@[expose] def walkEnd {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputMove := 0
      workActions := fun j ↦ (none, if j = i then (if (work i).isSome then 1 else 0) else 0)
      outS := none
      q' := if (work i).isSome then some () else none }

/-- Move the head of tape {lit}`i` left while it reads a bit, blanking each
bit read; on reading a blank, move right and halt. -/
@[expose] def blankLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputMove := 0
      workActions := fun j ↦
        if j = i then (if (work i).isSome then (some none, -1) else (none, 1)) else (none, 0)
      outS := none
      q' := if (work i).isSome then some () else none }

/-- Empty register {lit}`i` from a parked head: walk to its end, then blank
leftwards and park. -/
@[expose] def clear {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Unit ⊕ (Unit ⊕ Unit)) :=
  seq (walkEnd i) (seq (moveLeft i) (blankLeft i))

/-- The configuration of {name}`walkEnd` after {lit}`s` steps from a parked
start in its initial state. -/
@[expose] def walkCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with state := some (), workTapePos := Function.update cfg.workTapePos i (s : ℤ) }

/-- {name}`walkEnd` from cell {lit}`0` of a register holding {lit}`w` runs
{lit}`w.length + 1` steps to cell {lit}`w.length`. -/
theorem walkEnd_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (walkEnd i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) }
      (w.length + 1) B := by
  have hsym : ∀ s : ℕ, (walkCfg i cfg s).workTapeSymbols i = tapeOf w (s : ℤ) := by
    intro s
    change cfg.workTapes i (Function.update cfg.workTapePos i (s : ℤ) i) = _
    rw [Function.update_self, hw]
  have hstep : ∀ s : ℕ, s < w.length →
      (walkEnd i).step (walkCfg i cfg s) = walkCfg i cfg (s + 1) := by
    intro s hs
    have hsome : ((walkCfg i cfg s).workTapeSymbols i).isSome = true := by
      rw [hsym s, tapeOf_of_lt w _ (by omega) (by omega)]
      rfl
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if ((walkCfg i cfg s).workTapeSymbols i).isSome = true then some () else none) =
        some ()
      rw [hsome, ite_eq_left rfl]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos i (s : ℤ) j +
          ((if j = i then (if ((walkCfg i cfg s).workTapeSymbols i).isSome then 1 else 0)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ) j
      rw [hsome]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, ite_eq_left rfl,
          SignType.coe_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
  have hhalt : (walkEnd i).step (walkCfg i cfg w.length) =
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) } := by
    have hnone : ((walkCfg i cfg w.length).workTapeSymbols i).isSome = false := by
      rw [hsym _, tapeOf_of_le w _ (by omega)]
      rfl
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if ((walkCfg i cfg w.length).workTapeSymbols i).isSome = true
        then some () else none) = none
      rw [hnone, ite_eq_right (by simp)]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos i ((w.length : ℕ) : ℤ) j +
          ((if j = i
            then (if ((walkCfg i cfg w.length).workTapeSymbols i).isSome then 1 else 0)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i (w.length : ℤ) j
      rw [hnone]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, ite_eq_left rfl, ite_eq_right (by simp), SignType.coe_zero,
          add_zero]
      · rw [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ, (walkEnd i).outputSymbol (walkCfg i cfg s) = none := fun _ ↦ rfl
  have hzero : walkCfg i cfg 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · change Function.update cfg.workTapePos i (((0 : ℕ) : ℤ)) = cfg.workTapePos
      rw [show (((0 : ℕ) : ℤ)) = cfg.workTapePos i by omega, Function.update_eq_self]
  have key : ∀ s : ℕ, s ≤ w.length →
      (walkEnd i).configs cfg s = walkCfg i cfg s ∧ (walkEnd i).outputString cfg s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨by rw [configs_zero, hzero], rfl⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s]
        rfl
  obtain ⟨hcn, hon⟩ := key w.length (le_refl _)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact Option.some_ne_none _
  · rw [configs_succ_eq_step', hcn, hhalt]
  · intro t' ht' j
    by_cases hlt : t' ≤ w.length
    · rw [(key t' hlt).1]
      exact update_workTapePos_bounds i hpos _ (by omega) (by omega) j
    · rw [show t' = w.length + 1 by omega, configs_succ_eq_step', hcn, hhalt]
      exact update_workTapePos_bounds i hpos _ (by omega) (by omega) j
  · rw [outputString_succ, hon, hcn, hout _]
    rfl

/-- The configuration of {name}`blankLeft` after {lit}`s` steps from a start
in its initial state at cell {lit}`w.length - 1` of a register holding
{lit}`w`. -/
@[expose] def blankCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (w : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapes := Function.update cfg.workTapes i (tapeOf (w.drop s))
    workTapePos := Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) }

/-- {name}`blankLeft` from cell {lit}`w.length - 1` of a register holding
{lit}`w` runs {lit}`w.length + 1` steps, empties the register and parks. -/
theorem blankLeft_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = (w.length : ℤ) - 1) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (blankLeft i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i 0 }
      (w.length + 1) B := by
  have hsym : ∀ s : ℕ, (blankCfg i cfg w s).workTapeSymbols i =
      tapeOf (w.drop s) ((w.length : ℤ) - 1 - s) := by
    intro s
    change Function.update cfg.workTapes i (tapeOf (w.drop s)) i
      (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) i) = _
    rw [Function.update_self, Function.update_self]
  have hstep : ∀ s : ℕ, s < w.length →
      (blankLeft i).step (blankCfg i cfg w s) = blankCfg i cfg w (s + 1) := by
    intro s hs
    have hsome : ((blankCfg i cfg w s).workTapeSymbols i).isSome = true := by
      rw [hsym s, tapeOf_of_lt _ _ (by omega) (by rw [List.length_drop]; omega)]
      rfl
    have hblank : Function.update (tapeOf (w.drop s)) ((w.length : ℤ) - 1 - s) none =
        tapeOf (w.drop (s + 1)) := by
      rw [show ((w.length : ℤ) - 1 - s) = (((w.drop (s + 1)).length : ℕ) : ℤ) by
          rw [List.length_drop]; omega,
        List.drop_eq_getElem_cons hs, tapeOf_update_none]
    have hact : ∀ j : Fin k, ((blankLeft i).tr () (blankCfg i cfg w s).inputSymbol
        (blankCfg i cfg w s).workTapeSymbols).workActions j =
        if j = i then ((some none : Option (Option Bool)), (-1 : SignType)) else (none, 0) := by
      intro j
      change (if j = i then (if ((blankCfg i cfg w s).workTapeSymbols i).isSome
          then ((some none : Option (Option Bool)), (-1 : SignType)) else (none, 1))
        else (none, 0)) = _
      rw [hsome, ite_eq_left rfl]
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if ((blankCfg i cfg w s).workTapeSymbols i).isSome = true then some () else none) =
        some ()
      rw [hsome, ite_eq_left rfl]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes j (tapeOf (w.drop s)) j)
            (Function.update cfg.workTapePos j ((w.length : ℤ) - 1 - s) j) none =
          Function.update cfg.workTapes j (tapeOf (w.drop (s + 1))) j
        rw [Function.update_self, Function.update_self, Function.update_self]
        exact hblank
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapes i (tapeOf (w.drop s)) j =
          Function.update cfg.workTapes i (tapeOf (w.drop (s + 1))) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update cfg.workTapePos j ((w.length : ℤ) - 1 - s) j +
            ((-1 : SignType) : ℤ) =
          Function.update cfg.workTapePos j ((w.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ)) j
        rw [Function.update_self, Function.update_self, SignType.coe_neg_one]
        omega
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s) j +
            ((0 : SignType) : ℤ) =
          Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ)) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj, SignType.coe_zero, add_zero]
  have hpB : (w.length : ℤ) - 1 ≤ B := hp ▸ (hpos i).2
  have hhalt : (blankLeft i).step (blankCfg i cfg w w.length) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i 0 } := by
    have hnone : ((blankCfg i cfg w w.length).workTapeSymbols i).isSome = false := by
      rw [hsym _, tapeOf_neg _ _ (by omega)]
      rfl
    have hact : ∀ j : Fin k, ((blankLeft i).tr () (blankCfg i cfg w w.length).inputSymbol
        (blankCfg i cfg w w.length).workTapeSymbols).workActions j =
        if j = i then ((none : Option (Option Bool)), (1 : SignType)) else (none, 0) := by
      intro j
      change (if j = i then (if ((blankCfg i cfg w w.length).workTapeSymbols i).isSome
          then ((some none : Option (Option Bool)), (-1 : SignType)) else (none, 1))
        else (none, 0)) = _
      rw [hnone, ite_eq_right (show ¬(false = true) by simp)]
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if ((blankCfg i cfg w w.length).workTapeSymbols i).isSome = true
        then some () else none) = none
      rw [hnone, ite_eq_right (by simp)]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update cfg.workTapes j (tapeOf (w.drop w.length)) j =
          Function.update cfg.workTapes j (tapeOf []) j
        rw [Function.update_self, Function.update_self, List.drop_length]
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapes i (tapeOf (w.drop w.length)) j =
          Function.update cfg.workTapes i (tapeOf []) j
        rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · funext j
      simp only [hact j]
      by_cases hj : j = i
      · subst hj
        rw [ite_eq_left rfl]
        change Function.update cfg.workTapePos j ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ)) j +
            ((1 : SignType) : ℤ) = Function.update cfg.workTapePos j 0 j
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hj]
        change Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ)) j +
            ((0 : SignType) : ℤ) = Function.update cfg.workTapePos i 0 j
        rw [Function.update_of_ne hj, Function.update_of_ne hj, SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ, (blankLeft i).outputSymbol (blankCfg i cfg w s) = none := fun _ ↦ rfl
  have hzero : blankCfg i cfg w 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · change Function.update cfg.workTapes i (tapeOf (w.drop 0)) = cfg.workTapes
      rw [List.drop_zero, ← hw, Function.update_eq_self]
    · change Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - ((0 : ℕ) : ℤ)) =
        cfg.workTapePos
      rw [show ((w.length : ℤ) - 1 - ((0 : ℕ) : ℤ)) = cfg.workTapePos i by omega,
        Function.update_eq_self]
  have key : ∀ s : ℕ, s ≤ w.length →
      (blankLeft i).configs cfg s = blankCfg i cfg w s ∧
        (blankLeft i).outputString cfg s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨by rw [configs_zero, hzero], rfl⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s]
        rfl
  obtain ⟨hcn, hon⟩ := key w.length (le_refl _)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact Option.some_ne_none _
  · rw [configs_succ_eq_step', hcn, hhalt]
  · intro t' ht' j
    by_cases hlt : t' ≤ w.length
    · rw [(key t' hlt).1]
      exact update_workTapePos_bounds i hpos _ (by omega) (by omega) j
    · rw [show t' = w.length + 1 by omega, configs_succ_eq_step', hcn, hhalt]
      exact update_workTapePos_bounds i hpos _ (by omega) (by omega) j
  · rw [outputString_succ, hon, hcn, hout _]
    rfl

/-- {name}`clear` from a parked register holding {lit}`w` runs
{lit}`2 * w.length + 3` steps, empties it and parks. -/
theorem clear_runsTo {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Unit ⊕ (Unit ⊕ Unit)) input) (hq : cfg.state = some (clear i).q₀)
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (hp : cfg.workTapePos i = 0) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (clear i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i 0 }
      (2 * w.length + 3) B := by
  have hupd : ∀ a b : ℤ, Function.update (Function.update cfg.workTapePos i a) i b =
      Function.update cfg.workTapePos i b := by
    intro a b
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
  have hbound : ∀ j, -1 ≤ Function.update cfg.workTapePos i (w.length : ℤ) j ∧
      Function.update cfg.workTapePos i (w.length : ℤ) j ≤ B :=
    fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j
  have r₁ := walkEnd_runsTo i { cfg with state := some (walkEnd i).q₀ } rfl w hw hp B hB hpos
  have r₂ := moveLeft_runsTo i
    { cfg with
      state := some (moveLeft i).q₀
      workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) }
    rfl B hbound
    (by change (0 : ℤ) ≤ Function.update cfg.workTapePos i (w.length : ℤ) i
        rw [Function.update_self]
        omega)
  simp only [Function.update_self, hupd] at r₂
  have r₃ := blankLeft_runsTo i
    { cfg with
      state := some (blankLeft i).q₀
      workTapePos := Function.update cfg.workTapePos i ((w.length : ℤ) - 1) }
    rfl w hw
    (by change Function.update cfg.workTapePos i ((w.length : ℤ) - 1) i = (w.length : ℤ) - 1
        rw [Function.update_self])
    B (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)
  rw [hupd] at r₃
  have hinner := r₂.seq r₃
  rw [← liftL_start (moveLeft i) (blankLeft i)
    { cfg with
      state := some (seq (moveLeft i) (blankLeft i)).q₀
      workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) } rfl] at hinner
  have hseq := r₁.seq hinner
  rw [← liftL_start (walkEnd i) (seq (moveLeft i) (blankLeft i)) cfg hq,
    show w.length + 1 + (1 + (w.length + 1)) = 2 * w.length + 3 by omega] at hseq
  rw [show ({ cfg with
      state := none
      workTapes := Function.update cfg.workTapes i (tapeOf [])
      workTapePos := Function.update cfg.workTapePos i 0 } :
        Cfg k Bool (Unit ⊕ (Unit ⊕ Unit)) input) =
    liftR (S₁ := Unit) (liftR (S₁ := Unit)
      ({ cfg with
        state := (none : Option Unit)
        workTapes := Function.update cfg.workTapes i (tapeOf [])
        workTapePos := Function.update cfg.workTapePos i 0 } : Cfg k Bool Unit input)) from ?_]
  · exact hseq
  · apply Cfg.ext <;> rfl

end

end Geb.SizeBounded.Machine
