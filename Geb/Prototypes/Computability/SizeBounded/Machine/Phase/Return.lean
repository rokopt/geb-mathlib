/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq

set_option doc.verso true in
/-!
# The return phases

Every primitive of the calculus leaves the head of the register it works on
somewhere inside the register's word and returns it to cell {lit}`0`.
{lit}`moveLeft` moves a head one cell left; {lit}`retLeft` moves it left
while it reads a bit and, on the blank before the word, one cell right;
{lit}`returnTape` composes the two, so that a head anywhere from cell
{lit}`0` to the blank after the word returns to cell {lit}`0`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`moveLeft` — move one head one cell left and halt.
* {lit}`retLeft` — move one head left to the blank before the word, then one
  cell right.
* {lit}`returnTape` — return one head to cell {lit}`0`.
* {lit}`retCfg` — the closed form of {lit}`retLeft`'s configurations.

# Main statements

* {lit}`update_workTapePos_bounds` — updating one head to a cell within the
  interval keeps every head within it.
* {lit}`moveLeft_runsTo`, {lit}`retLeft_runsTo`, {lit}`returnTape_runsTo` —
  the run of each machine, naming the halted configuration and the step
  count.

# Tags

Turing machine, register, head position
-/

set_option doc.verso true

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Updating one head to a cell within {lit}`[-1, B]` keeps every head within
{lit}`[-1, B]`. -/
theorem update_workTapePos_bounds {k B : ℕ} {f : Fin k → ℤ} (i : Fin k)
    (hf : ∀ j, -1 ≤ f j ∧ f j ≤ B) (a : ℤ) (ha : -1 ≤ a) (haB : a ≤ B) (j : Fin k) :
    -1 ≤ Function.update f i a j ∧ Function.update f i a j ≤ B := by
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self]
    exact ⟨ha, haB⟩
  · rw [Function.update_of_ne hj]
    exact hf j

/-- Move the head of tape {lit}`i` one cell left and halt. -/
@[expose] def moveLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputTape := 0, workTapes := fun j ↦ (none, if j = i then -1 else 0),
      output := none, state := none }

/-- Move the head of tape {lit}`i` left while it reads a bit; on reading a
blank, move right and halt. -/
@[expose] def retLeft {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputTape := 0
      workTapes := fun j ↦ (none, if j = i then (if (work i).isSome then -1 else 1) else 0)
      output := none
      state := if (work i).isSome then some () else none }

/-- Return the head of tape {lit}`i` to cell {lit}`0` from any cell of its
word or the blank after it: one unconditional move left, then
{name}`retLeft`. -/
@[expose] def returnTape {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Unit ⊕ Unit) :=
  seq (moveLeft i) (retLeft i)

/-- {name}`moveLeft` runs one step. -/
theorem moveLeft_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B)
    (hi : 0 ≤ cfg.workTapePos i) :
    RunsTo (moveLeft i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i - 1) }
      1 B := by
  have hhalt : (moveLeft i).step cfg =
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i - 1) } := by
    rw [step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change cfg.workTapePos j + ((if j = i then (-1 : SignType) else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i (cfg.workTapePos i - 1) j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, ite_eq_left rfl, SignType.coe_neg_one, ← sub_eq_add_neg]
      · rw [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : (moveLeft i).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  have hB := (hpos i).2
  exact RunsTo.ofFamily (moveLeft i) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ j ↦ hpos j)
    (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)

/-- The configuration of {name}`retLeft` after {lit}`s` steps from a start in
its initial state whose head on tape {lit}`i` is at cell {lit}`p`. -/
@[expose] def retCfg {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (p : ℤ) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with state := some (), workTapePos := Function.update cfg.workTapePos i (p - s) }

/-- {name}`retLeft` from cell {lit}`p` of a register holding {lit}`w`, with
{lit}`-1 ≤ p < w.length`, runs {lit}`p + 2` steps and parks the head. -/
theorem retLeft_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (p : ℤ) (hp : cfg.workTapePos i = p) (hp0 : -1 ≤ p) (hpw : p < w.length) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (retLeft i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i 0 }
      (p + 2).toNat B := by
  have hpB : p ≤ B := hp ▸ (hpos i).2
  have hsym : ∀ s : ℕ, (retCfg i cfg p s).workTapeSymbols i = tapeOf w (p - s) := by
    intro s
    change cfg.workTapes i (Function.update cfg.workTapePos i (p - s) i) = _
    rw [Function.update_self, hw]
  have hstep : ∀ s : ℕ, (s : ℤ) ≤ p →
      (retLeft i).step (retCfg i cfg p s) = retCfg i cfg p (s + 1) := by
    intro s hs
    have hsome : ((retCfg i cfg p s).workTapeSymbols i).isSome = true := by
      rw [hsym s, tapeOf_of_lt w _ (by omega) (by omega)]
      rfl
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if ((retCfg i cfg p s).workTapeSymbols i).isSome = true then some () else none) =
        some ()
      rw [hsome, ite_eq_left rfl]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos i (p - s) j +
          ((if j = i then (if ((retCfg i cfg p s).workTapeSymbols i).isSome then -1 else 1)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i (p - (s + 1 : ℕ)) j
      rw [hsome]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl, ite_eq_left rfl,
          SignType.coe_neg_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hhalt : (retLeft i).step (retCfg i cfg p (p + 1).toNat) =
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 } := by
    have hnone : ((retCfg i cfg p (p + 1).toNat).workTapeSymbols i).isSome = false := by
      rw [hsym _, tapeOf_neg w _ (by omega)]
      rfl
    rw [step_of_state _ _ () rfl]
    apply Cfg.ext
    · change (if ((retCfg i cfg p (p + 1).toNat).workTapeSymbols i).isSome = true
        then some () else none) = none
      rw [hnone, ite_eq_right (by simp)]
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change Function.update cfg.workTapePos i (p - ((p + 1).toNat : ℕ)) j +
          ((if j = i
            then (if ((retCfg i cfg p (p + 1).toNat).workTapeSymbols i).isSome then -1 else 1)
            else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i 0 j
      rw [hnone]
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self, ite_eq_left rfl,
          ite_eq_right (by simp), SignType.coe_one]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, ite_eq_right hj,
          SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hzero : retCfg i cfg p 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · change Function.update cfg.workTapePos i (p - ((0 : ℕ) : ℤ)) = cfg.workTapePos
      rw [show p - ((0 : ℕ) : ℤ) = cfg.workTapePos i by omega, Function.update_eq_self]
    · rfl
  rw [show (p + 2).toNat = (p + 1).toNat + 1 by omega]
  have key := RunsTo.ofFamily (retLeft i) (retCfg i cfg p) (p + 1).toNat B _
    (fun _ _ ↦ Option.some_ne_none ()) (fun s hs ↦ hstep s (by omega)) hhalt rfl
    (fun _ _ ↦ rfl)
    (fun s hs j ↦ update_workTapePos_bounds i hpos (p - s) (by omega) (by omega) j)
    (fun j ↦ update_workTapePos_bounds i hpos 0 (by omega) (by omega) j)
  rwa [hzero] at key

/-- {name}`returnTape` from cell {lit}`p` with {lit}`0 ≤ p ≤ w.length` runs
{lit}`p + 2` steps and parks the head. -/
theorem returnTape_runsTo {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Unit ⊕ Unit) input) (hq : cfg.state = some (returnTape i).q₀)
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w)
    (p : ℤ) (hp : cfg.workTapePos i = p) (hp0 : 0 ≤ p) (hpw : p ≤ w.length) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    RunsTo (returnTape i) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 }
      (p + 2).toNat B := by
  have hpB : p ≤ B := hp ▸ (hpos i).2
  have r₁ := moveLeft_runsTo i { cfg with state := some (moveLeft i).q₀ } rfl B hpos
    (by change (0 : ℤ) ≤ cfg.workTapePos i
        omega)
  have r₂ := retLeft_runsTo i
    { cfg with
      state := some (retLeft i).q₀
      workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i - 1) }
    rfl w hw (p - 1)
    (by change Function.update cfg.workTapePos i (cfg.workTapePos i - 1) i = p - 1
        rw [Function.update_self, hp])
    (by omega) (by omega) B
    (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)
  have hseq := r₁.seq r₂
  rw [← liftL_start (moveLeft i) (retLeft i) cfg hq,
    show 1 + (p - 1 + 2).toNat = (p + 2).toNat by omega] at hseq
  rw [show ({ cfg with state := none, workTapePos := Function.update cfg.workTapePos i 0 } :
      Cfg k Bool (Unit ⊕ Unit) input) =
    liftR (S₁ := Unit)
      { cfg with
        state := (none : Option Unit)
        workTapePos := Function.update
          (Function.update cfg.workTapePos i (cfg.workTapePos i - 1)) i 0 } from ?_]
  · exact hseq
  · apply Cfg.ext
    · rfl
    · rfl
    · rfl
    · funext j
      change Function.update cfg.workTapePos i 0 j =
        Function.update (Function.update cfg.workTapePos i (cfg.workTapePos i - 1)) i 0 j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]
    · rfl

end

end Geb.SizeBounded.Machine
