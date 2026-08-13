/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Internal.Computability.TreeScanner.Machine

/-!
# The tree scanner's transition, resolved

`treeScanner.tr` resolved at each configuration the machine reaches, one
statement per case of its transition table, together with the
input-symbol projections those resolutions consume and the emission facts
they yield.

`Turing.MultiTapeTM.step` and `Turing.MultiTapeTM.outputSymbol` apply
`tm.tr q cfg.inputSymbol cfg.workTapeSymbols` to identical arguments, so
one resolution per case serves both a step lemma and the matching
no-emission lemma, and the input symbol is resolved once rather than
twice.

## Main statements

- `step_of_state` — a step from a known state, in the form that names
  `tr`.
- `seekCfg_inputSymbol`, `seekCfg_inputSymbol_end`,
  `sweepCfg_inputSymbol_succ`, `sweepCfg_inputSymbol_zero` — the input
  symbol at each configuration.
- `tr_seek_mid`, `tr_seek_exit`, `tr_plant`, `tr_live_leaf`,
  `tr_live_node_deep`, `tr_live_node_shallow`, `tr_live_end_accept`,
  `tr_live_end_reject`, `tr_dead_mid`, `tr_dead_end` — the transition
  resolved at each case.
- `outputSymbol_seekCfg`, `outputSymbol_plantCfg`,
  `outputSymbol_sweepCfg_succ` — the configurations that emit nothing.
- `seekCfg_step`, `configs_seek` — the seek phase: one step against the
  closed form, and the configuration and the output at every step up to
  the input's length.
- `seekCfg_exit`, `plantCfg_step` — the two phase boundaries: the seek's
  exit step, which writes the first marker, and the planting step, which
  writes the second and enters the sweep.
- `sweepCfg_step`, `configs_sweep` — the sweep phase: one step against the
  closed form, matching the machine's state and work head to the scan's
  liveness and pending count one bit at a time, and the configuration and
  the output at every step down to the input's left end.
- `sweepCfg_zero_halts`, `outputSymbol_sweepCfg_zero` — the emitting step at
  the input's left end: the machine halts, and the symbol it emits is
  `RankedAlphabet.Binary.binRanked.validBool` at the input.
- `halts_at`, `outputString_eq` — the three phases composed: the machine
  halts after `2 * w.length + 3` steps having emitted that one symbol.

## Implementation notes

The module is admitted to `GebMeta.classicalAllowedModules`. Its subject
is the machine's behaviour under `Turing.MultiTapeTM.step`,
`Turing.MultiTapeTM.configs` and `Turing.MultiTapeTM.outputString`, and
its statements read the input through
`Turing.MultiTapeTM.Cfg.inputSymbol`; each of those depends on
`Classical.choice` through Cslib's `Cfg.inputSymbol` and
`inputSymbolInner`, so nothing here can be stated choice-free.

`treeScanner`'s transition is an `ite` chain on state equality against
named definitions wrapping a `match` on `Option (Fin 2)`. Unfolded the
chain presents as `if ⟨3, _⟩ = ⟨0, _⟩ then …`, which no `simp` set
resolves and `rfl` does, so each resolution rewrites its arguments to
literals and closes by `rfl`. Where a case reads the work symbol, an
equation collapsing the work tape to a constant function comes first:
rewriting by `sweepCfg_workTapeSymbols_eq` alone leaves an `ite` on an
opaque depth inside the argument of `tr`, and the transition does not
reduce.

A resolution lemma takes no liveness hypothesis. `tr` receives the state
as an explicit argument, so the resolution cannot consult liveness; the
state is supplied by the caller from `sweepCfg_state`.

## Tags

Turing machine, transition, tree, preorder encoding
-/

@[expose] public section

namespace Geb.TreeScanner

open Turing MultiTapeTM RankedAlphabet.Binary

/-- A machine's step from a known state, in the form that names `tr`. -/
theorem step_of_state {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (q : State) (hq : cfg.state = some q) :
    tm.step cfg =
      { state := (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).q'
        inputPos := moveInputPos cfg.inputPos
          (tm.tr q cfg.inputSymbol cfg.workTapeSymbols).inputMove
        workTapes := fun i ↦
          match ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).1 with
          | none => cfg.workTapes i
          | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
        workTapePos := fun i ↦ cfg.workTapePos i +
          ((tm.tr q cfg.inputSymbol cfg.workTapeSymbols).workActions i).2 } := by
  unfold step
  rw [hq]
  rfl

section InputSymbol

/-- Short of the input's right end the seek configuration reads the bit at
its own index. -/
theorem seekCfg_inputSymbol (w : List Bool) (t : ℕ) (h : t < w.length) :
    (seekCfg w t (Nat.le_of_lt h)).inputSymbol = some (boolEmb w[t]) := by
  have hi := inputSymbolInner (cfg := seekCfg w t (Nat.le_of_lt h)) t
    (by rw [seekCfg_inputPos_val]; omega) (by rw [List.length_map]; exact h)
  rw [hi, List.getElem_map]

/-- At the input's right end the seek configuration reads blank. This takes
`Turing.MultiTapeTM.Cfg.inputSymbol`'s second guard, an equality at `ℕ`. -/
theorem seekCfg_inputSymbol_end (w : List Bool) :
    (seekCfg w w.length (Nat.le_refl _)).inputSymbol = none := by
  have hend : ((seekCfg w w.length (Nat.le_refl _)).inputPos : ℕ) =
      (w.map boolEmb).length + 1 := by
    rw [seekCfg_inputPos_val, List.length_map]
  unfold Cfg.inputSymbol
  split_ifs <;> rfl

/-- At a positive index the sweep configuration reads the bit one cell to
the left of its index. -/
theorem sweepCfg_inputSymbol_succ (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    (sweepCfg w (k + 1) h).inputSymbol = some (boolEmb w[k]) := by
  have hi := inputSymbolInner (cfg := sweepCfg w (k + 1) h) k
    (by rw [sweepCfg_inputPos_val]; omega) (by rw [List.length_map]; omega)
  rw [hi, List.getElem_map]

/-- At the input's left end the sweep configuration reads blank. This takes
`Turing.MultiTapeTM.Cfg.inputSymbol`'s first guard, an equality at
`Fin (n + 2)`. -/
theorem sweepCfg_inputSymbol_zero (w : List Bool) :
    (sweepCfg w 0 (Nat.zero_le _)).inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs with h₁ h₂
  · rfl
  · rfl
  · exact absurd (Fin.ext rfl) h₁

end InputSymbol

section Transition

/-- Short of the input's right end the seek step advances the input head. -/
theorem tr_seek_mid (w : List Bool) (t : ℕ) (h : t < w.length) :
    treeScanner.tr stSeek (seekCfg w t (Nat.le_of_lt h)).inputSymbol
        (seekCfg w t (Nat.le_of_lt h)).workTapeSymbols =
      { inputMove := 1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stSeek } := by
  rw [seekCfg_inputSymbol w t h]
  rfl

/-- At the input's right end the seek step writes the first marker and
enters the planting state. -/
theorem tr_seek_exit (w : List Bool) :
    treeScanner.tr stSeek (seekCfg w w.length (Nat.le_refl _)).inputSymbol
        (seekCfg w w.length (Nat.le_refl _)).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (some (some 0), 1),
        outS := none, q' := some stPlant } := by
  rw [seekCfg_inputSymbol_end]
  rfl

/-- The planting step writes the second marker at cell `1`, returns the work
head to cell `0` and enters the live state. It is uniform in the input
symbol: its row of the transition table is a catch-all in the input
column. -/
theorem tr_plant (w : List Bool) :
    treeScanner.tr stPlant (plantCfg w).inputSymbol (plantCfg w).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (some (some 1), -1),
        outS := none, q' := some stLive } := rfl

/-- A live sweep over a leaf bit raises the pending count by one, moving
the work head right. -/
theorem tr_live_leaf (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length)
    (hbit : w[k] = false) :
    treeScanner.tr stLive (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, 1),
        outS := none, q' := some stLive } := by
  rw [sweepCfg_inputSymbol_succ, hbit]
  rfl

/-- A live sweep over a node bit with at least two pending consumes two and
pushes one, so it stays live and lowers the pending count by one, moving
the work head left. -/
theorem tr_live_node_deep (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length)
    (hbit : w[k] = true) (hd : 2 ≤ depth (w.drop (k + 1))) :
    treeScanner.tr stLive (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, -1),
        outS := none, q' := some stLive } := by
  have hw : (sweepCfg w (k + 1) h).workTapeSymbols = fun _ ↦ (none : Option (Fin 2)) := by
    rw [sweepCfg_workTapeSymbols_eq]
    funext i
    split_ifs <;> first | rfl | omega
  rw [sweepCfg_inputSymbol_succ, hbit, hw]
  rfl

/-- A live sweep over a node bit with fewer than two pending has met a node
with too few subterms to its right, and dies. -/
theorem tr_live_node_shallow (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length)
    (hbit : w[k] = true) (hd : depth (w.drop (k + 1)) < 2) :
    treeScanner.tr stLive (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stDead } := by
  rw [sweepCfg_inputSymbol_succ, hbit]
  by_cases hd0 : depth (w.drop (k + 1)) = 0
  · have hw : (sweepCfg w (k + 1) h).workTapeSymbols = fun _ ↦ (some 0 : Option (Fin 2)) := by
      rw [sweepCfg_workTapeSymbols_eq]
      funext i
      split_ifs
      rfl
    rw [hw]
    rfl
  · have hw : (sweepCfg w (k + 1) h).workTapeSymbols = fun _ ↦ (some 1 : Option (Fin 2)) := by
      rw [sweepCfg_workTapeSymbols_eq]
      funext i
      split_ifs <;> first | rfl | omega
    rw [hw]
    rfl

/-- A live sweep at the input's left end with exactly one pending emits
acceptance and halts. -/
theorem tr_live_end_accept (w : List Bool) (hd : depth w = 1) :
    treeScanner.tr stLive (sweepCfg w 0 (Nat.zero_le _)).inputSymbol
        (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 1, q' := none } := by
  have hw : (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      fun _ ↦ (some 1 : Option (Fin 2)) := by
    rw [sweepCfg_workTapeSymbols_eq, List.drop_zero]
    funext i
    split_ifs <;> first | rfl | omega
  rw [sweepCfg_inputSymbol_zero, hw]
  rfl

/-- A live sweep at the input's left end with a pending count other than one
emits rejection and halts. -/
theorem tr_live_end_reject (w : List Bool) (hd : depth w ≠ 1) :
    treeScanner.tr stLive (sweepCfg w 0 (Nat.zero_le _)).inputSymbol
        (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 0, q' := none } := by
  rw [sweepCfg_inputSymbol_zero]
  by_cases hd0 : depth w = 0
  · have hw : (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
        fun _ ↦ (some 0 : Option (Fin 2)) := by
      rw [sweepCfg_workTapeSymbols_eq, List.drop_zero]
      funext i
      split_ifs
      rfl
    rw [hw]
    rfl
  · have hw : (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
        fun _ ↦ (none : Option (Fin 2)) := by
      rw [sweepCfg_workTapeSymbols_eq, List.drop_zero]
      funext i
      split_ifs
      rfl
    rw [hw]
    rfl

/-- A dead sweep short of the input's left end walks on unchanged. -/
theorem tr_dead_mid (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    treeScanner.tr stDead (sweepCfg w (k + 1) h).inputSymbol
        (sweepCfg w (k + 1) h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stDead } := by
  rw [sweepCfg_inputSymbol_succ]
  rfl

/-- A dead sweep at the input's left end emits rejection and halts. -/
theorem tr_dead_end (w : List Bool) :
    treeScanner.tr stDead (sweepCfg w 0 (Nat.zero_le _)).inputSymbol
        (sweepCfg w 0 (Nat.zero_le _)).workTapeSymbols =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 0, q' := none } := by
  rw [sweepCfg_inputSymbol_zero]
  rfl

end Transition

section OutputSymbol

/-- The seek phase emits nothing, at its exit step as at every other. -/
theorem outputSymbol_seekCfg (w : List Bool) (t : ℕ) (h : t ≤ w.length) :
    treeScanner.outputSymbol (seekCfg w t h) = none := by
  unfold outputSymbol
  simp only [seekCfg_state]
  by_cases ht : t = w.length
  · subst ht
    rw [tr_seek_exit]
  · rw [tr_seek_mid w t (by omega)]

/-- The planting step emits nothing. -/
theorem outputSymbol_plantCfg (w : List Bool) :
    treeScanner.outputSymbol (plantCfg w) = none := by
  unfold outputSymbol
  simp only [plantCfg_state]
  rw [tr_plant]

/-- The sweep emits nothing short of the input's left end, live or dead. -/
theorem outputSymbol_sweepCfg_succ (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    treeScanner.outputSymbol (sweepCfg w (k + 1) h) = none := by
  unfold outputSymbol
  by_cases hok : ok (w.drop (k + 1)) = true
  · have hst : (sweepCfg w (k + 1) h).state = some stLive := by
      rw [sweepCfg_state, ite_eq_left hok]
    simp only [hst]
    cases hbit : w[k] with
    | false => rw [tr_live_leaf w k h hbit]
    | true =>
      by_cases hd : 2 ≤ depth (w.drop (k + 1))
      · rw [tr_live_node_deep w k h hbit hd]
      · rw [tr_live_node_shallow w k h hbit (by omega)]
  · have hst : (sweepCfg w (k + 1) h).state = some stDead := by
      rw [sweepCfg_state, ite_eq_right hok]
    simp only [hst]
    rw [tr_dead_mid w k h]

end OutputSymbol

section Seek

/-- Short of the input's right end one seek step advances the input head by
one cell and leaves the blank work tape and its head untouched. -/
theorem seekCfg_step (w : List Bool) (t : ℕ) (h : t + 1 ≤ w.length) :
    treeScanner.step (seekCfg w t (by omega)) = seekCfg w (t + 1) h := by
  have hpos : moveInputPos (seekCfg w t (Nat.le_of_lt h)).inputPos SignType.pos =
      (seekCfg w (t + 1) h).inputPos := by
    rw [moveInputPos_pos_of_ne_right _
      (by rw [seekCfg_inputPos_val, List.length_map]; omega)]
    exact Fin.ext rfl
  rw [step_of_state _ _ stSeek (seekCfg_state w t (Nat.le_of_lt h)), tr_seek_mid w t h]
  refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
  · rfl
  · exact hpos
  · funext i
    rfl
  · funext i
    rfl

/-- The seek phase's configuration and output at every step up to the
input's length: the closed form of `seekCfg`, and nothing emitted. Both
conjuncts run in one recursion, the output obligation being what the
composition across the phase boundary needs alongside the configuration. -/
theorem configs_seek (w : List Bool) :
    ∀ t, ∀ h : t ≤ w.length,
      treeScanner.configs (treeScanner.initCfg (w.map boolEmb)) t = seekCfg w t h ∧
      treeScanner.outputString (treeScanner.initCfg (w.map boolEmb)) t = [] := by
  refine Nat.rec ?_ ?_
  · intro _
    refine ⟨?_, rfl⟩
    rw [configs_zero, seekCfg_zero]
  · intro t ih h
    obtain ⟨hc, ho⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc]
      exact seekCfg_step w t h
    · rw [outputString_succ, ho, hc, outputSymbol_seekCfg]
      rfl

/-- At the input's right end the seek step writes the first marker at cell
`0`, moves the work head right to cell `1` and the input head left. -/
theorem seekCfg_exit (w : List Bool) :
    treeScanner.step (seekCfg w w.length (Nat.le_refl _)) = plantCfg w := by
  have hpos : moveInputPos (seekCfg w w.length (Nat.le_refl _)).inputPos SignType.neg =
      (plantCfg w).inputPos := by
    rw [moveInputPos_neg_of_ne_left _
      (by simp only [Ne, Fin.ext_iff, seekCfg_inputPos_val, Fin.val_zero]; omega)]
    exact Fin.ext (by simp only [seekCfg_inputPos_val, plantCfg_inputPos_val]; omega)
  rw [step_of_state _ _ stSeek (seekCfg_state w w.length (Nat.le_refl _)), tr_seek_exit]
  refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
  · rfl
  · exact hpos
  · funext i z
    rw [seekCfg_workTapePos, Function.update_apply, seekCfg_workTapes, plantCfg_workTapes]
  · funext i
    rfl

end Seek

section Plant

/-- The planting step writes the second marker at cell `1` and returns the
work head to cell `0`, leaving the input head where it stands. -/
theorem plantCfg_step (w : List Bool) :
    treeScanner.step (plantCfg w) = sweepCfg w w.length (Nat.le_refl _) := by
  have hdepth : depth ([] : List Bool) = 0 := rfl
  rw [step_of_state _ _ stPlant (plantCfg_state w), tr_plant]
  refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
  · rw [sweepCfg_state, List.drop_length]
    rfl
  · exact moveInputPos_zero _
  · funext i z
    rw [plantCfg_workTapePos, Function.update_apply, plantCfg_workTapes, sweepCfg_workTapes]
    split_ifs <;> first | rfl | omega
  · funext i
    rw [sweepCfg_workTapePos, List.drop_length, plantCfg_workTapePos, hdepth,
      SignType.coe_neg_one]
    omega

end Plant

section Sweep

/-- One sweep step consumes the bit to the input head's left: the state stays
live exactly where the scan extended by that bit stays live, and the work
head carries the extended scan's pending count. -/
theorem sweepCfg_step (w : List Bool) (k : ℕ) (h : k + 1 ≤ w.length) :
    treeScanner.step (sweepCfg w (k + 1) h) = sweepCfg w k (by omega) := by
  have hdrop : w.drop k = w[k] :: w.drop (k + 1) := List.drop_eq_getElem_cons (by omega)
  have hpos : moveInputPos (sweepCfg w (k + 1) h).inputPos SignType.neg =
      (sweepCfg w k (by omega : k ≤ w.length)).inputPos := by
    rw [moveInputPos_neg_of_ne_left _
      (by simp only [Ne, Fin.ext_iff, sweepCfg_inputPos_val, Fin.val_zero]; omega)]
    exact Fin.ext (by simp only [sweepCfg_inputPos_val]; omega)
  by_cases hok : ok (w.drop (k + 1)) = true
  · have hst : (sweepCfg w (k + 1) h).state = some stLive := by
      rw [sweepCfg_state, ite_eq_left hok]
    cases hbit : w[k] with
    | false =>
      have hokk : ok (w.drop k) = true := by
        rw [hdrop, hbit, ok_cons_false]
        exact hok
      have hdk : depth (w.drop k) = depth (w.drop (k + 1)) + 1 := by
        rw [hdrop, hbit, depth_cons_false_of_ok _ hok]
      rw [step_of_state _ _ stLive hst, tr_live_leaf w k h hbit]
      refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
      · rw [sweepCfg_state, ite_eq_left hokk]
      · exact hpos
      · funext i
        rfl
      · funext i
        rw [sweepCfg_workTapePos, sweepCfg_workTapePos, hdk, SignType.coe_one]
        omega
    | true =>
      by_cases hd : 2 ≤ depth (w.drop (k + 1))
      · have hokk : ok (w.drop k) = true := by
          rw [hdrop, hbit, ok_cons_true, hok, decide_eq_true hd]
          rfl
        have hdk : depth (w.drop k) = depth (w.drop (k + 1)) - 1 := by
          rw [hdrop, hbit]
          exact depth_cons_true_of_ok_of_two_le_depth _ hok hd
        rw [step_of_state _ _ stLive hst, tr_live_node_deep w k h hbit hd]
        refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
        · rw [sweepCfg_state, ite_eq_left hokk]
        · exact hpos
        · funext i
          rfl
        · funext i
          rw [sweepCfg_workTapePos, sweepCfg_workTapePos, hdk, SignType.coe_neg_one]
          omega
      · have hd2 : depth (w.drop (k + 1)) < 2 := by omega
        have hokk : ok (w.drop k) = false := by
          rw [hdrop, hbit, ok_cons_true, hok, decide_eq_false hd]
          rfl
        have hdk : depth (w.drop k) = depth (w.drop (k + 1)) := by
          rw [hdrop, hbit, depth, depth, RankedAlphabet.scanFinal_cons,
            scanStep_true_of_live_of_buf_nil_of_depth_lt_two _ hok
              (buf_scanFinal_eq_nil _) hd2]
        rw [step_of_state _ _ stLive hst, tr_live_node_shallow w k h hbit hd2]
        refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
        · rw [sweepCfg_state, hokk]
          rfl
        · exact hpos
        · funext i
          rfl
        · funext i
          rw [sweepCfg_workTapePos, sweepCfg_workTapePos, hdk, SignType.coe_zero]
          omega
  · rw [Bool.not_eq_true] at hok
    have hst : (sweepCfg w (k + 1) h).state = some stDead := by
      rw [sweepCfg_state, hok]
      rfl
    have hokk : ok (w.drop k) = false := by
      rw [hdrop, ok, RankedAlphabet.scanFinal_cons, scanStep_of_not_live _ _ hok]
      exact hok
    have hdk : depth (w.drop k) = depth (w.drop (k + 1)) := by
      rw [hdrop, depth, depth, RankedAlphabet.scanFinal_cons,
        scanStep_of_not_live _ _ hok]
    rw [step_of_state _ _ stDead hst, tr_dead_mid w k h]
    refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
    · rw [sweepCfg_state, hokk]
      rfl
    · exact hpos
    · funext i
      rfl
    · funext i
      rw [sweepCfg_workTapePos, sweepCfg_workTapePos, hdk, SignType.coe_zero]
      omega

/-- The sweep phase's configuration and output at every step down to the
input's left end: the closed form of `sweepCfg`, and nothing emitted. The
family descends in its index while the step count ascends, so the motive
carries the equation linking the two and nothing subtracts. Both conjuncts
run in one recursion, the output obligation being what the composition
across the phase boundary needs alongside the configuration. -/
theorem configs_sweep (w : List Bool) :
    ∀ j, ∀ k, ∀ h : k + j = w.length,
      treeScanner.configs (sweepCfg w w.length (Nat.le_refl _)) j =
          sweepCfg w k (by omega) ∧
        treeScanner.outputString (sweepCfg w w.length (Nat.le_refl _)) j = [] := by
  refine Nat.rec ?_ ?_
  · intro k hk
    have hkn : k = w.length := by omega
    subst hkn
    exact ⟨configs_zero, rfl⟩
  · intro j ih k hk
    obtain ⟨hc, ho⟩ := ih (k + 1) (by omega)
    refine ⟨?_, ?_⟩
    · rw [configs_succ_eq_step', hc]
      exact sweepCfg_step w k (by omega)
    · rw [outputString_succ, ho, hc, outputSymbol_sweepCfg_succ w k (by omega)]
      rfl

end Sweep

section Emission

/-- At the input's left end the machine halts, live or dead. -/
theorem sweepCfg_zero_halts (w : List Bool) :
    (treeScanner.step (sweepCfg w 0 (Nat.zero_le _))).state = none := by
  by_cases hok : ok w = true
  · have hst : (sweepCfg w 0 (Nat.zero_le _)).state = some stLive := by
      rw [sweepCfg_state, List.drop_zero, ite_eq_left hok]
    rw [step_of_state _ _ stLive hst]
    by_cases hd : depth w = 1
    · rw [tr_live_end_accept w hd]
    · rw [tr_live_end_reject w hd]
  · have hst : (sweepCfg w 0 (Nat.zero_le _)).state = some stDead := by
      rw [sweepCfg_state, List.drop_zero, ite_eq_right hok]
    rw [step_of_state _ _ stDead hst, tr_dead_end]

/-- The emitted symbol is the decision function's value: the machine's
end-of-input cases — dead, live with the second marker under the work head,
and live otherwise — are the cases of `ok w && depth w == 1`. -/
theorem outputSymbol_sweepCfg_zero (w : List Bool) :
    treeScanner.outputSymbol (sweepCfg w 0 (Nat.zero_le _)) =
      some (boolEmb (binRanked.validBool w)) := by
  rw [validBool_eq_ok_and_depth]
  unfold outputSymbol
  by_cases hok : ok w = true
  · have hst : (sweepCfg w 0 (Nat.zero_le _)).state = some stLive := by
      rw [sweepCfg_state, List.drop_zero, ite_eq_left hok]
    simp only [hst]
    by_cases hd : depth w = 1
    · rw [tr_live_end_accept w hd, hok, hd]
      rfl
    · rw [tr_live_end_reject w hd, hok, beq_eq_false_iff_ne.mpr hd]
      rfl
  · rw [Bool.not_eq_true] at hok
    have hst : (sweepCfg w 0 (Nat.zero_le _)).state = some stDead := by
      rw [sweepCfg_state, List.drop_zero, hok]
      rfl
    simp only [hst]
    rw [tr_dead_end, hok]
    rfl

/-- The machine halts after `2 * w.length + 3` steps: `w.length` seek steps,
the seek's exit step, the planting step, `w.length` sweep steps, and the
emitting step. -/
theorem halts_at (w : List Bool) :
    (treeScanner.configs (treeScanner.initCfg (w.map boolEmb))
      (2 * w.length + 3)).state = none := by
  rw [show 2 * w.length + 3 = w.length + 1 + 1 + w.length + 1 by omega,
    configs_succ_eq_step', configs_add, configs_succ_eq_step', configs_succ_eq_step',
    (configs_seek w w.length (Nat.le_refl _)).1, seekCfg_exit, plantCfg_step,
    (configs_sweep w w.length 0 (by omega)).1]
  exact sweepCfg_zero_halts w

/-- Over the same `2 * w.length + 3` steps the machine emits one symbol, the
decision function's value at the input. -/
theorem outputString_eq (w : List Bool) :
    treeScanner.outputString (treeScanner.initCfg (w.map boolEmb))
        (2 * w.length + 3) =
      [boolEmb (binRanked.validBool w)] := by
  have hcfg : treeScanner.configs (treeScanner.initCfg (w.map boolEmb)) (w.length + 1 + 1) =
      sweepCfg w w.length (Nat.le_refl _) := by
    rw [configs_succ_eq_step', configs_succ_eq_step',
      (configs_seek w w.length (Nat.le_refl _)).1, seekCfg_exit]
    exact plantCfg_step w
  rw [show 2 * w.length + 3 = w.length + 1 + 1 + w.length + 1 by omega, outputString_succ,
    outputString_add_eq_append, hcfg, configs_add, hcfg,
    (configs_sweep w w.length 0 (by omega)).2, (configs_sweep w w.length 0 (by omega)).1,
    outputSymbol_sweepCfg_zero, outputString_succ, outputString_succ, configs_succ_eq_step',
    (configs_seek w w.length (Nat.le_refl _)).1, (configs_seek w w.length (Nat.le_refl _)).2,
    seekCfg_exit, outputSymbol_seekCfg, outputSymbol_plantCfg]
  rfl

end Emission

end Geb.TreeScanner
