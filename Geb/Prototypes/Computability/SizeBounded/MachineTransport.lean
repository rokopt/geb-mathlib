/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/

module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic

meta import GebMeta -- shake: keep

set_option doc.verso true

/-!
# Renaming finite machine representations

Renaming a multi-tape machine's alphabet and states preserves its steps, output and
visited work tape cells. This allows machines built over convenient finite types to be
transported to the {lit}`Fin` types required by CSLib's complexity predicate.

## Main definitions

* {lit}`mapTM` renames a machine along alphabet and state equivalences.
* {lit}`Cfg.mapSym` renames its configurations.

## Main statements

* {lit}`step_mapSym` identifies the transitions before and after renaming.
* {lit}`ComputesInTimeAndSpace.mapTM` preserves both resource counts exactly.

## Implementation notes

These correspondence lemmas use the existing CSLib machine semantics. The initial proof
was drafted with Aristotle and adapted to this repository's toolchain and recursor discipline.
They supply representation transport, not composition or an algebra compiler. These
correspondence proofs use classical choice from the external library.

## Tags

Turing machine, simulation, time, space
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {S S' Q Q' : Type*}

/-- A convenient normal form for the symbol under the input head: the input head position is
shifted by one. Positions {lit}`0` and {lit}`input.length + 1` scan the blank cells
surrounding the input. -/
lemma Cfg.inputSymbol_eq_getElem? {input : List S} (c : Cfg k S Q input) :
    c.inputSymbol = if (c.inputPos : ℕ) = 0 then none else input[(c.inputPos : ℕ) - 1]? := by
  have hlt := c.inputPos.isLt
  unfold Cfg.inputSymbol
  by_cases h₁ : (c.inputPos : ℕ) = 0
  · rw [dite_eq_left (Fin.ext (by simpa using h₁)), ite_eq_left h₁]
  · rw [dite_eq_right (fun h => h₁ (by simpa using congrArg Fin.val h)), ite_eq_right h₁]
    by_cases h₂ : (c.inputPos : ℕ) = input.length + 1
    · rw [dite_eq_left h₂, List.getElem?_eq_none (by omega)]
    · rw [dite_eq_right h₂, List.getElem?_eq_getElem (by omega)]

/-- {name}`moveInputPos` depends only on the numerical head position, so it commutes
with casts along equalities of input lengths. -/
lemma moveInputPos_cast {n m : ℕ} (h : n + 2 = m + 2) (p : Fin (n + 2)) (s : SignType) :
    moveInputPos (Fin.cast h p) s = Fin.cast h (moveInputPos p s) := by
  have hnm : n = m := by omega
  subst hnm
  rfl

/-- Rename the alphabet and the states of a multi-tape Turing machine along equivalences. -/
def mapTM (tm : MultiTapeTM k S Q) (e : S ≃ S') (d : Q ≃ Q') : MultiTapeTM k S' Q' where
  q₀ := d tm.q₀
  tr q input work :=
    let o := tm.tr (d.symm q) (input.map e.symm) (fun i => (work i).map e.symm)
    { inputMove := o.inputMove
      workActions := fun i => (((o.workActions i).1).map (Option.map e), (o.workActions i).2)
      outS := o.outS.map e
      q' := o.q'.map d }

variable {input : List S} {tm : MultiTapeTM k S Q} {e : S ≃ S'} {d : Q ≃ Q'}

/-- Rename the alphabet and the states of a configuration along equivalences. -/
def Cfg.mapSym (e : S ≃ S') (d : Q ≃ Q') (c : Cfg k S Q input) : Cfg k S' Q' (input.map e) where
  state := c.state.map d
  inputPos := finCongr (by simp) c.inputPos
  workTapes i z := (c.workTapes i z).map e
  workTapePos := c.workTapePos

/-- The renamed configuration has the renamed state. -/
@[simp]
lemma Cfg.mapSym_state (c : Cfg k S Q input) : (c.mapSym e d).state = c.state.map d := rfl

/-- Renaming leaves work tape head positions unchanged. -/
@[simp]
lemma Cfg.mapSym_workTapePos (c : Cfg k S Q input) : (c.mapSym e d).workTapePos =
    c.workTapePos := rfl

/-- Renaming leaves the numerical input head position unchanged. -/
@[simp]
lemma Cfg.mapSym_inputPos_val (c : Cfg k S Q input) :
    ((c.mapSym e d).inputPos : ℕ) = (c.inputPos : ℕ) := rfl

/-- Renaming maps the symbol at each work tape cell. -/
@[simp]
lemma Cfg.mapSym_workTapes (c : Cfg k S Q input) (i : Fin k) (z : ℤ) :
    (c.mapSym e d).workTapes i z = (c.workTapes i z).map e := rfl

/-- The renamed input head reads the renamed symbol. -/
lemma Cfg.inputSymbol_mapSym (c : Cfg k S Q input) :
    (c.mapSym e d).inputSymbol = c.inputSymbol.map e := by
  rw [Cfg.inputSymbol_eq_getElem?, Cfg.inputSymbol_eq_getElem?]
  have hv : (((c.mapSym e d).inputPos) : ℕ) = (c.inputPos : ℕ) := rfl
  rw [hv]
  by_cases h₁ : (c.inputPos : ℕ) = 0
  · simp [h₁]
  · rw [ite_eq_right h₁, ite_eq_right h₁, List.getElem?_map]

/-- The renamed work tape heads read the renamed symbols. -/
lemma Cfg.workTapeSymbols_mapSym (c : Cfg k S Q input) (i : Fin k) :
    (c.mapSym e d).workTapeSymbols i = (c.workTapeSymbols i).map e := rfl

/-- The transition of the renamed machine, evaluated at a renamed configuration, is the renaming
of the transition of the original machine. -/
lemma tr_mapTM_mapSym (c : Cfg k S Q input) (q : Q) :
    (tm.mapTM e d).tr (d q) (c.mapSym e d).inputSymbol (c.mapSym e d).workTapeSymbols =
      { inputMove := (tm.tr q c.inputSymbol c.workTapeSymbols).inputMove,
        workActions := fun i =>
          ((((tm.tr q c.inputSymbol c.workTapeSymbols).workActions i).1).map (Option.map e),
            ((tm.tr q c.inputSymbol c.workTapeSymbols).workActions i).2),
        outS := ((tm.tr q c.inputSymbol c.workTapeSymbols).outS).map e,
        q' := ((tm.tr q c.inputSymbol c.workTapeSymbols).q').map d } := by
  have hin : (Option.map e.symm ((c.mapSym e d).inputSymbol)) = c.inputSymbol := by
    rw [Cfg.inputSymbol_mapSym]
    simp
  have hwork : (fun i => Option.map e.symm ((c.mapSym e d).workTapeSymbols i)) =
      c.workTapeSymbols := by
    funext i
    rw [Cfg.workTapeSymbols_mapSym]
    simp
  unfold mapTM
  simp only [Equiv.symm_apply_apply, hin, hwork]

/-- Renaming commutes with one machine step. -/
lemma step_mapSym (c : Cfg k S Q input) :
    (tm.mapTM e d).step (c.mapSym e d) = (tm.step c).mapSym e d := by
  rcases hst : c.state with _ | q
  · rw [step_of_halt (by simp [Cfg.mapSym_state, hst]), step_of_halt hst]
  · unfold step
    simp only [Cfg.mapSym_state, hst, Option.map_some, tr_mapTM_mapSym]
    refine Cfg.ext rfl ?_ ?_ rfl
    · simp only [Cfg.mapSym, finCongr_apply]
      exact moveInputPos_cast _ _ _
    funext i z
    rcases hw : ((tm.tr q c.inputSymbol c.workTapeSymbols).workActions i).1 with _ | s
    · simp only [hw, Option.map_none, Cfg.mapSym_workTapes]
    · simp only [hw, Option.map_some, Cfg.mapSym_workTapes]
      by_cases hz : z = c.workTapePos i
      · subst hz
        simp
      · change Function.update (fun z => Option.map e (c.workTapes i z)) (c.workTapePos i)
          (Option.map e s) z = _
        rw [Function.update_of_ne hz, Function.update_of_ne hz]

/-- Renaming commutes with any number of machine steps. -/
lemma configs_mapSym (c : Cfg k S Q input) (t : ℕ) :
    (tm.mapTM e d).configs (c.mapSym e d) t = (tm.configs c t).mapSym e d := by
  refine Nat.rec (by simp) (fun t ih ↦ ?_) t
  rw [configs_succ_eq_step', configs_succ_eq_step', ih, step_mapSym]

/-- Renaming preserves the initial configuration. -/
lemma initCfg_mapSym : (tm.mapTM e d).initCfg (input.map e) =
    (tm.initCfg input).mapSym e d := by
  refine Cfg.ext rfl (Fin.ext (by simp [Cfg.mapSym])) ?_ rfl
  funext i z
  simp [Cfg.mapSym]

/-- The renamed machine emits the renamed output symbol. -/
lemma outputSymbol_mapSym (c : Cfg k S Q input) :
    (tm.mapTM e d).outputSymbol (c.mapSym e d) = (tm.outputSymbol c).map e := by
  unfold outputSymbol
  rcases hst : c.state with _ | q
  · simp [Cfg.mapSym, hst]
  · simp only [Cfg.mapSym_state, hst, Option.map_some, tr_mapTM_mapSym]

/-- The renamed machine emits the renamed output word. -/
lemma outputString_mapSym (c : Cfg k S Q input) (t : ℕ) :
    (tm.mapTM e d).outputString (c.mapSym e d) t = (tm.outputString c t).map e := by
  refine Nat.rec (by simp [outputString]) (fun t ih ↦ ?_) t
  rw [outputString_succ, outputString_succ, ih, configs_mapSym, outputSymbol_mapSym]
  rcases h : tm.outputSymbol (tm.configs c t) with _ | s <;> simp

/-- Renaming preserves the count of visited work tape cells. -/
lemma spaceUsed_mapSym (c : Cfg k S Q input) (t : ℕ) :
    (tm.mapTM e d).spaceUsed (c.mapSym e d) t = tm.spaceUsed c t := by
  have hpos : ∀ (t' : ℕ) (i : Fin k),
      ((tm.mapTM e d).configs (c.mapSym e d) t').workTapePos i = (tm.configs c t').workTapePos i :=
    fun t' i => by rw [configs_mapSym]; rfl
  unfold spaceUsed spaceUsedByTape visitedByTapeHead
  exact Finset.sum_congr rfl (fun i _ => by simp only [hpos])

/-- Renaming the alphabet and the states of a machine preserves its computations. -/
lemma ComputesInTimeAndSpace.mapTM {i o : List S} {t s : ℕ}
    (h : tm.ComputesInTimeAndSpace i o t s) :
    (tm.mapTM e d).ComputesInTimeAndSpace (i.map e) (o.map e) t s := by
  obtain ⟨hhalt, hout, hspace⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [initCfg_mapSym, configs_mapSym]
    simp only [Cfg.mapSym_state, hhalt, Option.map_none]
  · rw [initCfg_mapSym, outputString_mapSym, hout]
  · rw [initCfg_mapSym, spaceUsed_mapSym, hspace]

/-- Renaming preserves a machine's function and its resource bounds. -/
lemma ComputesFunInTimeAndSpace.mapTM {IOSymbol : Type*}
    {f : List IOSymbol → List IOSymbol} {toMachineSymbol : IOSymbol ↪ S} {t s : ℕ → ℕ}
    (h : tm.ComputesFunInTimeAndSpace f toMachineSymbol t s) :
    (tm.mapTM e d).ComputesFunInTimeAndSpace f (toMachineSymbol.trans e.toEmbedding) t s := by
  intro input
  obtain ⟨t', ht, s', hs, hrun⟩ := h input
  refine ⟨t', ht, s', hs, ?_⟩
  simpa only [List.map_map, Function.Embedding.coe_trans, Equiv.coe_toEmbedding]
    using hrun.mapTM (e := e) (d := d)

/-- A machine over arbitrary finite types witnesses CSLib's complexity predicate. -/
theorem computableInTimeAndSpace_of_finite [Finite S] [Finite Q]
    {IOSymbol : Type*} {f : List IOSymbol → List IOSymbol}
    {toMachineSymbol : IOSymbol ↪ S} {t s : ℕ → ℕ}
    (h : tm.ComputesFunInTimeAndSpace f toMachineSymbol t s) :
    ComputableInTimeAndSpace f t s := by
  let := Fintype.ofFinite S
  let := Fintype.ofFinite Q
  exact ⟨k, Fintype.card S, Fintype.card Q, _, _,
    h.mapTM (e := Fintype.equivFin S) (d := Fintype.equivFin Q)⟩

end Turing.MultiTapeTM
