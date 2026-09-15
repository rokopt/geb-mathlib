/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
import Geb.Prototypes.Computability.SizeBounded.Machine.Program

set_option doc.verso true

/-!
# Relabeling a machine's symbols and states

A {name}`Turing.MultiTapeTM` over the symbols {name}`Bool` and an arbitrary
state type is relabeled over the symbols {lit}`Fin 2` and the states
{lit}`Fin s` along an equivalence {lit}`State ≃ Fin s`: symbols travel by
{name}`finTwoEquiv` and states by the equivalence. The relabeled machine runs
the original one step for step, so
{name}`Turing.MultiTapeTM.configs`, {name}`Turing.MultiTapeTM.outputString`,
{name}`Turing.MultiTapeTM.initCfg` and {name}`Turing.MultiTapeTM.spaceUsed`
commute with the relabeling.

A configuration is indexed by the input it runs on, so a relabeled
configuration is indexed by the relabeled input; its head position is carried
across by {name}`Fin.cast` along {name}`List.length_map`, and
{name}`Turing.MultiTapeTM.moveInputPos` commutes with that cast.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.Cfg.inputSymbol`, which depends on
{lit}`Classical.choice`.

# Main definitions

* {lit}`bitEmb` — the two machine symbols as the image of the bits.
* {lit}`relabel` — the machine over {lit}`Fin 2` and {lit}`Fin s`.
* {lit}`relabelCfg` — the configuration of the relabeled machine.

# Main statements

* {lit}`step_relabel`, {lit}`configs_relabel` — the relabeled machine runs the
  original step for step.
* {lit}`outputSymbol_relabel`, {lit}`outputString_relabel` — the relabeled
  machine emits the relabeled output.
* {lit}`initCfg_relabel` — the relabeled initial configuration.
* {lit}`spaceUsed_relabel` — relabeling preserves the space used.

# Tags

Turing machine, relabeling, alphabet, states
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Bits as the two machine symbols. -/
@[expose] def bitEmb : Bool ↪ Fin 2 := finTwoEquiv.symm.toEmbedding

/-- The round trip of a bit through the two symbols. -/
theorem finTwoEquiv_bitEmb (b : Bool) : finTwoEquiv (bitEmb b) = b :=
  finTwoEquiv.apply_symm_apply b

/-- The round trip of an optional bit through the two symbols. -/
theorem map_map_bitEmb (o : Option Bool) : (o.map bitEmb).map finTwoEquiv = o := by
  cases o with
  | none => rfl
  | some b => exact congrArg some (finTwoEquiv_bitEmb b)

/-- Moving the input head commutes with the cast between the position types of
two inputs of equal length. -/
theorem moveInputPos_cast {n m : ℕ} (h : n + 2 = m + 2) (p : Fin (n + 2)) (d : SignType) :
    moveInputPos (Fin.cast h p) d = Fin.cast h (moveInputPos p d) := by
  have hnm : n = m := by omega
  subst hnm
  rfl

/-- A machine over bits and any state type, relabeled over the two symbols and
an initial segment of the naturals along an equivalence of its states. -/
@[expose] def relabel {k : ℕ} {State : Type} (tm : MultiTapeTM k Bool State) {s : ℕ}
    (eS : State ≃ Fin s) : MultiTapeTM k (Fin 2) (Fin s) where
  q₀ := eS tm.q₀
  tr q inp work :=
    let o := tm.tr (eS.symm q) (inp.map finTwoEquiv) fun i ↦ (work i).map finTwoEquiv
    { inputMove := o.inputMove
      workActions := fun i ↦ ((o.workActions i).1.map (Option.map bitEmb), (o.workActions i).2)
      outS := o.outS.map bitEmb
      q' := o.q'.map eS }

/-- A configuration relabeled. -/
@[expose] def relabelCfg {k : ℕ} {State : Type} {input : List Bool} {s : ℕ} (eS : State ≃ Fin s)
    (cfg : Cfg k Bool State input) : Cfg k (Fin 2) (Fin s) (input.map bitEmb) where
  state := cfg.state.map eS
  inputPos := Fin.cast (by rw [List.length_map]) cfg.inputPos
  workTapes := fun i z ↦ (cfg.workTapes i z).map bitEmb
  workTapePos := cfg.workTapePos

/-- The symbol under the input head of a relabeled configuration. -/
theorem inputSymbol_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) :
    (relabelCfg eS cfg).inputSymbol = cfg.inputSymbol.map bitEmb := by
  have hval : (relabelCfg eS cfg).inputPos.val = cfg.inputPos.val := rfl
  have hlen : (input.map bitEmb).length = input.length := List.length_map ..
  have h0 : ((relabelCfg eS cfg).inputPos = 0) ↔ (cfg.inputPos = 0) := by
    rw [Fin.ext_iff, Fin.ext_iff, hval]
    simp
  have h1 : ((relabelCfg eS cfg).inputPos.val = (input.map bitEmb).length + 1)
      ↔ (cfg.inputPos.val = input.length + 1) := by
    rw [hval, hlen]
  unfold Cfg.inputSymbol
  simp only [h0, h1]
  by_cases hz : cfg.inputPos = 0
  · simp [hz]
  · by_cases he : cfg.inputPos.val = input.length + 1
    · simp [hz, he]
    · simp only [hz, he, dite_false]
      simp only [hval, List.getElem_map, Option.map_some]

/-- The symbols under the work tape heads of a relabeled configuration. -/
theorem workTapeSymbols_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) (i : Fin k) :
    (relabelCfg eS cfg).workTapeSymbols i = (cfg.workTapeSymbols i).map bitEmb := rfl

/-- The relabeled machine steps the relabeled configuration. -/
theorem step_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (tm : MultiTapeTM k Bool State) (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) :
    (relabel tm eS).step (relabelCfg eS cfg) = relabelCfg eS (tm.step cfg) := by
  cases hq : cfg.state with
  | none =>
    have hn : (relabelCfg eS cfg).state = none := congrArg (Option.map (⇑eS)) hq
    rw [step_of_halt hn, step_of_halt hq]
  | some q =>
    have hs : (relabelCfg eS cfg).state = some (eS q) := congrArg (Option.map (⇑eS)) hq
    have hinp : Option.map finTwoEquiv (relabelCfg eS cfg).inputSymbol = cfg.inputSymbol := by
      rw [inputSymbol_relabel]
      exact map_map_bitEmb _
    have hwork : (fun i ↦ Option.map finTwoEquiv ((relabelCfg eS cfg).workTapeSymbols i))
        = cfg.workTapeSymbols := by
      funext i
      rw [workTapeSymbols_relabel]
      exact map_map_bitEmb _
    rw [step_of_state _ _ (eS q) hs, step_of_state _ _ q hq]
    simp only [relabel, Equiv.symm_apply_apply, hinp, hwork]
    generalize tm.tr q cfg.inputSymbol cfg.workTapeSymbols = o
    simp only [relabelCfg]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_cast (by rw [List.length_map]) cfg.inputPos _
    · funext i z
      dsimp only
      cases hw : (o.workActions i).1 with
      | none => rfl
      | some c =>
        simp only [Option.map_some]
        rw [Function.update_apply, Function.update_apply, apply_ite (Option.map (⇑bitEmb))]
    · rfl

/-- The relabeled machine's configuration sequence. -/
theorem configs_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (tm : MultiTapeTM k Bool State) (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) (t : ℕ) :
    (relabel tm eS).configs (relabelCfg eS cfg) t = relabelCfg eS (tm.configs cfg t) :=
  Nat.rec (by rw [configs_zero, configs_zero])
    (fun t ih ↦ by rw [configs_succ_eq_step', ih, step_relabel, configs_succ_eq_step']) t

/-- The symbol the relabeled machine emits in one step. -/
theorem outputSymbol_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (tm : MultiTapeTM k Bool State) (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) :
    (relabel tm eS).outputSymbol (relabelCfg eS cfg) = (tm.outputSymbol cfg).map bitEmb := by
  cases hq : cfg.state with
  | none =>
    have hn : (relabelCfg eS cfg).state = none := congrArg (Option.map (⇑eS)) hq
    rw [outputSymbol_of_halt hn, outputSymbol_of_halt hq]
    rfl
  | some q =>
    have hs : (relabelCfg eS cfg).state = some (eS q) := congrArg (Option.map (⇑eS)) hq
    have hinp : Option.map finTwoEquiv (relabelCfg eS cfg).inputSymbol = cfg.inputSymbol := by
      rw [inputSymbol_relabel]
      exact map_map_bitEmb _
    have hwork : (fun i ↦ Option.map finTwoEquiv ((relabelCfg eS cfg).workTapeSymbols i))
        = cfg.workTapeSymbols := by
      funext i
      rw [workTapeSymbols_relabel]
      exact map_map_bitEmb _
    unfold outputSymbol
    rw [hs, hq]
    simp only [relabel, Equiv.symm_apply_apply, hinp, hwork]

/-- The string the relabeled machine emits. -/
theorem outputString_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (tm : MultiTapeTM k Bool State) (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) (t : ℕ) :
    (relabel tm eS).outputString (relabelCfg eS cfg) t = (tm.outputString cfg t).map bitEmb :=
  Nat.rec (by simp [outputString])
    (fun t ih ↦ by
      rw [outputString_succ, outputString_succ, ih, List.map_append, configs_relabel,
        outputSymbol_relabel, Option.toList_map]) t

/-- The relabeled machine's initial configuration. -/
theorem initCfg_relabel {k : ℕ} {State : Type} {s : ℕ} (tm : MultiTapeTM k Bool State)
    (eS : State ≃ Fin s) (input : List Bool) :
    (relabel tm eS).initCfg (input.map bitEmb) = relabelCfg eS (tm.initCfg input) := by
  apply Cfg.ext
  · rfl
  · apply Fin.ext
    simp [relabelCfg]
  · rfl
  · rfl

/-- Relabeling preserves the space used. -/
theorem spaceUsed_relabel {k : ℕ} {State : Type} {input : List Bool} {s : ℕ}
    (tm : MultiTapeTM k Bool State) (eS : State ≃ Fin s) (cfg : Cfg k Bool State input) (t : ℕ) :
    (relabel tm eS).spaceUsed (relabelCfg eS cfg) t = tm.spaceUsed cfg t := by
  unfold spaceUsed spaceUsedByTape visitedByTapeHead
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hf : (fun t' ↦ ((relabel tm eS).configs (relabelCfg eS cfg) t').workTapePos i)
      = fun t' ↦ (tm.configs cfg t').workTapePos i :=
    funext fun t' ↦ by
      rw [configs_relabel]
      rfl
  exact congrArg Finset.card (by rw [hf])

end

end Geb.SizeBounded.Machine
