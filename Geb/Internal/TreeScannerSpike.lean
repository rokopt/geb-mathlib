/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# A two-state scanner spike

A two-state machine over one work tape carrying two markers, with a head
position that is an opaque function of the step. It measures what the
tree scanner's proofs will cost before they are written.

## Main definitions

- `spikeTM` — the two-state machine.
- `spikeEmb` — the embedding of the input alphabet into the machine
  alphabet.
- `spikeCfg` — the closed-form configuration at an opaque count.
- `spikeSeekCfg` — the blank-taped family, whose index-zero member is
  written in the form the initial configuration takes.
- `spikeCondCfg`, `spikeCondNext` — a configuration whose state field is an
  `ite` on an opaque decidable predicate, and the configuration it steps
  to.

## Main statements

- `spikeTM_tr_spikeA`, `spikeTM_tr_spikeB_leaf`, `spikeTM_tr_spikeB_node`,
  `spikeTM_tr_spikeB_end`, `spikeTM_tr_spikeB_marker` — the transition
  resolved at each arm.
- `step_of_state` — a step from a known state, in the form that names `tr`.
- `spikeCfg_workSymbol` — the work symbol at an opaque count.
- `spikeCfg_step` — one step against the closed form.
- `spikeCfg_outputSymbol` — the same transition resolution, serving the
  emission.
- `spikeCondCfg_step` — one step against a conditional state field.
- `spikeCfg_configs` — a two-index recursion with a bundled motive.
- `spikeCfg_configs_add` — two phases composed by `configs_add` and
  `outputString_add_eq_append`.

## Implementation notes

`spikeTM`'s transition is an `ite` chain on state equality against named
definitions, wrapping a `match` on `Option (Fin 2)`. The chain reduces by
`rfl` and by no `simp` set: unfolded it presents as
`if ⟨1, spikeB._proof_2⟩ = ⟨0, spikeA._proof_2⟩ then …`. Every transition
resolution here is therefore a `rfl` after the arguments are rewritten to
literals, and every step lemma opens with `step_of_state` rather than
`unfold step`, which leaves the outer `match` on the state unreduced and
presents the transition as the raw projection `spikeTM.2`.

## Tags

Turing machine, spike
-/

@[expose] public section

namespace Geb

open Turing MultiTapeTM

/-- The first of two states. -/
def spikeA : Fin 2 := ⟨0, by omega⟩

/-- The second of two states. -/
def spikeB : Fin 2 := ⟨1, by omega⟩

/-- A two-state machine written in the shape `treeScanner` will use: an
`ite` chain on state equality against named definitions, wrapping a
`match` on `Option (Fin 2)` with one numeral pattern and one wildcard,
with one branch binding neither argument. -/
def spikeTM : MultiTapeTM 1 (Fin 2) (Fin 2) where
  q₀ := spikeA
  tr q inSym work :=
    if q = spikeA then
      { inputMove := 1, workActions := fun _ ↦ (some (some 0), 1),
        outS := none, q' := some spikeB }
    else
      match inSym with
      | some 0 => { inputMove := -1, workActions := fun _ ↦ (none, 1),
                    outS := none, q' := some spikeB }
      | some _ =>
        match work 0 with
        | none => { inputMove := -1, workActions := fun _ ↦ (none, -1),
                    outS := none, q' := some spikeB }
        | some _ => { inputMove := -1, workActions := fun _ ↦ (none, 0),
                      outS := none, q' := some spikeB }
      | none => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                  outS := some 1, q' := none }

/-- The embedding of the input alphabet into the machine alphabet. -/
def spikeEmb : Bool ↪ Fin 2 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- The embedding sends `true` to the machine's node symbol. -/
theorem spikeEmb_true : spikeEmb true = 1 := rfl

/-- The transition at the first state, with both the input symbol and the
work symbols left opaque: the arm binds neither. -/
theorem spikeTM_tr_spikeA (inSym : Option (Fin 2)) (work : Fin 1 → Option (Fin 2)) :
    spikeTM.tr spikeA inSym work =
      { inputMove := 1, workActions := fun _ ↦ (some (some 0), 1),
        outS := none, q' := some spikeB } := rfl

/-- The transition at the second state on an embedded `false`, with the work
symbols left opaque: the arm binds none of them. -/
theorem spikeTM_tr_spikeB_leaf (work : Fin 1 → Option (Fin 2)) :
    spikeTM.tr spikeB (some (spikeEmb false)) work =
      { inputMove := -1, workActions := fun _ ↦ (none, 1),
        outS := none, q' := some spikeB } := rfl

/-- The transition at the second state on an embedded `true` over a blank
work tape. -/
theorem spikeTM_tr_spikeB_node :
    spikeTM.tr spikeB (some (spikeEmb true)) (fun _ ↦ none) =
      { inputMove := -1, workActions := fun _ ↦ (none, -1),
        outS := none, q' := some spikeB } := rfl

/-- The transition at the second state at the input's left end, where the
machine emits and halts. -/
theorem spikeTM_tr_spikeB_end (work : Fin 1 → Option (Fin 2)) :
    spikeTM.tr spikeB none work =
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := some 1, q' := none } := rfl

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

/-- The transition's leftward movement, as an integer. -/
theorem signNegOne : ((-1 : SignType) : ℤ) = -1 := rfl

/-- The spike's configuration at an opaque count `d`, with the input head
indexed by the same variable. -/
def spikeCfg (input : List (Fin 2)) (d : ℕ) (h : d ≤ input.length) :
    Cfg 1 (Fin 2) (Fin 2) input where
  state := some spikeB
  inputPos := ⟨d, by omega⟩
  workTapes _ z := if z = 0 then some 0 else if z = 1 then some 1 else none
  workTapePos _ := (d : ℤ)

/-- The spike's blank-taped family, with the input head at `t + 1`. At
`t = 0` it is written in the form the initial configuration takes. -/
def spikeSeekCfg (input : List (Fin 2)) (t : ℕ) (h : t ≤ input.length) :
    Cfg 1 (Fin 2) (Fin 2) input where
  state := some spikeA
  inputPos := ⟨t + 1, by omega⟩
  workTapes _ _ := none
  workTapePos _ := 0

section SpikeCfgProjections

variable {input : List (Fin 2)} {d : ℕ} {h : d ≤ input.length}

/-- The closed form is in the second state. -/
@[simp] theorem spikeCfg_state : (spikeCfg input d h).state = some spikeB := rfl

/-- The input head is at the count. -/
@[simp] theorem spikeCfg_inputPos_val : (spikeCfg input d h).inputPos.val = d := rfl

/-- The work head is at the count, on the one work tape. -/
@[simp] theorem spikeCfg_workTapePos (i : Fin 1) :
    (spikeCfg input d h).workTapePos i = (d : ℤ) := rfl

/-- The work symbol under the head separates a count of `0`, a count of `1`
and a count of at least `2`. -/
theorem spikeCfg_workSymbol :
    (spikeCfg input d h).workTapeSymbols 0 =
      if d = 0 then some 0 else if d = 1 then some 1 else none := by
  unfold Cfg.workTapeSymbols spikeCfg
  dsimp only
  split_ifs <;> first | rfl | omega

/-- Above the second marker the work tape reads blank on every tape. -/
theorem spikeCfg_workTapeSymbols_blank (h2 : 2 ≤ d) :
    (spikeCfg input d h).workTapeSymbols = fun _ ↦ none := by
  funext i
  unfold Cfg.workTapeSymbols spikeCfg
  dsimp only
  split_ifs <;> first | rfl | omega

/-- At a count of at least one, short of the input's right end, the input
head reads the symbol one cell to the left of the count. -/
theorem spikeCfg_inputSymbol (hd : 1 ≤ d) :
    (spikeCfg input d h).inputSymbol = some (input[d - 1]'(by omega)) :=
  inputSymbolInner (d - 1) (by rw [spikeCfg_inputPos_val]; omega) (by omega)

/-- At a count of zero the input head is at the left end, where it reads
blank. This takes `Cfg.inputSymbol`'s first guard. -/
theorem spikeCfg_inputSymbol_zero (h0 : (0 : ℕ) ≤ input.length) :
    (spikeCfg input 0 h0).inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs with h₁ h₂
  · rfl
  · rfl
  · exact absurd (Fin.ext rfl) h₁

end SpikeCfgProjections

/-- The input symbol of a configuration over an embedded word, read back as
an embedded bit. -/
theorem spikeCfg_inputSymbol_map (w : List Bool) (d : ℕ) (hd : 1 ≤ d) (hlt : d ≤ w.length) :
    (spikeCfg (w.map spikeEmb) d (by rw [List.length_map]; omega)).inputSymbol =
      some (spikeEmb (w[d - 1]'(by omega))) := by
  rw [spikeCfg_inputSymbol hd, List.getElem_map]

/-- The transition at the closed form, above the second marker and at an
input bit of `true`. One resolution, cited by both `step` and
`outputSymbol`. -/
theorem spikeTM_tr_spikeCfg (input : List (Fin 2)) (d : ℕ) (h : d ≤ input.length)
    (h2 : 2 ≤ d) (hs : input[d - 1]'(by omega) = spikeEmb true) :
    spikeTM.tr spikeB (spikeCfg input d h).inputSymbol (spikeCfg input d h).workTapeSymbols =
      { inputMove := -1, workActions := fun _ ↦ (none, -1),
        outS := none, q' := some spikeB } := by
  rw [spikeCfg_inputSymbol (by omega : 1 ≤ d), hs, spikeCfg_workTapeSymbols_blank h2]
  exact spikeTM_tr_spikeB_node

/-- One step of the spike from the closed form decrements the count. -/
theorem spikeCfg_step (input : List (Fin 2)) (d : ℕ) (hi : d ≤ input.length)
    (h : 2 ≤ d) (hs : input[d - 1]'(by omega) = spikeEmb true) :
    spikeTM.step (spikeCfg input d hi) = spikeCfg input (d - 1) (by omega) := by
  have hpos : moveInputPos (spikeCfg input d hi).inputPos SignType.neg =
      (spikeCfg input (d - 1) (by omega : d - 1 ≤ input.length)).inputPos := by
    rw [moveInputPos_neg_of_ne_left _
      (Fin.ne_of_val_ne (by rw [spikeCfg_inputPos_val, Fin.val_zero]; omega))]
    exact Fin.ext rfl
  rw [step_of_state _ _ spikeB spikeCfg_state, spikeTM_tr_spikeCfg input d hi h hs]
  refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
  · rfl
  · exact hpos
  · funext i
    rfl
  · funext i
    rw [spikeCfg_workTapePos i, spikeCfg_workTapePos i, signNegOne]
    omega

/-- The spike emits nothing from the closed form above the second marker. -/
theorem spikeCfg_outputSymbol (input : List (Fin 2)) (d : ℕ) (hi : d ≤ input.length)
    (h : 2 ≤ d) (hs : input[d - 1]'(by omega) = spikeEmb true) :
    spikeTM.outputSymbol (spikeCfg input d hi) = none := by
  unfold outputSymbol
  simp only [spikeCfg_state]
  rw [spikeTM_tr_spikeCfg input d hi h hs]

/-- The transition at the second state on an embedded `true` over a marked
work cell: the third arm of the marker split. -/
theorem spikeTM_tr_spikeB_marker (s : Fin 2) :
    spikeTM.tr spikeB (some (spikeEmb true)) (fun _ ↦ some s) =
      { inputMove := -1, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some spikeB } := rfl

/-- A configuration whose state is chosen by an opaque decidable predicate,
with the work head on the first marker. -/
def spikeCondCfg (input : List (Fin 2)) (d : ℕ) (h : d ≤ input.length)
    (P : Prop) [Decidable P] : Cfg 1 (Fin 2) (Fin 2) input where
  state := if P then some spikeA else some spikeB
  inputPos := ⟨d, by omega⟩
  workTapes _ z := if z = 0 then some 0 else if z = 1 then some 1 else none
  workTapePos _ := 0

/-- The configuration `spikeCondCfg` steps to. Both arms reach the second
state, and the predicate survives in the two head positions. -/
def spikeCondNext (input : List (Fin 2)) (d : ℕ) (h : d ≤ input.length)
    (P : Prop) [Decidable P] : Cfg 1 (Fin 2) (Fin 2) input where
  state := some spikeB
  inputPos := if P then ⟨d + 1, by omega⟩ else ⟨d - 1, by omega⟩
  workTapes _ z := if z = 0 then some 0 else if z = 1 then some 1 else none
  workTapePos _ := if P then 1 else 0

section SpikeCondCfgProjections

variable {input : List (Fin 2)} {d : ℕ} {h : d ≤ input.length} {P : Prop} [Decidable P]

/-- The conditional configuration's input head is at the count. -/
@[simp] theorem spikeCondCfg_inputPos_val : (spikeCondCfg input d h P).inputPos.val = d := rfl

/-- The conditional configuration's work head is on the first marker. -/
@[simp] theorem spikeCondCfg_workTapePos (i : Fin 1) :
    (spikeCondCfg input d h P).workTapePos i = 0 := rfl

/-- The conditional configuration's work head reads the first marker. -/
theorem spikeCondCfg_workTapeSymbols :
    (spikeCondCfg input d h P).workTapeSymbols = fun _ ↦ some 0 := by
  funext i
  rfl

/-- The conditional configuration's input symbol, at a count of at least
one. -/
theorem spikeCondCfg_inputSymbol (hd : 1 ≤ d) :
    (spikeCondCfg input d h P).inputSymbol = some (input[d - 1]'(by omega)) :=
  inputSymbolInner (d - 1) (by rw [spikeCondCfg_inputPos_val]; omega) (by omega)

/-- The conditional configuration is in the first state where the predicate
holds. -/
theorem spikeCondCfg_state_pos (hP : P) :
    (spikeCondCfg input d h P).state = some spikeA := by
  unfold spikeCondCfg
  dsimp only
  rw [ite_eq_left hP]

/-- The conditional configuration is in the second state where the predicate
fails. -/
theorem spikeCondCfg_state_neg (hP : ¬P) :
    (spikeCondCfg input d h P).state = some spikeB := by
  unfold spikeCondCfg
  dsimp only
  rw [ite_eq_right hP]

end SpikeCondCfgProjections

/-- One step of the spike from the conditional configuration, in both
directions of the predicate. -/
theorem spikeCondCfg_step (input : List (Fin 2)) (d : ℕ) (hi : d ≤ input.length)
    (hd : 1 ≤ d) (hs : input[d - 1]'(by omega) = spikeEmb true)
    (P : Prop) [Decidable P] :
    spikeTM.step (spikeCondCfg input d hi P) = spikeCondNext input d hi P := by
  by_cases hP : P
  · rw [step_of_state _ _ spikeA (spikeCondCfg_state_pos hP), spikeTM_tr_spikeA]
    have hpos : moveInputPos (spikeCondCfg input d hi P).inputPos SignType.pos =
        (⟨d + 1, by omega⟩ : Fin (input.length + 2)) := by
      rw [moveInputPos_pos_of_ne_right _ (by rw [spikeCondCfg_inputPos_val]; omega)]
      exact Fin.ext rfl
    refine Cfg.ext ?_ ?_ ?_ ?_
    · rfl
    · dsimp only [spikeCondNext]
      rw [ite_eq_left hP]
      exact hpos
    · dsimp only [spikeCondNext]
      funext i
      rw [spikeCondCfg_workTapePos]
      exact Function.update_eq_self 0 _
    · dsimp only [spikeCondNext]
      funext i
      rw [ite_eq_left hP]
      rfl
  · rw [step_of_state _ _ spikeB (spikeCondCfg_state_neg hP), spikeCondCfg_inputSymbol hd, hs,
      spikeCondCfg_workTapeSymbols, spikeTM_tr_spikeB_marker]
    have hneg : moveInputPos (spikeCondCfg input d hi P).inputPos SignType.neg =
        (⟨d - 1, by omega⟩ : Fin (input.length + 2)) := by
      rw [moveInputPos_neg_of_ne_left _
        (Fin.ne_of_val_ne (by rw [spikeCondCfg_inputPos_val, Fin.val_zero]; omega))]
      exact Fin.ext rfl
    refine Cfg.ext ?_ ?_ ?_ ?_
    · rfl
    · dsimp only [spikeCondNext]
      rw [ite_eq_right hP]
      exact hneg
    · dsimp only [spikeCondNext]
      funext i
      rfl
    · dsimp only [spikeCondNext]
      funext i
      rw [ite_eq_right hP]
      rfl

/-- The closed form at every step short of the count, by a recursion whose
motive carries the linking equation between the step count and the family's
index. -/
theorem spikeCfg_configs (input : List (Fin 2)) (n : ℕ) (hi : n ≤ input.length)
    (hs : ∀ i, ∀ _ : i < n, input[i] = 1) :
    ∀ j, ∀ _ : j < n,
      spikeTM.configs (spikeCfg input n hi) j = spikeCfg input (n - j) (by omega) ∧
      spikeTM.outputString (spikeCfg input n hi) j = [] := by
  have key : ∀ j, ∀ k, ∀ _ : k + j = n, ∀ _ : 1 ≤ k,
      spikeTM.configs (spikeCfg input n hi) j = spikeCfg input k (by omega) ∧
      spikeTM.outputString (spikeCfg input n hi) j = [] := by
    refine Nat.rec ?_ ?_
    · intro k hk _
      have hkn : k = n := by omega
      subst hkn
      exact ⟨configs_zero, rfl⟩
    · intro j ih k hk hk1
      obtain ⟨hc, ho⟩ := ih (k + 1) (by omega) (by omega)
      have hbit : input[k + 1 - 1]'(by omega) = spikeEmb true := by
        rw [spikeEmb_true]
        exact hs k (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc,
          spikeCfg_step input (k + 1) (by omega) (by omega) hbit]
        congr 1
      · rw [outputString_succ, ho, hc,
          spikeCfg_outputSymbol input (k + 1) (by omega) (by omega) hbit]
        rfl
  intro j hj
  exact key j (n - j) (by omega) (by omega)

/-- Two phases of the spike's run, composed by `configs_add` and
`outputString_add_eq_append`. -/
theorem spikeCfg_configs_add (input : List (Fin 2)) (n : ℕ) (hi : n ≤ input.length)
    (hs : ∀ i, ∀ _ : i < n, input[i] = 1) (a b : ℕ) (hab : a + b < n) :
    spikeTM.configs (spikeCfg input n hi) (a + b) = spikeCfg input (n - (a + b)) (by omega) ∧
      spikeTM.outputString (spikeCfg input n hi) (a + b) = [] := by
  obtain ⟨hca, hoa⟩ := spikeCfg_configs input n hi hs a (by omega)
  obtain ⟨hcb, hob⟩ :=
    spikeCfg_configs input (n - a) (by omega) (fun i hi' ↦ hs i (by omega)) b (by omega)
  refine ⟨?_, ?_⟩
  · rw [configs_add, hca, hcb]
    congr 1
    omega
  · rw [outputString_add_eq_append, hoa, hca, hob]
    rfl

end Geb
