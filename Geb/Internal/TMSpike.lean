/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas

/-!
# Prototype of a first concrete `MultiTapeTM`

Not library content: committed for the record and removed once the
tree-scanner machine lands. Measures what proving anything about
`Turing.MultiTapeTM` costs, at two machines: `haltNow`, halting on its
first step with no work tapes, and `copyIn`, copying its input onto a
work tape and to the output.

## Main definitions

* `Turing.haltNow` — the machine halting on its first step, emitting one
  symbol, using no work tapes.
* `Turing.boolEmb` — the embedding of the input alphabet into the machine
  alphabet.
* `Turing.copyIn` — the machine copying its input onto work tape `0` and
  to the output, halting when the input head runs off the right end.
* `Turing.copyCfg` — the closed form of `copyIn`'s configuration after `t`
  steps.
* `Turing.inputSymbolCF`, `Turing.stepCF` — choice-free reimplementations
  of `Turing.MultiTapeTM.Cfg.inputSymbol` and `Turing.MultiTapeTM.step`,
  locating the root of the axiom taint.

## Main statements

* `Turing.haltNow_computes` — `haltNow` computes the constant function
  `fun _ ↦ [true]` in one step and no space.
* `Turing.copyIn_computes` — `copyIn` computes the identity, halting one
  step after its last input symbol, in space bounded by
  `Turing.MultiTapeTM.spaceUsed`.
* `Turing.id_computable` — the identity on words is
  `Turing.MultiTapeTM.ComputableInTimeAndSpace` in linear time and linear
  space.

## Tags

Turing machine, multi-tape, prototype, axiom measurement
-/

@[expose] public section

-- The linters that make an imprecise `simp` set an error are off in this
-- prototype, which does not measure the cost of making every `simp` set
-- precise.
set_option linter.unusedSimpArgs false

namespace Turing

open MultiTapeTM

/-- The machine that halts on its first step, emitting one symbol. -/
def haltNow : MultiTapeTM 0 (Fin 2) (Fin 1) where
  q₀ := 0
  tr _ _ _ :=
    { inputMove := 0
      workActions := fun i ↦ i.elim0
      outS := some 1
      q' := none }

/-- `haltNow` halts at step one, having emitted `[1]`, using no space. -/
theorem haltNow_computes (input : List (Fin 2)) :
    ComputesInTimeAndSpace haltNow input [1] 1 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [configs_succ_eq_step']
    rfl
  · rw [outputString_succ]
    rfl
  · exact spaceUsed_zero_tapes_eq_zero _ _ rfl

/-- The embedding of the input alphabet into the machine alphabet. -/
def boolEmb : Bool ↪ Fin 2 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- The constant function `fun _ ↦ [true]` is computable in one step and no
space. -/
theorem const_computable :
    ComputableInTimeAndSpace (fun _ : List Bool ↦ [true]) (fun _ ↦ 1) (fun _ ↦ 0) :=
  ⟨0, 2, 1, boolEmb, haltNow, fun _ ↦ ⟨1, le_refl _, 0, le_refl _, haltNow_computes _⟩⟩

/-- The halting conjunct alone. -/
theorem haltNow_halts (input : List (Fin 2)) :
    (haltNow.configs (haltNow.initCfg input) 1).state = none := by
  rw [configs_succ_eq_step']
  rfl

/-- The output conjunct alone. -/
theorem haltNow_output (input : List (Fin 2)) :
    haltNow.outputString (haltNow.initCfg input) 1 = [1] := by
  rw [outputString_succ]
  rfl

/-- The space conjunct alone. -/
theorem haltNow_space (input : List (Fin 2)) :
    haltNow.spaceUsed (haltNow.initCfg input) 1 = 0 :=
  spaceUsed_zero_tapes_eq_zero _ _ rfl

/-! ## `copyIn`: the copying machine -/

/-- The machine that copies its input onto work tape 0 and to the output,
halting when the input head runs off the right end. -/
def copyIn : MultiTapeTM 1 (Fin 2) (Fin 1) where
  q₀ := 0
  tr _ s _ :=
    match s with
    | none => { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }
    | some c =>
      { inputMove := 1, workActions := fun _ ↦ (some (some c), 1), outS := some c, q' := some 0 }

/-- The configuration `copyIn` is in after `t` steps, for `t` at most the input
length: `t` symbols copied, both heads advanced by `t`. -/
def copyCfg (input : List (Fin 2)) (t : ℕ) (ht : t ≤ input.length) :
    Cfg 1 (Fin 2) (Fin 1) input where
  state := some 0
  inputPos := ⟨t + 1, by omega⟩
  workTapes _ z := if h : 0 ≤ z ∧ z < (t : ℤ) then some (input[z.toNat]'(by omega)) else none
  workTapePos _ := (t : ℤ)

section CopyCfgProjections

variable {input : List (Fin 2)} {t : ℕ} {ht : t ≤ input.length}

/-- After `t` steps `copyIn` is still in its only state. -/
@[simp] theorem copyCfg_state : (copyCfg input t ht).state = some 0 := rfl

/-- After `t` steps the input head is at position `t + 1`. -/
@[simp] theorem copyCfg_inputPos_val : (copyCfg input t ht).inputPos.val = t + 1 := rfl

/-- After `t` steps the work-tape head is at position `t`, for every work
tape (there is exactly one). -/
@[simp] theorem copyCfg_workTapePos (i : Fin 1) :
    (copyCfg input t ht).workTapePos i = (t : ℤ) := rfl

/-- After `t` steps the work tape holds the input's first `t` symbols, at
positions `0` to `t - 1`, and is blank elsewhere. Not `@[simp]`: a step
lemma cites this rather than letting `simp` unfold `copyCfg` in place. -/
theorem copyCfg_workTapes (i : Fin 1) (z : ℤ) :
    (copyCfg input t ht).workTapes i z =
      if h : 0 ≤ z ∧ z < (t : ℤ) then some (input[z.toNat]'(by omega)) else none := rfl

/-- After `t` steps, for `t` short of the input length, the input head reads
the symbol at position `t`. -/
@[simp] theorem copyCfg_inputSymbol (h : t < input.length) :
    (copyCfg input t (Nat.le_of_lt h)).inputSymbol = some input[t] :=
  inputSymbolInner t (by simp; omega) h

end CopyCfgProjections

/-- One step of `copyIn` from the closed form advances it by one. -/
theorem copyIn_step (input : List (Fin 2)) (t : ℕ) (h : t < input.length) :
    copyIn.step (copyCfg input t (Nat.le_of_lt h)) = copyCfg input (t + 1) h := by
  have hpos : moveInputPos (copyCfg input t (Nat.le_of_lt h)).inputPos SignType.pos =
      (copyCfg input (t + 1) h).inputPos := by
    rw [moveInputPos_pos_of_ne_right _ (by simp; omega)]
    apply Fin.ext
    simp
  have htape : ∀ i : Fin 1,
      Function.update ((copyCfg input t (Nat.le_of_lt h)).workTapes i) (t : ℤ)
          (some input[t]) = (copyCfg input (t + 1) h).workTapes i := by
    intro i
    funext z
    rw [Function.update_apply, copyCfg_workTapes, copyCfg_workTapes]
    split_ifs with h1 h2 h3 h4 <;>
      first
        | rfl
        | omega
        | (subst h1; simp)
  unfold step
  simp only [copyCfg_state, copyCfg_inputSymbol h, copyCfg_workTapePos, copyIn]
  refine Cfg.ext ?_ ?_ ?_ ?_ <;> dsimp only
  · rfl
  · exact hpos
  · funext i
    exact htape i
  · funext i
    rfl

/-- The closed form of `copyIn`'s configuration at every step up to the input
length. Driven by `Nat.rec`, since `Cfg` is indexed by `input` and so admits no
induction on the input. -/
theorem copyIn_configs (input : List (Fin 2)) :
    ∀ t, (ht : t ≤ input.length) →
      copyIn.configs (copyIn.initCfg input) t = copyCfg input t ht := by
  refine Nat.rec ?_ ?_
  · intro _
    rw [configs_zero]
    ext <;> simp [copyCfg, copyIn]
  · intro t ih ht
    rw [configs_succ_eq_step', ih (by omega), copyIn_step input t (by omega)]

/-- `copyIn`'s output after three steps on `[0, 1]` is `[0, 1]`. Closed by
`decide`: a concrete machine's output reduces in the kernel. The same
assertion by `#guard` fails at elaboration, with "Invalid `meta`
definition, `initCfg` is not accessible here"; the test mirror asserts by
`decide` instead. -/
theorem copyIn_outputString_zero_one :
    copyIn.outputString (copyIn.initCfg [0, 1]) 3 = [0, 1] := by decide

/-- At the right end the input head reads blank. -/
theorem copyCfg_inputSymbol_end (input : List (Fin 2)) :
    (copyCfg input input.length (Nat.le_refl _)).inputSymbol = none := by
  unfold Cfg.inputSymbol
  split_ifs with ha hb
  · rfl
  · rfl
  · exact absurd (by simp) hb

/-- The symbol emitted at each copying step. -/
theorem copyIn_outputSymbol (input : List (Fin 2)) (t : ℕ) (h : t < input.length) :
    copyIn.outputSymbol (copyCfg input t (Nat.le_of_lt h)) = some input[t] := by
  unfold outputSymbol
  simp only [copyCfg_state, copyCfg_inputSymbol h, copyIn]

/-- Nothing is emitted once the input head is past the right end. -/
theorem copyIn_outputSymbol_end (input : List (Fin 2)) :
    copyIn.outputSymbol (copyCfg input input.length (Nat.le_refl _)) = none := by
  unfold outputSymbol
  simp only [copyCfg_state, copyCfg_inputSymbol_end, copyIn]

/-- The output after `t` steps is the input's first `t` symbols. -/
theorem copyIn_outputString (input : List (Fin 2)) :
    ∀ t, t ≤ input.length →
      copyIn.outputString (copyIn.initCfg input) t = input.take t := by
  refine Nat.rec ?_ ?_
  · intro _
    simp [outputString]
  · intro t ih ht
    rw [outputString_succ, ih (by omega), copyIn_configs input t (by omega),
      copyIn_outputSymbol input t (by omega), List.take_add_one,
      List.getElem?_eq_getElem (by omega)]

/-- `copyIn` halts one step after the last symbol, having output its input,
using space bounded linearly in the input length. -/
theorem copyIn_computes (input : List (Fin 2)) :
    ComputesInTimeAndSpace copyIn input input (input.length + 1)
      (copyIn.spaceUsed (copyIn.initCfg input) (input.length + 1)) := by
  have hcfg := copyIn_configs input input.length (Nat.le_refl _)
  refine ⟨?_, ?_, rfl⟩
  · rw [configs_succ_eq_step', hcfg]
    unfold step
    simp only [copyCfg_state, copyCfg_inputSymbol_end, copyIn]
  · rw [outputString_succ, copyIn_outputString input input.length (Nat.le_refl _), hcfg,
      copyIn_outputSymbol_end]
    simp

/-- The identity on words is computable in linear time and linear space. The
space bound is not computed: `spaceUsed_linear` derives it from the time bound. -/
theorem id_computable :
    ComputableInTimeAndSpace (fun w : List Bool ↦ w) (fun n ↦ n + 1) (fun n ↦ n + 2) := by
  refine ⟨1, 2, 1, boolEmb, copyIn, fun input ↦ ?_⟩
  have h := copyIn_computes (List.map boolEmb input)
  rw [List.length_map] at h
  refine ⟨input.length + 1, Nat.le_refl _,
    copyIn.spaceUsed (copyIn.initCfg (List.map boolEmb input)) (input.length + 1), ?_, h⟩
  exact le_trans (spaceUsed_linear _ _) (by simp)

#print axioms copyIn_computes
#print axioms id_computable

/-- A choice-free reimplementation of `Cfg.inputSymbol`: the same definition
with the `by grind` bound replaced. Locates the taint. -/
def inputSymbolCF {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (cfg : Cfg k Symbol State input) : Option Symbol :=
  if h₁ : cfg.inputPos.val = 0 then none
  else if h₂ : cfg.inputPos.val = input.length + 1 then none
  else input[cfg.inputPos.val - 1]'(by have := cfg.inputPos.isLt; omega)

/-- A choice-free clone of `step`, differing only in calling `inputSymbolCF`.
If this measures clean, `Cfg.inputSymbol` is the sole root of the taint. -/
def stepCF {k : ℕ} {Symbol State : Type} {input : List Symbol}
    (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State input :=
  match cfg.state with
  | none => cfg
  | some q =>
    let out := tm.tr q (inputSymbolCF cfg) cfg.workTapeSymbols
    { state := out.q'
      inputPos := moveInputPos cfg.inputPos out.inputMove
      workTapes i := match (out.workActions i).1 with
        | none => cfg.workTapes i
        | some s => Function.update (cfg.workTapes i) (cfg.workTapePos i) s
      workTapePos i := (cfg.workTapePos i) + (out.workActions i).2 }

/-- The `DecidableEq ℤ` instance search actually selects in this closure —
`Finset.image` in `visitedByTapeHead` requires one. -/
def intDecEq : DecidableEq ℤ := inferInstance

-- Is a machine definition itself choice-free, or does the taint reach it?
#print axioms copyIn
#print axioms haltNow
#print axioms copyCfg
#print axioms Turing.MultiTapeTM
#print axioms Turing.MultiTapeTM.Cfg
#print axioms Turing.MultiTapeTM.inputSymbolInner
#print axioms intDecEq
#print axioms Finset.image
#print axioms Finset.card
#print axioms stepCF
#print axioms Turing.MultiTapeTM.Cfg.workTapeSymbols
#print axioms inputSymbolCF
#print axioms Function.update
#print axioms Turing.MultiTapeTM.configs
#print axioms haltNow_halts
#print axioms haltNow_output
#print axioms haltNow_space
#print axioms haltNow_computes
#print axioms const_computable
#print axioms boolEmb
#print axioms Turing.MultiTapeTM.configs_succ_eq_step'
#print axioms Turing.MultiTapeTM.outputString_succ
#print axioms Turing.MultiTapeTM.spaceUsed_zero_tapes_eq_zero
#print axioms Turing.MultiTapeTM.step
#print axioms Turing.MultiTapeTM.outputString
#print axioms Turing.MultiTapeTM.spaceUsed
#print axioms Turing.MultiTapeTM.visitedByTapeHead
#print axioms Turing.MultiTapeTM.moveInputPos
#print axioms Turing.MultiTapeTM.Cfg.inputSymbol

end Turing
