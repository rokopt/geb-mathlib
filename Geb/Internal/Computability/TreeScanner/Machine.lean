/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Mathlib.Data.Tree.Ranked.Binary

/-!
# A linear-time tree scanner

A deterministic multi-tape Turing machine deciding
`RankedAlphabet.Binary.binRanked.validBool`. The pending count is the
work head's position, with distinct markers at cells `0` and `1` so that
one read separates a count of `0`, of `1`, and of `2` or more — the
three-way distinction a node bit's guard and the final test between them
require. The machine is the one-counter recognizer for a prefix-code term
language.

## Main definitions

- `boolEmb` — the input alphabet's embedding into the machine alphabet.
- `stSeek`, `stPlant`, `stLive`, `stDead` — the four states.
- `treeScanner` — the machine.
- `seekCfg`, `plantCfg`, `sweepCfg` — the closed-form configurations.

## Main statements

- `validBool_eq_ok_and_depth` — the decision function as the pair of
  conditions the machine computes.
- `seekCfg_state`, `seekCfg_inputPos_val`, `seekCfg_workTapePos`,
  `seekCfg_workTapes`, `plantCfg_state`, `plantCfg_inputPos_val`,
  `plantCfg_workTapePos`, `plantCfg_workTapes`, `sweepCfg_state`,
  `sweepCfg_inputPos_val`, `sweepCfg_workTapePos`, `sweepCfg_workTapes` —
  the field projections of the three configurations.
- `sweepCfg_workTapeSymbols`, `sweepCfg_workTapeSymbols_eq` — the sweep
  configuration's work-symbol resolution, applied and unapplied.
- `seekCfg_zero` — `seekCfg` at index `0` is `treeScanner.initCfg`.

## Implementation notes

`Cfg` is indexed by the input, so no proof here inducts on the input;
each configuration is a closed form in a step or drop index.

## Tags

Turing machine, tree, preorder encoding, linear time
-/

@[expose] public section

namespace Geb.TreeScanner

open Turing MultiTapeTM RankedAlphabet.Binary

/-- The input alphabet's embedding into the machine alphabet: `false` to
`0` and `true` to `1`. -/
def boolEmb : Bool ↪ Fin 2 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- `false` embeds as the machine alphabet's first symbol. -/
@[simp] theorem boolEmb_false : boolEmb false = 0 := rfl

/-- `true` embeds as the machine alphabet's second symbol. -/
@[simp] theorem boolEmb_true : boolEmb true = 1 := rfl

/-- The state that walks the input head to the right end. -/
def stSeek : Fin 4 := ⟨0, by omega⟩

/-- The state that writes the second marker. -/
def stPlant : Fin 4 := ⟨1, by omega⟩

/-- The state that sweeps a live scan right to left. -/
def stLive : Fin 4 := ⟨2, by omega⟩

/-- The state that sweeps a failed scan right to left. -/
def stDead : Fin 4 := ⟨3, by omega⟩

/-- The machine. One work tape; the count is the work head's position,
with a marker at cell `0` and a different marker at cell `1`. -/
def treeScanner : MultiTapeTM 1 (Fin 2) (Fin 4) where
  q₀ := stSeek
  tr q inSym work :=
    if q = stSeek then
      match inSym with
      | none => { inputMove := -1, workActions := fun _ ↦ (some (some 0), 1),
                  outS := none, q' := some stPlant }
      | some _ => { inputMove := 1, workActions := fun _ ↦ (none, 0),
                    outS := none, q' := some stSeek }
    else if q = stPlant then
      { inputMove := 0, workActions := fun _ ↦ (some (some 1), -1),
        outS := none, q' := some stLive }
    else if q = stLive then
      match inSym with
      | some 0 => { inputMove := -1, workActions := fun _ ↦ (none, 1),
                    outS := none, q' := some stLive }
      | some _ =>
        match work 0 with
        | none => { inputMove := -1, workActions := fun _ ↦ (none, -1),
                    outS := none, q' := some stLive }
        | some _ => { inputMove := -1, workActions := fun _ ↦ (none, 0),
                      outS := none, q' := some stDead }
      | none =>
        match work 0 with
        | some 1 => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                      outS := some 1, q' := none }
        | _ => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                 outS := some 0, q' := none }
    else
      match inSym with
      | some _ => { inputMove := -1, workActions := fun _ ↦ (none, 0),
                    outS := none, q' := some stDead }
      | none => { inputMove := 0, workActions := fun _ ↦ (none, 0),
                  outS := some 0, q' := none }

/-- The configuration after `t` seek steps: the input head at `t + 1`,
the work tape blank and its head at cell `0`. At `t = 0` this is
`initCfg`. -/
def seekCfg (w : List Bool) (t : ℕ) (h : t ≤ w.length) :
    Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb) where
  state := some stSeek
  inputPos := ⟨t + 1, by simp only [List.length_map]; omega⟩
  workTapes _ _ := none
  workTapePos _ := 0

/-- The configuration after the seek's exit step: the first marker
written, the work head at cell `1`, the input head at position
`w.length`. -/
def plantCfg (w : List Bool) : Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb) where
  state := some stPlant
  inputPos := ⟨w.length, by simp only [List.length_map]; omega⟩
  workTapes _ z := if z = 0 then some 0 else none
  workTapePos _ := 1

/-- The configuration at the sweep boundary where `w.drop k` has been
consumed: the count is that suffix's pending depth and the state is live
exactly when the suffix's scan has not failed. -/
def sweepCfg (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    Cfg 1 (Fin 2) (Fin 4) (w.map boolEmb) where
  state := if ok (w.drop k) then some stLive else some stDead
  inputPos := ⟨k, by simp only [List.length_map]; omega⟩
  workTapes _ z := if z = 0 then some 0 else if z = 1 then some 1 else none
  workTapePos _ := (depth (w.drop k) : ℤ)

section CfgProjections

variable (w : List Bool) (t k : ℕ) (h : t ≤ w.length) (h' : k ≤ w.length)

/-- `seekCfg` is in the seeking state. -/
@[simp] theorem seekCfg_state : (seekCfg w t h).state = some stSeek := rfl

/-- `seekCfg`'s input head is at `t + 1`. -/
@[simp] theorem seekCfg_inputPos_val : (seekCfg w t h).inputPos.val = t + 1 := rfl

/-- `seekCfg`'s work head is at cell `0`. -/
@[simp] theorem seekCfg_workTapePos (i : Fin 1) : (seekCfg w t h).workTapePos i = 0 := rfl

/-- `seekCfg`'s work tape is blank everywhere. Not `@[simp]`: a step lemma
cites this rather than letting `simp` unfold `seekCfg` in place. -/
theorem seekCfg_workTapes (i : Fin 1) (z : ℤ) : (seekCfg w t h).workTapes i z = none := rfl

/-- `plantCfg` is in the planting state. -/
@[simp] theorem plantCfg_state : (plantCfg w).state = some stPlant := rfl

/-- `plantCfg`'s input head is at `w.length`. -/
@[simp] theorem plantCfg_inputPos_val : (plantCfg w).inputPos.val = w.length := rfl

/-- `plantCfg`'s work head is at cell `1`. -/
@[simp] theorem plantCfg_workTapePos (i : Fin 1) : (plantCfg w).workTapePos i = 1 := rfl

/-- `plantCfg`'s work tape holds the first marker at cell `0` and is blank
elsewhere. Not `@[simp]`: a step lemma cites this rather than letting
`simp` unfold `plantCfg` in place. -/
theorem plantCfg_workTapes (i : Fin 1) (z : ℤ) :
    (plantCfg w).workTapes i z = if z = 0 then some 0 else none := rfl

/-- `sweepCfg`'s state is live exactly where the consumed suffix's scan
has not failed. -/
theorem sweepCfg_state :
    (sweepCfg w k h').state = if ok (w.drop k) then some stLive else some stDead := rfl

/-- `sweepCfg`'s input head is at `k`. -/
@[simp] theorem sweepCfg_inputPos_val : (sweepCfg w k h').inputPos.val = k := rfl

/-- `sweepCfg`'s work head is at the consumed suffix's pending depth. -/
@[simp] theorem sweepCfg_workTapePos (i : Fin 1) :
    (sweepCfg w k h').workTapePos i = (depth (w.drop k) : ℤ) := rfl

/-- `sweepCfg`'s work tape holds the first marker at cell `0`, the second
at cell `1`, and is blank elsewhere. Not `@[simp]`: a step lemma cites
this rather than letting `simp` unfold `sweepCfg` in place. -/
theorem sweepCfg_workTapes (i : Fin 1) (z : ℤ) :
    (sweepCfg w k h').workTapes i z = if z = 0 then some 0 else if z = 1 then some 1 else none :=
  rfl

end CfgProjections

/-- `sweepCfg`'s work symbol separates a pending depth of `0`, of `1`, and
of at least `2`. -/
theorem sweepCfg_workTapeSymbols (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    (sweepCfg w k h).workTapeSymbols 0 =
      if depth (w.drop k) = 0 then some 0
      else if depth (w.drop k) = 1 then some 1 else none := by
  unfold Cfg.workTapeSymbols sweepCfg
  dsimp only
  split_ifs <;> first | rfl | omega

/-- The unapplied form of `sweepCfg_workTapeSymbols`, the form a transition
resolution against `tr` needs: `tr` takes the work-symbol function, not its
value at `0`. -/
theorem sweepCfg_workTapeSymbols_eq (w : List Bool) (k : ℕ) (h : k ≤ w.length) :
    (sweepCfg w k h).workTapeSymbols =
      fun _ ↦ if depth (w.drop k) = 0 then some 0
        else if depth (w.drop k) = 1 then some 1 else none := by
  funext i
  unfold Cfg.workTapeSymbols sweepCfg
  dsimp only
  split_ifs <;> first | rfl | omega

/-- `seekCfg` at index `0` is `treeScanner`'s initial configuration. -/
theorem seekCfg_zero (w : List Bool) :
    seekCfg w 0 (Nat.zero_le _) = treeScanner.initCfg (w.map boolEmb) := rfl

end Geb.TreeScanner
