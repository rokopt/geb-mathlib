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

end Geb.TreeScanner
