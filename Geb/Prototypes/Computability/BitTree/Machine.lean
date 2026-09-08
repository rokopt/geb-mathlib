/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Scanner
public import Geb.Prototypes.Computability.TreeScanner.Machine

set_option doc.verso true

/-!
# A single-pass machine for binary trees with bitstring leaves

The input head advances once per bit. The work head stores the number of
pending subtrees; a marker at cell one detects completion of the last leaf.
Two initial steps position the work head and install the marker.

## Main definitions

* {lit}`unaryScanner` implements the fused structural and payload scan.
* {lit}`scanCfg` describes a configuration after a prefix has been consumed.

## Tags

binary tree, bitstring, Turing machine, recognizer
-/

@[expose] public section

namespace Geb.BitTree

open Turing MultiTapeTM
open Geb.TreeScanner (boolEmb)

/-- The scanner modes occupy the last five machine states. -/
def modeState : Mode → Fin 7
  | .tree => 2
  | .string => 3
  | .bit => 4
  | .done => 5
  | .dead => 6

/-- Consume one input bit, moving the counter head by the given displacement. -/
def consume (q : Fin 7) (d : SignType) : TransitionOut 1 (Fin 2) (Fin 7) where
  inputMove := 1
  workActions _ := (none, d)
  outS := none
  q' := some q

/-- A fused recognizer with one work tape and a unary pending-subtree counter. -/
def unaryScanner : MultiTapeTM 1 (Fin 2) (Fin 7) where
  q₀ := 0
  tr q input work :=
    if q = 0 then
      { inputMove := 0, workActions := fun _ ↦ (none, 1), outS := none, q' := some 1 }
    else if q = 1 then
      { inputMove := 0, workActions := fun _ ↦ (some (some 0), 0),
        outS := none, q' := some 2 }
    else match input with
      | none =>
        { inputMove := 0, workActions := fun _ ↦ (none, 0),
          outS := some (boolEmb (q == 5)), q' := none }
      | some b =>
        if q = 2 then
          if b = 0 then consume 3 0 else consume 2 1
        else if q = 3 then
          if b = 0 then consume (if work 0 = some 0 then 5 else 2) (-1)
          else consume 4 0
        else if q = 4 then consume 3 0
        else consume 6 0

/-- The configuration between the two initialization steps. -/
def plantCfg (w : List Bool) : Cfg 1 (Fin 2) (Fin 7) (w.map boolEmb) where
  state := some 1
  inputPos := 1
  workTapes _ _ := none
  workTapePos _ := 1

/-- A configuration at a prefix boundary, with its pure scanner state. -/
def scanCfg (w : List Bool) (t : ℕ) (h : t ≤ w.length) (s : State) :
    Cfg 1 (Fin 2) (Fin 7) (w.map boolEmb) where
  state := some (modeState s.1)
  inputPos := ⟨t + 1, by simp only [List.length_map]; omega⟩
  workTapes _ z := if z = 1 then some 0 else none
  workTapePos _ := s.2

/-- Fork tags increment the counter; string terminators decrement it. -/
def counterMove (m : Mode) (b : Bool) : SignType :=
  match m, b with
  | .tree, true => 1
  | .string, false => -1
  | _, _ => 0

/-- The transition table implements the pure scanner's finite control. -/
theorem tr_scan (m : Mode) (n : ℕ) (b : Bool) :
    unaryScanner.tr (modeState m) (some (boolEmb b))
        (fun _ ↦ if n = 1 then some 0 else none) =
      consume (modeState (step (m, n) b).1) (counterMove m b) := by
  have hf : boolEmb false = 0 := rfl
  have ht : boolEmb true = 1 := rfl
  cases m <;> cases b <;> by_cases h : n = 1 <;>
    simp [unaryScanner, modeState, step, finish, counterMove, hf, ht, h]

/-- The head displacement agrees with the natural-number counter on live states. -/
theorem counterMove_add (m : Mode) (n : ℕ) (b : Bool)
    (h : m = .string → 0 < n) :
    (n : ℤ) + (counterMove m b : ℤ) = ((step (m, n) b).2 : ℤ) := by
  cases m <;> cases b <;> try rfl
  change (n : ℤ) - 1 = ((finish n).2 : ℤ)
  unfold finish
  split_ifs with hn
  · subst n
    rfl
  · dsimp only
    have hp := h rfl
    omega

/-- A transition increases the pending count by at most one. -/
theorem step_counter_le (s : State) (b : Bool) : (step s b).2 ≤ s.2 + 1 := by
  rcases s with ⟨m, n⟩
  cases m <;> cases b <;>
    first | exact Nat.le_succ _ | exact Nat.le_refl _
          | (change (finish n).2 ≤ n + 1; unfold finish; split <;> dsimp only <;> omega)

/-- A scan's pending count is bounded by its initial count plus its input length. -/
theorem foldl_counter_le (w : List Bool) :
    ∀ s : State, (w.foldl step s).2 ≤ s.2 + w.length := by
  refine List.rec ?_ ?_ w
  · intro s
    exact Nat.le_refl _
  · intro b bs ih s
    have h := ih (step s b)
    have hstep := step_counter_le s b
    simp only [List.foldl_cons, List.length_cons]
    omega

/-- There are at most one plus the input length pending subtrees. -/
theorem scan_counter_le (w : List Bool) : (scan w).2 ≤ w.length + 1 := by
  simpa only [scan, Nat.add_comm] using foldl_counter_le w (.tree, 1)

/-- Extending the scanned prefix applies one pure transition. -/
theorem scan_take_succ (w : List Bool) (t : ℕ) (h : t < w.length) :
    scan (w.take (t + 1)) = step (scan (w.take t)) w[t] := by
  simp only [scan, List.take_succ_eq_append_getElem h, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

end Geb.BitTree
