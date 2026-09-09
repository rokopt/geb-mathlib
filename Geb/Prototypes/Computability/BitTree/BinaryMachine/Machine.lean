/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import Geb.Prototypes.Computability.BitTree.Scanner

set_option doc.verso true

/-!
# A binary-counter machine for trees with bitstring leaves

The machine reads the input from left to right. Its first two work tapes hold
the number of forks plus one and the number of completed leaves in binary.
Their heads remain aligned. The third head records the number of unequal bit
positions, so equality is detected at its marked origin without scanning the
binary representations. Each carry changes this number by one at each bit flip.

## Main definitions

* {lit}`machine` is the three-work-tape machine.
* {lit}`digit` reads a binary digit, including the tagged origin digits.
* {lit}`flipped` flips a digit while preserving the origin tag.
* {lit}`modeState` embeds scanner modes into finite machine control.
* {lit}`startCfg`, {lit}`consumeCfg` and {lit}`returnCfg` describe phase boundaries.
* {lit}`HeadBound` bounds all work-head positions.

## Implementation notes

The alphabet has four symbols. Symbols zero and one are ordinary digits;
symbols two and three tag the least significant position. A blank is read as
zero. The third tape has one marker, at its origin. Input movement occurs only
when consuming a bit; carry and return transitions leave the input head fixed.

## Tags

Turing machine, binary counter, bitstring, tree
-/

@[expose] public section

namespace Geb.BitTree.BinaryMachine

open Turing MultiTapeTM

/-- Embed input and output booleans into the machine alphabet. -/
def boolEmb : Bool ↪ Fin 4 where
  toFun b := if b then 1 else 0
  inj' a b := by cases a <;> cases b <;> simp

/-- Read a digit, with a blank representing zero. -/
def digit (s : Option (Fin 4)) : Bool := s == some 1 || s == some 3

/-- Detect a tagged least significant digit. -/
def origin (s : Option (Fin 4)) : Bool := s == some 2 || s == some 3

/-- Flip one digit, preserving its origin tag. -/
def flipped (s : Option (Fin 4)) : Fin 4 :=
  if origin s then (if digit s then 2 else 3) else (if digit s then 0 else 1)

/-- Reading a flipped digit gives the boolean complement. -/
theorem digit_flipped (s : Option (Fin 4)) : digit (some (flipped s)) = !digit s := by
  unfold flipped
  cases origin s <;> cases digit s <;> rfl

/-- Flipping a digit preserves its origin tag. -/
theorem origin_flipped (s : Option (Fin 4)) : origin (some (flipped s)) = origin s := by
  unfold flipped
  cases origin s <;> cases digit s <;> rfl

/-- The mismatch count rises when two equal digits become different. -/
def mismatchMove (a b : Option (Fin 4)) : SignType :=
  if digit a == digit b then 1 else -1

/-- Write both origin digits and the mismatch tape's origin marker. -/
def stInit : Fin 10 := 0
/-- Enter scanning after initialization. -/
def stStart : Fin 10 := 1
/-- Expect a tree constructor. -/
def stTree : Fin 10 := 2
/-- Expect a string continuation or terminator. -/
def stString : Fin 10 := 3
/-- Consume one payload bit. -/
def stBit : Fin 10 := 4
/-- The complete tree has ended; only end of input is accepted. -/
def stDone : Fin 10 := 5
/-- A malformed prefix has been found. -/
def stDead : Fin 10 := 6
/-- Increment the number of forks plus one. -/
def stCarryFork : Fin 10 := 7
/-- Increment the number of completed leaves. -/
def stCarryLeaf : Fin 10 := 8
/-- Return both binary heads to their origins. -/
def stReturn : Fin 10 := 9

/-- A transition consuming one input symbol without changing work tapes. -/
def consume (q : Fin 10) : TransitionOut 3 (Fin 4) (Fin 10) where
  inputMove := 1
  workActions _ := (none, 0)
  outS := none
  q' := some q

/-- Emit one boolean and halt. -/
def finish (b : Bool) : TransitionOut 3 (Fin 4) (Fin 10) where
  inputMove := 0
  workActions _ := (none, 0)
  outS := some (boolEmb b)
  q' := none

/-- Flip the selected counter's current bit and maintain the mismatch count.
Carry transitions move both binary heads right; the first zero ends the carry. -/
def carry (leaf : Bool) (work : Fin 3 → Option (Fin 4)) :
    TransitionOut 3 (Fin 4) (Fin 10) :=
  let selected : Fin 3 := if leaf then 1 else 0
  { inputMove := 0
    workActions := fun i ↦
      if i = 2 then (none, mismatchMove (work 0) (work 1))
      else (if i = selected then some (some (flipped (work i))) else none, 1)
    outS := none
    q' := some (if digit (work selected) then
      (if leaf then stCarryLeaf else stCarryFork) else stReturn) }

/-- A three-work-tape recognizer whose counters are incremented monotonically. -/
def machine : MultiTapeTM 3 (Fin 4) (Fin 10) where
  q₀ := stInit
  tr q input work :=
    if q = stInit then
      { inputMove := 0
        workActions := fun i ↦
          if i = 0 then (some (some 3), 0)
          else if i = 1 then (some (some 2), 0)
          else (some (some 0), 1)
        outS := none
        q' := some stStart }
    else if q = stStart then
      { inputMove := 0, workActions := fun _ ↦ (none, 0),
        outS := none, q' := some stTree }
    else if q = stCarryFork then carry false work
    else if q = stCarryLeaf then carry true work
    else if q = stReturn then
      if origin (work 0) then
        { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none,
          q' := some (if work 2 == some 0 then stDone else stTree) }
      else
        { inputMove := 0,
          workActions := fun i ↦ (none, if i = 2 then 0 else -1),
          outS := none, q' := some stReturn }
    else
      match input with
      | none => finish (q == stDone)
      | some b =>
        if q = stTree then consume (if b == 0 then stString else stCarryFork)
        else if q = stString then consume (if b == 0 then stCarryLeaf else stBit)
        else if q = stBit then consume stString
        else consume stDead

/-- Every input transition is stationary or moves right. -/
theorem inputMove_ne_neg (q : Fin 10) (input : Option (Fin 4))
    (work : Fin 3 → Option (Fin 4)) : (machine.tr q input work).inputMove ≠ -1 := by
  cases input <;> simp only [machine] <;> split_ifs <;> first
    | exact (by decide : (0 : SignType) ≠ -1)
    | exact (by decide : (1 : SignType) ≠ -1)

/-- All transitions move the two binary heads by the same displacement. -/
theorem binaryHeads_move_eq (q : Fin 10) (input : Option (Fin 4))
    (work : Fin 3 → Option (Fin 4)) :
    ((machine.tr q input work).workActions 0).2 =
      ((machine.tr q input work).workActions 1).2 := by
  cases input <;> simp only [machine] <;> split_ifs <;> simp [carry, consume, finish]

/-- A stationary or right-moving displacement cannot lower an input position. -/
theorem le_moveInputPos {n : ℕ} (p : Fin (n + 2)) (d : SignType) (h : d ≠ -1) :
    p.val ≤ (moveInputPos p d).val := by
  cases d with
  | neg => exact False.elim (h rfl)
  | zero =>
    unfold moveInputPos
    have hz : ((p.val : ℤ) + (SignType.zero.cast : ℤ)).toNat = p.val := by
      change ((p.val : ℤ) + 0).toNat = p.val
      omega
    rw [hz]
    dsimp only
    split
    · exact Nat.le_refl _
    · exact Nat.le_of_lt_succ p.isLt
  | pos =>
    unfold moveInputPos
    have hz : ((p.val : ℤ) + (SignType.pos.cast : ℤ)).toNat = p.val + 1 := by
      change ((p.val : ℤ) + 1).toNat = p.val + 1
      omega
    rw [hz]
    dsimp only
    split
    · exact Nat.le_succ _
    · exact Nat.le_of_lt_succ p.isLt

/-- The initialized configuration has counter values one and zero. -/
def startCfg (input : List (Fin 4)) : Cfg 3 (Fin 4) (Fin 10) input where
  state := some stTree
  inputPos := 1
  workTapes i z := if z = 0 then some (if i = 0 then 3 else if i = 1 then 2 else 0)
    else none
  workTapePos i := if i = 2 then 1 else 0

/-- The digits read at nonnegative positions of a work tape. -/
def digits {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (i : Fin 3) (j : ℕ) : Bool := digit (cfg.workTapes i j)

/-- Both carry states resolve to the common carry transition. -/
theorem tr_carry (leaf : Bool) (input : Option (Fin 4))
    (work : Fin 3 → Option (Fin 4)) :
    machine.tr (if leaf then stCarryLeaf else stCarryFork) input work = carry leaf work := by
  cases leaf <;> rfl

/-- A return configuration with the binary heads at a specified nonnegative position. -/
def returnCfg {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (p : ℕ) : Cfg 3 (Fin 4) (Fin 10) input where
  state := some stReturn
  inputPos := cfg.inputPos
  workTapes := cfg.workTapes
  workTapePos i := if i = 2 then cfg.workTapePos 2 else p

/-- The configuration reached when the return's final state change has completed. -/
def returnedCfg {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input) :
    Cfg 3 (Fin 4) (Fin 10) input :=
  { returnCfg cfg 0 with
    state := some (if cfg.workTapes 2 (cfg.workTapePos 2) == some 0 then stDone else stTree) }

/-- A configuration already in the return state equals its return normal form. -/
theorem returnCfg_self {input : List (Fin 4)}
    (cfg : Cfg 3 (Fin 4) (Fin 10) input) (p : ℕ)
    (hq : cfg.state = some stReturn)
    (hp0 : cfg.workTapePos 0 = p) (hp1 : cfg.workTapePos 1 = p) :
    returnCfg cfg p = cfg := by
  refine Cfg.ext hq.symm rfl rfl ?_
  funext i
  exact Fin.cases hp0.symm (Fin.cases hp1.symm (Fin.cases rfl (fun i ↦ Fin.elim0 i))) i

/-- The finite machine state corresponding to a scanner mode. -/
def modeState : Mode → Fin 10
  | .tree => stTree
  | .string => stString
  | .bit => stBit
  | .done => stDone
  | .dead => stDead

/-- The state entered by consuming one bit, before any counter update. -/
def postReadState : Mode → Bool → Fin 10
  | .tree, false => stString
  | .tree, true => stCarryFork
  | .string, false => stCarryLeaf
  | .string, true => stBit
  | .bit, _ => stString
  | .done, _ => stDead
  | .dead, _ => stDead

/-- Reading a bit selects the grammar transition without modifying work tapes. -/
theorem tr_read (m : Mode) (b : Bool) (work : Fin 3 → Option (Fin 4)) :
    machine.tr (modeState m) (some (boolEmb b)) work = consume (postReadState m b) := by
  cases m <;> cases b <;> rfl

/-- Reading a bit changes the input position and finite control only. -/
def consumeCfg {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input) (q : Fin 10) :
    Cfg 3 (Fin 4) (Fin 10) input :=
  { cfg with state := some q, inputPos := moveInputPos cfg.inputPos 1 }

/-- The input position advances by one when it is not the right end marker. -/
theorem consumeCfg_inputPos {input : List (Fin 4)} (cfg : Cfg 3 (Fin 4) (Fin 10) input)
    (q : Fin 10) (h : cfg.inputPos.val < input.length + 1) :
    (consumeCfg cfg q).inputPos.val = cfg.inputPos.val + 1 := by
  change (moveInputPos cfg.inputPos SignType.pos).val = _
  unfold moveInputPos
  have hz : ((cfg.inputPos.val : ℤ) + (SignType.pos.cast : ℤ)).toNat =
      cfg.inputPos.val + 1 := by
    change ((cfg.inputPos.val : ℤ) + 1).toNat = cfg.inputPos.val + 1
    omega
  rw [hz]
  dsimp only
  split
  · rfl
  · omega

/-- The right end marker emits the accepting-mode test and halts. -/
theorem tr_end (m : Mode) (work : Fin 3 → Option (Fin 4)) :
    machine.tr (modeState m) none work = finish (decide (m = .done)) := by
  cases m <;> rfl

/-- Every work head lies in the nonnegative interval bounded by the chosen width. -/
def HeadBound {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 3 (Fin 4) (Fin 10) input) :
    Prop := ∀ i, 0 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ (width : ℤ)

end Geb.BitTree.BinaryMachine
