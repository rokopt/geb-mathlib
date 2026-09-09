/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.Scanner
public import Geb.Prototypes.Computability.BitTree.Elias.Counter
public import Geb.Prototypes.Computability.BitTree.Elias.Machine

set_option doc.verso true

/-!
# Binary words at scanner boundaries

The scalar scanner describes decoded values. The machine stores fixed-width
binary words, retaining leading zeros after decrementing. The relation between
these descriptions also records the phases where a field is empty or initialized.

## Main definitions

* {lit}`scanCfg` describes all four tapes at an input boundary.
* {lit}`Words` relates the binary fields to a scalar scanner phase.
* {lit}`nextWords` updates the two finite words for one consumed input bit.

## Tags

Elias delta code, simulation, binary counter
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM

/-- The finite state corresponding to each normalized scalar phase. -/
def modeState : Scanner.Mode → Control
  | .tree => stTree
  | .zeros _ => stZeros
  | .size _ _ => stSizeBit
  | .length _ _ => stLengthBit
  | .payload _ => stPayloadBit
  | .done => stDone
  | .dead => stDead

/-- Normalized modes always denote states that consume external input. -/
theorem modeState_read (m : Scanner.Mode) :
    modeState m = stTree ∨ modeState m = stZeros ∨ modeState m = stSizeBit ∨
      modeState m = stLengthBit ∨ modeState m = stPayloadBit ∨
      modeState m = stDone ∨ modeState m = stDead := by
  cases m <;> simp only [modeState, eq_self, true_or, or_true]

/-- The unary header counter is used only in the two initial header phases. -/
def zeroCount : Scanner.Mode → ℕ
  | .zeros z => z
  | .size r _ => r
  | _ => 0

/-- A configuration with unary counters and two binary fields at their right-hand blanks. -/
def scanCfg (input : List (Fin 3)) (pos : Fin (input.length + 2)) (q : Control)
    (pending zeros : ℕ) (bs cs : List Bool) : Cfg 4 (Fin 3) Control input where
  state := some q
  inputPos := pos
  workTapes i := if i = 2 then wordTape bs else if i = 3 then wordTape cs else wordTape []
  workTapePos i :=
    if i = 0 then pending else if i = 1 then zeros
    else if i = 2 then bs.length + 1 else cs.length + 1

/-- A normalized scalar state with its explicit binary field representations. -/
def modelCfg (input : List (Fin 3)) (pos : Fin (input.length + 2)) (s : Scanner.State)
    (bs cs : List Bool) : Cfg 4 (Fin 3) Control input :=
  scanCfg input pos (modeState s.1) s.2 (zeroCount s.1) bs cs

/-- The four explicit head positions determine a boundary configuration's space interval. -/
theorem scanCfg_headBound (input : List (Fin 3)) (pos : Fin (input.length + 2)) (q : Control)
    (pending zeros : ℕ) (bs cs : List Bool) (width : ℕ)
    (hp : pending ≤ width) (hz : zeros ≤ width)
    (hb : bs.length + 1 ≤ width) (hc : cs.length + 1 ≤ width) :
    HeadBound width (scanCfg input pos q pending zeros bs cs) := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j ↦ Fin.elim0 j)))) i
  · change 0 ≤ (pending : ℤ) ∧ (pending : ℤ) ≤ (width : ℤ)
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hp⟩
  · change 0 ≤ (zeros : ℤ) ∧ (zeros : ℤ) ≤ (width : ℤ)
    exact ⟨Int.natCast_nonneg _, Int.ofNat_le.mpr hz⟩
  · change 0 ≤ (bs.length : ℤ) + 1 ∧ (bs.length : ℤ) + 1 ≤ (width : ℤ)
    exact ⟨by omega, by omega⟩
  · change 0 ≤ (cs.length : ℤ) + 1 ∧ (cs.length : ℤ) + 1 ≤ (width : ℤ)
    exact ⟨by omega, by omega⟩

/-- The binary fields required at each scanner phase. -/
def Words : Scanner.Mode → List Bool → List Bool → Prop
  | .tree, bs, cs | .done, bs, cs | .dead, bs, cs => bs = [] ∧ cs = []
  | .zeros _, bs, cs => bs = [] ∧ cs = [true]
  | .size _ v, bs, cs => Counter.value bs = v ∧ cs = [true]
  | .length r v, bs, cs => Counter.value bs = r ∧ Counter.value cs = v
  | .payload r, bs, cs => Counter.value bs = 0 ∧ Counter.value cs = r

/-- Binary-word updates associated with one complete input transition. -/
def nextWords : Scanner.Mode → List Bool → List Bool → Bool → List Bool × List Bool
  | .tree, bs, cs, true => (bs, cs)
  | .tree, _, _, false => ([], [true])
  | .zeros _, bs, cs, false => (bs, cs)
  | .zeros z, _, cs, true => if z = 0 then ([], []) else ([true], cs)
  | .size r _, bs, cs, b =>
    if r = 1 then (Counter.decrement (b :: bs), cs) else (b :: bs, cs)
  | .length r _, bs, cs, b =>
    (Counter.decrement bs, if r = 1 then Counter.decrement (b :: cs) else b :: cs)
  | .payload r, bs, cs, _ =>
    if r = 1 then ([], []) else (bs, Counter.decrement cs)
  | .done, bs, cs, _ => (bs, cs)
  | .dead, bs, cs, _ => (bs, cs)

/-- Exact transition costs for the read, countdown, and erasure subroutines. -/
def bitCost : Scanner.Mode → List Bool → List Bool → Bool → ℕ
  | .tree, _, _, _ => 1
  | .zeros _, _, _, false => 1
  | .zeros z, _, _, true => if z = 0 then 16 else 2
  | .size r _, bs, _, _ => if r = 1 then 2 * bs.length + 7 else 2
  | .length r _, bs, cs, _ =>
    if r = 1 then 2 * bs.length + 2 * cs.length + 9 else 2 * bs.length + 4
  | .payload r, bs, cs, _ =>
    if r = 1 then 2 * cs.length + max bs.length cs.length + 7 else 2 * cs.length + 4
  | .done, _, _, _ => 1
  | .dead, _, _, _ => 1

end Geb.BitTree.Elias.Machine
