/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.EliasBinary.Machine
public import Geb.Prototypes.Computability.BitTree.EliasBinary.Cost

set_option doc.verso true

/-!
# The boundary representation of an account

At every input boundary of the second pass, the nine tapes are determined by the account.
The pending pair always holds the forks and leaves counters with the ruler head at its
phase-dependent position. The size pair is idle, being read, or a complete counter pair; the
length pair is idle, being read relative to its eventual least significant cell, or a
complete counter pair.

## Main definitions

* {lit}`widthOf` is the head and counter width for an input of a given length.
* {lit}`phaseState` is the finite state at each scanner phase.
* {lit}`IdleSize`, {lit}`SizeRead`, {lit}`IdleLength` and {lit}`LengthRead` describe the
  two header pairs in their phases.
* {lit}`LiveRep` describes the tapes of an account that has not been abandoned.
* {lit}`Represents` is the complete boundary invariant.

## Main statements

* {lit}`LiveRep.headBound` bounds every head at a live boundary.
* {lit}`Represents.ofLive` and {lit}`Represents.dead` build the invariant in its two cases.
* The {lit}`congr` statements transport every predicate along a configuration with the same
  tapes and head positions.

## Tags

Turing machine, simulation, invariant, Elias delta code
-/

@[expose] public section

namespace Geb.BitTree.EliasBinary

open Turing MultiTapeTM
open Geb.BitTree.Elias.Scanner
open Geb.BitTree.BinaryMachine (digit origin mismatchCount bitsAt mismatchCount_le)

/-- The head and counter width for an input of the given length. -/
def widthOf (n : ℕ) : ℕ := (2 * n + 2).size + 1

/-- The finite state at each scanner phase. -/
def phaseState : Elias.Scanner.State → Control
  | (.tree, _) => stTree
  | (.zeros _, _) => stZeros
  | (.size _ _, _) => stSizeBit
  | (.length _ _, _) => stLengthBit
  | (.payload _, _) => stPayloadBit
  | (.done, _) => stDone
  | (.dead, _) => stDead

/-- Every phase state reads input. -/
theorem phaseState_read (s : Elias.Scanner.State) :
    phaseState s = stTree ∨ phaseState s = stZeros ∨ phaseState s = stSizeBit ∨
      phaseState s = stLengthBit ∨ phaseState s = stPayloadBit ∨ phaseState s = stDone ∨
      phaseState s = stDead := by
  rcases s with ⟨m, _⟩
  cases m <;> simp [phaseState]

/-- A tape holding only a marker at its origin. -/
def MarkerTape (tape : ℤ → Option (Fin 4)) : Prop := ∀ z, tape z = if z = 0 then some 0 else none

/-- A blank tape. -/
def BlankTape (tape : ℤ → Option (Fin 4)) : Prop := ∀ z, tape z = none

/-- A tape holding only a tagged zero at its origin. -/
def TaggedZeroTape (tape : ℤ → Option (Fin 4)) : Prop :=
  ∀ z, tape z = if z = 0 then some 2 else none

/-- The eventual least significant cell of the length register during the length field. -/
def lengthLsb (r v : ℕ) : ℤ := ((r + v.size - 1 : ℕ) : ℤ)

/-- The size pair outside the size and length fields. -/
structure IdleSize {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) : Prop where
  /-- The register holds its tagged origin only. -/
  register : TaggedZeroTape (cfg.workTapes 3)
  /-- The register head is at the origin. -/
  registerPos : cfg.workTapePos 3 = 0
  /-- The counter is blank. -/
  counter : BlankTape (cfg.workTapes 4)
  /-- The counter head is at the origin. -/
  counterPos : cfg.workTapePos 4 = 0
  /-- The mismatch tape holds its marker. -/
  marker : MarkerTape (cfg.workTapes 5)
  /-- The mismatch head is at the origin. -/
  mismPos : cfg.workTapePos 5 = 0

/-- The size pair while the size field is read: the digits read so far occupy the cells from
the remaining count upwards, least significant first, and the counter holds one. -/
structure SizeRead {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input)
    (r v : ℕ) : Prop where
  /-- The register: tagged origin, the digits of the value read so far, blanks elsewhere. -/
  register : ∀ z, cfg.workTapes 3 z = if z = 0 then some 2
    else if (r : ℤ) ≤ z ∧ z < r + v.size then some (plain (bitsAt v (z - r).toNat)) else none
  /-- The register head is at the next cell to write. -/
  registerPos : cfg.workTapePos 3 = r - 1
  /-- The counter holds one. -/
  counter : ∀ z, cfg.workTapes 4 z = if z = 0 then some 1 else none
  /-- The counter head is at the origin. -/
  counterPos : cfg.workTapePos 4 = 0
  /-- The mismatch tape holds its marker. -/
  marker : MarkerTape (cfg.workTapes 5)
  /-- The mismatch head counts the unequal cells. -/
  mismPos : cfg.workTapePos 5 =
    (mismatchCount width (digitsFrom cfg 3 0 1) (digitsFrom cfg 4 0 1) : ℤ)

/-- The length pair outside the length field and payload. -/
structure IdleLength {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) : Prop where
  /-- The register is blank. -/
  register : BlankTape (cfg.workTapes 6)
  /-- The register head is at the origin. -/
  registerPos : cfg.workTapePos 6 = 0
  /-- The counter is blank. -/
  counter : BlankTape (cfg.workTapes 7)
  /-- The counter head is at the origin. -/
  counterPos : cfg.workTapePos 7 = 0
  /-- The mismatch tape holds its marker. -/
  marker : MarkerTape (cfg.workTapes 8)
  /-- The mismatch head is at the origin. -/
  mismPos : cfg.workTapePos 8 = 0

/-- The cells of the size pair that the length field's transitions never visit: the negative
cells of both digit tapes and the counter's cells beyond its digits. -/
structure SizeSpare {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input) (c : ℕ) :
    Prop where
  /-- The register is blank at negative cells. -/
  registerNeg : ∀ z, z < 0 → cfg.workTapes 3 z = none
  /-- The counter is blank at negative cells. -/
  counterNeg : ∀ z, z < 0 → cfg.workTapes 4 z = none
  /-- The counter is blank beyond its digits. -/
  counterBeyond : ∀ j : ℕ, c.size ≤ j → cfg.workTapes 4 j = none

/-- The length pair while the length field is read: relative to the eventual least significant
cell, the register holds the value read so far shifted by the remaining count. -/
structure LengthRead {input : List (Fin 4)} (cfg : Cfg 9 (Fin 4) Control input)
    (r v : ℕ) : Prop where
  /-- The digits read so far, at their eventual significance. -/
  digits : digitsFrom cfg 6 (lengthLsb r v) (-1) = bitsAt (v * 2 ^ r)
  /-- Cells below the remaining count and beyond the register are blank. -/
  blank : ∀ j, cfg.workTapes 6 (cell (lengthLsb r v) (-1) j) = none ↔ j < r ∨ r + v.size ≤ j
  /-- No cell is tagged yet. -/
  untagged : ∀ z, origin (cfg.workTapes 6 z) = false
  /-- Cells beyond the eventual least significant cell are blank. -/
  beyond : ∀ z, lengthLsb r v < z → cfg.workTapes 6 z = none
  /-- The register head is at the next cell to write. -/
  registerPos : cfg.workTapePos 6 = v.size
  /-- The counter is blank. -/
  counter : BlankTape (cfg.workTapes 7)
  /-- The counter head travels with the register head. -/
  counterPos : cfg.workTapePos 7 = v.size
  /-- The mismatch tape holds its marker. -/
  marker : MarkerTape (cfg.workTapes 8)
  /-- The mismatch head counts the ones read so far. -/
  mismPos : cfg.workTapePos 8 = (pop v : ℤ)
  /-- The size pair is blank where the length field's transitions never visit. -/
  spare : SizeSpare cfg v.size

/-- The two header pairs at each phase. -/
def PhaseRep {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) : Prop :=
  match a.state with
  | (.size r v, _) => SizeRead width cfg r v ∧ IdleLength cfg
  | (.length r v, _) =>
    PairRep sizeLayout 0 width cfg (r + v.size) v.size ∧ LengthRead cfg r v
  | (.payload r, _) => IdleSize cfg ∧
    PairRep lengthLayout ((a.total.size - 1 : ℕ) : ℤ) width cfg a.total (a.total - r) ∧
    ∀ z, z < 0 ∨ ((a.total.size - 1 : ℕ) : ℤ) < z →
      cfg.workTapes 6 z = none ∧ cfg.workTapes 7 z = none
  | _ => IdleSize cfg ∧ IdleLength cfg

/-- The tape contents at a boundary of an account that has not been abandoned. -/
structure LiveRep {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) : Prop where
  /-- The pending pair holds both counters. -/
  pending : PairData pendingLayout 0 width cfg a.forks a.leaves
  /-- The forks head serves as the ruler. -/
  forksPos : cfg.workTapePos 0 = rulerPos a.state
  /-- The leaves head is at the origin. -/
  leavesPos : cfg.workTapePos 1 = 0
  /-- The header pairs are in their phase. -/
  phase : PhaseRep width cfg a

/-- The complete boundary invariant: the finite control, the head bounds, and, unless the
account has been abandoned, the tape contents. -/
structure Represents {input : List (Fin 4)} (width : ℕ) (cfg : Cfg 9 (Fin 4) Control input)
    (a : Account) : Prop where
  /-- Finite control at the phase state. -/
  state : cfg.state = some (phaseState a.state)
  /-- Every head is within the interval. -/
  bound : HeadBound width cfg
  /-- The tape contents of a live account. -/
  live : a.state.1 ≠ .dead → LiveRep width cfg a

/-- The pending pair with both heads at the origin, outside the ruler phases. -/
theorem LiveRep.pendingRep {input : List (Fin 4)} {width : ℕ}
    {cfg : Cfg 9 (Fin 4) Control input} {a : Account} (h : LiveRep width cfg a)
    (hr : rulerPos a.state = 0) : PairRep pendingLayout 0 width cfg a.forks a.leaves :=
  ⟨h.pending, by change cfg.workTapePos 0 = 0; rw [h.forksPos, hr]; rfl,
    by change cfg.workTapePos 1 = 0; exact h.leavesPos⟩

/-- The counter values of a valid account fit the width. -/
theorem forks_size_lt_width (n : ℕ) (w : List Bool) (a : Account) (ha : a = account n w)
    (hw : w.length ≤ n) : a.forks.size + 1 ≤ widthOf n ∧ (a.forks + 1).size + 1 ≤ widthOf n ∧
      (a.leaves + 1).size ≤ widthOf n := by
  subst ha
  have hs := account_forks_le n w
  have hl := account_leaves_le n w
  unfold widthOf
  refine ⟨?_, ?_, ?_⟩
  · have := Geb.BitTree.Counter.size_mono (show (account n w).forks ≤ 2 * n + 2 by omega)
    omega
  · have := Geb.BitTree.Counter.size_mono (show (account n w).forks + 1 ≤ 2 * n + 2 by omega)
    omega
  · have := Geb.BitTree.Counter.size_mono (show (account n w).leaves + 1 ≤ 2 * n + 2 by omega)
    omega

/-! ## Counting lemmas -/

/-- Appending a digit adds it to the number of ones. -/
theorem pop_bit (b : Bool) (v : ℕ) (hv : 0 < v) : pop (Nat.bit b v) = pop v + b.toNat := by
  unfold pop
  rw [Nat.bits_append_bit v b (fun h ↦ by omega), List.count_cons]
  cases b <;> rfl

/-- Counting the positions of a list holding {lit}`true` counts its {lit}`true` entries. -/
theorem countP_range_getD (l : List Bool) :
    (List.range l.length).countP (fun j ↦ l[j]?.getD false) = l.count true := by
  refine List.rec ?_ ?_ l
  · rfl
  · intro b l ih
    rw [List.length_cons, List.range_succ_eq_map, List.countP_cons, List.countP_map,
      List.count_cons]
    have hc : (List.range l.length).countP ((fun j ↦ (b :: l)[j]?.getD false) ∘ Nat.succ) =
        l.count true := by
      rw [← ih]
      apply List.countP_congr
      intro j _
      rfl
    rw [hc]
    cases b <;> rfl

/-- Below the width, the ones of a counter are its mismatches against zero. -/
theorem mismatchCount_bitsAt_zero (x m : ℕ) (h : x.size ≤ m) :
    mismatchCount m (bitsAt x) (bitsAt 0) = pop x := by
  have hz : ∀ j, bitsAt 0 j = false := fun j ↦ rfl
  have hext : ∀ d, mismatchCount (x.size + d) (bitsAt x) (bitsAt 0) =
      mismatchCount x.size (bitsAt x) (bitsAt 0) := by
    refine Nat.rec rfl ?_
    intro d ih
    change mismatchCount (x.size + d + 1) (bitsAt x) (bitsAt 0) = _
    rw [Geb.BitTree.BinaryMachine.mismatchCount_succ, ih,
      Geb.BitTree.BinaryMachine.bitsAt_of_size_le x _ (by omega), hz]
    rfl
  have hm := hext (m - x.size)
  rw [show x.size + (m - x.size) = m by omega] at hm
  rw [hm]
  unfold mismatchCount
  have hp : (fun i ↦ bitsAt x i != bitsAt 0 i) = fun j ↦ x.bits[j]?.getD false := by
    funext i
    rw [hz]
    change (bitsAt x i != false) = bitsAt x i
    cases bitsAt x i <;> rfl
  rw [hp, ← Geb.BitTree.Counter.length_bits, countP_range_getD]
  rfl

/-- A mismatch count is unchanged by widening past the positions where the streams agree. -/
theorem mismatchCount_eq_of_agree (m width : ℕ) (a b : ℕ → Bool) (hm : m ≤ width)
    (h : ∀ j, m ≤ j → a j = b j) : mismatchCount width a b = mismatchCount m a b := by
  have hext : ∀ d, mismatchCount (m + d) a b = mismatchCount m a b := by
    refine Nat.rec rfl ?_
    intro d ih
    change mismatchCount (m + d + 1) a b = _
    rw [Geb.BitTree.BinaryMachine.mismatchCount_succ, ih, h _ (by omega), ite_eq_left rfl,
      Nat.add_zero]
  have := hext (width - m)
  rwa [show m + (width - m) = width by omega] at this

/-- One is zero with its least significant bit flipped. -/
theorem bitsAt_one_eq_flip : bitsAt 1 = Geb.BitTree.BinaryMachine.flipAt (bitsAt 0) 0 := by
  funext j
  cases j with
  | zero => rfl
  | succ j => rfl

/-- The mismatches of a counter against one, from its ones and its least significant bit. -/
theorem mismatchCount_bitsAt_one (x width : ℕ) (hx : x.size ≤ width) (hw : 0 < width) :
    (mismatchCount width (bitsAt x) (bitsAt 1) : ℤ) =
      pop x + if bitsAt x 0 then -1 else 1 := by
  rw [bitsAt_one_eq_flip, Geb.BitTree.BinaryMachine.mismatchCount_flip_right width 0 _ _ hw,
    mismatchCount_bitsAt_zero x width hx]
  have hz : bitsAt 0 0 = false := rfl
  rw [hz]
  cases bitsAt x 0 <;> rfl

/-- A head at a number of ones is within the interval. -/
theorem bounds_of_pop {z : ℤ} {v width : ℕ} (h : z = (pop v : ℤ)) (hv : v.size ≤ width) :
    -1 ≤ z ∧ z ≤ width := by
  have := pop_le_size v
  exact ⟨by omega, by omega⟩

/-- A head at a mismatch count is within the interval. -/
theorem bounds_of_mismatch {z : ℤ} {width : ℕ} {f g : ℕ → Bool}
    (h : z = (mismatchCount width f g : ℤ)) : -1 ≤ z ∧ z ≤ width := by
  have := mismatchCount_le width f g
  exact ⟨by omega, by omega⟩

/-- A property of the nine work tapes follows from its nine instances. -/
theorem forall_fin_nine {P : Fin 9 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3)
    (h4 : P 4) (h5 : P 5) (h6 : P 6) (h7 : P 7) (h8 : P 8) (i : Fin 9) : P i :=
  match i with
  | 0 => h0
  | 1 => h1
  | 2 => h2
  | 3 => h3
  | 4 => h4
  | 5 => h5
  | 6 => h6
  | 7 => h7
  | 8 => h8

/-- Every head is within the interval at a live boundary of a valid account. -/
theorem LiveRep.headBound {input : List (Fin 4)} {n width : ℕ}
    {cfg : Cfg 9 (Fin 4) Control input} {a : Account} (h : LiveRep width cfg a)
    (hv : AccountValid n a) (hw : a.forks.size + 1 ≤ width) : HeadBound width cfg := by
  have hrp := hv.rulerPos_le
  have hsw := hv.sizeWidth_le
  have hph := h.phase
  have hts := hv.total_size_le
  intro i
  refine forall_fin_nine (P := fun i ↦ -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ width)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i
  · rw [h.forksPos]
    constructor <;> omega
  · rw [h.leavesPos]
    constructor <;> omega
  · have hm0 : cfg.workTapePos 2 = _ := h.pending.mismatchPos
    exact bounds_of_mismatch hm0
  all_goals
    rcases hs : a.state with ⟨m, k⟩
    rw [hs] at hrp hsw hts
    unfold PhaseRep at hph
    rw [hs] at hph
    cases m
    all_goals dsimp only [rulerPos, sizeWidth] at hrp hsw hph
  -- the size register head
  all_goals try
    (first
       | (rw [hph.1.registerPos]; constructor <;> omega)
       | (rw [show cfg.workTapePos 3 = 0 from hph.1.firstPos]; constructor <;> omega))
  -- the size counter head
  all_goals try
    (first
       | (rw [hph.1.counterPos]; constructor <;> omega)
       | (rw [show cfg.workTapePos 4 = 0 from hph.1.secondPos]; constructor <;> omega))
  -- the size mismatch head
  all_goals try
    (first
       | (rw [hph.1.mismPos]; constructor <;> omega)
       | exact bounds_of_mismatch hph.1.mismPos
       | exact bounds_of_mismatch (show cfg.workTapePos 5 = _ from hph.1.mismatchPos))
  -- the length register head
  all_goals try
    (first
       | (rw [hph.2.registerPos]; constructor <;> omega)
       | (rw [show cfg.workTapePos 6 = _ from hph.2.1.firstPos]
          have := hts _ rfl
          constructor <;> omega))
  -- the length counter head
  all_goals try
    (first
       | (rw [hph.2.counterPos]; constructor <;> omega)
       | (rw [show cfg.workTapePos 7 = _ from hph.2.1.secondPos]
          have := hts _ rfl
          constructor <;> omega))
  -- the length mismatch head
  all_goals
    (first
       | (rw [hph.2.mismPos]; constructor <;> omega)
       | exact bounds_of_pop hph.2.mismPos (by omega)
       | exact bounds_of_mismatch (show cfg.workTapePos 8 = _ from hph.2.1.mismatchPos))

/-! ## Transport along configurations with the same tapes and heads -/

section Congr

variable {input : List (Fin 4)} {cfg cfg' : Cfg 9 (Fin 4) Control input}
  (ht : ∀ i, cfg'.workTapes i = cfg.workTapes i) (hp : ∀ i, cfg'.workTapePos i = cfg.workTapePos i)

include ht hp

omit hp in
/-- Digit streams depend on the tapes only. -/
theorem digitsFrom_congr (i : Fin 9) (lsb : ℤ) (d : SignType) :
    digitsFrom cfg' i lsb d = digitsFrom cfg i lsb d := by
  funext j
  simp only [digitsFrom, ht]

/-- A counter pair's contents transport. -/
theorem PairData.congr {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    (h : PairData lay lsb width cfg a b) : PairData lay lsb width cfg' a b :=
  ⟨by rw [digitsFrom_congr ht]; exact h.firstDigits,
    by rw [digitsFrom_congr ht]; exact h.secondDigits,
    fun z ↦ by rw [ht]; exact h.originTag z, fun j ↦ by rw [ht]; exact h.firstBlank j,
    fun z ↦ by rw [ht]; exact h.marker z, by rw [hp]; exact h.mismatchPos, h.firstSize,
    h.secondSize⟩

/-- A counter pair with its heads transports. -/
theorem PairRep.congr {lay : Layout} {lsb : ℤ} {width a b : ℕ}
    (h : PairRep lay lsb width cfg a b) : PairRep lay lsb width cfg' a b :=
  ⟨h.toPairData.congr ht hp, by rw [hp]; exact h.firstPos, by rw [hp]; exact h.secondPos⟩

/-- An idle size pair transports. -/
theorem IdleSize.congr (h : IdleSize cfg) : IdleSize cfg' :=
  ⟨by rw [ht]; exact h.register, by rw [hp]; exact h.registerPos, by rw [ht]; exact h.counter,
    by rw [hp]; exact h.counterPos, by rw [ht]; exact h.marker, by rw [hp]; exact h.mismPos⟩

/-- A size pair being read transports. -/
theorem SizeRead.congr {width r v : ℕ} (h : SizeRead width cfg r v) : SizeRead width cfg' r v :=
  ⟨fun z ↦ by rw [ht]; exact h.register z, by rw [hp]; exact h.registerPos,
    fun z ↦ by rw [ht]; exact h.counter z, by rw [hp]; exact h.counterPos,
    by rw [ht]; exact h.marker,
    by rw [hp, digitsFrom_congr ht, digitsFrom_congr ht]; exact h.mismPos⟩

/-- An idle length pair transports. -/
theorem IdleLength.congr (h : IdleLength cfg) : IdleLength cfg' :=
  ⟨by rw [ht]; exact h.register, by rw [hp]; exact h.registerPos, by rw [ht]; exact h.counter,
    by rw [hp]; exact h.counterPos, by rw [ht]; exact h.marker, by rw [hp]; exact h.mismPos⟩

omit hp in
/-- Transport of the spare cells. -/
theorem SizeSpare.congr {c : ℕ} (h : SizeSpare cfg c) : SizeSpare cfg' c :=
  ⟨fun z hz ↦ by rw [ht]; exact h.registerNeg z hz, fun z hz ↦ by rw [ht]; exact h.counterNeg z hz,
    fun j hj ↦ by rw [ht]; exact h.counterBeyond j hj⟩

/-- A length pair being read transports. -/
theorem LengthRead.congr {r v : ℕ} (h : LengthRead cfg r v) : LengthRead cfg' r v :=
  ⟨by rw [digitsFrom_congr ht]; exact h.digits, fun j ↦ by rw [ht]; exact h.blank j,
    fun z ↦ by rw [ht]; exact h.untagged z, fun z hz ↦ by rw [ht]; exact h.beyond z hz,
    by rw [hp]; exact h.registerPos, by rw [ht]; exact h.counter, by rw [hp]; exact h.counterPos,
    by rw [ht]; exact h.marker, by rw [hp]; exact h.mismPos, h.spare.congr ht⟩

/-- The phase data transports. -/
theorem PhaseRep.congr {width : ℕ} {a : Account} (h : PhaseRep width cfg a) :
    PhaseRep width cfg' a := by
  unfold PhaseRep at h ⊢
  rcases hs : a.state with ⟨m, k⟩
  rw [hs] at h
  cases m with
  | size r v => exact ⟨h.1.congr ht hp, h.2.congr ht hp⟩
  | length r v => exact ⟨h.1.congr ht hp, h.2.congr ht hp⟩
  | payload r =>
    exact ⟨h.1.congr ht hp, h.2.1.congr ht hp, fun z hz ↦ by rw [ht, ht]; exact h.2.2 z hz⟩
  | tree => exact ⟨h.1.congr ht hp, h.2.congr ht hp⟩
  | zeros z => exact ⟨h.1.congr ht hp, h.2.congr ht hp⟩
  | done => exact ⟨h.1.congr ht hp, h.2.congr ht hp⟩
  | dead => exact ⟨h.1.congr ht hp, h.2.congr ht hp⟩

/-- The live representation transports. -/
theorem LiveRep.congr {width : ℕ} {a : Account} (h : LiveRep width cfg a) :
    LiveRep width cfg' a :=
  ⟨h.pending.congr ht hp, by rw [hp]; exact h.forksPos, by rw [hp]; exact h.leavesPos,
    h.phase.congr ht hp⟩

omit ht in
/-- The head bound transports. -/
theorem HeadBound.congr {width : ℕ} (h : HeadBound width cfg) : HeadBound width cfg' :=
  fun i ↦ by rw [hp]; exact h i

end Congr

/-- A live boundary of a valid account is a boundary. -/
theorem Represents.ofLive {input : List (Fin 4)} {n width : ℕ}
    {cfg : Cfg 9 (Fin 4) Control input} {a : Account} (hs : cfg.state = some (phaseState a.state))
    (h : LiveRep width cfg a) (hv : AccountValid n a) (hw : a.forks.size + 1 ≤ width) :
    Represents width cfg a :=
  ⟨hs, h.headBound hv hw, fun _ ↦ h⟩

/-- An abandoned account is represented by the rejecting state within the head bounds. -/
theorem Represents.dead {input : List (Fin 4)} {width : ℕ}
    {cfg : Cfg 9 (Fin 4) Control input} {a : Account} (hd : a.state.1 = .dead)
    (hs : cfg.state = some stDead) (hb : HeadBound width cfg) : Represents width cfg a :=
  ⟨by
    rcases hst : a.state with ⟨m, k⟩
    rw [hst] at hd
    simp only at hd
    subst hd
    exact hs, hb, fun h ↦ (h hd).elim⟩

end Geb.BitTree.EliasBinary
