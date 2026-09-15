/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The copying phases

Copying a register onto an empty one takes one sweep of two heads.
{lit}`copyWalk` moves both right while the source reads a bit, writing the bit
read at the destination's cell, and halts on the blank after the source's
word, the destination then holding that word. {lit}`revWalk` moves the
source's head left from the word's last cell instead, so that the destination
receives the word's reverse, and moves the source's head right on halting,
which parks it.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`copyWalk` — copy one register onto an empty one.
* {lit}`revWalk` — copy the reverse of one register onto an empty one.
* {lit}`copyCfg`, {lit}`revCfg` — the closed forms of the two sweeps'
  configurations.

# Main statements

* {lit}`copyWalk_runsTo`, {lit}`revWalk_runsTo` — the run of each machine,
  naming the halted configuration and the step count.

# Tags

Turing machine, register, copying
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Copy tape {lit}`i` onto tape {lit}`j` cell by cell, both heads moving
right, until {lit}`i` reads a blank; halt without moving. -/
@[expose] def copyWalk {k : ℕ} (i j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some b =>
      { inputMove := 0
        workActions := fun l ↦ if l = j then (some (some b), 1) else if l = i then (none, 1)
          else (none, 0)
        outS := none, q' := some () }
    | none =>
      { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none }

/-- Copy tape {lit}`i` onto tape {lit}`j` cell by cell, {lit}`i`'s head moving
left and {lit}`j`'s right, until {lit}`i` reads a blank; then move {lit}`i`
right and halt. -/
@[expose] def revWalk {k : ℕ} (i j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work i with
    | some b =>
      { inputMove := 0
        workActions := fun l ↦ if l = j then (some (some b), 1) else if l = i then (none, -1)
          else (none, 0)
        outS := none, q' := some () }
    | none =>
      { inputMove := 0, workActions := fun l ↦ (none, if l = i then 1 else 0),
        outS := none, q' := none }

/-- The configuration of {name}`copyWalk` after {lit}`s` steps from parked
heads, tape {lit}`i` holding {lit}`w` and tape {lit}`j` empty. -/
@[expose] def copyCfg {k : ℕ} {input : List Bool} (i j : Fin k) (cfg : Cfg k Bool Unit input)
    (w : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapes := Function.update cfg.workTapes j (tapeOf (w.drop (w.length - s)))
    workTapePos := Function.update (Function.update cfg.workTapePos i (s : ℤ)) j (s : ℤ) }

/-- {name}`copyWalk` from parked heads, {lit}`i` holding {lit}`w` and
{lit}`j` empty, runs {lit}`w.length + 1` steps; {lit}`j` then holds {lit}`w`
and both heads are at {lit}`w.length`. -/
theorem copyWalk_runsTo {k : ℕ} {input : List Bool} (i j : Fin k) (hij : i ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (w : List Bool) (hi : cfg.workTapes i = tapeOf w) (hj : cfg.workTapes j = tapeOf [])
    (hpi : cfg.workTapePos i = 0) (hpj : cfg.workTapePos j = 0) (B : ℕ) (hB : w.length ≤ B)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (copyWalk i j) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w)
        workTapePos :=
          Function.update (Function.update cfg.workTapePos i (w.length : ℤ)) j (w.length : ℤ) }
      (w.length + 1) B := by
  have htrS : ∀ (inp : Option Bool) (work : Fin k → Option Bool) (b : Bool), work i = some b →
      (copyWalk i j).tr () inp work =
        { inputMove := 0
          workActions := fun l ↦ if l = j then (some (some b), 1) else if l = i then (none, 1)
            else (none, 0)
          outS := none, q' := some () } := by
    intro inp work b hb
    simp only [copyWalk, hb]
  have htrN : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = none →
      (copyWalk i j).tr () inp work =
        { inputMove := 0, workActions := fun _ ↦ (none, 0), outS := none, q' := none } := by
    intro inp work hb
    simp only [copyWalk, hb]
  have hsym : ∀ s : ℕ, (copyCfg i j cfg w s).workTapeSymbols i = tapeOf w (s : ℤ) := by
    intro s
    change Function.update cfg.workTapes j (tapeOf (w.drop (w.length - s))) i
      (Function.update (Function.update cfg.workTapePos i (s : ℤ)) j (s : ℤ) i) = _
    simp only [Function.update_of_ne hij, Function.update_self, hi]
  have hbound : ∀ a b : ℤ, -1 ≤ a → a ≤ B → -1 ≤ b → b ≤ B → ∀ l,
      -1 ≤ Function.update (Function.update cfg.workTapePos i a) j b l ∧
        Function.update (Function.update cfg.workTapePos i a) j b l ≤ B :=
    fun a b ha haB hb hbB l ↦ update_workTapePos_bounds j
      (fun m ↦ update_workTapePos_bounds i hpos a ha haB m) b hb hbB l
  have hstep : ∀ s : ℕ, s < w.length →
      (copyWalk i j).step (copyCfg i j cfg w s) = copyCfg i j cfg w (s + 1) := by
    intro s hs
    have hidx : s < w.reverse.length := by simp; omega
    have hb : (copyCfg i j cfg w s).workTapeSymbols i = some (w.reverse[s]'hidx) := by
      rw [hsym s, tapeOf_of_lt w _ (by omega) (by omega)]
      simp
    rw [step_of_state _ _ () rfl, htrS _ _ _ hb]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes j (tapeOf (w.drop (w.length - s))) j)
            (Function.update (Function.update cfg.workTapePos i (s : ℤ)) j (s : ℤ) j)
            (some (w.reverse[s]'hidx)) =
          Function.update cfg.workTapes j (tapeOf (w.drop (w.length - (s + 1)))) j
        rw [Function.update_self, Function.update_self, Function.update_self,
          drop_length_sub_succ w s hs, tapeOf_cons,
          show (((w.drop (w.length - s)).length : ℕ) : ℤ) = (s : ℤ) by
            rw [List.length_drop]; omega]
      · rw [ite_eq_right hl]
        by_cases hli : l = i
        · rw [hli, ite_eq_left rfl]
          change Function.update cfg.workTapes j (tapeOf (w.drop (w.length - s))) i =
            Function.update cfg.workTapes j (tapeOf (w.drop (w.length - (s + 1)))) i
          rw [Function.update_of_ne hij, Function.update_of_ne hij]
        · rw [ite_eq_right hli]
          change Function.update cfg.workTapes j (tapeOf (w.drop (w.length - s))) l =
            Function.update cfg.workTapes j (tapeOf (w.drop (w.length - (s + 1)))) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapePos i (s : ℤ)) j (s : ℤ) j +
            ((1 : SignType) : ℤ) =
          Function.update (Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ)) j
            ((s + 1 : ℕ) : ℤ) j
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hl]
        by_cases hli : l = i
        · rw [hli, ite_eq_left rfl]
          change Function.update (Function.update cfg.workTapePos i (s : ℤ)) j (s : ℤ) i +
              ((1 : SignType) : ℤ) =
            Function.update (Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ)) j
              ((s + 1 : ℕ) : ℤ) i
          rw [Function.update_of_ne hij, Function.update_of_ne hij, Function.update_self,
            Function.update_self, SignType.coe_one]
          omega
        · rw [ite_eq_right hli]
          change Function.update (Function.update cfg.workTapePos i (s : ℤ)) j (s : ℤ) l +
              ((0 : SignType) : ℤ) =
            Function.update (Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ)) j
              ((s + 1 : ℕ) : ℤ) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl, Function.update_of_ne hli,
            Function.update_of_ne hli, SignType.coe_zero, add_zero]
  have hhalt : (copyWalk i j).step (copyCfg i j cfg w w.length) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w)
        workTapePos :=
          Function.update (Function.update cfg.workTapePos i (w.length : ℤ)) j
            (w.length : ℤ) } := by
    have hb : (copyCfg i j cfg w w.length).workTapeSymbols i = none := by
      rw [hsym _, tapeOf_of_le w _ (by omega)]
    rw [step_of_state _ _ () rfl, htrN _ _ hb]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext l
      change Function.update cfg.workTapes j (tapeOf (w.drop (w.length - w.length))) l =
        Function.update cfg.workTapes j (tapeOf w) l
      rw [Nat.sub_self, List.drop_zero]
    · funext l
      change Function.update (Function.update cfg.workTapePos i ((w.length : ℕ) : ℤ)) j
          ((w.length : ℕ) : ℤ) l + ((0 : SignType) : ℤ) =
        Function.update (Function.update cfg.workTapePos i (w.length : ℤ)) j (w.length : ℤ) l
      rw [SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ, (copyWalk i j).outputSymbol (copyCfg i j cfg w s) = none := by
    intro s
    change ((copyWalk i j).tr () (copyCfg i j cfg w s).inputSymbol
      (copyCfg i j cfg w s).workTapeSymbols).outS = none
    rcases hw : (copyCfg i j cfg w s).workTapeSymbols i with _ | b
    · rw [htrN _ _ hw]
    · rw [htrS _ _ _ hw]
  have hzero : copyCfg i j cfg w 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · change Function.update cfg.workTapes j (tapeOf (w.drop (w.length - 0))) = cfg.workTapes
      rw [Nat.sub_zero, List.drop_length, ← hj, Function.update_eq_self]
    · funext l
      change Function.update (Function.update cfg.workTapePos i ((0 : ℕ) : ℤ)) j ((0 : ℕ) : ℤ) l =
        cfg.workTapePos l
      by_cases hl : l = j
      · rw [hl, Function.update_self]
        omega
      · rw [Function.update_of_ne hl]
        by_cases hli : l = i
        · rw [hli, Function.update_self]
          omega
        · rw [Function.update_of_ne hli]
  have key : ∀ s : ℕ, s ≤ w.length →
      (copyWalk i j).configs cfg s = copyCfg i j cfg w s ∧
        (copyWalk i j).outputString cfg s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨by rw [configs_zero, hzero], rfl⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s]
        rfl
  obtain ⟨hcn, hon⟩ := key w.length (le_refl _)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact Option.some_ne_none _
  · rw [configs_succ_eq_step', hcn, hhalt]
  · intro t' ht' l
    by_cases hlt : t' ≤ w.length
    · rw [(key t' hlt).1]
      exact hbound (t' : ℤ) (t' : ℤ) (by omega) (by omega) (by omega) (by omega) l
    · rw [show t' = w.length + 1 by omega, configs_succ_eq_step', hcn, hhalt]
      exact hbound (w.length : ℤ) (w.length : ℤ) (by omega) (by omega) (by omega) (by omega) l
  · rw [outputString_succ, hon, hcn, hout _]
    rfl

/-- The configuration of {name}`revWalk` after {lit}`s` steps from a start in
its initial state with {lit}`i`'s head at cell {lit}`w.length - 1` of a
register holding {lit}`w` and {lit}`j` empty and parked. -/
@[expose] def revCfg {k : ℕ} {input : List Bool} (i j : Fin k) (cfg : Cfg k Bool Unit input)
    (w : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapes := Function.update cfg.workTapes j (tapeOf (w.take s).reverse)
    workTapePos :=
      Function.update (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s)) j (s : ℤ) }

/-- {name}`revWalk` from {lit}`i`'s head at {lit}`w.length - 1` on a register
holding {lit}`w` and {lit}`j` empty and parked runs {lit}`w.length + 1`
steps; {lit}`j` then holds {lit}`w.reverse` with its head at {lit}`w.length`,
and {lit}`i`'s head is parked. -/
theorem revWalk_runsTo {k : ℕ} {input : List Bool} (i j : Fin k) (hij : i ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (w : List Bool) (hi : cfg.workTapes i = tapeOf w) (hj : cfg.workTapes j = tapeOf [])
    (hpi : cfg.workTapePos i = (w.length : ℤ) - 1) (hpj : cfg.workTapePos j = 0) (B : ℕ)
    (hB : w.length ≤ B)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (revWalk i j) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w.reverse)
        workTapePos := Function.update (Function.update cfg.workTapePos i 0) j (w.length : ℤ) }
      (w.length + 1) B := by
  have htrS : ∀ (inp : Option Bool) (work : Fin k → Option Bool) (b : Bool), work i = some b →
      (revWalk i j).tr () inp work =
        { inputMove := 0
          workActions := fun l ↦ if l = j then (some (some b), 1) else if l = i then (none, -1)
            else (none, 0)
          outS := none, q' := some () } := by
    intro inp work b hb
    simp only [revWalk, hb]
  have htrN : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work i = none →
      (revWalk i j).tr () inp work =
        { inputMove := 0, workActions := fun l ↦ (none, if l = i then 1 else 0),
          outS := none, q' := none } := by
    intro inp work hb
    simp only [revWalk, hb]
  have hsym : ∀ s : ℕ, (revCfg i j cfg w s).workTapeSymbols i =
      tapeOf w ((w.length : ℤ) - 1 - s) := by
    intro s
    change Function.update cfg.workTapes j (tapeOf (w.take s).reverse) i
      (Function.update (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s)) j (s : ℤ) i)
      = _
    simp only [Function.update_of_ne hij, Function.update_self, hi]
  have hbound : ∀ a b : ℤ, -1 ≤ a → a ≤ B → -1 ≤ b → b ≤ B → ∀ l,
      -1 ≤ Function.update (Function.update cfg.workTapePos i a) j b l ∧
        Function.update (Function.update cfg.workTapePos i a) j b l ≤ B :=
    fun a b ha haB hb hbB l ↦ update_workTapePos_bounds j
      (fun m ↦ update_workTapePos_bounds i hpos a ha haB m) b hb hbB l
  have hstep : ∀ s : ℕ, s < w.length →
      (revWalk i j).step (revCfg i j cfg w s) = revCfg i j cfg w (s + 1) := by
    intro s hs
    have hrev : w.reverse[((w.length : ℤ) - 1 - (s : ℤ)).toNat]'(by simp; omega) = w[s]'hs := by
      rw [List.getElem_reverse]
      congr 1
      omega
    have hb : (revCfg i j cfg w s).workTapeSymbols i = some (w[s]'hs) := by
      rw [hsym s, tapeOf_of_lt w _ (by omega) (by omega), hrev]
    rw [step_of_state _ _ () rfl, htrS _ _ _ hb]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes j (tapeOf (w.take s).reverse) j)
            (Function.update (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s)) j
              (s : ℤ) j)
            (some (w[s]'hs)) =
          Function.update cfg.workTapes j (tapeOf (w.take (s + 1)).reverse) j
        rw [Function.update_self, Function.update_self, Function.update_self,
          reverse_take_succ w s hs, tapeOf_cons,
          show (((w.take s).reverse.length : ℕ) : ℤ) = (s : ℤ) by
            rw [List.length_reverse, List.length_take]; omega]
      · rw [ite_eq_right hl]
        by_cases hli : l = i
        · rw [hli, ite_eq_left rfl]
          change Function.update cfg.workTapes j (tapeOf (w.take s).reverse) i =
            Function.update cfg.workTapes j (tapeOf (w.take (s + 1)).reverse) i
          rw [Function.update_of_ne hij, Function.update_of_ne hij]
        · rw [ite_eq_right hli]
          change Function.update cfg.workTapes j (tapeOf (w.take s).reverse) l =
            Function.update cfg.workTapes j (tapeOf (w.take (s + 1)).reverse) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s)) j
            (s : ℤ) j + ((1 : SignType) : ℤ) =
          Function.update (Function.update cfg.workTapePos i
            ((w.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ))) j ((s + 1 : ℕ) : ℤ) j
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hl]
        by_cases hli : l = i
        · rw [hli, ite_eq_left rfl]
          change Function.update (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s)) j
              (s : ℤ) i + ((-1 : SignType) : ℤ) =
            Function.update (Function.update cfg.workTapePos i
              ((w.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ))) j ((s + 1 : ℕ) : ℤ) i
          rw [Function.update_of_ne hij, Function.update_of_ne hij, Function.update_self,
            Function.update_self, SignType.coe_neg_one]
          omega
        · rw [ite_eq_right hli]
          change Function.update (Function.update cfg.workTapePos i ((w.length : ℤ) - 1 - s)) j
              (s : ℤ) l + ((0 : SignType) : ℤ) =
            Function.update (Function.update cfg.workTapePos i
              ((w.length : ℤ) - 1 - ((s + 1 : ℕ) : ℤ))) j ((s + 1 : ℕ) : ℤ) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl, Function.update_of_ne hli,
            Function.update_of_ne hli, SignType.coe_zero, add_zero]
  have hhalt : (revWalk i j).step (revCfg i j cfg w w.length) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf w.reverse)
        workTapePos :=
          Function.update (Function.update cfg.workTapePos i 0) j (w.length : ℤ) } := by
    have hb : (revCfg i j cfg w w.length).workTapeSymbols i = none := by
      rw [hsym _, tapeOf_neg w _ (by omega)]
    rw [step_of_state _ _ () rfl, htrN _ _ hb]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext l
      change Function.update cfg.workTapes j (tapeOf (w.take w.length).reverse) l =
        Function.update cfg.workTapes j (tapeOf w.reverse) l
      rw [List.take_length]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_right (fun h ↦ hij h.symm)]
        change Function.update (Function.update cfg.workTapePos i
            ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ))) j ((w.length : ℕ) : ℤ) j +
            ((0 : SignType) : ℤ) =
          Function.update (Function.update cfg.workTapePos i 0) j (w.length : ℤ) j
        rw [Function.update_self, Function.update_self, SignType.coe_zero, add_zero]
      · by_cases hli : l = i
        · rw [hli, ite_eq_left rfl]
          change Function.update (Function.update cfg.workTapePos i
              ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ))) j ((w.length : ℕ) : ℤ) i +
              ((1 : SignType) : ℤ) =
            Function.update (Function.update cfg.workTapePos i 0) j (w.length : ℤ) i
          rw [Function.update_of_ne hij, Function.update_of_ne hij, Function.update_self,
            Function.update_self, SignType.coe_one]
          omega
        · rw [ite_eq_right hli]
          change Function.update (Function.update cfg.workTapePos i
              ((w.length : ℤ) - 1 - ((w.length : ℕ) : ℤ))) j ((w.length : ℕ) : ℤ) l +
              ((0 : SignType) : ℤ) =
            Function.update (Function.update cfg.workTapePos i 0) j (w.length : ℤ) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl, Function.update_of_ne hli,
            Function.update_of_ne hli, SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ, (revWalk i j).outputSymbol (revCfg i j cfg w s) = none := by
    intro s
    change ((revWalk i j).tr () (revCfg i j cfg w s).inputSymbol
      (revCfg i j cfg w s).workTapeSymbols).outS = none
    rcases hw : (revCfg i j cfg w s).workTapeSymbols i with _ | b
    · rw [htrN _ _ hw]
    · rw [htrS _ _ _ hw]
  have hzero : revCfg i j cfg w 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · change Function.update cfg.workTapes j (tapeOf (w.take 0).reverse) = cfg.workTapes
      rw [List.take_zero, List.reverse_nil, ← hj, Function.update_eq_self]
    · funext l
      change Function.update (Function.update cfg.workTapePos i
          ((w.length : ℤ) - 1 - ((0 : ℕ) : ℤ))) j ((0 : ℕ) : ℤ) l = cfg.workTapePos l
      by_cases hl : l = j
      · rw [hl, Function.update_self]
        omega
      · rw [Function.update_of_ne hl]
        by_cases hli : l = i
        · rw [hli, Function.update_self]
          omega
        · rw [Function.update_of_ne hli]
  have key : ∀ s : ℕ, s ≤ w.length →
      (revWalk i j).configs cfg s = revCfg i j cfg w s ∧
        (revWalk i j).outputString cfg s = [] := by
    refine Nat.rec ?_ ?_
    · intro _
      exact ⟨by rw [configs_zero, hzero], rfl⟩
    · intro s ih hs
      obtain ⟨hc, ho⟩ := ih (by omega)
      refine ⟨?_, ?_⟩
      · rw [configs_succ_eq_step', hc, hstep s (by omega)]
      · rw [outputString_succ, ho, hc, hout s]
        rfl
  obtain ⟨hcn, hon⟩ := key w.length (le_refl _)
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, rfl⟩
  · intro t' ht'
    rw [(key t' (by omega)).1]
    exact Option.some_ne_none _
  · rw [configs_succ_eq_step', hcn, hhalt]
  · intro t' ht' l
    by_cases hlt : t' ≤ w.length
    · rw [(key t' hlt).1]
      exact hbound ((w.length : ℤ) - 1 - t') (t' : ℤ) (by omega) (by omega) (by omega)
        (by omega) l
    · rw [show t' = w.length + 1 by omega, configs_succ_eq_step', hcn, hhalt]
      exact hbound 0 (w.length : ℤ) (by omega) (by omega) (by omega) (by omega) l
  · rw [outputString_succ, hon, hcn, hout _]
    rfl

end

end Geb.SizeBounded.Machine
