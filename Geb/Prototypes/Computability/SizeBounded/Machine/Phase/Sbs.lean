/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Program
public import Geb.Prototypes.Computability.SizeBounded.Basic
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Walk -- shake: keep
import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return

set_option doc.verso true

/-!
# The successor phase

The size-bounded successor prepends a bit to the word held by one register
when the result is no longer than the word held by a second, and leaves the
first word alone otherwise. {lit}`sbsWalk` copies the first register onto an
empty one as {name}`Geb.SizeBounded.Machine.copyWalk` does, with the second
register's head moving right alongside the source's while it reads a bit; at
the blank after the source's word the bit is written, and the destination's
head moved, exactly when the second head still reads a bit, which is the
condition of {name}`Geb.SizeBounded.sbsSem`.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`sbsWalk` — the machine of the size-bounded successor.
* {lit}`sbsCfg` — the closed form of its configurations.

# Main statements

* {lit}`sbsWalk_runsTo` — the run of the machine, naming the halted
  configuration and the step count.

# Tags

Turing machine, register, successor
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM

public section

/-- Copy tape {lit}`x` onto tape {lit}`j` as {name}`copyWalk` does, moving
{lit}`y`'s head right alongside while it reads a bit; when {lit}`x` reads a
blank, write {lit}`b` on {lit}`j` and move its head right if {lit}`y` still
reads a bit, and halt. -/
@[expose] def sbsWalk {k : ℕ} (b : Bool) (x y j : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    match work x with
    | some c =>
      { inputMove := 0
        workActions := fun l ↦ if l = j then (some (some c), 1) else if l = x then (none, 1)
          else if l = y then (none, if (work y).isSome then 1 else 0) else (none, 0)
        outS := none, q' := some () }
    | none =>
      { inputMove := 0
        workActions := fun l ↦
          if l = j then (if (work y).isSome then (some (some b), 1) else (none, 0)) else (none, 0)
        outS := none, q' := none }

/-- The configuration of {name}`sbsWalk` after {lit}`s` steps from parked
heads, tape {lit}`x` holding {lit}`u`, tape {lit}`y` holding {lit}`v` and tape
{lit}`j` empty. -/
@[expose] def sbsCfg {k : ℕ} {input : List Bool} (x y j : Fin k)
    (cfg : Cfg k Bool Unit input) (u v : List Bool) (s : ℕ) : Cfg k Bool Unit input :=
  { cfg with
    state := some ()
    workTapes := Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s)))
    workTapePos :=
      Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
        ((min s v.length : ℕ) : ℤ)) j (s : ℤ) }

/-- {name}`sbsWalk` from parked heads, {lit}`x` holding {lit}`u`, {lit}`y`
holding {lit}`v` and {lit}`j` empty, runs {lit}`u.length + 1` steps; {lit}`j`
then holds {name}`Geb.SizeBounded.sbsSem` at {lit}`b`, {lit}`u` and {lit}`v`
with its head after it, {lit}`x`'s head is at {lit}`u.length` and {lit}`y`'s
at the smaller of the two lengths. -/
theorem sbsWalk_runsTo {k : ℕ} {input : List Bool} (b : Bool) (x y j : Fin k)
    (hxy : x ≠ y) (hxj : x ≠ j) (hyj : y ≠ j)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ())
    (u v : List Bool) (hx : cfg.workTapes x = tapeOf u) (hy : cfg.workTapes y = tapeOf v)
    (hj : cfg.workTapes j = tapeOf [])
    (hpx : cfg.workTapePos x = 0) (hpy : cfg.workTapePos y = 0) (hpj : cfg.workTapePos j = 0)
    (B : ℕ) (hu : u.length ≤ B) (hv : v.length ≤ B)
    (hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B) :
    RunsTo (sbsWalk b x y j) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b u v))
        workTapePos :=
          Function.update (Function.update (Function.update cfg.workTapePos x (u.length : ℤ)) y
            (min u.length v.length : ℕ)) j ((sbsSem b u v).length : ℤ) }
      (u.length + 1) B := by
  have htrS : ∀ (inp : Option Bool) (work : Fin k → Option Bool) (c : Bool), work x = some c →
      (sbsWalk b x y j).tr () inp work =
        { inputMove := 0
          workActions := fun l ↦ if l = j then (some (some c), 1) else if l = x then (none, 1)
            else if l = y then (none, if (work y).isSome then 1 else 0) else (none, 0)
          outS := none, q' := some () } := by
    intro inp work c hc
    simp only [sbsWalk, hc]
  have htrN : ∀ (inp : Option Bool) (work : Fin k → Option Bool), work x = none →
      (sbsWalk b x y j).tr () inp work =
        { inputMove := 0
          workActions := fun l ↦
            if l = j then (if (work y).isSome then (some (some b), 1) else (none, 0))
            else (none, 0)
          outS := none, q' := none } := by
    intro inp work hc
    simp only [sbsWalk, hc]
  have hsymX : ∀ s : ℕ, (sbsCfg x y j cfg u v s).workTapeSymbols x = tapeOf u (s : ℤ) := by
    intro s
    change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s))) x
      (Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
        ((min s v.length : ℕ) : ℤ)) j (s : ℤ) x) = _
    simp only [Function.update_of_ne hxj, Function.update_of_ne hxy, Function.update_self, hx]
  have hsymY : ∀ s : ℕ, (sbsCfg x y j cfg u v s).workTapeSymbols y =
      tapeOf v ((min s v.length : ℕ) : ℤ) := by
    intro s
    change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s))) y
      (Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
        ((min s v.length : ℕ) : ℤ)) j (s : ℤ) y) = _
    simp only [Function.update_of_ne hyj, Function.update_self, hy]
  have hyS : ∀ s : ℕ, s < v.length →
      ((sbsCfg x y j cfg u v s).workTapeSymbols y).isSome = true := by
    intro s hsv
    rw [hsymY s, tapeOf_of_lt v _ (by omega) (by omega)]
    rfl
  have hyN : ∀ s : ℕ, v.length ≤ s → (sbsCfg x y j cfg u v s).workTapeSymbols y = none := by
    intro s hsv
    rw [hsymY s, tapeOf_of_le v _ (by omega)]
  have hmove : ∀ s : ℕ,
      (if ((sbsCfg x y j cfg u v s).workTapeSymbols y).isSome then (1 : SignType) else 0) =
        if s < v.length then 1 else 0 := by
    intro s
    by_cases hsv : s < v.length
    · rw [hyS s hsv, ite_eq_left rfl, ite_eq_left hsv]
    · rw [hyN s (by omega), ite_eq_right (by simp), ite_eq_right hsv]
  have hbound : ∀ a c d : ℤ, -1 ≤ a → a ≤ B → -1 ≤ c → c ≤ B → -1 ≤ d → d ≤ B → ∀ l,
      -1 ≤ Function.update (Function.update (Function.update cfg.workTapePos x a) y c) j d l ∧
        Function.update (Function.update (Function.update cfg.workTapePos x a) y c) j d l ≤ B :=
    fun a c d ha haB hc hcB hd hdB l ↦ update_workTapePos_bounds j
      (fun m ↦ update_workTapePos_bounds y
        (fun n ↦ update_workTapePos_bounds x hpos a ha haB n) c hc hcB m) d hd hdB l
  have hstep : ∀ s : ℕ, s < u.length →
      (sbsWalk b x y j).step (sbsCfg x y j cfg u v s) = sbsCfg x y j cfg u v (s + 1) := by
    intro s hs
    have hidx : s < u.reverse.length := by simp; omega
    have hb : (sbsCfg x y j cfg u v s).workTapeSymbols x = some (u.reverse[s]'hidx) := by
      rw [hsymX s, tapeOf_of_lt u _ (by omega) (by omega)]
      simp
    rw [step_of_state _ _ () rfl, htrS _ _ _ hb, hmove s]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_left rfl]
        change Function.update (Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s))) j)
            (Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
              ((min s v.length : ℕ) : ℤ)) j (s : ℤ) j)
            (some (u.reverse[s]'hidx)) =
          Function.update cfg.workTapes j (tapeOf (u.drop (u.length - (s + 1)))) j
        rw [Function.update_self, Function.update_self, Function.update_self,
          drop_length_sub_succ u s hs, tapeOf_cons,
          show (((u.drop (u.length - s)).length : ℕ) : ℤ) = (s : ℤ) by
            rw [List.length_drop]; omega]
      · rw [ite_eq_right hl]
        by_cases hlx : l = x
        · rw [hlx, ite_eq_left rfl]
          change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s))) x =
            Function.update cfg.workTapes j (tapeOf (u.drop (u.length - (s + 1)))) x
          rw [Function.update_of_ne hxj, Function.update_of_ne hxj]
        · rw [ite_eq_right hlx]
          by_cases hly : l = y
          · rw [hly, ite_eq_left rfl]
            change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s))) y =
              Function.update cfg.workTapes j (tapeOf (u.drop (u.length - (s + 1)))) y
            rw [Function.update_of_ne hyj, Function.update_of_ne hyj]
          · rw [ite_eq_right hly]
            change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - s))) l =
              Function.update cfg.workTapes j (tapeOf (u.drop (u.length - (s + 1)))) l
            rw [Function.update_of_ne hl, Function.update_of_ne hl]
    · funext l
      dsimp only
      by_cases hl : l = j
      · rw [hl, ite_eq_left rfl]
        change Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
            ((min s v.length : ℕ) : ℤ)) j (s : ℤ) j + ((1 : SignType) : ℤ) =
          Function.update (Function.update (Function.update cfg.workTapePos x ((s + 1 : ℕ) : ℤ)) y
            ((min (s + 1) v.length : ℕ) : ℤ)) j ((s + 1 : ℕ) : ℤ) j
        rw [Function.update_self, Function.update_self, SignType.coe_one]
        omega
      · rw [ite_eq_right hl]
        by_cases hlx : l = x
        · rw [hlx, ite_eq_left rfl]
          change Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
              ((min s v.length : ℕ) : ℤ)) j (s : ℤ) x + ((1 : SignType) : ℤ) =
            Function.update (Function.update (Function.update cfg.workTapePos x ((s + 1 : ℕ) : ℤ))
              y ((min (s + 1) v.length : ℕ) : ℤ)) j ((s + 1 : ℕ) : ℤ) x
          rw [Function.update_of_ne hxj, Function.update_of_ne hxj, Function.update_of_ne hxy,
            Function.update_of_ne hxy, Function.update_self, Function.update_self,
            SignType.coe_one]
          omega
        · rw [ite_eq_right hlx]
          by_cases hly : l = y
          · rw [hly, ite_eq_left rfl]
            change Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
                ((min s v.length : ℕ) : ℤ)) j (s : ℤ) y +
                ((if s < v.length then 1 else 0 : SignType) : ℤ) =
              Function.update (Function.update (Function.update cfg.workTapePos x
                ((s + 1 : ℕ) : ℤ)) y ((min (s + 1) v.length : ℕ) : ℤ)) j ((s + 1 : ℕ) : ℤ) y
            rw [Function.update_of_ne hyj, Function.update_of_ne hyj, Function.update_self,
              Function.update_self]
            by_cases hsv : s < v.length
            · rw [ite_eq_left hsv, SignType.coe_one]
              omega
            · rw [ite_eq_right hsv, SignType.coe_zero]
              omega
          · rw [ite_eq_right hly]
            change Function.update (Function.update (Function.update cfg.workTapePos x (s : ℤ)) y
                ((min s v.length : ℕ) : ℤ)) j (s : ℤ) l + ((0 : SignType) : ℤ) =
              Function.update (Function.update (Function.update cfg.workTapePos x
                ((s + 1 : ℕ) : ℤ)) y ((min (s + 1) v.length : ℕ) : ℤ)) j ((s + 1 : ℕ) : ℤ) l
            rw [Function.update_of_ne hl, Function.update_of_ne hl, Function.update_of_ne hly,
              Function.update_of_ne hly, Function.update_of_ne hlx, Function.update_of_ne hlx,
              SignType.coe_zero, add_zero]
  have hhalt : (sbsWalk b x y j).step (sbsCfg x y j cfg u v u.length) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes j (tapeOf (sbsSem b u v))
        workTapePos :=
          Function.update (Function.update (Function.update cfg.workTapePos x (u.length : ℤ)) y
            (min u.length v.length : ℕ)) j ((sbsSem b u v).length : ℤ) } := by
    have hb : (sbsCfg x y j cfg u v u.length).workTapeSymbols x = none := by
      rw [hsymX _, tapeOf_of_le u _ (by omega)]
    rw [step_of_state _ _ () rfl, htrN _ _ hb]
    unfold sbsSem
    by_cases h : u.length + 1 ≤ v.length
    · rw [hyS u.length (by omega), ite_eq_left rfl, ite_eq_left h]
      apply Cfg.ext
      · rfl
      · change moveInputPos cfg.inputPos 0 = cfg.inputPos
        rw [moveInputPos_zero]
      · funext l
        dsimp only
        by_cases hl : l = j
        · rw [hl, ite_eq_left rfl]
          change Function.update (Function.update cfg.workTapes j
              (tapeOf (u.drop (u.length - u.length))) j)
              (Function.update (Function.update (Function.update cfg.workTapePos x
                ((u.length : ℕ) : ℤ)) y ((min u.length v.length : ℕ) : ℤ)) j
                ((u.length : ℕ) : ℤ) j)
              (some b) =
            Function.update cfg.workTapes j (tapeOf (b :: u)) j
          rw [Function.update_self, Function.update_self, Function.update_self, Nat.sub_self,
            List.drop_zero, tapeOf_cons]
        · rw [ite_eq_right hl]
          change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - u.length))) l =
            Function.update cfg.workTapes j (tapeOf (b :: u)) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl]
      · funext l
        dsimp only
        by_cases hl : l = j
        · rw [hl, ite_eq_left rfl]
          change Function.update (Function.update (Function.update cfg.workTapePos x
              ((u.length : ℕ) : ℤ)) y ((min u.length v.length : ℕ) : ℤ)) j ((u.length : ℕ) : ℤ) j +
              ((1 : SignType) : ℤ) =
            Function.update (Function.update (Function.update cfg.workTapePos x (u.length : ℤ)) y
              ((min u.length v.length : ℕ) : ℤ)) j (((b :: u).length : ℕ) : ℤ) j
          rw [Function.update_self, Function.update_self, SignType.coe_one, List.length_cons]
          omega
        · rw [ite_eq_right hl]
          change Function.update (Function.update (Function.update cfg.workTapePos x
              ((u.length : ℕ) : ℤ)) y ((min u.length v.length : ℕ) : ℤ)) j ((u.length : ℕ) : ℤ) l +
              ((0 : SignType) : ℤ) =
            Function.update (Function.update (Function.update cfg.workTapePos x (u.length : ℤ)) y
              ((min u.length v.length : ℕ) : ℤ)) j (((b :: u).length : ℕ) : ℤ) l
          rw [Function.update_of_ne hl, Function.update_of_ne hl, SignType.coe_zero, add_zero]
    · rw [hyN u.length (by omega), ite_eq_right (by simp), ite_eq_right h]
      simp only [ite_self]
      apply Cfg.ext
      · rfl
      · change moveInputPos cfg.inputPos 0 = cfg.inputPos
        rw [moveInputPos_zero]
      · funext l
        change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - u.length))) l =
          Function.update cfg.workTapes j (tapeOf u) l
        rw [Nat.sub_self, List.drop_zero]
      · funext l
        change Function.update (Function.update (Function.update cfg.workTapePos x
            ((u.length : ℕ) : ℤ)) y ((min u.length v.length : ℕ) : ℤ)) j ((u.length : ℕ) : ℤ) l +
            ((0 : SignType) : ℤ) =
          Function.update (Function.update (Function.update cfg.workTapePos x (u.length : ℤ)) y
            ((min u.length v.length : ℕ) : ℤ)) j ((u.length : ℕ) : ℤ) l
        rw [SignType.coe_zero, add_zero]
  have hout : ∀ s : ℕ, (sbsWalk b x y j).outputSymbol (sbsCfg x y j cfg u v s) = none := by
    intro s
    change ((sbsWalk b x y j).tr () (sbsCfg x y j cfg u v s).inputSymbol
      (sbsCfg x y j cfg u v s).workTapeSymbols).outS = none
    rcases hw : (sbsCfg x y j cfg u v s).workTapeSymbols x with _ | c
    · rw [htrN _ _ hw]
    · rw [htrS _ _ _ hw]
  have hzero : sbsCfg x y j cfg u v 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · change Function.update cfg.workTapes j (tapeOf (u.drop (u.length - 0))) = cfg.workTapes
      rw [Nat.sub_zero, List.drop_length, ← hj, Function.update_eq_self]
    · funext l
      change Function.update (Function.update (Function.update cfg.workTapePos x ((0 : ℕ) : ℤ)) y
        ((min 0 v.length : ℕ) : ℤ)) j ((0 : ℕ) : ℤ) l = cfg.workTapePos l
      by_cases hl : l = j
      · rw [hl, Function.update_self]
        omega
      · rw [Function.update_of_ne hl]
        by_cases hly : l = y
        · rw [hly, Function.update_self]
          omega
        · rw [Function.update_of_ne hly]
          by_cases hlx : l = x
          · rw [hlx, Function.update_self]
            omega
          · rw [Function.update_of_ne hlx]
  have hlen : (sbsSem b u v).length ≤ B := by
    unfold sbsSem
    by_cases h : u.length + 1 ≤ v.length
    · rw [ite_eq_left h, List.length_cons]
      omega
    · rw [ite_eq_right h]
      omega
  have key := RunsTo.ofFamily (sbsWalk b x y j) (sbsCfg x y j cfg u v) u.length B _
    (fun _ _ ↦ Option.some_ne_none ()) hstep hhalt rfl (fun s _ ↦ hout s)
    (fun s hs l ↦ hbound (s : ℤ) ((min s v.length : ℕ) : ℤ) (s : ℤ) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) l)
    (fun l ↦ hbound (u.length : ℤ) ((min u.length v.length : ℕ) : ℤ)
      ((sbsSem b u v).length : ℤ) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) l)
  rwa [hzero] at key

end

end Geb.SizeBounded.Machine
