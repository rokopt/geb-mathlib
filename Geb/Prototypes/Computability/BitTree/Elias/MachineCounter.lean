/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Elias.MachineSteps
public import Geb.Prototypes.Computability.BitTree.Elias.Counter
public import Geb.Prototypes.Computability.TreeScanner.Steps

set_option doc.verso true

/-!
# Execution of binary countdowns

The countdown enters its least significant digit from the blank on the right. Borrowing and
the following leftward scan visit the digit positions once; the return scan visits them once
more, retaining whether the decremented counter contains a one.

## Main statements

* {lit}`configs_decrement` gives the exact countdown result and transition count.
* {lit}`configs_decrement_headBound` bounds every intermediate work-tape head.

## Tags

Turing machine, binary counter, decrement, simulation
-/

@[expose] public section

namespace Geb.BitTree.Elias.Machine

open Turing MultiTapeTM
open Geb.TreeScanner (step_of_state)

/-- A stationary-input counter action with no write changes only its selected head and state. -/
theorem counterAction_none_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (bs : List Bool) (q q' : Control) (p p' : ℕ) (d : SignType)
    (htr : machine.tr q (counterCfg cfg v bs q p).inputSymbol
      (counterCfg cfg v bs q p).workTapeSymbols = counterAction v none d q')
    (hp : (p : ℤ) + d = p') :
    machine.step (counterCfg cfg v bs q p) = counterCfg cfg v bs q' p' ∧
      machine.outputSymbol (counterCfg cfg v bs q p) = none := by
  constructor
  · rw [step_of_state _ _ q rfl, htr]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
    · funext i z
      by_cases hi : i = counterTape v <;> simp [counterAction, counterCfg, jump, hi]
    · funext i
      by_cases hi : i = counterTape v <;> simp [counterAction, counterCfg, jump, hi, hp]
  · change (machine.tr q _ _).outS = none
    rw [htr]
    rfl

/-- A writing counter action realizes a prescribed change of the finite digit word. -/
theorem counterAction_write_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (bs bs' : List Bool) (q q' : Control) (p p' : ℕ) (d : SignType) (b : Bool)
    (htr : machine.tr q (counterCfg cfg v bs q p).inputSymbol
      (counterCfg cfg v bs q p).workTapeSymbols =
        counterAction v (some (some (boolEmb b))) d q')
    (hp : (p : ℤ) + d = p')
    (hw : Function.update (wordTape bs) (p : ℤ) (some (boolEmb b)) = wordTape bs') :
    machine.step (counterCfg cfg v bs q p) = counterCfg cfg v bs' q' p' ∧
      machine.outputSymbol (counterCfg cfg v bs q p) = none := by
  constructor
  · rw [step_of_state _ _ q rfl, htr]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
    · funext i z
      by_cases hi : i = counterTape v
      · simp only [counterAction, counterCfg, jump, hi, ↓reduceIte]
        exact congrFun hw z
      · simp [counterAction, counterCfg, jump, hi]
    · funext i
      by_cases hi : i = counterTape v <;> simp [counterAction, counterCfg, jump, hi, hp]
  · change (machine.tr q _ _).outS = none
    rw [htr]
    rfl

/-- Countdown entry moves left from the right-hand blank without writing. -/
theorem step_decrement {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (bs : List Bool) :
    machine.step (counterCfg cfg v bs (stDecrement v) (bs.length + 1)) =
      counterCfg cfg v bs (stBorrow v false) bs.length := by
  rw [step_of_state _ _ (stDecrement v) rfl, tr_decrement]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_
  · funext i z
    by_cases hi : i = counterTape v <;> simp [counterAction, counterCfg, jump, hi]
  · funext i
    by_cases hi : i = counterTape v <;> simp [counterAction, counterCfg, jump, hi]

/-- Countdown entry emits no output. -/
theorem outputSymbol_decrement {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (bs : List Bool) :
    machine.outputSymbol (counterCfg cfg v bs (stDecrement v) (bs.length + 1)) = none := by
  change (machine.tr (stDecrement v) _ _).outS = none
  rw [tr_decrement]
  rfl

/-- The leftward scan inspects the next higher digit and preserves the stored word. -/
theorem left_cons_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen b : Bool) (lower higher : List Bool) :
    machine.step (counterCfg cfg v (lower ++ b :: higher)
      (stLeft v seen) (higher.length + 1)) =
      counterCfg cfg v (lower ++ b :: higher) (stLeft v (seen || b)) higher.length ∧
    machine.outputSymbol (counterCfg cfg v (lower ++ b :: higher)
      (stLeft v seen) (higher.length + 1)) = none := by
  apply counterAction_none_run
  · rw [tr_left]
    have hr : (counterCfg cfg v (lower ++ b :: higher) (stLeft v seen)
        (higher.length + 1)).workTapeSymbols (counterTape v) = some (boolEmb b) := by
      simpa only [Cfg.workTapeSymbols, counterCfg, ite_true] using wordTape_split lower higher b
    simp only [sweepLeft, hr]
    cases b <;> cases seen <;> rfl
  · simp

/-- At the origin, the leftward scan turns right with its accumulated zero-test flag. -/
theorem left_zero_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (bs : List Bool) :
    machine.step (counterCfg cfg v bs (stLeft v seen) 0) =
      counterCfg cfg v bs (stRight v seen) 1 ∧
    machine.outputSymbol (counterCfg cfg v bs (stLeft v seen) 0) = none := by
  apply counterAction_none_run (d := 1)
  · rw [tr_left]
    have hr : (counterCfg cfg v bs (stLeft v seen) 0).workTapeSymbols (counterTape v) =
        some 2 := by simp [counterCfg, Cfg.workTapeSymbols, wordTape_zero]
    simp only [sweepLeft, hr, beq_self_eq_true, ↓reduceIte]
  · rfl

/-- The leftward scan accumulates the disjunction of all unvisited higher digits. -/
theorem configs_left {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (higher : List Bool) : ∀ lower seen,
    machine.configs (counterCfg cfg v (lower ++ higher) (stLeft v seen) higher.length)
        higher.length =
      counterCfg cfg v (lower ++ higher) (stLeft v (seen || higher.any id)) 0 ∧
    machine.outputString (counterCfg cfg v (lower ++ higher) (stLeft v seen) higher.length)
        higher.length = [] := by
  apply List.rec (motive := fun higher ↦ ∀ lower seen,
    machine.configs (counterCfg cfg v (lower ++ higher) (stLeft v seen) higher.length)
        higher.length =
      counterCfg cfg v (lower ++ higher) (stLeft v (seen || higher.any id)) 0 ∧
    machine.outputString (counterCfg cfg v (lower ++ higher) (stLeft v seen) higher.length)
        higher.length = []) ?_ ?_ higher
  · intro lower seen
    simp only [List.length_nil, configs_zero, List.any_nil, Bool.or_false]
    exact ⟨trivial, rfl⟩
  · intro b higher ih lower seen
    obtain ⟨hs, ho⟩ := left_cons_run cfg v seen b lower higher
    obtain ⟨hc, hout⟩ := ih (lower ++ [b]) (seen || b)
    simp only [List.append_assoc, List.singleton_append] at hc hout
    constructor
    · rw [List.length_cons, configs_succ_eq_step, hs, hc]
      simp only [List.any_cons, id_eq, Bool.or_assoc]
    · let current := counterCfg cfg v (lower ++ b :: higher)
        (stLeft v seen) (higher.length + 1)
      change machine.outputString current (higher.length + 1) = []
      rw [show higher.length + 1 = 1 + higher.length by omega, outputString_add_eq_append]
      have hone : machine.outputString current 1 = [] := by
        rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero, ho]
        rfl
      rw [hone]
      change [] ++ machine.outputString (machine.step current) higher.length = []
      rw [hs, hout]
      rfl

/-- The rightward scan crosses every represented digit without inspecting its value. -/
theorem right_pos_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (bs : List Bool) (j : ℕ) (hj : j < bs.length) :
    machine.step (counterCfg cfg v bs (stRight v seen) (j + 1)) =
      counterCfg cfg v bs (stRight v seen) (j + 2) ∧
    machine.outputSymbol (counterCfg cfg v bs (stRight v seen) (j + 1)) = none := by
  apply counterAction_none_run (d := 1)
  · rw [tr_right]
    have hr : (counterCfg cfg v bs (stRight v seen) (j + 1)).workTapeSymbols
        (counterTape v) ≠ none := by
      simp only [Cfg.workTapeSymbols, counterCfg, ite_true, wordTape_succ]
      rw [List.getElem?_eq_getElem (by simpa only [List.length_reverse] using hj)]
      simp
    simp only [sweepRight, beq_iff_eq, hr, ↓reduceIte]
  · simp
    omega

/-- Reaching the right-hand blank completes the countdown. -/
theorem right_end_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (bs : List Bool) :
    machine.step (counterCfg cfg v bs (stRight v seen) (bs.length + 1)) =
      counterCfg cfg v bs (afterDecrement v seen) (bs.length + 1) ∧
    machine.outputSymbol (counterCfg cfg v bs (stRight v seen) (bs.length + 1)) = none := by
  apply counterAction_none_run (d := 0)
  · rw [tr_right]
    have hr : (counterCfg cfg v bs (stRight v seen) (bs.length + 1)).workTapeSymbols
        (counterTape v) = none := by
      simpa only [Cfg.workTapeSymbols, counterCfg, ite_true] using wordTape_end bs
    simp [sweepRight, hr, counterAction, jump]
  · simp

/-- Starting inside the word, the rightward scan reaches its blank and resumes decoding. -/
theorem configs_right {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (bs : List Bool) (t : ℕ) : ∀ p, 0 < p → p + t = bs.length + 1 →
    machine.configs (counterCfg cfg v bs (stRight v seen) p) (t + 1) =
      counterCfg cfg v bs (afterDecrement v seen) (bs.length + 1) ∧
    machine.outputString (counterCfg cfg v bs (stRight v seen) p) (t + 1) = [] := by
  apply Nat.rec (motive := fun t ↦ ∀ p, 0 < p → p + t = bs.length + 1 →
    machine.configs (counterCfg cfg v bs (stRight v seen) p) (t + 1) =
      counterCfg cfg v bs (afterDecrement v seen) (bs.length + 1) ∧
    machine.outputString (counterCfg cfg v bs (stRight v seen) p) (t + 1) = []) ?_ ?_ t
  · intro p _ hp
    have he : p = bs.length + 1 := by omega
    subst p
    obtain ⟨hs, ho⟩ := right_end_run cfg v seen bs
    constructor
    · exact hs
    · rw [outputString_succ, configs_zero, ho]
      rfl
  · intro t ih p hp hpt
    cases p with
    | zero => omega
    | succ j =>
      obtain ⟨hs, ho⟩ := right_pos_run cfg v seen bs j (by omega)
      obtain ⟨hc, hout⟩ := ih (j + 2) (by omega) (by omega)
      constructor
      · rw [configs_succ_eq_step, hs, hc]
      · let current := counterCfg cfg v bs (stRight v seen) (j + 1)
        change machine.outputString current (t + 1 + 1) = []
        rw [show t + 1 + 1 = 1 + (t + 1) by omega, outputString_add_eq_append]
        have hone : machine.outputString current 1 = [] := by
          rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero, ho]
          rfl
        rw [hone]
        change [] ++ machine.outputString (machine.step current) (t + 1) = []
        rw [hs, hout]
        rfl

/-- Borrowing across a zero sets that digit and continues toward the origin. -/
theorem borrow_false_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (lower higher : List Bool) :
    machine.step (counterCfg cfg v (lower ++ false :: higher)
      (stBorrow v seen) (higher.length + 1)) =
      counterCfg cfg v (lower ++ true :: higher) (stBorrow v true) higher.length ∧
    machine.outputSymbol (counterCfg cfg v (lower ++ false :: higher)
      (stBorrow v seen) (higher.length + 1)) = none := by
  apply counterAction_write_run (d := -1) (b := true)
  · rw [tr_borrow]
    have hr : (counterCfg cfg v (lower ++ false :: higher) (stBorrow v seen)
        (higher.length + 1)).workTapeSymbols (counterTape v) = some (boolEmb false) := by
      simpa only [Cfg.workTapeSymbols, counterCfg, ite_true] using wordTape_split lower higher false
    simp only [borrow, hr]
    rfl
  · simp
  · exact wordTape_update_split lower higher false true

/-- Borrowing stops at the first one, clearing it before the leftward scan. -/
theorem borrow_true_run {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (lower higher : List Bool) :
    machine.step (counterCfg cfg v (lower ++ true :: higher)
      (stBorrow v seen) (higher.length + 1)) =
      counterCfg cfg v (lower ++ false :: higher) (stLeft v seen) higher.length ∧
    machine.outputSymbol (counterCfg cfg v (lower ++ true :: higher)
      (stBorrow v seen) (higher.length + 1)) = none := by
  apply counterAction_write_run (d := -1) (b := false)
  · rw [tr_borrow]
    have hr : (counterCfg cfg v (lower ++ true :: higher) (stBorrow v seen)
        (higher.length + 1)).workTapeSymbols (counterTape v) = some (boolEmb true) := by
      simpa only [Cfg.workTapeSymbols, counterCfg, ite_true] using wordTape_split lower higher true
    simp only [borrow, hr]
    rfl
  · simp
  · exact wordTape_update_split lower higher true false

/-- Borrowing and the subsequent scan together visit each remaining digit exactly once. -/
theorem configs_borrow {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (higher : List Bool) : ∀ lower seen, 0 < Counter.value higher →
    machine.configs (counterCfg cfg v (lower ++ higher) (stBorrow v seen) higher.length)
        higher.length =
      counterCfg cfg v (lower ++ Counter.decrement higher)
        (stLeft v (seen || (Counter.decrement higher).any id)) 0 ∧
    machine.outputString (counterCfg cfg v (lower ++ higher) (stBorrow v seen) higher.length)
        higher.length = [] := by
  apply List.rec (motive := fun higher ↦ ∀ lower seen, 0 < Counter.value higher →
    machine.configs (counterCfg cfg v (lower ++ higher) (stBorrow v seen) higher.length)
        higher.length =
      counterCfg cfg v (lower ++ Counter.decrement higher)
        (stLeft v (seen || (Counter.decrement higher).any id)) 0 ∧
    machine.outputString (counterCfg cfg v (lower ++ higher) (stBorrow v seen) higher.length)
        higher.length = []) ?_ ?_ higher
  · intro lower seen h
    simp [Counter.value] at h
  · intro b higher ih lower seen h
    cases b with
    | false =>
      have hh : 0 < Counter.value higher := by
        rw [Counter.value_cons] at h
        simp only [Bool.toNat_false] at h
        omega
      obtain ⟨hs, ho⟩ := borrow_false_run cfg v seen lower higher
      obtain ⟨hc, hout⟩ := ih (lower ++ [true]) true hh
      simp only [List.append_assoc, List.singleton_append, Bool.true_or] at hc hout
      constructor
      · rw [List.length_cons, configs_succ_eq_step, hs, hc]
        simp [Counter.decrement]
      · let current := counterCfg cfg v (lower ++ false :: higher)
          (stBorrow v seen) (higher.length + 1)
        change machine.outputString current (higher.length + 1) = []
        rw [show higher.length + 1 = 1 + higher.length by omega, outputString_add_eq_append]
        have hone : machine.outputString current 1 = [] := by
          rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero, ho]
          rfl
        rw [hone]
        change [] ++ machine.outputString (machine.step current) higher.length = []
        rw [hs, hout]
        rfl
    | true =>
      obtain ⟨hs, ho⟩ := borrow_true_run cfg v seen lower higher
      obtain ⟨hc, hout⟩ := configs_left cfg v higher (lower ++ [false]) seen
      simp only [List.append_assoc, List.singleton_append] at hc hout
      constructor
      · rw [List.length_cons, configs_succ_eq_step, hs, hc]
        simp [Counter.decrement]
      · let current := counterCfg cfg v (lower ++ true :: higher)
          (stBorrow v seen) (higher.length + 1)
        change machine.outputString current (higher.length + 1) = []
        rw [show higher.length + 1 = 1 + higher.length by omega, outputString_add_eq_append]
        have hone : machine.outputString current 1 = [] := by
          rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero, ho]
          rfl
        rw [hone]
        change [] ++ machine.outputString (machine.step current) higher.length = []
        rw [hs, hout]
        rfl

/-- A single silent transition is a one-step execution with empty output. -/
theorem configs_output_one {input : List (Fin 3)}
    (cfg next : Cfg 4 (Fin 3) Control input)
    (hs : machine.step cfg = next) (ho : machine.outputSymbol cfg = none) :
    machine.configs cfg 1 = next ∧ machine.outputString cfg 1 = [] := by
  constructor
  · exact hs
  · rw [show 1 = 0 + 1 from rfl, outputString_succ, configs_zero, ho]
    rfl

/-- A positive fixed-width counter decrements and tests its result in twice its width plus three
transitions, preserving the input and all other tapes and emitting nothing. -/
theorem configs_decrement {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (bs : List Bool) (hbs : 0 < Counter.value bs) :
    machine.configs (counterCfg cfg v bs (stDecrement v) (bs.length + 1))
        (2 * bs.length + 3) =
      counterCfg cfg v (Counter.decrement bs)
        (afterDecrement v ((Counter.decrement bs).any id)) (bs.length + 1) ∧
    machine.outputString (counterCfg cfg v bs (stDecrement v) (bs.length + 1))
        (2 * bs.length + 3) = [] := by
  have hentry := configs_output_one _ _ (step_decrement cfg v bs)
    (outputSymbol_decrement cfg v bs)
  have hborrow := configs_borrow cfg v bs [] false hbs
  simp only [List.nil_append, Bool.false_or] at hborrow
  obtain ⟨hz, hoz⟩ := left_zero_run cfg v ((Counter.decrement bs).any id)
    (Counter.decrement bs)
  have hturn := configs_output_one _ _ hz hoz
  have hright := configs_right cfg v ((Counter.decrement bs).any id)
    (Counter.decrement bs) bs.length 1 (by omega) (by rw [Counter.length_decrement]; omega)
  rw [Counter.length_decrement] at hright
  have hfirst := configs_output_add _ _ _ 1 bs.length hentry hborrow
  have hsecond := configs_output_add _ _ _ (1 + bs.length) 1 hfirst hturn
  have hall := configs_output_add _ _ _ (1 + bs.length + 1) (bs.length + 1) hsecond hright
  simpa only [show 1 + bs.length + 1 + (bs.length + 1) = 2 * bs.length + 3 by omega] using hall

/-- A bounded starting configuration followed by a bounded tail gives a bounded successor run. -/
theorem headBound_succ {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (n width : ℕ) (hcfg : HeadBound width cfg)
    (hnext : ∀ t ≤ n, HeadBound width (machine.configs (machine.step cfg) t))
    (t : ℕ) (ht : t ≤ n + 1) : HeadBound width (machine.configs cfg t) := by
  cases t with
  | zero => exact hcfg
  | succ t =>
    rw [configs_succ_eq_step]
    exact hnext t (by omega)

/-- Every prefix of the leftward scan stays between the origin and its starting head. -/
theorem configs_left_headBound {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (higher : List Bool) (width : ℕ) (hcfg : HeadBound width cfg) :
    ∀ lower seen, higher.length ≤ width → ∀ t ≤ higher.length,
      HeadBound width (machine.configs
        (counterCfg cfg v (lower ++ higher) (stLeft v seen) higher.length) t) := by
  apply List.rec (motive := fun higher ↦ ∀ lower seen, higher.length ≤ width →
    ∀ t ≤ higher.length, HeadBound width (machine.configs
      (counterCfg cfg v (lower ++ higher) (stLeft v seen) higher.length) t)) ?_ ?_ higher
  · intro lower seen hw t ht
    have he : t = 0 := by simpa using ht
    subst t
    exact headBound_counterCfg cfg v _ _ _ width hcfg hw
  · intro b higher ih lower seen hw t ht
    apply headBound_succ _ higher.length width
      (headBound_counterCfg cfg v _ _ _ width hcfg hw) ?_ t ht
    intro r hr
    rw [List.length_cons, (left_cons_run cfg v seen b lower higher).1]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (lower ++ [b]) (seen || b) (by simp only [List.length_cons] at hw; omega) r hr

/-- Borrowing and its leftward scan stay in the initial head interval. -/
theorem configs_borrow_headBound {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v : Bool) (higher : List Bool) (width : ℕ) (hcfg : HeadBound width cfg) :
    ∀ lower seen, 0 < Counter.value higher → higher.length ≤ width → ∀ t ≤ higher.length,
      HeadBound width (machine.configs
        (counterCfg cfg v (lower ++ higher) (stBorrow v seen) higher.length) t) := by
  apply List.rec (motive := fun higher ↦ ∀ lower seen, 0 < Counter.value higher →
    higher.length ≤ width → ∀ t ≤ higher.length, HeadBound width (machine.configs
      (counterCfg cfg v (lower ++ higher) (stBorrow v seen) higher.length) t)) ?_ ?_ higher
  · intro lower seen h
    simp [Counter.value] at h
  · intro b higher ih lower seen h hw t ht
    apply headBound_succ _ higher.length width
      (headBound_counterCfg cfg v _ _ _ width hcfg hw) ?_ t ht
    intro r hr
    have hwidth : higher.length ≤ width := by simp only [List.length_cons] at hw; omega
    cases b with
    | false =>
      have hh : 0 < Counter.value higher := by
        rw [Counter.value_cons] at h
        simp only [Bool.toNat_false] at h
        omega
      rw [List.length_cons, (borrow_false_run cfg v seen lower higher).1]
      simpa only [List.append_assoc, List.singleton_append] using
        ih (lower ++ [true]) true hh hwidth r hr
    | true =>
      rw [List.length_cons, (borrow_true_run cfg v seen lower higher).1]
      simpa only [List.append_assoc, List.singleton_append] using
        configs_left_headBound cfg v higher width hcfg (lower ++ [false]) seen hwidth r hr

/-- Every prefix of the rightward scan stays at or before the right-hand blank. -/
theorem configs_right_headBound {input : List (Fin 3)} (cfg : Cfg 4 (Fin 3) Control input)
    (v seen : Bool) (bs : List Bool) (width : ℕ) (hcfg : HeadBound width cfg)
    (hw : bs.length + 1 ≤ width) (n : ℕ) : ∀ p, 0 < p → p + n = bs.length + 1 →
    ∀ t ≤ n + 1, HeadBound width
      (machine.configs (counterCfg cfg v bs (stRight v seen) p) t) := by
  apply Nat.rec (motive := fun n ↦ ∀ p, 0 < p → p + n = bs.length + 1 →
    ∀ t ≤ n + 1, HeadBound width
      (machine.configs (counterCfg cfg v bs (stRight v seen) p) t)) ?_ ?_ n
  · intro p _ hp t ht
    have he : p = bs.length + 1 := by omega
    subst p
    apply headBound_succ _ 0 width (headBound_counterCfg cfg v _ _ _ width hcfg hw) ?_ t ht
    intro r hr
    have he : r = 0 := by omega
    subst r
    rw [configs_zero, (right_end_run cfg v seen bs).1]
    exact headBound_counterCfg cfg v _ _ _ width hcfg hw
  · intro n ih p hp hn t ht
    cases p with
    | zero => omega
    | succ j =>
      apply headBound_succ _ (n + 1) width
        (headBound_counterCfg cfg v _ _ _ width hcfg (by omega)) ?_ t ht
      intro r hr
      rw [(right_pos_run cfg v seen bs j (by omega)).1]
      exact ih (j + 2) (by omega) (by omega) r hr

/-- All countdown prefixes preserve any nonnegative head bound containing the represented word
and its right-hand blank. -/
theorem configs_decrement_headBound {input : List (Fin 3)}
    (cfg : Cfg 4 (Fin 3) Control input) (v : Bool) (bs : List Bool) (width : ℕ)
    (hcfg : HeadBound width cfg) (hw : bs.length + 1 ≤ width)
    (hbs : 0 < Counter.value bs) (t : ℕ) (ht : t ≤ 2 * bs.length + 3) :
    HeadBound width (machine.configs
      (counterCfg cfg v bs (stDecrement v) (bs.length + 1)) t) := by
  have hborrow := (configs_borrow cfg v bs [] false hbs).1
  simp only [List.nil_append, Bool.false_or] at hborrow
  have hright : ∀ r ≤ bs.length + 1, HeadBound width (machine.configs
      (counterCfg cfg v (Counter.decrement bs)
        (stRight v ((Counter.decrement bs).any id)) 1) r) := by
    apply configs_right_headBound cfg v _ _ width hcfg
      (by simpa only [Counter.length_decrement] using hw) bs.length 1 (by omega)
    rw [Counter.length_decrement]
    omega
  have hturn : ∀ r ≤ 1 + (bs.length + 1), HeadBound width (machine.configs
      (counterCfg cfg v (Counter.decrement bs)
        (stLeft v ((Counter.decrement bs).any id)) 0) r) := by
    intro r hr
    apply headBound_succ _ (bs.length + 1) width
      (headBound_counterCfg cfg v _ _ 0 width hcfg (by omega)) ?_ r (by omega)
    rw [(left_zero_run cfg v ((Counter.decrement bs).any id) (Counter.decrement bs)).1]
    exact hright
  have htail : ∀ r ≤ bs.length + (1 + (bs.length + 1)), HeadBound width (machine.configs
      (counterCfg cfg v bs (stBorrow v false) bs.length) r) := by
    apply headBound_add _ bs.length (1 + (bs.length + 1)) width
    · intro r hr
      simpa only [List.nil_append] using
        configs_borrow_headBound cfg v bs width hcfg [] false hbs (by omega) r hr
    · rw [hborrow]
      exact hturn
  apply headBound_succ _ (bs.length + (1 + (bs.length + 1))) width
    (headBound_counterCfg cfg v _ _ _ width hcfg hw) ?_ t (by omega)
  rw [step_decrement]
  exact htail

end Geb.BitTree.Elias.Machine
