/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Inc
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
public import Geb.Prototypes.Computability.Oitavem.Word
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Counting a generated word

An emitting machine can provide the length of its output without storing that
output. The machine {lit}`countOutput` adds one binary counter tape and replaces
each emitted bit by an increment. It preserves the simulated work tapes and heads
between simulated steps. The counter increment leaves those heads in place.

## Main definitions

* {lit}`countOutput` counts a machine's emissions on an additional tape.
* {lit}`countOutputCfg` describes the configurations between simulated steps.
* {lit}`emitNumber` emits a counter in Oitavem's shortlex encoding.
* {lit}`lengthMachine` composes output counting and numerical emission.

## Main statements

* {lit}`inc_runsTo` increments a counter while other heads remain in place.
* {lit}`countOutput_runsTo` turns a halting emitter into an exact length reader.
* {lit}`emitNumber_emits` verifies the encoding, including zero and leading zeroes.
* {lit}`lengthMachine_computable` packages composition with numerical length in
  CSLib's simultaneous time and space predicate.

## Implementation notes

The CSLib machine contracts and the finite-control instance used to package
computability depend on {lit}`Classical.choice`; this module is included in
{lit}`GebMeta.classicalAllowedModules`.

## Tags

Turing machine, logarithmic space, generated word, output length
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Increment one parked counter while leaving the other heads in place. -/
theorem inc_runsTo {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Unit ⊕ Unit ⊕ Unit) input) (hq : cfg.state = some (inc i).q₀)
    (n B : ℕ) (hw : cfg.workTapes i = tapeOf (counterWord n))
    (hp : cfg.workTapePos i = 0) (hB : (n + 1).size ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    ∃ t ≤ 2 * B + 4, RunsTo (inc i) cfg
      { cfg with state := none
                 workTapes := Function.update cfg.workTapes i (tapeOf (counterWord (n + 1))) }
      t B := by
  let d := (counterWord n).reverse
  have hd : (incL d).reverse = counterWord (n + 1) := incL_counterWord n
  have hdB : (incL d).length ≤ B := by
    rw [← List.length_reverse (as := incL d), hd, length_counterWord]
    exact hB
  have hc := carry_lt_length_incL d
  have hself : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [← hp, Function.update_eq_self]
  have r₁ := incWalk_runsTo i { cfg with state := some (incWalk i).q₀ } rfl d
    (by simpa only [d, List.reverse_reverse] using hw) hp B hdB hpos
  have r₂ := returnTape_runsTo i
    { cfg with state := some (returnTape i).q₀
               workTapes := Function.update cfg.workTapes i (tapeOf (incL d).reverse)
               workTapePos := Function.update cfg.workTapePos i (carry d : ℤ) }
    rfl (incL d).reverse (by simp only [Function.update_self]) (carry d : ℤ)
    (by simp only [Function.update_self]) (by omega)
    (by rw [List.length_reverse]; omega) B
    (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)
  rw [Function.update_idem, hself,
    show ((carry d : ℤ) + 2).toNat = carry d + 2 by omega] at r₂
  have hall := r₁.seq r₂
  rw [← liftL_start (incWalk i) (returnTape i) cfg hq, hd] at hall
  exact ⟨_, by omega, hall⟩

/-- Finite control for simulation or a counter increment followed by resumption. -/
abbrev CountOutputState (S : Type) := S ⊕ (Option S × (Unit ⊕ Unit ⊕ Unit))

/-- Simulate a machine, counting its emissions on tape zero and suppressing its
output. Simulated tape {lit}`i` is physical tape {lit}`i.succ`. -/
@[expose] def countOutput {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :
    MultiTapeTM (k + 1) Bool (CountOutputState S) where
  q₀ := .inl P.q₀
  tr q input work := match q with
    | .inl p =>
      let a := P.tr p input (fun i ↦ work i.succ)
      { inputTape := a.inputTape
        workTapes := Fin.cons (none, 0) a.workTapes
        output := none
        state := if a.output.isSome then some (.inr (a.state, (inc (0 : Fin (k + 1))).q₀))
          else a.state.map Sum.inl }
    | .inr (next, q) =>
      let a := (inc (0 : Fin (k + 1))).tr q input work
      { a with state := match a.state with
          | some q' => some (.inr (next, q'))
          | none => next.map Sum.inl }

/-- A simulated configuration, with a counter and the caller's unchanged output. -/
@[expose] def countOutputCfg {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) (n : ℕ) (out : List Bool) :
    Cfg (k + 1) Bool (CountOutputState S) input where
  state := cfg.state.map Sum.inl
  inputPos := cfg.inputPos
  workTapes := Fin.cons (tapeOf (counterWord n)) cfg.workTapes
  workTapePos := Fin.cons 0 cfg.workTapePos
  output := out

/-- Embed the counter subroutine, returning to the saved simulated state at its halt. -/
@[expose] def countOutputLift {k : ℕ} {S : Type} {input : List Bool}
    (next : Option S) (cfg : Cfg (k + 1) Bool (Unit ⊕ Unit ⊕ Unit) input) :
    Cfg (k + 1) Bool (CountOutputState S) input :=
  { cfg with state := match cfg.state with
      | some q => some (.inr (next, q))
      | none => next.map Sum.inl }

/-- A live increment step is a step of the counting machine. -/
theorem countOutput_step_lift {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (next : Option S)
    (cfg : Cfg (k + 1) Bool (Unit ⊕ Unit ⊕ Unit) input) (hlive : cfg.state ≠ none) :
    (countOutput P).step (countOutputLift next cfg) =
      countOutputLift next ((inc 0).step cfg) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
  rw [step_of_state _ _ (.inr (next, q)) (by simp only [countOutputLift, hq]),
    step_of_state _ _ q hq]
  rfl

/-- A run of the increment subroutine lifts until its return to the simulation. -/
theorem countOutput_runFrom_lift {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (next : Option S)
    (cfg : Cfg (k + 1) Bool (Unit ⊕ Unit ⊕ Unit) input) (t : ℕ)
    (hlive : ∀ j < t, ((inc 0).runFrom cfg j).state ≠ none) :
    (countOutput P).runFrom (countOutputLift next cfg) t =
      countOutputLift next ((inc 0).runFrom cfg t) := by
  apply Nat.rec (motive := fun t ↦ (∀ j < t, ((inc 0).runFrom cfg j).state ≠ none) →
      (countOutput P).runFrom (countOutputLift next cfg) t =
        countOutputLift next ((inc 0).runFrom cfg t)) ?_ ?_ t hlive
  · intro _
    rfl
  · intro j ih hj
    rw [runFrom_succ_eq_step', ih (fun l hl ↦ hj l (by omega)),
      countOutput_step_lift _ _ _ (hj j (by omega)), runFrom_succ_eq_step']

/-- Increment arrivals lift without moving the suspended machine's work heads. -/
theorem Arrives.liftCountOutput {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (next : Option S)
    {cfg cfg' : Cfg (k + 1) Bool (Unit ⊕ Unit ⊕ Unit) input} {t B : ℕ}
    (h : Arrives (inc 0) cfg cfg' t B) :
    Arrives (countOutput P) (countOutputLift next cfg) (countOutputLift next cfg') t B where
  live := by
    intro j hj
    rw [countOutput_runFrom_lift P next cfg j (fun l hl ↦ h.live l (by omega))]
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (h.live j hj)
    simp only [countOutputLift, hq, ne_eq, reduceCtorEq, not_false_eq_true]
  runFrom_eq := by rw [countOutput_runFrom_lift P next cfg t h.live, h.runFrom_eq]
  pos := by
    intro j hj i
    rw [countOutput_runFrom_lift P next cfg j (fun l hl ↦ h.live l (by omega))]
    exact h.pos j hj i

/-- Counting suppresses every emission, including during counter increments. -/
theorem countOutput_outputSymbol {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg (k + 1) Bool (CountOutputState S) input) :
    (countOutput P).outputSymbol cfg = none := by
  cases hq : cfg.state with
  | none => exact outputSymbol_of_halt hq
  | some q =>
    cases q with
    | inl q => simp only [outputSymbol, hq, countOutput]
    | inr q =>
      rcases q with ⟨next, q⟩
      cases q with
      | inl q => simp [outputSymbol, hq, countOutput, inc, seq, incWalk]
      | inr q =>
        cases q with
        | inl q => simp [outputSymbol, hq, countOutput, inc, seq, returnTape, moveLeft]
        | inr q => simp [outputSymbol, hq, countOutput, inc, seq, returnTape, retLeft]

/-- The counting machine's output stays empty on every execution segment. -/
theorem countOutput_outputString {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg (k + 1) Bool (CountOutputState S) input) (t : ℕ) :
    (countOutput P).outputString cfg t = [] := by
  apply Nat.rec (motive := fun t ↦ (countOutput P).outputString cfg t = []) rfl ?_ t
  intro j ih
  rw [outputString_succ, ih, countOutput_outputSymbol]
  rfl

/-- One simulated step starts an increment exactly when it emits a bit. -/
theorem countOutput_step_run {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (q : S)
    (hq : cfg.state = some q) (n : ℕ) (out : List Bool) :
    (countOutput P).step (countOutputCfg cfg n out) =
      if (P.outputSymbol cfg).isSome then
        countOutputLift (P.step cfg).state
          { countOutputCfg (P.step cfg) n out with state := some (inc (0 : Fin (k + 1))).q₀ }
      else countOutputCfg (P.step cfg) n out := by
  have hi : (countOutputCfg cfg n out).inputSymbol = cfg.inputSymbol := rfl
  have hw : (fun i ↦ (countOutputCfg cfg n out).workTapeSymbols i.succ) =
      cfg.workTapeSymbols := rfl
  rw [step_of_state _ _ (.inl q) (by simp only [countOutputCfg, hq, Option.map_some]),
    step_of_state _ _ q hq]
  simp only [countOutput]
  rw [hi, hw]
  simp only [outputSymbol, hq, countOutputCfg, countOutputLift]
  split_ifs
  all_goals
    apply Cfg.ext
    · rfl
    · rfl
    · funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    · funext i
      refine Fin.cases ?_ (fun _ ↦ rfl) i
      simp only [Fin.cons_zero, SignType.coe_zero, add_zero]
    · exact List.append_nil _

/-- Bounds on suspended work heads also bound the parked counter head. -/
theorem countOutputCfg_pos {k : ℕ} {S : Type} {input : List Bool}
    (cfg : Cfg k Bool S input) (n B : ℕ) (out : List Bool)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    ∀ i, -1 ≤ (countOutputCfg cfg n out).workTapePos i ∧
      (countOutputCfg cfg n out).workTapePos i ≤ B :=
  Fin.cases (by change -1 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ B; omega) hpos

/-- A simulated step and its optional increment stay within the common head bound. -/
theorem countOutput_step_arrives {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input)
    (hlive : cfg.state ≠ none) (n B : ℕ) (out : List Bool) (hB : (n + 1).size ≤ B)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ (P.step cfg).workTapePos i ∧ (P.step cfg).workTapePos i ≤ B) :
    ∃ t ≤ 2 * B + 5, Arrives (countOutput P) (countOutputCfg cfg n out)
      (countOutputCfg (P.step cfg) (n + (P.outputSymbol cfg).toList.length) out) t B := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
  have hlive' : (countOutputCfg cfg n out).state ≠ none := by
    simp only [countOutputCfg, hq, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]
  have hp := countOutputCfg_pos cfg n B out hpos
  have hp' := countOutputCfg_pos (P.step cfg) n B out hpos'
  cases ho : P.outputSymbol cfg with
  | none =>
    simp only [Option.toList_none, List.length_nil, Nat.add_zero]
    have hs : (countOutput P).step (countOutputCfg cfg n out) =
        countOutputCfg (P.step cfg) n out := by
      simpa only [ho, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
        countOutput_step_run P cfg q hq n out
    exact ⟨1, by omega, (Reaches.ofStep _ _ _ B hlive' hs
      (countOutput_outputSymbol P _) hp hp').toArrives⟩
  | some b =>
    simp only [Option.toList_some, List.length_singleton]
    let c : Cfg (k + 1) Bool (Unit ⊕ Unit ⊕ Unit) input :=
      { countOutputCfg (P.step cfg) n out with state := some (inc (0 : Fin (k + 1))).q₀ }
    have hs : (countOutput P).step (countOutputCfg cfg n out) =
        countOutputLift (P.step cfg).state c := by
      simpa only [ho, Option.isSome_some, ↓reduceIte] using
        countOutput_step_run P cfg q hq n out
    have r₁ := (Reaches.ofStep _ _ _ B hlive' hs
      (countOutput_outputSymbol P _) hp hp').toArrives
    obtain ⟨t, ht, r₂⟩ := inc_runsTo (0 : Fin (k + 1)) c rfl n B rfl rfl hB hp'
    have heq : countOutputLift (P.step cfg).state
        { c with state := none
                 workTapes := Function.update c.workTapes 0 (tapeOf (counterWord (n + 1))) } =
        countOutputCfg (P.step cfg) (n + 1) out := by
      apply Cfg.ext
      · rfl
      · rfl
      · funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · simp only [countOutputLift, countOutputCfg, c, Function.update_self, Fin.cons_zero]
        · simp only [countOutputLift, countOutputCfg, c,
            Function.update_of_ne (Fin.succ_ne_zero j), Fin.cons_succ]
      · rfl
      · rfl
    have r := r₁.trans (Arrives.liftCountOutput P (P.step cfg).state r₂.toArrives)
    rw [heq] at r
    exact ⟨1 + t, by omega, r⟩

/-- Simulation counts the exact output length. The extra space depends on the
output length, independently of how many silent steps the machine takes. -/
theorem countOutput_arrives {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) {cfg cfg' : Cfg k Bool S input} {t B : ℕ}
    (h : Arrives P cfg cfg' t B) (n : ℕ) (out : List Bool)
    (hB : (n + (P.outputString cfg t).length + 1).size ≤ B) :
    ∃ u ≤ t * (2 * B + 5), Arrives (countOutput P) (countOutputCfg cfg n out)
      (countOutputCfg cfg' (n + (P.outputString cfg t).length) out) u B := by
  have hlen (j : ℕ) (hj : j ≤ t) :
      (P.outputString cfg j).length ≤ (P.outputString cfg t).length := by
    have heq := outputString_add_eq_append P cfg j (t - j)
    rw [show j + (t - j) = t by omega] at heq
    rw [heq, List.length_append]
    omega
  have key : ∀ j, j ≤ t → ∃ u ≤ j * (2 * B + 5),
      Arrives (countOutput P) (countOutputCfg cfg n out)
        (countOutputCfg (P.runFrom cfg j) (n + (P.outputString cfg j).length) out) u B := by
    refine Nat.rec ?_ ?_
    · intro _
      refine ⟨0, by omega, ?_⟩
      change Arrives (countOutput P) (countOutputCfg cfg n out) (countOutputCfg cfg n out) 0 B
      refine ⟨fun j hj ↦ by omega, rfl, ?_⟩
      intro j hj
      obtain rfl : j = 0 := by omega
      exact countOutputCfg_pos cfg n B out (h.pos 0 (by omega))
    · intro j ih hj
      obtain ⟨u, hu, r⟩ := ih (by omega)
      have hsize : (n + (P.outputString cfg j).length + 1).size ≤ B :=
        (size_le_size (by have := hlen j (by omega); omega)).trans hB
      have hstepPos : ∀ i, -1 ≤ (P.step (P.runFrom cfg j)).workTapePos i ∧
          (P.step (P.runFrom cfg j)).workTapePos i ≤ B := by
        rw [← runFrom_succ_eq_step']
        exact h.pos (j + 1) hj
      obtain ⟨v, hv, r'⟩ := countOutput_step_arrives P (P.runFrom cfg j)
        (h.live j (by omega)) (n + (P.outputString cfg j).length) B out hsize
        (h.pos j (by omega)) hstepPos
      have heq : n + (P.outputString cfg j).length +
          (P.outputSymbol (P.runFrom cfg j)).toList.length =
          n + (P.outputString cfg (j + 1)).length := by
        rw [outputString_succ, List.length_append, Nat.add_assoc]
      rw [heq, ← runFrom_succ_eq_step'] at r'
      exact ⟨u + v, by rw [Nat.succ_mul]; omega, r.trans r'⟩
  obtain ⟨u, hu, r⟩ := key t le_rfl
  rw [h.runFrom_eq] at r
  exact ⟨u, hu, r⟩

/-- A halting emitter becomes a halting length reader. Its old tapes and heads
have exactly their original final values, and the caller's output is preserved. -/
theorem countOutput_runsTo {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ}
    (h : Emits P cfg cfg' w t B) (n : ℕ) (out : List Bool)
    (hB : (n + w.length + 1).size ≤ B) :
    ∃ u ≤ t * (2 * B + 5), RunsTo (countOutput P) (countOutputCfg cfg n out)
      (countOutputCfg cfg' (n + w.length) out) u B := by
  obtain ⟨u, hu, r⟩ := countOutput_arrives P h.toArrives n out (by rwa [h.output])
  rw [h.output] at r
  refine ⟨u, hu, ⟨⟨r, countOutput_outputString P _ _⟩, ?_⟩⟩
  simp only [countOutputCfg, h.halted, Option.map_none]

/-- The initial counting configuration adds exactly one blank tape. -/
theorem countOutput_initCfg {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S)
    (input : List Bool) :
    countOutputCfg (P.initCfg input) 0 [] = (countOutput P).initCfg input := by
  apply Cfg.ext
  · rfl
  · rfl
  · funext i
    refine Fin.cases ?_ (fun _ ↦ rfl) i
    exact tapeOf_nil
  · funext i
    exact Fin.cases rfl (fun _ ↦ rfl) i
  · rfl

/-- The counter library's canonical digits agree with the standard binary digits. -/
theorem counterDigits_eq_bits (n : ℕ) : ofNat n = n.bits := by
  apply Nat.binaryRec (motive := fun n ↦ ofNat n = n.bits) rfl ?_ n
  intro b m ih
  by_cases hm : m = 0
  · subst m
    cases b <;> rfl
  · rw [Nat.bits_append_bit m b (fun h ↦ (hm h).elim), Nat.bit_val]
    cases b
    · change ofNat (2 * m + 0) = false :: m.bits
      rw [Nat.add_zero, ofNat_two_mul m (Nat.pos_of_ne_zero hm), ih]
    · change ofNat (2 * m + 1) = true :: m.bits
      rw [ofNat_two_mul_add_one, ih]

/-- Scan a tape rightwards, delaying each bit until the next bit is seen. The
final buffered bit is discarded, so the machine emits the word without its last bit. -/
@[expose] def emitDropLast {k : ℕ} (i : Fin k) : MultiTapeTM k Bool (Option Bool) where
  q₀ := none
  tr q _ work := match work i with
    | none =>
      { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none }
    | some b =>
      { inputTape := 0, workTapes := fun j ↦ (none, if j = i then 1 else 0),
        output := q, state := some (some b) }

/-- The configuration after scanning a prefix, with at most its final bit buffered. -/
@[expose] def emitDropLastCfg {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Option Bool) input) (d : List Bool) (s : ℕ) :
    Cfg k Bool (Option Bool) input :=
  { cfg with state := some ((d.take s).getLast?)
             workTapePos := Function.update cfg.workTapePos i (s : ℤ)
             output := cfg.output ++ (d.take s).dropLast }

/-- Delayed emission removes exactly the final digit, without changing any tape
or moving any other head. -/
theorem emitDropLast_emits {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Option Bool) input) (hq : cfg.state = some none)
    (d : List Bool) (hw : cfg.workTapes i = tapeOf d.reverse) (hp : cfg.workTapePos i = 0)
    (B : ℕ) (hB : d.length ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    Emits (emitDropLast i) cfg
      { cfg with state := none
                 workTapePos := Function.update cfg.workTapePos i (d.length : ℤ)
                 output := cfg.output ++ d.dropLast }
      d.dropLast (d.length + 1) B := by
  have hsplit (w : List Bool) : w.dropLast ++ w.getLast?.toList = w := by
    rcases List.eq_nil_or_concat w with rfl | ⟨v, b, rfl⟩
    · rfl
    · simp
  have hsym (s : ℕ) : (emitDropLastCfg i cfg d s).workTapeSymbols i = d[s]? := by
    change cfg.workTapes i (Function.update cfg.workTapePos i (s : ℤ) i) = d[s]?
    rw [Function.update_self, hw, tapeOf_reverse_natCast]
  have htr (s : ℕ) (hs : s < d.length) :
      (emitDropLast i).tr (d.take s).getLast? (emitDropLastCfg i cfg d s).inputSymbol
        (emitDropLastCfg i cfg d s).workTapeSymbols =
      { inputTape := 0, workTapes := fun j ↦ (none, if j = i then 1 else 0),
        output := (d.take s).getLast?, state := some (some d[s]) } := by
    simp only [emitDropLast, hsym s, List.getElem?_eq_getElem hs]
  have hnone : (emitDropLast i).tr (d.take d.length).getLast?
      (emitDropLastCfg i cfg d d.length).inputSymbol
      (emitDropLastCfg i cfg d d.length).workTapeSymbols =
      { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := none, state := none } := by
    simp only [emitDropLast, hsym d.length, List.getElem?_length]
  have hstep : ∀ s < d.length,
      (emitDropLast i).step (emitDropLastCfg i cfg d s) =
        emitDropLastCfg i cfg d (s + 1) := by
    intro s hs
    rw [step_of_state _ _ _ rfl, htr s hs]
    apply Cfg.ext
    · simp only [emitDropLastCfg, List.take_succ_eq_append_getElem hs, List.getLast?_concat]
    · exact moveInputPos_zero _
    · rfl
    · funext j
      change Function.update cfg.workTapePos i (s : ℤ) j +
          ((if j = i then 1 else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i ((s + 1 : ℕ) : ℤ) j
      by_cases hj : j = i
      · subst j
        simp only [Function.update_self, ↓reduceIte, SignType.coe_one]
        omega
      · simp only [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
    · change cfg.output ++ (d.take s).dropLast ++ (d.take s).getLast?.toList =
        cfg.output ++ (d.take (s + 1)).dropLast
      rw [List.take_succ_eq_append_getElem hs, List.dropLast_concat, List.append_assoc,
        hsplit]
  have hhalt : (emitDropLast i).step (emitDropLastCfg i cfg d d.length) =
      { cfg with state := none
                 workTapePos := Function.update cfg.workTapePos i (d.length : ℤ)
                 output := cfg.output ++ d.dropLast } := by
    rw [step_of_state _ _ _ rfl, hnone]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext j
      simp only [emitDropLastCfg, SignType.coe_zero, add_zero]
    · simp only [emitDropLastCfg, List.take_length, Option.toList_none, List.append_nil]
  have hout : ∀ s ≤ d.length, (d.take (min (s + 1) d.length)).dropLast =
      (d.take (min s d.length)).dropLast ++
        ((emitDropLast i).outputSymbol (emitDropLastCfg i cfg d s)).toList := by
    intro s hs
    rw [Nat.min_eq_left hs]
    by_cases hs' : s < d.length
    · rw [Nat.min_eq_left (by omega)]
      change (d.take (s + 1)).dropLast = (d.take s).dropLast ++
        ((emitDropLast i).tr (d.take s).getLast? _ _).output.toList
      rw [htr s hs', List.take_succ_eq_append_getElem hs', List.dropLast_concat,
        hsplit]
    · obtain rfl : s = d.length := by omega
      change (d.take (min (d.length + 1) d.length)).dropLast =
        (d.take d.length).dropLast ++ ((emitDropLast i).tr _ _ _).output.toList
      rw [hnone, Nat.min_eq_right (by omega)]
      exact (List.append_nil _).symm
  have hstart : emitDropLastCfg i cfg d 0 = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · rfl
    · change Function.update cfg.workTapePos i 0 = cfg.workTapePos
      rw [← hp, Function.update_eq_self]
    · exact List.append_nil _
  have h := Emits.ofFamily (emitDropLast i) (emitDropLastCfg i cfg d)
    (fun s ↦ (d.take (min s d.length)).dropLast) d.length B _
    (fun _ _ ↦ Option.some_ne_none _) hstep hhalt rfl rfl hout
    (fun s hs j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)
    (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)
  simpa only [hstart, Nat.min_eq_right (by omega : d.length ≤ d.length + 1),
    List.take_length] using h

/-- Emit a binary counter in Oitavem's shortlex encoding: increment, then omit
the binary sentinel. The other tapes and heads remain in place. -/
@[expose] def emitNumber {k : ℕ} (i : Fin k) := seq (inc i) (emitDropLast i)

/-- Numerical emission returns exactly the enumeration word, using only the
counter's logarithmic tape interval and a constant amount of control. -/
theorem emitNumber_emits {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool ((Unit ⊕ Unit ⊕ Unit) ⊕ Option Bool) input)
    (hq : cfg.state = some (emitNumber i).q₀) (n B : ℕ)
    (hw : cfg.workTapes i = tapeOf (counterWord n)) (hp : cfg.workTapePos i = 0)
    (hB : (n + 1).size ≤ B)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    ∃ t ≤ 3 * B + 5, Emits (emitNumber i) cfg
      { cfg with state := none
                 workTapes := Function.update cfg.workTapes i (tapeOf (counterWord (n + 1)))
                 workTapePos := Function.update cfg.workTapePos i ((n + 1).size : ℤ)
                 output := cfg.output ++ unrank n }
      (unrank n) t B := by
  obtain ⟨t, ht, r₁⟩ := inc_runsTo i { cfg with state := some (inc i).q₀ }
    rfl n B hw hp hB hpos
  have r₂ := emitDropLast_emits i
    { cfg with state := some (emitDropLast i).q₀
               workTapes := Function.update cfg.workTapes i (tapeOf (counterWord (n + 1))) }
    rfl (ofNat (n + 1)) (by exact Function.update_self ..) hp B
    (by rwa [length_ofNat_eq_size]) hpos
  have h := r₁.seqEmits r₂
  rw [← liftL_start (inc i) (emitDropLast i) cfg hq] at h
  have hd : (ofNat (n + 1)).dropLast = unrank n := by rw [counterDigits_eq_bits]; rfl
  refine ⟨t + ((n + 1).size + 1), by omega, ?_⟩
  simpa only [emitNumber, liftR, Option.map_none, hd, length_ofNat_eq_size] using h

/-- Compute the encoded length of an emitter's output, without storing that output. -/
@[expose] def lengthMachine {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :=
  seq (countOutput P) (emitNumber 0)

/-- Composition with numerical length adds one counter tape and emits exactly
the shortlex word for the length. Original work heads need not be parked at return. -/
theorem lengthMachine_emits {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) {cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ}
    (h : Emits P (P.initCfg input) cfg' w t B) (hB : (w.length + 1).size ≤ B) :
    ∃ cfg'' u, u ≤ t * (2 * B + 5) + (3 * B + 5) ∧
      Emits (lengthMachine P) ((lengthMachine P).initCfg input) cfg''
        (unrank w.length) u B := by
  obtain ⟨u, hu, r⟩ := countOutput_runsTo P h 0 [] (by simpa only [Nat.zero_add] using hB)
  rw [countOutput_initCfg, Nat.zero_add] at r
  have hp := r.pos u le_rfl
  rw [r.runFrom_eq] at hp
  obtain ⟨v, hv, e⟩ := emitNumber_emits (0 : Fin (k + 1))
    { countOutputCfg cfg' w.length [] with state := some (emitNumber (0 : Fin (k + 1))).q₀ }
    rfl w.length B rfl rfl hB hp
  have hall := r.seqEmits e
  have hstart : liftL (emitNumber 0) ((countOutput P).initCfg input) =
      (lengthMachine P).initCfg input := rfl
  rw [hstart] at hall
  exact ⟨_, u + v, by omega, hall⟩

/-- A uniformly bounded finite-control emitter yields a machine computing its
output length in Oitavem's encoding, with explicit time and space bounds. -/
theorem lengthMachine_computable {k : ℕ} {S : Type} [Finite S]
    (P : MultiTapeTM k Bool S) (f : List Bool → List Bool) (T B : ℕ → ℕ)
    (hP : ∀ w, ∃ cfg' t, t ≤ T w.length ∧ Emits P (P.initCfg w) cfg' (f w) t (B w.length))
    (hB : ∀ w, ((f w).length + 1).size ≤ B w.length) :
    ComputableInTimeAndSpaceOfLength (fun w ↦ unrank (f w).length)
      (.refl _) (.refl _) (fun n ↦ T n * (2 * B n + 5) + (3 * B n + 5))
      (fun n ↦ (k + 1) * (B n + 2)) := by
  let : Fintype S := Fintype.ofFinite S
  refine ⟨k + 1, CountOutputState S ⊕ ((Unit ⊕ Unit ⊕ Unit) ⊕ Option Bool),
    inferInstance, lengthMachine P, fun w ↦ ?_⟩
  obtain ⟨cfg', t, ht, h⟩ := hP w
  obtain ⟨cfg'', u, hu, e⟩ := lengthMachine_emits P h (hB w)
  refine ⟨u, hu.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ ht) _),
    (lengthMachine P).spaceUsed ((lengthMachine P).initCfg w) u,
    e.spaceUsed_le, ?_, ?_, rfl⟩
  · change ((lengthMachine P).runFrom ((lengthMachine P).initCfg w) u).state = none
    rw [e.runFrom_eq]
    exact e.halted
  · rw [initCfg_runFrom_output]
    exact e.output
end

end Geb.Oitavem.Machine
