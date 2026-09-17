/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Wrapper
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.Count
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Primitives.EmitSuffix
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Theorem
public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Compile.Bound

set_option doc.verso true in
/-!
# The machine of an expression of the subalgebra

A compiled program of the calculus reads and writes registers holding
representations; a {name}`Turing.MultiTapeTM` reads an input tape and emits
an output string. The input {lit}`w` is the representation
{lit}`⟨[], w.length⟩`, the empty word before the whole input as end segment,
so the reader is {name}`Geb.SizeBounded.Logspace.Machine.countInput`, which
counts the input's length into the argument register's counter tape and
leaves its word tape empty; the value is a word before an end segment, so the
writer is {name}`Geb.SizeBounded.Machine.writer`, which emits the output
register's word tape, followed by one move to park that tape's head and
{name}`Geb.SizeBounded.Logspace.Machine.emitSuffix`, which emits the end
segment the output register's counter tape names. {lit}`machine` sequences
the four over {lit}`regsBound e.1.1.1 + 4` tapes: tapes {lit}`0` and {lit}`1`
are the argument register, tapes {lit}`2` and {lit}`3` the output register,
and the compiled program's need is met from tape {lit}`4` up. The input's
word tape, empty throughout, serves as the suffix emitter's scratch tape.

{lit}`machine_emits` composes the count's run, the program's contract
{name}`Geb.SizeBounded.Logspace.Machine.LOf.correct`, the writer's emission,
the move and the suffix emission, and identifies the emitted string with the
expression's meaning by {name}`Geb.SizeBounded.Logspace.den_repSem`. The
word bound the program runs under is the expression's constant, so the tape
bound is that constant plus the input's binary size plus one: the space is
logarithmic in the input's length.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.runFrom` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's {name}`Turing.Cfg.inputSymbol`.

# Main definitions

* {lit}`moveRight` — one move right of a tape's head.
* {lit}`tapes`, {lit}`argReg`, {lit}`outReg`, {lit}`argValuation`,
  {lit}`program` — the tape count, the two registers, the valuation the
  reader produces, and the compiled program at the wrapper's allocation.
* {lit}`State`, {lit}`machine` — the machine's state type and the machine.
* {lit}`wordBound`, {lit}`time` — the word bound and the step count on an
  input of a given length.

# Main statements

* {lit}`moveRight_runsTo` — the move's run.
* {lit}`machine_emits` — the machine emits the expression's value at the
  input.

# Tags

Turing machine, input tape, output, compilation, logspace
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.Machine

open Turing MultiTapeTM
open scoped FinEnum
open Geb.SizeBounded (nsiConst)
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace (LOf Rep den_repSem)

public section

/-- One move right of the head of tape {lit}`i`. -/
@[expose] def moveRight {k : ℕ} (i : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ _ :=
    { inputTape := 0, workTapes := fun j ↦ (none, if j = i then 1 else 0),
      output := none, state := none }

/-- {name}`moveRight` runs one step. -/
theorem moveRight_runsTo {k : ℕ} {input : List Bool} (i : Fin k) (cfg : Cfg k Bool Unit input)
    (hq : cfg.state = some ()) (B : ℕ)
    (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B)
    (hi : cfg.workTapePos i + 1 ≤ B) :
    RunsTo (moveRight i) cfg
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i + 1) }
      1 B := by
  have hhalt : (moveRight i).step cfg =
      { cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (cfg.workTapePos i + 1) } := by
    rw [step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · change moveInputPos cfg.inputPos 0 = cfg.inputPos
      rw [moveInputPos_zero]
    · rfl
    · funext j
      change cfg.workTapePos j + ((if j = i then (1 : SignType) else 0 : SignType) : ℤ) =
        Function.update cfg.workTapePos i (cfg.workTapePos i + 1) j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_self, ite_eq_left rfl, SignType.coe_one]
      · rw [Function.update_of_ne hj, ite_eq_right hj, SignType.coe_zero, add_zero]
    · exact List.append_nil _
  have hlive : cfg.state ≠ none := by
    rw [hq]
    exact Option.some_ne_none _
  have hout : (moveRight i).outputSymbol cfg = none := by
    unfold outputSymbol
    rw [hq]
    rfl
  have hB := (hpos i).1
  exact RunsTo.ofFamily (moveRight i) (fun _ ↦ cfg) 0 B _ (fun _ _ ↦ hlive)
    (fun _ h ↦ absurd h (by omega)) hhalt rfl (fun _ _ ↦ hout) (fun _ _ j ↦ hpos j)
    (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) hi j)

/-- The tapes of an expression's machine: the argument register, the output
register, and the compiled program's need. -/
@[expose] def tapes (e : LOf 1) : ℕ := regsBound e.1.1.1 + 4

/-- The four tapes of the two registers are below the count. -/
theorem lt_tapes (e : LOf 1) (t : ℕ) (h : t < 4) : t < tapes e := by
  unfold tapes
  omega

/-- The argument register: tapes {lit}`0` and {lit}`1`. -/
@[expose] def argReg (e : LOf 1) : Reg (tapes e) :=
  fun t ↦ ⟨t, lt_tapes e t (by have := t.isLt; omega)⟩

/-- The output register: tapes {lit}`2` and {lit}`3`. -/
@[expose] def outReg (e : LOf 1) : Reg (tapes e) :=
  fun t ↦ ⟨2 + t, lt_tapes e _ (by have := t.isLt; omega)⟩

/-- The valuation the reader produces on input {lit}`w`: the argument register's
counter tape holds the input's length, every other tape is empty. -/
@[expose] def argValuation (e : LOf 1) (w : List Bool) : Fin (tapes e) → List Bool :=
  Function.update (fun _ ↦ []) ⟨1, lt_tapes e 1 (by omega)⟩ (counterWord w.length)

/-- The compiled program of {lit}`e` reading the argument register, writing the
output register, with the tapes from {lit}`4` free. -/
@[expose] def program (e : LOf 1) : Prog (tapes e) :=
  (LOf.compile (tapes e) e).prog ![argReg e] (outReg e) 4 (by rw [LOf.regs]; unfold tapes; omega)

/-- The state type of an expression's machine. -/
abbrev State (e : LOf 1) : Type :=
  StateOf (countInput (⟨1, lt_tapes e 1 (by omega)⟩ : Fin (tapes e))) ⊕
    ((program e).State ⊕ (WriterState ⊕ (Unit ⊕
      StateOf (emitSuffix (⟨3, lt_tapes e 3 (by omega)⟩ : Fin (tapes e))
        ⟨0, lt_tapes e 0 (by omega)⟩))))

/-- The state type is enumerable, by the compiled program's enumeration and the
scoped instances for sums and {lit}`Unit`. -/
instance (e : LOf 1) : FinEnum (State e) :=
  @FinEnum.finSum _ _ inferInstance (@FinEnum.finSum _ _ (program e).enum
    (@FinEnum.finSum _ _ inferInstance (@FinEnum.finSum _ _ inferInstance inferInstance)))

/-- The machine of an expression: the count, the compiled program, the writer,
the move, the suffix emitter. -/
@[expose] def machine (e : LOf 1) : MultiTapeTM (tapes e) Bool (State e) :=
  seq (countInput ⟨1, lt_tapes e 1 (by omega)⟩)
    (seq (program e).tm
      (seq (writer ⟨2, lt_tapes e 2 (by omega)⟩)
        (seq (moveRight ⟨2, lt_tapes e 2 (by omega)⟩)
          (emitSuffix ⟨3, lt_tapes e 3 (by omega)⟩ ⟨0, lt_tapes e 0 (by omega)⟩))))

/-- The word bound the machine runs under: the expression's constant. -/
@[expose] def wordBound (e : LOf 1) : ℕ := nsiConst e.1.1.1

/-- The machine's step count on an input of length {lit}`n`. -/
@[expose] def time (e : LOf 1) (n : ℕ) : ℕ :=
  countInputTime (bound (wordBound e) n) n + timeBound e.1.1.1 (wordBound e) n +
    (2 * bound (wordBound e) n + 3) + 1 + emitSuffixTime (bound (wordBound e) n) n

/-- The machine of {lit}`e` on {lit}`w` emits {lit}`e`'s meaning at {lit}`w`
within {name}`time`, every head within the tape bound at the expression's
constant. -/
theorem machine_emits (e : LOf 1) (w : List Bool) :
    ∃ cfg' t', t' ≤ time e w.length ∧
      Emits (machine e) ((machine e).initCfg w) cfg' (e.sem ![w]) t'
        (bound (wordBound e) w.length) := by
  have h0 : 0 < tapes e := lt_tapes e 0 (by omega)
  have h1 : 1 < tapes e := lt_tapes e 1 (by omega)
  have h2 : 2 < tapes e := lt_tapes e 2 (by omega)
  have h3 : 3 < tapes e := lt_tapes e 3 (by omega)
  have h01 : (⟨0, h0⟩ : Fin (tapes e)) ≠ ⟨1, h1⟩ := Fin.ne_of_val_ne (by change 0 ≠ 1; omega)
  have h30 : (⟨3, h3⟩ : Fin (tapes e)) ≠ ⟨0, h0⟩ := Fin.ne_of_val_ne (by change 3 ≠ 0; omega)
  have hBM : wordBound e ≤ bound (wordBound e) w.length := by unfold bound; omega
  have hsize : Nat.size w.length ≤ bound (wordBound e) w.length := by unfold bound; omega
  have hσ0 : argValuation e w ⟨0, h0⟩ = [] := Function.update_of_ne h01 _ _
  have hσ1 : argValuation e w ⟨1, h1⟩ = counterWord w.length := Function.update_self _ _ _
  have hσB : Bounded (argValuation e w) (bound (wordBound e) w.length) := fun i ↦ by
    by_cases hi : i = ⟨1, h1⟩
    · rw [hi, hσ1, length_counterWord]
      exact hsize
    · rw [show argValuation e w i = [] from Function.update_of_ne hi _ _]
      exact Nat.zero_le _
  -- the count
  obtain ⟨t₁, ht₁, h₁⟩ := countInput_runsTo (⟨1, h1⟩ : Fin (tapes e))
    ({ (machine e).initCfg w with state := some (countInput (⟨1, h1⟩ : Fin (tapes e))).q₀ } :
      Cfg (tapes e) Bool (StateOf (countInput (⟨1, h1⟩ : Fin (tapes e)))) w)
    rfl (fun _ ↦ []) (fun _ ↦ tapeOf_nil.symm) (fun _ ↦ rfl) rfl (bound (wordBound e) w.length)
    (fun _ ↦ Nat.zero_le _) hsize
  -- the compiled program
  have hadm : Admissible ![argReg e] (outReg e) 4 := by
    refine ⟨fun x y hxy ↦ ?_, fun i b ↦ ?_, fun b ↦ ?_, ?_, fun i b b' ↦ ?_⟩
    · obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      rw [Fin.fin_one_eq_zero x1, Fin.fin_one_eq_zero y1] at hxy ⊢
      have := congrArg Fin.val hxy
      change (x2 : ℕ) = (y2 : ℕ) at this
      rw [Fin.ext this]
    · rw [Fin.fin_one_eq_zero i]
      change (b : ℕ) < 4
      have := b.isLt
      omega
    · change 2 + (b : ℕ) < 4
      have := b.isLt
      omega
    · exact Fin.ne_of_val_ne (by change 2 + 0 ≠ 2 + 1; omega)
    · rw [Fin.fin_one_eq_zero i]
      exact Fin.ne_of_val_ne (by change (b : ℕ) ≠ 2 + (b' : ℕ); have := b.isLt; omega)
  have hpre : EnvWF (wordBound e) w (argValuation e w) ![argReg e] := fun i ↦ by
    rw [Fin.fin_one_eq_zero i]
    refine ⟨?_, w.length, Nat.le_refl _, ?_⟩
    · change (argValuation e w ⟨0, h0⟩).length ≤ wordBound e
      rw [hσ0]
      exact Nat.zero_le _
    · change argValuation e w ⟨1, h1⟩ = _
      exact hσ1
  obtain ⟨F, hT, hval, -, hwf⟩ := LOf.correct (tapes e) e ![argReg e] (outReg e) 4
    (by rw [LOf.regs]; unfold tapes; omega) hadm (wordBound e) (Nat.le_refl _)
  obtain ⟨hFB, t₂, ht₂, h₂⟩ := hT w
    ({ state := some (program e).tm.q₀
       inputPos := ⟨0, by omega⟩
       workTapes := fun i ↦ tapeOf (argValuation e w i)
       workTapePos := fun _ ↦ 0
       output := [] } : Cfg (tapes e) Bool (program e).State w)
    (argValuation e w) rfl (fun _ ↦ rfl) rfl (fun _ ↦ rfl) hpre hσB
  rw [LOf.time] at ht₂
  obtain ⟨hwlen, l, hl, hC⟩ := hwf w (argValuation e w) hpre
  change (F w (argValuation e w) ⟨2, h2⟩).length ≤ wordBound e at hwlen
  change F w (argValuation e w) ⟨3, h3⟩ = counterWord l at hC
  -- the writer
  have h₃ := writer_emits (⟨2, h2⟩ : Fin (tapes e))
    ({ state := some (writer (⟨2, h2⟩ : Fin (tapes e))).q₀
       inputPos := ⟨0, by omega⟩
       workTapes := fun i ↦ tapeOf (F w (argValuation e w) i)
       workTapePos := fun _ ↦ 0
       output := [] } : Cfg (tapes e) Bool WriterState w)
    rfl (F w (argValuation e w) ⟨2, h2⟩) rfl (fun _ ↦ rfl) (bound (wordBound e) w.length)
    (hFB _)
  -- the move
  have hmr := moveRight_runsTo (⟨2, h2⟩ : Fin (tapes e))
    ({ state := some (moveRight (⟨2, h2⟩ : Fin (tapes e))).q₀
       inputPos := ⟨0, by omega⟩
       workTapes := fun i ↦ tapeOf (F w (argValuation e w) i)
       workTapePos := Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1)
       output := [] ++ F w (argValuation e w) ⟨2, h2⟩ } : Cfg (tapes e) Bool Unit w)
    rfl (bound (wordBound e) w.length)
    (fun j ↦ by
      change -1 ≤ Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1) j ∧
        Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1) j ≤
          (bound (wordBound e) w.length : ℤ)
      by_cases hj : j = ⟨2, h2⟩
      · rw [hj, Function.update_self]
        constructor <;> omega
      · rw [Function.update_of_ne hj]
        constructor <;> omega)
    (by
      change Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1) ⟨2, h2⟩ + 1 ≤
        (bound (wordBound e) w.length : ℤ)
      rw [Function.update_self]
      omega)
  -- the suffix
  have hpark : Parked
      ({ state := some (emitSuffix (⟨3, h3⟩ : Fin (tapes e)) ⟨0, h0⟩).q₀
         inputPos := ⟨0, by omega⟩
         workTapes := fun i ↦ tapeOf (F w (argValuation e w) i)
         workTapePos := Function.update
           (Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1)) ⟨2, h2⟩
           (Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1) ⟨2, h2⟩ + 1)
         output := [] ++ F w (argValuation e w) ⟨2, h2⟩ } :
        Cfg (tapes e) Bool (StateOf (emitSuffix (⟨3, h3⟩ : Fin (tapes e)) ⟨0, h0⟩)) w) := by
    intro j
    change Function.update (Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1))
      ⟨2, h2⟩ (Function.update (fun _ ↦ (0 : ℤ)) (⟨2, h2⟩ : Fin (tapes e)) (-1) ⟨2, h2⟩ + 1) j = 0
    by_cases hj : j = ⟨2, h2⟩
    · rw [hj, Function.update_self, Function.update_self]
      omega
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  obtain ⟨t₄, ht₄, h₄⟩ := emitSuffix_emits (⟨3, h3⟩ : Fin (tapes e)) ⟨0, h0⟩ h30 _ rfl
    (F w (argValuation e w)) (fun _ ↦ rfl) hpark rfl l hC hl (bound (wordBound e) w.length) hFB
  -- the emitted string is the meaning
  have hrtake : w.rtake w.length = w := by
    rw [List.rtake_eq_reverse_take_reverse, ← List.length_reverse, List.take_length,
      List.reverse_reverse]
  have hden := den_repSem w e (fun i ↦ readRep (argValuation e w) (![argReg e] i)) fun i ↦ by
    rw [Fin.fin_one_eq_zero i]
    change counterValue (argValuation e w ⟨1, h1⟩) ≤ w.length
    rw [hσ1, counterValue_counterWord]
  have hv : readRep (F w (argValuation e w)) (outReg e) =
      LOf.repSem w e fun i ↦ readRep (argValuation e w) (![argReg e] i) :=
    hval w (argValuation e w) hpre
  rw [← hv] at hden
  have hx : (fun i ↦ (readRep (argValuation e w) (![argReg e] i)).den w) = ![w] := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    change [] ++ w.rtake (counterValue (argValuation e w ⟨1, h1⟩)) = w
    rw [hσ1, counterValue_counterWord, List.nil_append, hrtake]
  rw [hx] at hden
  change F w (argValuation e w) ⟨2, h2⟩ ++
    w.rtake (counterValue (F w (argValuation e w) ⟨3, h3⟩)) = _ at hden
  rw [hC, counterValue_counterWord] at hden
  -- the composite
  have hall := h₁.seqEmits (h₂.seqEmits (h₃.seqEmits (hmr.seqEmits h₄)))
  rw [hden] at hall
  rw [liftL_start (countInput (⟨1, h1⟩ : Fin (tapes e)))
    (seq (program e).tm (seq (writer ⟨2, h2⟩) (seq (moveRight ⟨2, h2⟩)
      (emitSuffix ⟨3, h3⟩ ⟨0, h0⟩)))) ((machine e).initCfg w) rfl]
  refine ⟨_, _, ?_, hall⟩
  unfold time
  omega

end

end Geb.SizeBounded.Logspace.Machine
