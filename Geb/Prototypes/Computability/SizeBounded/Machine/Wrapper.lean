/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Machine.Seq
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Input
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Output
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Return
public import Geb.Prototypes.Computability.SizeBounded.Machine.Phase.Clear
public import Geb.Prototypes.Computability.SizeBounded.Machine.Compile.Theorem
public import Geb.Prototypes.Computability.SizeBounded.Machine.Bound

set_option doc.verso true

/-!
# The machine of an expression

A compiled program of the calculus reads and writes registers; a
{name}`Turing.MultiTapeTM` reads an input tape and emits an output string. The
two phases that bridge the difference are {lit}`reader`, which loads the input
into a register and parks its head, and {lit}`writer`, which emits a register's
word. {lit}`machine` sequences the reader, the compiled program of an
expression of one argument and the writer, over
{lit}`regsBound e.1.1 + 2` registers: register {lit}`0` holds the input,
register {lit}`1` receives the value, and the compiled program's need is met
from register {lit}`2` up.

{lit}`machine_emits` composes the reader's run, the program's contract
{name}`Geb.SizeBounded.Machine.SOf.correct` and the writer's emission. The
contract states its step count existentially, so the composite's step count is
existential too, bounded by the sum of the three phases' bounds.

The registers and the compiled program are written out rather than abbreviated
by local definitions: the program the contract speaks of is the compiler's, and
matching it against the machine's second component is a definitional comparison
of machines, which a local definition standing between the two sides defeats.

The module is admitted to {lit}`GebMeta.classicalAllowedModules`: its
statements mention {name}`Turing.MultiTapeTM.configs` and
{name}`Turing.MultiTapeTM.outputString`, each depending on
{lit}`Classical.choice` through Cslib's
{name}`Turing.MultiTapeTM.Cfg.inputSymbol`.

# Main definitions

* {lit}`reader`, {lit}`writer` — the input-loading and output-emitting phases.
* {lit}`ReaderState`, {lit}`WriterState`, {lit}`State` — their state types and
  the machine's.
* {lit}`tapes`, {lit}`program`, {lit}`machine` — the register count, the
  compiled program at the wrapper's allocation, and the whole machine.
* {lit}`bound`, {lit}`time` — the length bound and the step count on an input
  of a given length.

# Main statements

* {lit}`reader_runsTo` — the reader's run, naming the halted configuration and
  the step count.
* {lit}`writer_emits` — the writer's emission.
* {lit}`machine_emits` — the machine emits the expression's value at the input.

# Tags

Turing machine, input tape, output, compilation, size-bounded
-/

namespace Geb.SizeBounded.Machine

open Turing MultiTapeTM
open scoped FinEnum
open Geb.SizeBounded (SOf nsiConst)

public section

/-- The input reader: the input head to the right end, one cell back, the walk
left writing the input at register {lit}`j` in the reversed layout, and the
return of {lit}`j`'s head. -/
@[expose] def reader {k : ℕ} (j : Fin k) :=
  seq inRight (seq inBack (seq (inLeft j) (returnTape j)))

/-- The state type of {name}`reader`. -/
abbrev ReaderState : Type := Unit ⊕ (Unit ⊕ (Unit ⊕ (Unit ⊕ Unit)))

/-- {name}`reader` from the initial input head and an empty parked register
{lit}`j` runs {lit}`3 * input.length + 5` steps and leaves {lit}`j` holding the
input, parked, the input head at the blank before the input. -/
theorem reader_runsTo {k : ℕ} {input : List Bool} (j : Fin k)
    (cfg : Cfg k Bool ReaderState input) (hq : cfg.state = some (reader j).q₀)
    (hp : cfg.inputPos.val = 1) (hj : cfg.workTapes j = tapeOf []) (hpark : Parked cfg)
    (B : ℕ) (hB : input.length ≤ B) :
    RunsTo (reader j) cfg
      { cfg with
        state := none
        inputPos := ⟨0, by omega⟩
        workTapes := Function.update cfg.workTapes j (tapeOf input) }
      (3 * input.length + 5) B := by
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have hself : Function.update cfg.workTapePos j (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos j from (hpark j).symm, Function.update_eq_self]
  have r₁ := inRight_runsTo (k := k) { cfg with state := some (inRight (k := k)).q₀ } rfl hp B hpos
  have r₂ := inBack_runsTo (k := k)
    { cfg with
      state := some (inBack (k := k)).q₀
      inputPos := ⟨input.length + 1, by omega⟩ } rfl rfl B hpos
  have r₃ := inLeft_runsTo j
    { cfg with state := some (inLeft j).q₀, inputPos := ⟨input.length, by omega⟩ }
    rfl rfl hj (hpark j) B hB hpos
  have r₄ := returnTape_runsTo j
    ({ cfg with
      state := some (returnTape j).q₀
      inputPos := ⟨0, by omega⟩
      workTapes := Function.update cfg.workTapes j (tapeOf input)
      workTapePos := Function.update cfg.workTapePos j (input.length : ℤ) } :
      Cfg k Bool (Unit ⊕ Unit) input)
    rfl input
    (by change Function.update cfg.workTapes j (tapeOf input) j = tapeOf input
        rw [Function.update_self])
    (input.length : ℤ)
    (by change Function.update cfg.workTapePos j (input.length : ℤ) j = (input.length : ℤ)
        rw [Function.update_self])
    (by omega) (by omega) B
    (fun l ↦ update_workTapePos_bounds j hpos _ (by omega) (by omega) l)
  rw [Function.update_idem, hself,
    show ((input.length : ℤ) + 2).toNat = input.length + 2 from by omega] at r₄
  have h₃₄ := r₃.seq r₄
  rw [← liftL_start (inLeft j) (returnTape j)
    { cfg with
      state := some (seq (inLeft j) (returnTape j)).q₀
      inputPos := ⟨input.length, by omega⟩ } rfl] at h₃₄
  have h₂₃₄ := r₂.seq h₃₄
  rw [← liftL_start (inBack (k := k)) (seq (inLeft j) (returnTape j))
    { cfg with
      state := some (seq (inBack (k := k)) (seq (inLeft j) (returnTape j))).q₀
      inputPos := ⟨input.length + 1, by omega⟩ } rfl] at h₂₃₄
  have h₁₂₃₄ := r₁.seq h₂₃₄
  rw [← liftL_start (inRight (k := k)) (seq (inBack (k := k)) (seq (inLeft j) (returnTape j)))
      cfg hq,
    show input.length + 1 + (1 + (input.length + 1 + (input.length + 2))) =
      3 * input.length + 5 from by omega] at h₁₂₃₄
  rw [show ({ cfg with
        state := none
        inputPos := ⟨0, by omega⟩
        workTapes := Function.update cfg.workTapes j (tapeOf input) } :
      Cfg k Bool ReaderState input) =
    liftR (liftR (liftR ({ cfg with
      state := (none : Option (Unit ⊕ Unit))
      inputPos := ⟨0, by omega⟩
      workTapes := Function.update cfg.workTapes j (tapeOf input) } :
        Cfg k Bool (Unit ⊕ Unit) input))) from ?_]
  · exact h₁₂₃₄
  · apply Cfg.ext <;> rfl

/-- The output writer: register {lit}`i`'s head to its first blank, one cell
back, and the walk left emitting the register's word. -/
@[expose] def writer {k : ℕ} (i : Fin k) := seq (walkEnd i) (seq (moveLeft i) (emitLeft i))

/-- The state type of {name}`writer`. -/
abbrev WriterState : Type := Unit ⊕ (Unit ⊕ Unit)

/-- {name}`writer` from a parked register {lit}`i` holding {lit}`w` runs
{lit}`2 * w.length + 3` steps and emits {lit}`w`. -/
theorem writer_emits {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool WriterState input) (hq : cfg.state = some (writer i).q₀)
    (w : List Bool) (hw : cfg.workTapes i = tapeOf w) (hpark : Parked cfg) (B : ℕ)
    (hB : w.length ≤ B) :
    Emits (writer i) cfg
      { cfg with state := none, workTapePos := Function.update cfg.workTapePos i (-1) }
      w (2 * w.length + 3) B := by
  have hpos : ∀ l, -1 ≤ cfg.workTapePos l ∧ cfg.workTapePos l ≤ B := by
    intro l
    rw [hpark l]
    constructor <;> omega
  have r₁ := walkEnd_runsTo i { cfg with state := some (walkEnd i).q₀ } rfl w hw (hpark i)
    B hB hpos
  have r₂ := moveLeft_runsTo i
    { cfg with
      state := some (moveLeft i).q₀
      workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) }
    rfl B
    (fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l)
    (by change (0 : ℤ) ≤ Function.update cfg.workTapePos i (w.length : ℤ) i
        rw [Function.update_self]
        omega)
  have hmv : Function.update (Function.update cfg.workTapePos i (w.length : ℤ)) i
        (Function.update cfg.workTapePos i (w.length : ℤ) i - 1) =
      Function.update cfg.workTapePos i ((w.length : ℤ) - 1) := by
    rw [Function.update_self, Function.update_idem]
  rw [hmv] at r₂
  have r₃ := emitLeft_emits i
    { cfg with
      state := some (emitLeft i).q₀
      workTapePos := Function.update cfg.workTapePos i ((w.length : ℤ) - 1) }
    rfl w hw
    (by change Function.update cfg.workTapePos i ((w.length : ℤ) - 1) i = (w.length : ℤ) - 1
        rw [Function.update_self])
    B hB (fun l ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) l)
  rw [Function.update_idem] at r₃
  have h₂₃ := r₂.seqEmits r₃
  rw [← liftL_start (moveLeft i) (emitLeft i)
    { cfg with
      state := some (seq (moveLeft i) (emitLeft i)).q₀
      workTapePos := Function.update cfg.workTapePos i (w.length : ℤ) } rfl] at h₂₃
  have h₁₂₃ := r₁.seqEmits h₂₃
  rw [← liftL_start (walkEnd i) (seq (moveLeft i) (emitLeft i)) cfg hq,
    show w.length + 1 + (1 + (w.length + 1)) = 2 * w.length + 3 from by omega] at h₁₂₃
  rw [show ({ cfg with
        state := none
        workTapePos := Function.update cfg.workTapePos i (-1) } :
      Cfg k Bool WriterState input) =
    liftR (liftR ({ cfg with
      state := (none : Option Unit)
      workTapePos := Function.update cfg.workTapePos i (-1) } : Cfg k Bool Unit input)) from ?_]
  · exact h₁₂₃
  · apply Cfg.ext <;> rfl

/-- The registers of an expression's machine: the input register, the output
register, and the compiled program's need. -/
@[expose] def tapes (e : SOf 1) : ℕ := regsBound e.1.1 + 2

/-- The compiled program of {lit}`e` reading register {lit}`0`, writing register
{lit}`1`, with the registers from {lit}`2` free. -/
@[expose] def program (e : SOf 1) : Prog (tapes e) :=
  (SOf.compile (tapes e) e).prog ![⟨0, by unfold tapes; omega⟩] ⟨1, by unfold tapes; omega⟩ 2
    (by rw [SOf.regs]; unfold tapes; omega)

/-- The state type of an expression's machine. -/
abbrev State (e : SOf 1) : Type := ReaderState ⊕ ((program e).State ⊕ WriterState)

/-- The state type is enumerable, by the compiled program's enumeration and the
scoped instances for sums and {lit}`Unit`. -/
instance (e : SOf 1) : FinEnum (State e) :=
  @FinEnum.finSum _ _ inferInstance (@FinEnum.finSum _ _ (program e).enum inferInstance)

/-- The machine of an expression: the reader, the compiled program, the writer. -/
@[expose] def machine (e : SOf 1) : MultiTapeTM (tapes e) Bool (State e) :=
  seq (reader ⟨0, by unfold tapes; omega⟩)
    (seq (program e).tm (writer ⟨1, by unfold tapes; omega⟩))

/-- The length bound the machine runs under on an input of length {lit}`n`: the
length or the expression's constant. -/
@[expose] def bound (e : SOf 1) (n : ℕ) : ℕ := max n (nsiConst e.1.1)

/-- The machine's step count on an input of length {lit}`n`. -/
@[expose] def time (e : SOf 1) (n : ℕ) : ℕ :=
  (3 * n + 5) + stepBound e.1.1 (bound e n) + (2 * bound e n + 3)

/-- The machine of {lit}`e` on {lit}`w` emits {lit}`e`'s meaning at {lit}`w`,
in the reader's, the program's and the writer's steps, every head within the
bound. -/
theorem machine_emits (e : SOf 1) (w : List Bool) :
    ∃ cfg' t', t' ≤ (3 * w.length + 5) + stepBound e.1.1 (bound e w.length) +
        (2 * (e.sem ![w]).length + 3) ∧
      Emits (machine e) ((machine e).initCfg w) cfg' (e.sem ![w]) t' (bound e w.length) := by
  have h0 : 0 < tapes e := by unfold tapes; omega
  have h1 : 1 < tapes e := by unfold tapes; omega
  have hB : w.length ≤ bound e w.length := Nat.le_max_left _ _
  have hK : nsiConst e.1.1 ≤ bound e w.length := Nat.le_max_right _ _
  have hσ₀ : Bounded (Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w)
      (bound e w.length) := Bounded.update (fun _ ↦ Nat.zero_le _) hB
  have h₁ := reader_runsTo (⟨0, h0⟩ : Fin (tapes e))
    ({ (machine e).initCfg w with
        state := some (reader (⟨0, h0⟩ : Fin (tapes e))).q₀ } :
      Cfg (tapes e) Bool ReaderState w)
    rfl rfl tapeOf_nil.symm (fun _ ↦ rfl) (bound e w.length) hB
  obtain ⟨F, hT, hval, -, hbd⟩ := SOf.correct (tapes e) e ![(⟨0, h0⟩ : Fin (tapes e))]
    (⟨1, h1⟩ : Fin (tapes e)) 2 (by rw [SOf.regs]; unfold tapes; omega)
    (fun a b _ ↦ Subsingleton.elim a b)
    (fun i ↦ by rw [Fin.fin_one_eq_zero i, Matrix.cons_val_zero]; exact Nat.zero_lt_two)
    Nat.one_lt_two
    (fun i ↦ by
      rw [Fin.fin_one_eq_zero i, Matrix.cons_val_zero]
      exact Fin.ne_of_val_ne Nat.zero_ne_one)
    (bound e w.length) hK
  obtain ⟨t, ht, h₂⟩ := hT
    ({ state := some (program e).tm.q₀
       inputPos := ⟨0, by omega⟩
       workTapes := Function.update (fun _ _ ↦ none) (⟨0, h0⟩ : Fin (tapes e)) (tapeOf w)
       workTapePos := fun _ ↦ 0 } : Cfg (tapes e) Bool (program e).State w)
    (Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w)
    rfl (fun _ ↦ rfl)
    (fun i ↦ by
      change Function.update (fun _ _ ↦ none) (⟨0, h0⟩ : Fin (tapes e)) (tapeOf w) i =
        tapeOf (Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w i)
      by_cases hi : i = (⟨0, h0⟩ : Fin (tapes e))
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        exact tapeOf_nil.symm)
    hσ₀ (hbd _ hσ₀)
  have hcomp : Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w ∘
      ![(⟨0, h0⟩ : Fin (tapes e))] = ![w] := by
    funext i
    rw [Fin.fin_one_eq_zero i]
    change Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w
        (![(⟨0, h0⟩ : Fin (tapes e))] 0) = ![w] 0
    rw [Matrix.cons_val_zero, Matrix.cons_val_zero, Function.update_self]
  have hF : F (Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w)
      (⟨1, h1⟩ : Fin (tapes e)) = e.sem ![w] := by
    rw [hval, hcomp]
  have h₃ := writer_emits (⟨1, h1⟩ : Fin (tapes e))
    ({ state := some (writer (⟨1, h1⟩ : Fin (tapes e))).q₀
       inputPos := ⟨0, by omega⟩
       workTapes := fun i ↦
         tapeOf (F (Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w) i)
       workTapePos := fun _ ↦ 0 } : Cfg (tapes e) Bool WriterState w)
    rfl (e.sem ![w])
    (by
      change tapeOf (F (Function.update (fun _ ↦ ([] : List Bool)) (⟨0, h0⟩ : Fin (tapes e)) w)
          (⟨1, h1⟩ : Fin (tapes e))) = tapeOf (e.sem ![w])
      rw [hF])
    (fun _ ↦ rfl) (bound e w.length) (by rw [← hF]; exact hbd _ hσ₀ _)
  have h₁₂₃ := h₁.seqEmits (h₂.seqEmits h₃)
  rw [liftL_start (reader (⟨0, h0⟩ : Fin (tapes e)))
    (seq (program e).tm (writer (⟨1, h1⟩ : Fin (tapes e)))) ((machine e).initCfg w) rfl]
  exact ⟨_, _, by omega, h₁₂₃⟩

end

end Geb.SizeBounded.Machine
