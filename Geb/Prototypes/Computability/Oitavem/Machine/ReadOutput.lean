/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Machine.Phase.Dec
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Reading one digit of a machine's output without storing it

A digit reader wraps a fixed emitter {lit}`P` in a machine that simulates it,
suppresses everything it emits, and retains a single emitted bit: the one whose
index is the query {lit}`q`, supplied at run time as the binary counter on an
extra countdown tape. The reader adds two tapes to {lit}`P`'s: tape {lit}`0`
holds the countdown, tape {lit}`1` receives the retained bit, and {lit}`P`'s
tape {lit}`i` is the reader's tape {lit}`i + 2`. The complete output is never
stored: the countdown is decremented once per emission until it reads zero, the
bit emitted at that point is written on the result tape, a Boolean latch in the
finite control records that it has been, and the rest of the run proceeds
silently. When {lit}`P` emits at most {lit}`q` bits the result tape stays blank,
which is how "no such bit" is distinguished from the bit {lit}`false`.

# Main definitions

* {lit}`EmbedsSub`, {lit}`liftSub` — a machine embedding a subroutine's control,
  and the embedding of the subroutine's configurations.
* {lit}`countTape`, {lit}`resultTape`, {lit}`oldTape`, {lit}`tapeCase` — the
  reader's tape layout.
* {lit}`ReadState`, {lit}`readOutput` — the reader's finite control and machine.
* {lit}`wrapCfg` — a configuration of {lit}`P` together with the reader's extra
  tapes.

# Main statements

* {lit}`RunsTo.liftSub` — a run of an embedded subroutine is a reach of the
  embedding machine.
* {lit}`dec_runsTo` — the decrement of a counter register whose own head is
  parked, the other heads being anywhere within the bound.
* {lit}`readOutput_runsTo` — the reader's contract: from the wrapped
  configuration it runs to the wrapped halted configuration whose result tape
  holds the queried digit.

# Implementation notes

The proof was developed with Aristotle. Its machine contracts inherit
{lit}`Classical.choice` from CSLib, so this module is included in
{lit}`GebMeta.classicalAllowedModules`.

# Tags

Turing machine, output, binary counter, logspace, digit reader
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-! ## Embedding a subroutine's control -/

/-- {lit}`W` embeds the subroutine {lit}`A` along {lit}`ι`, resuming at
{lit}`r`: at an embedded state {lit}`W` acts as {lit}`A` does, continuing at the
embedded successor and, where {lit}`A` would halt, at {lit}`r`. -/
@[expose] def EmbedsSub {n : ℕ} {SA SW : Type} (W : MultiTapeTM n Bool SW)
    (A : MultiTapeTM n Bool SA) (ι : SA → SW) (r : Option SW) : Prop :=
  ∀ (q : SA) (inp : Option Bool) (work : Fin n → Option Bool),
    W.tr (ι q) inp work =
      { A.tr q inp work with
        state := ((A.tr q inp work).state).elim r (fun s ↦ some (ι s)) }

/-- A configuration of the subroutine, as one of the embedding machine: a halted
one becomes the resume state. -/
@[expose] def liftSub {n : ℕ} {SA SW : Type} {input : List Bool} (ι : SA → SW)
    (r : Option SW) (c : Cfg n Bool SA input) : Cfg n Bool SW input :=
  { c with state := c.state.elim r (fun s ↦ some (ι s)) }

/-- The lift keeps the tapes. -/
@[simp] theorem liftSub_workTapes {n : ℕ} {SA SW : Type} {input : List Bool}
    (ι : SA → SW) (r : Option SW) (c : Cfg n Bool SA input) :
    (liftSub ι r c).workTapes = c.workTapes := rfl

/-- The lift keeps the heads. -/
@[simp] theorem liftSub_workTapePos {n : ℕ} {SA SW : Type} {input : List Bool}
    (ι : SA → SW) (r : Option SW) (c : Cfg n Bool SA input) :
    (liftSub ι r c).workTapePos = c.workTapePos := rfl

/-- The lift keeps the input head. -/
@[simp] theorem liftSub_inputPos {n : ℕ} {SA SW : Type} {input : List Bool}
    (ι : SA → SW) (r : Option SW) (c : Cfg n Bool SA input) :
    (liftSub ι r c).inputPos = c.inputPos := rfl

/-- The lift of a live configuration is live. -/
theorem liftSub_state_of_live {n : ℕ} {SA SW : Type} {input : List Bool}
    (ι : SA → SW) (r : Option SW) (c : Cfg n Bool SA input) (q : SA)
    (hq : c.state = some q) : (liftSub ι r c).state = some (ι q) := by
  unfold liftSub
  rw [hq]
  rfl

/-- The lift of a halted configuration is the resume state. -/
theorem liftSub_state_of_halt {n : ℕ} {SA SW : Type} {input : List Bool}
    (ι : SA → SW) (r : Option SW) (c : Cfg n Bool SA input) (hq : c.state = none) :
    (liftSub ι r c).state = r := by
  unfold liftSub
  rw [hq]
  rfl

/-- A step of the embedding machine from a lifted live configuration is the lift
of the subroutine's step. -/
theorem EmbedsSub.step {n : ℕ} {SA SW : Type} {input : List Bool}
    {W : MultiTapeTM n Bool SW} {A : MultiTapeTM n Bool SA} {ι : SA → SW}
    {r : Option SW} (h : EmbedsSub W A ι r) (c : Cfg n Bool SA input) (q : SA)
    (hq : c.state = some q) : W.step (liftSub ι r c) = liftSub ι r (A.step c) := by
  rw [step_of_state W _ (ι q) (liftSub_state_of_live ι r c q hq), step_of_state A c q hq,
    h q (liftSub ι r c).inputSymbol (liftSub ι r c).workTapeSymbols]
  rfl

/-- The embedding machine emits from a lifted live configuration what the
subroutine emits. -/
theorem EmbedsSub.outputSymbol {n : ℕ} {SA SW : Type} {input : List Bool}
    {W : MultiTapeTM n Bool SW} {A : MultiTapeTM n Bool SA} {ι : SA → SW}
    {r : Option SW} (h : EmbedsSub W A ι r) (c : Cfg n Bool SA input) (q : SA)
    (hq : c.state = some q) :
    W.outputSymbol (liftSub ι r c) = A.outputSymbol c := by
  unfold MultiTapeTM.outputSymbol
  rw [liftSub_state_of_live ι r c q hq, hq]
  change (W.tr (ι q) (liftSub ι r c).inputSymbol (liftSub ι r c).workTapeSymbols).output =
    (A.tr q c.inputSymbol c.workTapeSymbols).output
  rw [h q (liftSub ι r c).inputSymbol (liftSub ι r c).workTapeSymbols]
  rfl

/-- While the subroutine has not halted, the embedding machine mirrors it. -/
theorem EmbedsSub.runFrom {n : ℕ} {SA SW : Type} {input : List Bool}
    {W : MultiTapeTM n Bool SW} {A : MultiTapeTM n Bool SA} {ι : SA → SW}
    {r : Option SW} (h : EmbedsSub W A ι r) (c : Cfg n Bool SA input) :
    ∀ t, (∀ t' < t, (A.runFrom c t').state ≠ none) →
      W.runFrom (liftSub ι r c) t = liftSub ι r (A.runFrom c t) :=
  Nat.rec (fun _ ↦ by rw [runFrom_zero, runFrom_zero])
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [runFrom_succ_eq_step', ih (fun t' ht' ↦ hlive t' (by omega)),
        runFrom_succ_eq_step', h.step (A.runFrom c t) q hq])

/-- While the subroutine has not halted, the embedding machine emits what it
emits. -/
theorem EmbedsSub.outputString {n : ℕ} {SA SW : Type} {input : List Bool}
    {W : MultiTapeTM n Bool SW} {A : MultiTapeTM n Bool SA} {ι : SA → SW}
    {r : Option SW} (h : EmbedsSub W A ι r) (c : Cfg n Bool SA input) :
    ∀ t, (∀ t' < t, (A.runFrom c t').state ≠ none) →
      W.outputString (liftSub ι r c) t = A.outputString c t :=
  Nat.rec (fun _ ↦ rfl)
    (fun t ih hlive ↦ by
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hlive t (by omega))
      rw [outputString_succ, outputString_succ, ih (fun t' ht' ↦ hlive t' (by omega)),
        h.runFrom c t (fun t' ht' ↦ hlive t' (by omega)),
        h.outputSymbol (A.runFrom c t) q hq])

/-- A run of the subroutine is a reach of the embedding machine, from the lifted
source to the lifted target, which holds the resume state. -/
theorem RunsTo.liftSub {n : ℕ} {SA SW : Type} {input : List Bool}
    {W : MultiTapeTM n Bool SW} {A : MultiTapeTM n Bool SA} {ι : SA → SW}
    {r : Option SW} (h : EmbedsSub W A ι r) {c c' : Cfg n Bool SA input} {t B : ℕ}
    (hrun : RunsTo A c c' t B) :
    Reaches W (Geb.Oitavem.Machine.liftSub ι r c)
      (Geb.Oitavem.Machine.liftSub ι r c') t B where
  live := fun t' ht' ↦ by
    rw [h.runFrom c t' (fun s hs ↦ hrun.live s (by omega))]
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hrun.live t' ht')
    rw [liftSub_state_of_live ι r _ q hq]
    exact Option.some_ne_none _
  runFrom_eq := by rw [h.runFrom c t hrun.live, hrun.runFrom_eq]
  pos := fun t' ht' i ↦ by
    rw [h.runFrom c t' (fun s hs ↦ hrun.live s (by omega)), liftSub_workTapePos]
    exact hrun.pos t' ht' i
  output := by rw [h.outputString c t hrun.live, hrun.output]

/-! ## The reader's tape layout -/

/-- The countdown tape of the reader. -/
@[expose] def countTape {k : ℕ} : Fin (k + 2) := 0

/-- The result tape of the reader. -/
@[expose] def resultTape {k : ℕ} : Fin (k + 2) := Fin.succ 0

/-- The reader's tape carrying the emitter's tape {lit}`i`. -/
@[expose] def oldTape {k : ℕ} (i : Fin k) : Fin (k + 2) := i.succ.succ

/-- A value per reader tape, given one for the countdown tape, one for the
result tape and one per tape of the emitter. -/
@[expose] def tapeCase {k : ℕ} {α : Sort*} (c r : α) (f : Fin k → α) : Fin (k + 2) → α :=
  Fin.cases c (Fin.cases r f)

/-- The value at the countdown tape. -/
@[simp] theorem tapeCase_countTape {k : ℕ} {α : Sort*} (c r : α) (f : Fin k → α) :
    tapeCase c r f countTape = c := rfl

/-- The value at the result tape. -/
@[simp] theorem tapeCase_resultTape {k : ℕ} {α : Sort*} (c r : α) (f : Fin k → α) :
    tapeCase c r f resultTape = r := rfl

/-- The value at a tape of the emitter. -/
@[simp] theorem tapeCase_oldTape {k : ℕ} {α : Sort*} (c r : α) (f : Fin k → α) (i : Fin k) :
    tapeCase c r f (oldTape i) = f i := rfl

/-- The countdown tape is not the result tape. -/
theorem countTape_ne_resultTape {k : ℕ} : (countTape : Fin (k + 2)) ≠ resultTape := by
  intro h
  exact absurd (congrArg Fin.val h) (by simp [countTape, resultTape])

/-- Every reader tape is the countdown tape, the result tape or a tape of the
emitter. -/
theorem tapeCase_cases {k : ℕ} (j : Fin (k + 2)) :
    j = countTape ∨ j = resultTape ∨ ∃ i : Fin k, j = oldTape i :=
  Fin.cases (Or.inl rfl)
    (Fin.cases (Or.inr (Or.inl rfl)) (fun i ↦ Or.inr (Or.inr ⟨i, rfl⟩))) j

/-! ## The decrement of a counter whose own head alone is parked -/

/-- The decrement of a canonical digit list is the predecessor's. -/
theorem decL_ofNat (l : ℕ) : decL (ofNat l) = ofNat (l - 1) := by
  cases l with
  | zero => rfl
  | succ m => exact decL_ofNat_succ m

/-- {name}`Geb.SizeBounded.Logspace.Machine.dec` decrements the counter on tape
{lit}`i` from a head parked at cell {lit}`0`, the other heads being anywhere
within the bound: the contract of
{name}`Geb.SizeBounded.Logspace.Machine.dec_transforms` without its parking
assumption on the other tapes. -/
theorem dec_runsTo {k : ℕ} {input : List Bool} (i : Fin k)
    (cfg : Cfg k Bool (Fin 3 ⊕ (Unit ⊕ Unit)) input) (hq : cfg.state = some (dec i).q₀) (l : ℕ)
    (hw : cfg.workTapes i = tapeOf (counterWord l)) (hp : cfg.workTapePos i = 0) (B : ℕ)
    (hB : Nat.size l ≤ B) (hpos : ∀ j, -1 ≤ cfg.workTapePos j ∧ cfg.workTapePos j ≤ B) :
    ∃ t ≤ 2 * B + 6, RunsTo (dec i) cfg
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (counterWord (l - 1))) } t B := by
  have hlenB : (ofNat l).length ≤ B := by rw [length_ofNat_eq_size]; exact hB
  have hself : Function.update cfg.workTapePos i (0 : ℤ) = cfg.workTapePos := by
    rw [show (0 : ℤ) = cfg.workTapePos i from hp.symm, Function.update_eq_self]
  obtain ⟨p, t, hp', ht, r₁⟩ := decWalk_runsTo i { cfg with state := some (decWalk i).q₀ } rfl
    (ofNat l) hw hp B hlenB hpos
  have hpB : p ≤ B := le_trans hp' (le_trans (length_decL_le _) hlenB)
  have r₂ := returnTape_runsTo i
    { cfg with
      state := some (returnTape i).q₀
      workTapes := Function.update cfg.workTapes i (tapeOf (decL (ofNat l)).reverse)
      workTapePos := Function.update cfg.workTapePos i (p : ℤ) }
    rfl (decL (ofNat l)).reverse
    (by change Function.update cfg.workTapes i (tapeOf (decL (ofNat l)).reverse) i = _
        rw [Function.update_self])
    (p : ℤ)
    (by change Function.update cfg.workTapePos i (p : ℤ) i = (p : ℤ)
        rw [Function.update_self])
    (by omega) (by rw [List.length_reverse]; omega) B
    (fun j ↦ update_workTapePos_bounds i hpos _ (by omega) (by omega) j)
  rw [Function.update_idem, hself, show ((p : ℤ) + 2).toNat = p + 2 from by omega] at r₂
  have hall := r₁.seq r₂
  rw [← liftL_start (decWalk i) (returnTape i) cfg hq] at hall
  refine ⟨t + (p + 2), by omega, ?_⟩
  have hcfg : (liftR { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (decL (ofNat l)).reverse) } :
      Cfg k Bool (Fin 3 ⊕ (Unit ⊕ Unit)) input) =
      { cfg with
        state := none
        workTapes := Function.update cfg.workTapes i (tapeOf (counterWord (l - 1))) } := by
    apply Cfg.ext
    · rfl
    · rfl
    · change Function.update cfg.workTapes i (tapeOf (decL (ofNat l)).reverse) = _
      rw [decL_ofNat]
      rfl
    · rfl
    · rfl
  rw [hcfg] at hall
  exact hall

/-! ## The reader's control and machine -/

/-- The reader's finite control: simulating the emitter at a state, with the
latch recording whether the queried digit has been retained; or running the
countdown's decrement, remembering the emitter's state to resume at. -/
abbrev ReadState (S : Type) : Type :=
  (S × Bool) ⊕ ((Fin 3 ⊕ (Unit ⊕ Unit)) × Option S)

/-- The reader's action at a simulated step that touches neither extra tape:
the emitter's action on its own tapes, emitting nothing. -/
@[expose] def simAction {k : ℕ} {S : Type} (a : Action k Bool S) (latch : Bool) :
    Action (k + 2) Bool (ReadState S) where
  inputTape := a.inputTape
  workTapes := tapeCase (none, 0) (none, 0) a.workTapes
  output := none
  state := a.state.map (fun q ↦ .inl (q, latch))

/-- The reader's action at the emission it retains: the emitter's action, the
bit written at the parked result head, and the latch set. -/
@[expose] def captureAction {k : ℕ} {S : Type} (a : Action k Bool S) (b : Bool) :
    Action (k + 2) Bool (ReadState S) :=
  { simAction a true with workTapes := tapeCase (none, 0) (some (some b), 0) a.workTapes }

/-- The reader's action at an emission it counts down past: the emitter's
action, and the decrement entered at its initial state. -/
@[expose] def decEnterAction {k : ℕ} {S : Type} (a : Action k Bool S) :
    Action (k + 2) Bool (ReadState S) :=
  { simAction a false with
    state := some (.inr ((dec (countTape : Fin (k + 2))).q₀, a.state)) }

/-- The reader's action at a simulated step, given the emitter's action, the
latch and the symbol under the countdown head. -/
@[expose] def simTr {k : ℕ} {S : Type} (a : Action k Bool S) (latch : Bool)
    (c : Option Bool) : Action (k + 2) Bool (ReadState S) :=
  match a.output with
  | none => simAction a latch
  | some b =>
    if latch then simAction a true
    else
      match c with
      | none => captureAction a b
      | some _ => decEnterAction a

/-- The reader's action at a step of the decrement, resuming the simulation at
{lit}`resume` once the decrement halts. -/
@[expose] def decTr {k : ℕ} {S : Type} (d : Action (k + 2) Bool (Fin 3 ⊕ (Unit ⊕ Unit)))
    (resume : Option S) : Action (k + 2) Bool (ReadState S) :=
  { d with
    state := d.state.elim (resume.map (fun q ↦ .inl (q, false)))
      (fun s ↦ some (.inr (s, resume))) }

/-- The digit reader of the emitter {lit}`P`: {lit}`P` simulated on the tapes
{lit}`oldTape i`, its emissions suppressed, the countdown on tape
{name}`countTape` decremented once per emission until it reads zero, and the
bit emitted then written on tape {name}`resultTape`. -/
@[expose] def readOutput {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) :
    MultiTapeTM (k + 2) Bool (ReadState S) where
  q₀ := .inl (P.q₀, false)
  tr q inp work :=
    match q with
    | .inl (q, latch) => simTr (P.tr q inp (fun i ↦ work (oldTape i))) latch (work countTape)
    | .inr (s, resume) => decTr ((dec countTape).tr s inp work) resume

/-- The reader embeds the decrement of the countdown tape at every resumption
point. -/
theorem embedsSub_dec {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (resume : Option S) :
    EmbedsSub (readOutput P) (dec countTape) (fun s ↦ .inr (s, resume))
      (resume.map (fun q ↦ .inl (q, false))) := fun _ _ _ ↦ rfl

/-- The action at an emitter step that emits nothing. -/
theorem simTr_of_output_none {k : ℕ} {S : Type} (a : Action k Bool S) (latch : Bool)
    (c : Option Bool) (h : a.output = none) :
    simTr a latch c = simAction a latch := by
  unfold simTr
  rw [h]

/-- The action at an emission after the digit has been retained. -/
theorem simTr_of_latch {k : ℕ} {S : Type} (a : Action k Bool S) (c : Option Bool)
    (b : Bool) (h : a.output = some b) : simTr a true c = simAction a true := by
  unfold simTr
  rw [h]
  rfl

/-- The action at the emission the reader retains. -/
theorem simTr_capture {k : ℕ} {S : Type} (a : Action k Bool S) (b : Bool)
    (h : a.output = some b) : simTr a false none = captureAction a b := by
  unfold simTr
  rw [h]
  rfl

/-- The action at an emission the reader counts down past. -/
theorem simTr_decEnter {k : ℕ} {S : Type} (a : Action k Bool S) (b x : Bool)
    (h : a.output = some b) : simTr a false (some x) = decEnterAction a := by
  unfold simTr
  rw [h]
  rfl

/-! ## Wrapped configurations -/

/-- A configuration of the emitter together with the reader's extra tapes: the
countdown holding {lit}`l`, the result tape holding {lit}`res`, both heads
parked, and the caller's output {lit}`out`. -/
@[expose] def wrapCfg {k : ℕ} {S : Type} {input : List Bool} (cfgP : Cfg k Bool S input)
    (latch : Bool) (l : ℕ) (res out : List Bool) : Cfg (k + 2) Bool (ReadState S) input where
  state := cfgP.state.map (fun q ↦ .inl (q, latch))
  inputPos := cfgP.inputPos
  workTapes := tapeCase (tapeOf (counterWord l)) (tapeOf res) cfgP.workTapes
  workTapePos := tapeCase 0 0 cfgP.workTapePos
  output := out

/-- The wrapped configuration of a live one is live at the simulating state. -/
theorem wrapCfg_state_of_live {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) (q : S)
    (hq : cfgP.state = some q) :
    (wrapCfg cfgP latch l res out).state = some (.inl (q, latch)) := by
  unfold wrapCfg
  rw [hq]
  rfl

/-- The wrapped configuration of a halted one is halted. -/
theorem wrapCfg_state_of_halt {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool)
    (hq : cfgP.state = none) : (wrapCfg cfgP latch l res out).state = none := by
  unfold wrapCfg
  rw [hq]
  rfl

/-- The wrapped configuration reads the emitter's input symbol. -/
@[simp] theorem wrapCfg_inputSymbol {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) :
    (wrapCfg cfgP latch l res out).inputSymbol = cfgP.inputSymbol := rfl

/-- The wrapped configuration reads the emitter's work symbols on the emitter's
tapes. -/
theorem wrapCfg_workTapeSymbols_oldTape {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) :
    (fun i ↦ (wrapCfg cfgP latch l res out).workTapeSymbols (oldTape i)) =
      cfgP.workTapeSymbols := rfl

/-- The wrapped configuration reads the countdown's least significant digit. -/
@[simp] theorem wrapCfg_workTapeSymbols_countTape {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) :
    (wrapCfg cfgP latch l res out).workTapeSymbols countTape =
      tapeOf (counterWord l) 0 := rfl

/-! ## The reader's simulating steps -/

/-- The reader's step from a wrapped live configuration, given the action its
control takes: the emitter steps on its own tapes, the countdown is untouched,
and the result tape is written as the action says. -/
theorem step_wrapCfg {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfgP : Cfg k Bool S input) (q : S) (hq : cfgP.state = some q) (latch : Bool) (l : ℕ)
    (res out : List Bool) (wr : Option (Option Bool)) (st : Option (ReadState S))
    (hA : simTr (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols) latch (tapeOf (counterWord l) 0) =
      { inputTape := (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).inputTape
        workTapes := tapeCase (none, 0) (wr, 0)
          (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).workTapes
        output := none
        state := st }) :
    (readOutput P).step (wrapCfg cfgP latch l res out) =
      { state := st
        inputPos := (P.step cfgP).inputPos
        workTapes := tapeCase (tapeOf (counterWord l))
          (wr.elim (tapeOf res) (Function.update (tapeOf res) 0)) (P.step cfgP).workTapes
        workTapePos := tapeCase 0 0 (P.step cfgP).workTapePos
        output := out } := by
  have htr : (readOutput P).tr (.inl (q, latch)) (wrapCfg cfgP latch l res out).inputSymbol
      (wrapCfg cfgP latch l res out).workTapeSymbols =
      simTr (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols) latch
        (tapeOf (counterWord l) 0) := rfl
  rw [step_of_state _ _ _ (wrapCfg_state_of_live cfgP latch l res out q hq), htr, hA,
    step_of_state P cfgP q hq]
  apply Cfg.ext
  · rfl
  · rfl
  · funext j
    rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
    · rfl
    · cases wr with
      | none => rfl
      | some s => rfl
    · rfl
  · funext j
    rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
    · exact add_zero 0
    · exact add_zero 0
    · rfl
  · exact List.append_nil out

/-- The countdown head reads a blank exactly at the value zero. -/
theorem tapeOf_counterWord_zero (l : ℕ) : tapeOf (counterWord l) 0 = none ↔ l = 0 := by
  have hz : tapeOf (counterWord l) 0 = (ofNat l)[0]? := by
    rw [tapeOf_counterWord l 0]
    simp
  rw [hz, List.getElem?_eq_none_iff]
  constructor
  · intro hlen
    exact (ofNat_eq_nil_iff l).mp
      (List.length_eq_zero_iff.mp (Nat.le_antisymm hlen (Nat.zero_le _)))
  · intro hl
    rw [hl]
    exact Nat.le_refl 0

/-- Writing a bit at the parked head of a blank register gives the register of
that one bit. -/
theorem update_tapeOf_nil (b : Bool) :
    Function.update (tapeOf []) (0 : ℤ) (some b) = tapeOf [b] := by
  rw [tapeOf_cons b []]
  rfl

/-- A step of the emitter that emits nothing is simulated in one step, leaving
both extra tapes as they were. -/
theorem step_wrapCfg_silent {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfgP : Cfg k Bool S input) (q : S) (hq : cfgP.state = some q) (latch : Bool) (l : ℕ)
    (res out : List Bool)
    (h : (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).output = none) :
    (readOutput P).step (wrapCfg cfgP latch l res out) =
      wrapCfg (P.step cfgP) latch l res out := by
  rw [step_wrapCfg P cfgP q hq latch l res out none
    ((P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).state.map (fun q ↦ .inl (q, latch)))
    (by rw [simTr_of_output_none _ latch _ h]; rfl)]
  apply Cfg.ext
  · rw [step_of_state P cfgP q hq]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- After the digit has been retained, an emission is simulated in one step and
changes nothing on the extra tapes. -/
theorem step_wrapCfg_after_capture {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfgP : Cfg k Bool S input) (q : S) (hq : cfgP.state = some q)
    (l : ℕ) (res out : List Bool) (b : Bool)
    (h : (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).output = some b) :
    (readOutput P).step (wrapCfg cfgP true l res out) =
      wrapCfg (P.step cfgP) true l res out := by
  rw [step_wrapCfg P cfgP q hq true l res out none
    ((P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).state.map (fun q ↦ .inl (q, true)))
    (by rw [simTr_of_latch _ _ b h]; rfl)]
  apply Cfg.ext
  · rw [step_of_state P cfgP q hq]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The emission at which the countdown reads zero is retained: it is written
on the blank result tape and the latch is set, in one step. -/
theorem step_wrapCfg_capture {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfgP : Cfg k Bool S input) (q : S) (hq : cfgP.state = some q) (out : List Bool) (b : Bool)
    (h : (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).output = some b) :
    (readOutput P).step (wrapCfg cfgP false 0 [] out) =
      wrapCfg (P.step cfgP) true 0 [b] out := by
  have hzero : tapeOf (counterWord 0) 0 = none := (tapeOf_counterWord_zero 0).mpr rfl
  rw [step_wrapCfg P cfgP q hq false 0 [] out (some (some b))
    ((P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).state.map (fun q ↦ .inl (q, true)))
    (by rw [hzero, simTr_capture _ b h]; rfl)]
  apply Cfg.ext
  · rw [step_of_state P cfgP q hq]
    rfl
  · rfl
  · change tapeCase (tapeOf (counterWord 0)) (Function.update (tapeOf []) (0 : ℤ) (some b))
      (P.step cfgP).workTapes = _
    rw [update_tapeOf_nil b]
    rfl
  · rfl
  · rfl

/-- An emission at a positive countdown enters the decrement, the emitter's own
step having been taken. -/
theorem step_wrapCfg_decEnter {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfgP : Cfg k Bool S input) (q : S) (hq : cfgP.state = some q) (l : ℕ) (res out : List Bool)
    (b : Bool) (hl : l ≠ 0)
    (h : (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).output = some b) :
    (readOutput P).step (wrapCfg cfgP false l res out) =
      { wrapCfg (P.step cfgP) false l res out with
        state := some (.inr ((dec (countTape : Fin (k + 2))).q₀, (P.step cfgP).state)) } := by
  obtain ⟨x, hx⟩ : ∃ x, tapeOf (counterWord l) 0 = some x := by
    cases hc : tapeOf (counterWord l) 0 with
    | none => exact absurd ((tapeOf_counterWord_zero l).mp hc) hl
    | some x => exact ⟨x, rfl⟩
  rw [step_wrapCfg P cfgP q hq false l res out none
    (some (.inr ((dec (countTape : Fin (k + 2))).q₀,
      (P.tr q cfgP.inputSymbol cfgP.workTapeSymbols).state)))
    (by rw [hx, simTr_decEnter _ b x h]; rfl)]
  apply Cfg.ext
  · rw [step_of_state P cfgP q hq]
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## One step of the emitter -/

/-- The result tape is not the countdown tape. -/
theorem resultTape_ne_countTape {k : ℕ} : (resultTape : Fin (k + 2)) ≠ countTape := by
  intro h
  have hv : (resultTape : Fin (k + 2)).val = (countTape : Fin (k + 2)).val := congrArg Fin.val h
  simp [resultTape, countTape] at hv

/-- A tape of the emitter is not the countdown tape. -/
theorem oldTape_ne_countTape {k : ℕ} (i : Fin k) : oldTape i ≠ countTape := by
  intro h
  have hv : (oldTape i).val = (countTape : Fin (k + 2)).val := congrArg Fin.val h
  simp [oldTape, countTape] at hv

/-- Overwriting the countdown tape's contents. -/
theorem update_tapeCase_countTape {k : ℕ} {α : Type*} (c c' r : α) (f : Fin k → α) :
    Function.update (tapeCase c r f) countTape c' = tapeCase c' r f := by
  funext j
  rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
  · rw [Function.update_self]
    rfl
  · rw [Function.update_of_ne resultTape_ne_countTape]
    rfl
  · rw [Function.update_of_ne (oldTape_ne_countTape i)]
    rfl

/-- The reader's actions never emit. -/
theorem simTr_output {k : ℕ} {S : Type} (a : Action k Bool S) (latch : Bool) (c : Option Bool) :
    (simTr a latch c).output = none := by
  unfold simTr
  cases h : a.output with
  | none => rfl
  | some b =>
    cases latch with
    | true => rfl
    | false =>
      cases c with
      | none => rfl
      | some x => rfl

/-- The reader emits nothing while simulating the emitter. -/
theorem readOutput_outputSymbol_wrapCfg {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ)
    (res out : List Bool) :
    (readOutput P).outputSymbol (wrapCfg cfgP latch l res out) = none := by
  unfold MultiTapeTM.outputSymbol
  cases hq : cfgP.state with
  | none => rw [wrapCfg_state_of_halt cfgP latch l res out hq]
  | some q =>
    rw [wrapCfg_state_of_live cfgP latch l res out q hq]
    exact simTr_output _ _ _

/-- The heads of a wrapped configuration stay within the bound as long as the
emitter's do. -/
theorem wrapCfg_pos {k : ℕ} {S : Type} {input : List Bool} (cfgP : Cfg k Bool S input)
    (latch : Bool) (l : ℕ) (res out : List Bool) (B : ℕ)
    (h : ∀ i, -1 ≤ cfgP.workTapePos i ∧ cfgP.workTapePos i ≤ B) (j : Fin (k + 2)) :
    -1 ≤ (wrapCfg cfgP latch l res out).workTapePos j ∧
      (wrapCfg cfgP latch l res out).workTapePos j ≤ B := by
  rcases tapeCase_cases j with rfl | rfl | ⟨i, rfl⟩
  · exact ⟨by change (-1 : ℤ) ≤ 0; omega, by change (0 : ℤ) ≤ (B : ℤ); omega⟩
  · exact ⟨by change (-1 : ℤ) ≤ 0; omega, by change (0 : ℤ) ≤ (B : ℤ); omega⟩
  · exact h i

/-- The reader's configuration after the emitter's first {lit}`s` steps: the
emitter's configuration, the countdown holding what is left of the query, the
result tape holding the queried digit once it has been emitted, and the
caller's output. -/
@[expose] def readCfg {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (query : ℕ) (out : List Bool) (s : ℕ) :
    Cfg (k + 2) Bool (ReadState S) input :=
  wrapCfg (P.runFrom cfg s) ((P.outputString cfg s)[query]?).isSome
    (query - (P.outputString cfg s).length) ((P.outputString cfg s)[query]?).toList out

/-- The reader's configuration, in terms of the word emitted so far. -/
theorem readCfg_eq {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (query : ℕ) (out : List Bool) (s : ℕ) (v : List Bool)
    (hv : P.outputString cfg s = v) :
    readCfg P cfg query out s =
      wrapCfg (P.runFrom cfg s) (v[query]?).isSome (query - v.length) ((v[query]?).toList) out := by
  unfold readCfg
  rw [hv]

/-- The reader emits nothing at a configuration of the simulation. -/
theorem readOutput_outputSymbol_readCfg {k : ℕ} {S : Type} {input : List Bool}
    (P : MultiTapeTM k Bool S) (cfg : Cfg k Bool S input) (query : ℕ) (out : List Bool)
    (s : ℕ) : (readOutput P).outputSymbol (readCfg P cfg query out s) = none :=
  readOutput_outputSymbol_wrapCfg _ _ _ _ _ _

/-- While the emitter runs, the reader's configuration is live. -/
theorem readCfg_live {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (query : ℕ) (out : List Bool) (s : ℕ)
    (h : (P.runFrom cfg s).state ≠ none) : (readCfg P cfg query out s).state ≠ none := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp h
  unfold readCfg
  rw [wrapCfg_state_of_live _ _ _ _ _ q hq]
  exact Option.some_ne_none _

/-- The reader's heads stay within the bound as long as the emitter's do. -/
theorem readCfg_pos {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (query : ℕ) (out : List Bool) (B s : ℕ)
    (h : ∀ i, -1 ≤ (P.runFrom cfg s).workTapePos i ∧ (P.runFrom cfg s).workTapePos i ≤ B) :
    ∀ j, -1 ≤ (readCfg P cfg query out s).workTapePos j ∧
      (readCfg P cfg query out s).workTapePos j ≤ B :=
  wrapCfg_pos _ _ _ _ _ B h

/-- One step of the emitter is simulated by the reader within {lit}`2 * B + 8`
steps: one step for the emitter's own action, and, at an emission before the
queried one, the decrement of the countdown. -/
theorem readOutput_reaches_succ {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    (cfg : Cfg k Bool S input) (query : ℕ) (out : List Bool) (B : ℕ)
    (hquery : Nat.size query ≤ B) (s : ℕ) (hlive : (P.runFrom cfg s).state ≠ none)
    (hpos : ∀ i, -1 ≤ (P.runFrom cfg s).workTapePos i ∧ (P.runFrom cfg s).workTapePos i ≤ B)
    (hpos' : ∀ i, -1 ≤ (P.runFrom cfg (s + 1)).workTapePos i ∧
      (P.runFrom cfg (s + 1)).workTapePos i ≤ B) :
    ∃ ts ≤ 2 * B + 8, Reaches (readOutput P) (readCfg P cfg query out s)
      (readCfg P cfg query out (s + 1)) ts B := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
  obtain ⟨u, hu⟩ : ∃ u, P.outputString cfg s = u := ⟨_, rfl⟩
  have hstepcfg : P.runFrom cfg (s + 1) = P.step (P.runFrom cfg s) := runFrom_succ_eq_step'
  have houts : P.outputSymbol (P.runFrom cfg s) =
      (P.tr q (P.runFrom cfg s).inputSymbol (P.runFrom cfg s).workTapeSymbols).output := by
    unfold MultiTapeTM.outputSymbol
    rw [hq]
  have hsucc : P.outputString cfg (s + 1) =
      u ++ (P.outputSymbol (P.runFrom cfg s)).toList := by
    rw [outputString_succ, hu]
  have hposP' : ∀ i, -1 ≤ (P.step (P.runFrom cfg s)).workTapePos i ∧
      (P.step (P.runFrom cfg s)).workTapePos i ≤ B := by
    rw [← hstepcfg]
    exact hpos'
  cases ho : P.outputSymbol (P.runFrom cfg s) with
  | none =>
    refine ⟨1, by omega, ?_⟩
    have htgt : readCfg P cfg query out (s + 1) =
        wrapCfg (P.step (P.runFrom cfg s)) ((u[query]?).isSome) (query - u.length)
          ((u[query]?).toList) out := by
      rw [readCfg_eq P cfg query out (s + 1) u (by rw [hsucc, ho]; exact List.append_nil u),
        hstepcfg]
    have hsrc : readCfg P cfg query out s =
        wrapCfg (P.runFrom cfg s) ((u[query]?).isSome) (query - u.length)
          ((u[query]?).toList) out := readCfg_eq P cfg query out s u hu
    rw [hsrc, htgt]
    exact Reaches.ofStep _ _ _ B
      (by rw [wrapCfg_state_of_live _ _ _ _ _ q hq]; exact Option.some_ne_none _)
      (step_wrapCfg_silent P (P.runFrom cfg s) q hq _ _ _ _ (by rw [← houts, ho]))
      (readOutput_outputSymbol_wrapCfg _ _ _ _ _ _)
      (wrapCfg_pos _ _ _ _ _ B hpos) (wrapCfg_pos _ _ _ _ _ B hposP')
  | some b =>
    have hsucc' : P.outputString cfg (s + 1) = u ++ [b] := by rw [hsucc, ho]; rfl
    rcases Nat.lt_trichotomy query u.length with hlt | heq | hgt
    · obtain ⟨x, hx⟩ : ∃ x, u[query]? = some x := ⟨u[query]'hlt, List.getElem?_eq_getElem hlt⟩
      have hsrc : readCfg P cfg query out s = wrapCfg (P.runFrom cfg s) true 0 [x] out := by
        rw [readCfg_eq P cfg query out s u hu, hx, show query - u.length = 0 from by omega]
        rfl
      have htgt : readCfg P cfg query out (s + 1) =
          wrapCfg (P.step (P.runFrom cfg s)) true 0 [x] out := by
        rw [readCfg_eq P cfg query out (s + 1) (u ++ [b]) hsucc', hstepcfg,
          List.getElem?_append_left hlt, hx,
          show query - (u ++ [b]).length = 0 from by rw [List.length_append]; omega]
        rfl
      refine ⟨1, by omega, ?_⟩
      rw [hsrc, htgt]
      exact Reaches.ofStep _ _ _ B
        (by rw [wrapCfg_state_of_live _ _ _ _ _ q hq]; exact Option.some_ne_none _)
        (step_wrapCfg_after_capture P (P.runFrom cfg s) q hq 0 [x] out b (by rw [← houts, ho]))
        (readOutput_outputSymbol_wrapCfg _ _ _ _ _ _)
        (wrapCfg_pos _ _ _ _ _ B hpos) (wrapCfg_pos _ _ _ _ _ B hposP')
    · have hnone : u[query]? = none := List.getElem?_eq_none (by omega)
      have hsrc : readCfg P cfg query out s = wrapCfg (P.runFrom cfg s) false 0 [] out := by
        rw [readCfg_eq P cfg query out s u hu, hnone, show query - u.length = 0 from by omega]
        rfl
      have hb : (u ++ [b])[query]? = some b := by
        rw [List.getElem?_append_right (by omega), heq, Nat.sub_self]
        rfl
      have htgt : readCfg P cfg query out (s + 1) =
          wrapCfg (P.step (P.runFrom cfg s)) true 0 [b] out := by
        rw [readCfg_eq P cfg query out (s + 1) (u ++ [b]) hsucc', hstepcfg, hb,
          show query - (u ++ [b]).length = 0 from by rw [List.length_append]; omega]
        rfl
      refine ⟨1, by omega, ?_⟩
      rw [hsrc, htgt]
      exact Reaches.ofStep _ _ _ B
        (by rw [wrapCfg_state_of_live _ _ _ _ _ q hq]; exact Option.some_ne_none _)
        (step_wrapCfg_capture P (P.runFrom cfg s) q hq out b (by rw [← houts, ho]))
        (readOutput_outputSymbol_wrapCfg _ _ _ _ _ _)
        (wrapCfg_pos _ _ _ _ _ B hpos) (wrapCfg_pos _ _ _ _ _ B hposP')
    · have hnone : u[query]? = none := List.getElem?_eq_none (by omega)
      have hnone' : (u ++ [b])[query]? = none :=
        List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega)
      have hl0 : query - u.length ≠ 0 := by omega
      have hsrc : readCfg P cfg query out s =
          wrapCfg (P.runFrom cfg s) false (query - u.length) [] out := by
        rw [readCfg_eq P cfg query out s u hu, hnone]
        rfl
      have htgt : readCfg P cfg query out (s + 1) =
          wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length - 1) [] out := by
        rw [readCfg_eq P cfg query out (s + 1) (u ++ [b]) hsucc', hstepcfg, hnone',
          show query - (u ++ [b]).length = query - u.length - 1 from by
            rw [List.length_append, List.length_singleton]; omega]
        rfl
      have hstep1 := step_wrapCfg_decEnter P (P.runFrom cfg s) q hq (query - u.length) [] out b
        hl0 (by rw [← houts, ho])
      obtain ⟨t₁, ht₁, r₁⟩ := dec_runsTo (countTape : Fin (k + 2))
        { wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length) [] out with
          state := some (dec (countTape : Fin (k + 2))).q₀ }
        rfl (query - u.length) rfl rfl B
        (le_trans (size_le_size (by omega : query - u.length ≤ query)) hquery)
        (wrapCfg_pos (P.step (P.runFrom cfg s)) false (query - u.length) [] out B hposP')
      have r₂ := RunsTo.liftSub (embedsSub_dec P (P.step (P.runFrom cfg s)).state) r₁
      have hmid : { wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length) [] out with
            state := some (.inr ((dec (countTape : Fin (k + 2))).q₀,
              (P.step (P.runFrom cfg s)).state)) } =
          liftSub (fun s' ↦ (.inr (s', (P.step (P.runFrom cfg s)).state) : ReadState S))
            (((P.step (P.runFrom cfg s)).state).map (fun q ↦ .inl (q, false)))
            { wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length) [] out with
              state := some (dec (countTape : Fin (k + 2))).q₀ } := by
        apply Cfg.ext <;> rfl
      have hend : liftSub (fun s' ↦ (.inr (s', (P.step (P.runFrom cfg s)).state) : ReadState S))
          (((P.step (P.runFrom cfg s)).state).map (fun q ↦ .inl (q, false)))
          { wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length) [] out with
            state := none
            workTapes := Function.update
              (wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length) [] out).workTapes
              countTape (tapeOf (counterWord (query - u.length - 1))) } =
          wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length - 1) [] out := by
        apply Cfg.ext
        · rfl
        · rfl
        · exact update_tapeCase_countTape _ _ _ _
        · rfl
        · rfl
      have rstep : Reaches (readOutput P)
          (wrapCfg (P.runFrom cfg s) false (query - u.length) [] out)
          (liftSub (fun s' ↦ (.inr (s', (P.step (P.runFrom cfg s)).state) : ReadState S))
            (((P.step (P.runFrom cfg s)).state).map (fun q ↦ .inl (q, false)))
            { wrapCfg (P.step (P.runFrom cfg s)) false (query - u.length) [] out with
              state := some (dec (countTape : Fin (k + 2))).q₀ }) 1 B := by
        rw [← hmid]
        exact Reaches.ofStep _ _ _ B
          (by rw [wrapCfg_state_of_live _ _ _ _ _ q hq]; exact Option.some_ne_none _)
          hstep1 (readOutput_outputSymbol_wrapCfg _ _ _ _ _ _)
          (wrapCfg_pos (P.runFrom cfg s) false (query - u.length) [] out B hpos)
          (wrapCfg_pos (P.step (P.runFrom cfg s)) false (query - u.length) [] out B hposP')
      have rall := rstep.trans r₂
      rw [hend] at rall
      exact ⟨1 + t₁, by omega, by rw [hsrc, htgt]; exact rall⟩

/-! ## The reader's contract -/

/-- A configuration reaches itself in no steps. -/
theorem Reaches.refl {n : ℕ} {SW : Type} {input : List Bool} (W : MultiTapeTM n Bool SW)
    (c : Cfg n Bool SW input) (B : ℕ)
    (hpos : ∀ i, -1 ≤ c.workTapePos i ∧ c.workTapePos i ≤ B) : Reaches W c c 0 B where
  live := fun t' ht' ↦ absurd ht' (by omega)
  runFrom_eq := runFrom_zero
  pos := fun t' ht' i ↦ by
    rw [show t' = 0 from by omega, runFrom_zero]
    exact hpos i
  output := rfl

/-- The reader simulates the emitter's first {lit}`s` steps within
{lit}`s * (2 * B + 8)` steps of its own. -/
theorem readOutput_reaches {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ} (hem : Emits P cfg cfg' w t B)
    (query : ℕ) (out : List Bool) (B' : ℕ) (hB : B ≤ B') (hquery : Nat.size query ≤ B') :
    ∀ s ≤ t, ∃ ts ≤ s * (2 * B' + 8),
      Reaches (readOutput P) (readCfg P cfg query out 0) (readCfg P cfg query out s) ts B' := by
  have hposB : ∀ s' ≤ t, ∀ i, -1 ≤ (P.runFrom cfg s').workTapePos i ∧
      (P.runFrom cfg s').workTapePos i ≤ (B' : ℤ) := fun s' hs' i ↦
    ⟨(hem.pos s' hs' i).1,
      le_trans (hem.pos s' hs' i).2 (by exact_mod_cast hB : (B : ℤ) ≤ (B' : ℤ))⟩
  refine Nat.rec ?_ ?_
  · intro _
    exact ⟨0, by omega,
      Reaches.refl _ _ B' (readCfg_pos P cfg query out B' 0 (hposB 0 (Nat.zero_le t)))⟩
  · intro s ih hs
    obtain ⟨ts, hts, r⟩ := ih (by omega)
    obtain ⟨t₁, ht₁, r₁⟩ := readOutput_reaches_succ P cfg query out B' hquery s
      (hem.live s (by omega)) (hposB s (by omega)) (hposB (s + 1) (by omega))
    refine ⟨ts + t₁, ?_, r.trans r₁⟩
    rw [Nat.succ_mul]
    exact Nat.add_le_add hts ht₁

/-- The reader's contract. From the emitter's configuration wrapped with the
query on the countdown tape, a blank result tape, both extra heads parked and
an arbitrary caller output, the reader runs to the emitter's halted
configuration wrapped with the queried digit on the result tape, the countdown
holding {lit}`query - w.length` and the caller's output unchanged, within
{lit}`t * (2 * B' + 8)` steps and with every head within {lit}`B'`. -/
theorem readOutput_runsTo {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ} (hem : Emits P cfg cfg' w t B)
    (query : ℕ) (out : List Bool) (B' : ℕ) (hB : B ≤ B') (hquery : Nat.size query ≤ B') :
    ∃ ts ≤ t * (2 * B' + 8),
      RunsTo (readOutput P) (wrapCfg cfg false query [] out)
        (wrapCfg cfg' ((w[query]?).isSome) (query - w.length) ((w[query]?).toList) out) ts B' := by
  obtain ⟨ts, hts, r⟩ := readOutput_reaches P hem query out B' hB hquery t (le_refl t)
  have hhalt : (readCfg P cfg query out t).state = none := by
    unfold readCfg
    rw [hem.runFrom_eq]
    exact wrapCfg_state_of_halt _ _ _ _ _ hem.halted
  have h0 : readCfg P cfg query out 0 = wrapCfg cfg false query [] out := by
    unfold readCfg
    rw [runFrom_zero]
    rfl
  have h1 : readCfg P cfg query out t =
      wrapCfg cfg' ((w[query]?).isSome) (query - w.length) ((w[query]?).toList) out := by
    unfold readCfg
    rw [hem.runFrom_eq, hem.output]
  have run : RunsTo (readOutput P) (readCfg P cfg query out 0) (readCfg P cfg query out t) ts B' :=
    ⟨r, hhalt⟩
  rw [h0, h1] at run
  exact ⟨ts, hts, run⟩

/-- The countdown tape of a wrapped configuration. -/
@[simp] theorem wrapCfg_workTapes_countTape {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) :
    (wrapCfg cfgP latch l res out).workTapes countTape = tapeOf (counterWord l) := rfl

/-- The result tape of a wrapped configuration. -/
@[simp] theorem wrapCfg_workTapes_resultTape {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) :
    (wrapCfg cfgP latch l res out).workTapes resultTape = tapeOf res := rfl

/-- The emitter's tapes in a wrapped configuration. -/
@[simp] theorem wrapCfg_workTapes_oldTape {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) (i : Fin k) :
    (wrapCfg cfgP latch l res out).workTapes (oldTape i) = cfgP.workTapes i := rfl

/-- The emitter's heads in a wrapped configuration. -/
@[simp] theorem wrapCfg_workTapePos_oldTape {k : ℕ} {S : Type} {input : List Bool}
    (cfgP : Cfg k Bool S input) (latch : Bool) (l : ℕ) (res out : List Bool) (i : Fin k) :
    (wrapCfg cfgP latch l res out).workTapePos (oldTape i) = cfgP.workTapePos i := rfl

/-- The reader's contract, with the final configuration's tapes spelled out:
the result tape holds exactly the queried digit of the emitted word, the
emitter's tapes, heads and input head are those it halts in, the caller's
output is untouched, and the countdown holds the query less the number of bits
emitted. -/
theorem readOutput_reads_digit {k : ℕ} {S : Type} {input : List Bool} (P : MultiTapeTM k Bool S)
    {cfg cfg' : Cfg k Bool S input} {w : List Bool} {t B : ℕ} (hem : Emits P cfg cfg' w t B)
    (query : ℕ) (out : List Bool) (B' : ℕ) (hB : B ≤ B') (hquery : Nat.size query ≤ B') :
    ∃ ts ≤ t * (2 * B' + 8), ∃ cfgW : Cfg (k + 2) Bool (ReadState S) input,
      RunsTo (readOutput P) (wrapCfg cfg false query [] out) cfgW ts B' ∧
        cfgW.state = none ∧
        cfgW.workTapes resultTape = tapeOf (w[query]?).toList ∧
        cfgW.workTapePos resultTape = 0 ∧
        cfgW.workTapes countTape = tapeOf (counterWord (query - w.length)) ∧
        cfgW.workTapePos countTape = 0 ∧
        (∀ i, cfgW.workTapes (oldTape i) = cfg'.workTapes i) ∧
        (∀ i, cfgW.workTapePos (oldTape i) = cfg'.workTapePos i) ∧
        cfgW.inputPos = cfg'.inputPos ∧ cfgW.output = out := by
  obtain ⟨ts, hts, run⟩ := readOutput_runsTo P hem query out B' hB hquery
  exact ⟨ts, hts, _, run, wrapCfg_state_of_halt _ _ _ _ _ hem.halted, rfl, rfl, rfl, rfl,
    fun _ ↦ rfl, fun _ ↦ rfl, rfl, rfl⟩

end

end Geb.Oitavem.Machine
