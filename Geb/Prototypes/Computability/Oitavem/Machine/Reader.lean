/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Allocate
public import Geb.Prototypes.Computability.Oitavem.Machine.Read
public import Geb.Prototypes.Computability.Oitavem.Machine.While

set_option doc.verso true in
/-!
# Streaming through digit readers

A digit reader returns the requested digit as an optional singleton word. Its
query register and the environment survive the call. A streaming loop uses this
interface to emit a virtual word in list order, retaining only the current index
and digit. The first missing digit terminates the loop.

## Main definitions

* {lit}`ReadsAt` specifies a digit subroutine preserving all but its result register.
* {lit}`emitBit` emits the symbol at a parked result head without changing any tape.
* {lit}`emitReader` streams a word by querying its digits in order.

## Main statements

* {lit}`emitReader_emitsIn` proves exact output, termination, and a bound throughout
  every nested reader call. The final query register contains the word's length.

## Implementation notes

Reader scratch can be included in the precondition with its initialized contents.
Its restoration makes repeated calls preserve the valuation. Both the word and
the precondition must be independent of the query and result registers. The
contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, word reader, streaming, composition
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- A silent digit reader with a saved binary query and a single result register.
Queries through the first out-of-range position must halt and obey the bound. -/
@[expose] def ReadsAt {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (Q R : Fin k)
    (Pre : List Bool → (Fin k → List Bool) → Prop)
    (W : List Bool → (Fin k → List Bool) → List Bool) (T B : ℕ → ℕ) : Prop :=
  TransformsIn P
    (fun input σ ↦ Pre input σ ∧ ∃ q, σ Q = counterWord q ∧ q ≤ (W input σ).length)
    (fun input σ ↦ Function.update σ R ((W input σ)[counterValue (σ Q)]?).toList) T B

/-- The physical input supplies a digit reader when its scratch register is initialized. -/
theorem inputAt_readsAt {k : ℕ} (Q C R : Fin k)
    (hQC : Q ≠ C) (hQR : Q ≠ R) (hCR : C ≠ R) (B : ℕ → ℕ)
    (hB1 : ∀ n, 1 ≤ B n) :
    ReadsAt (inputAt Q C R) Q R (fun _ σ ↦ σ C = []) (fun input _ ↦ input)
      (fun n ↦ inputAtTime (B n) n n) B := by
  refine ((inputAt_transformsIn Q C R hQC hQR hCR B id hB1).mono_pre ?_).congr ?_
  · exact fun _ _ _ h ↦ h.2
  · intro input σ h
    rw [← h.1, Function.update_eq_self]

/-- A stored word supplies a digit reader with restored scratch tapes. -/
theorem readStored_readsAt {k : ℕ} (r : Fin 5 → Fin k) (hr : Function.Injective r)
    (B : ℕ → ℕ) :
    ReadsAt (readStored r) (r 1) (r 4) (fun _ σ ↦ σ (r 2) = [] ∧ σ (r 3) = [])
      (fun _ σ ↦ σ (r 0)) (fun n ↦ readStoredTime (B n) (B n)) B := by
  refine ((readStored_transformsIn r hr B B).mono_pre ?_).congr ?_
  · intro input σ hB h
    obtain ⟨q, hq, hlen⟩ := h.2
    exact ⟨q, hq, hlen.trans (hB (r 0))⟩
  · intro input σ h
    have h2 : Function.update σ (r 2) [] = σ := by rw [← h.1.1, Function.update_eq_self]
    have h3 : Function.update σ (r 3) [] = σ := by rw [← h.1.2, Function.update_eq_self]
    simp only [h2, h3]

/-- A generator restoring its valuation supplies a digit reader with reusable scratch.
The countdown is initialized in the precondition and restored by every query. -/
theorem generatedAt_readsAt {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : EmitsIn P Pre (fun _ σ ↦ σ) W T B) (Q : Fin k) (hB1 : ∀ n, 1 ≤ B n) :
    ReadsAt (generatedAt P Q) (oldTape Q) resultTape
      (fun input σ ↦ σ countTape = [] ∧ Pre input (fun i ↦ σ (oldTape i)))
      (fun input σ ↦ W input (fun i ↦ σ (oldTape i)))
      (fun n ↦ T n * (2 * B n + 8) + 13 * B n + 30) B := by
  refine ((generatedAt_transformsIn hP Q hB1).mono_pre ?_).congr ?_
  · intro input σ _ hpre
    obtain ⟨q, hq, _⟩ := hpre.2
    exact ⟨⟨q, hq⟩, hpre.1.2⟩
  · intro input σ hpre
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j ↦ ?_)) i
    · change [] = Function.update σ resultTape _ countTape
      rw [Function.update_of_ne countTape_ne_resultTape, hpre.1.1]
    · change _ = Function.update σ resultTape _ resultTape
      rw [Function.update_self]
      rfl
    · exact (Function.update_of_ne (oldTape_ne_resultTape j) _ _).symm

/-- A digit reader can be placed in a larger caller layout. The new protected tapes
are absent from its precondition and represented word and remain unchanged. -/
theorem ReadsAt.onTapes {k m l : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    {Q R : Fin k} {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : ReadsAt P Q R Pre W T B) (e : Fin m ≃ Fin k ⊕ Fin l) :
    ReadsAt (Machine.onTapes P e) (e.symm (.inl Q)) (e.symm (.inl R))
      (fun input σ ↦ Pre input (fun i ↦ σ (e.symm (.inl i))))
      (fun input σ ↦ W input (fun i ↦ σ (e.symm (.inl i)))) T B := by
  refine (TransformsIn.onTapes hP e).congr ?_
  intro input σ _
  funext i
  rcases hi : e i with j | j
  · have he : i = e.symm (.inl j) := (e.symm_apply_apply i).symm.trans (congrArg e.symm hi)
    rw [he, onTapesVal_left]
    by_cases hj : j = R
    · subst j
      simp
    · rw [Function.update_of_ne hj, Function.update_of_ne]
      exact fun h ↦ hj (Sum.inl.inj (e.symm.injective h))
  · have he : i = e.symm (.inr j) := (e.symm_apply_apply i).symm.trans (congrArg e.symm hi)
    rw [he, onTapesVal_right, Function.update_of_ne]
    intro h
    have := e.symm.injective h
    cases this

/-- Emit the symbol under a work head in one step, leaving every tape and head unchanged. -/
@[expose] def emitBit {k : ℕ} (R : Fin k) : MultiTapeTM k Bool Unit where
  q₀ := ()
  tr _ _ work :=
    { inputTape := 0, workTapes := fun _ ↦ (none, 0), output := work R, state := none }

/-- The one-step emitter preserves the entire workspace. -/
theorem emitBit_emits {k : ℕ} {input : List Bool} (R : Fin k)
    (cfg : Cfg k Bool Unit input) (hq : cfg.state = some ()) (B : ℕ)
    (hpos : ∀ i, -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B) :
    Emits (emitBit R) cfg
      { cfg with state := none, output := cfg.output ++ (cfg.workTapeSymbols R).toList }
      (cfg.workTapeSymbols R).toList 1 B := by
  have hs : (emitBit R).step cfg =
      { cfg with state := none, output := cfg.output ++ (cfg.workTapeSymbols R).toList } := by
    rw [step_of_state _ _ () hq]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      exact add_zero _
    · rfl
  refine ⟨⟨?_, by simpa only [runFrom_succ_eq_step', runFrom_zero] using hs, ?_⟩, ?_, rfl⟩
  · intro s h
    have : s = 0 := by omega
    simpa only [this, runFrom_zero, hq] using Option.some_ne_none ()
  · intro s h i
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl
    · exact hpos i
    · simpa only [runFrom_succ_eq_step', runFrom_zero, hs] using hpos i
  · simp [outputString_succ, outputSymbol, hq, emitBit]
    rfl

/-- Emit the current digit, advance the query, and read the next digit until it is missing. -/
@[expose] def emitReaderLoop {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (Q R : Fin k) :=
  whileNonblank (some R) (seq (emitBit R) (seq (inc Q) P))

/-- A reader loop emits the represented word while preserving its environment.
The query and digit ports must not be part of that environment. -/
theorem emitReaderLoop_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (Q R : Fin k) (hQR : Q ≠ R)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : ReadsAt P Q R Pre W T B)
    (hpre : ∀ input σ q r, Pre input σ →
      Pre input (Function.update (Function.update σ Q q) R r))
    (hword : ∀ input σ q r,
      W input (Function.update (Function.update σ Q q) R r) = W input σ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (emitReaderLoop P Q R)
      (fun input σ ↦ Pre input σ ∧ σ Q = [] ∧ σ R = ((W input σ)[0]?).toList)
      (fun input σ ↦ Function.update
        (Function.update σ Q (counterWord (W input σ).length)) R []) W
      (fun n ↦ N n * (T n + 2 * B n + 6) + 1) B := by
  intro input cfg σ hq hpark hpos hσ hinit hB
  obtain ⟨hp, hQ, hR⟩ := hinit
  let w := W input σ
  let v (j : ℕ) := Function.update (Function.update σ Q (counterWord j)) R (w[j]?).toList
  let c : ℕ → Cfg k Bool (StateOf (seq (emitBit R) (seq (inc Q) P))) input := fun j ↦
    { cfg with state := none, workTapes := fun i ↦ tapeOf (v j i)
               output := cfg.output ++ w.take j }
  have hb (j : ℕ) (hj : j ≤ w.length) : Bounded (v j) (B input.length) :=
    (hB.update (by
      rw [length_counterWord]
      exact (size_le_size (hj.trans (hlen input σ hp))).trans (hsize _))).update
      (Option.length_toList_le.trans (hB1 _))
  have hvQ (j : ℕ) : v j Q = counterWord j := by
    simp [v, Function.update_of_ne hQR]
  have hprobe (j : ℕ) : probeOf (some R) (c j) = w[j]? := by
    change tapeOf (v j R) (cfg.workTapePos R) = _
    rw [hpark R, show v j R = (w[j]?).toList from Function.update_self ..]
    cases w[j]? <;> simp [tapeOf]
  have hheads (i : Fin k) : -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length := by
    rw [hpark i]
    constructor <;> omega
  obtain ⟨t, ht, hr⟩ := arrives_whileNonblank (some R) (seq (emitBit R) (seq (inc Q) P))
    (B input.length) (T input.length + 2 * B input.length + 5) w.length c
    (by
      intro j hj
      rw [hprobe, List.getElem?_eq_getElem hj]
      exact Option.some_ne_none _)
    (by rw [hprobe, List.getElem?_length])
    (by
      intro j hj
      let u := Function.update (Function.update σ Q (counterWord (j + 1))) R (w[j]?).toList
      have hu : Function.update (v j) Q (counterWord (j + 1)) = u := by
        dsimp only [v, u]
        rw [Function.update_comm hQR.symm, Function.update_idem]
      have huB : Bounded u (B input.length) :=
        (hB.update (by
          rw [length_counterWord]
          exact (size_le_size ((by omega : j + 1 ≤ w.length).trans (hlen input σ hp))).trans
            (hsize _))).update (Option.length_toList_le.trans (hB1 _))
      have re := emitBit_emits R { c j with state := some () } rfl (B input.length) hheads
      have hd : ({ c j with state := some () } : Cfg k Bool Unit input).workTapeSymbols R =
          w[j]? := hprobe j
      rw [hd] at re
      let ce : Cfg k Bool (StateOf (inc Q)) input :=
        { c j with state := some (inc Q).q₀, output := (c j).output ++ (w[j]?).toList }
      obtain ⟨s, hs, ri⟩ := inc_transforms Q (B input.length) ce (v j) rfl hpark
        (fun _ ↦ rfl) (hb j (by omega)) (by
          dsimp only
          rw [hvQ, incL_counterWord, hu]
          exact huB)
      dsimp only at ri
      rw [hvQ, incL_counterWord, hu] at ri
      have huQ : u Q = counterWord (j + 1) := by
        simp [u, Function.update_of_ne hQR]
      obtain ⟨_, a, ha, ra⟩ := hP input
        { after ce u with state := some P.q₀ } u rfl hpark hpos (fun _ ↦ rfl)
        ⟨hpre input σ _ _ hp, j + 1, huQ, by rw [hword]; exact Nat.succ_le_of_lt hj⟩ huB
      have hnext : Function.update u R ((W input u)[counterValue (u Q)]?).toList = v (j + 1) := by
        rw [huQ, counterValue_counterWord, show W input u = w from hword input σ _ _]
        exact Function.update_idem ..
      dsimp only at ra
      rw [hnext] at ra
      have r := re.seqEmits (ri.seq ra).toEmits
      rw [List.append_nil, ← liftL_start (emitBit R) (seq (inc Q) P)
        { c j with state := some (seq (emitBit R) (seq (inc Q) P)).q₀ } rfl] at r
      refine ⟨1 + (s + a), by omega, (r.congr_target ?_).toArrives⟩
      apply Cfg.ext
      · rfl
      · rfl
      · rfl
      · rfl
      · change (cfg.output ++ w.take j) ++ (w[j]?).toList = cfg.output ++ w.take (j + 1)
        rw [List.append_assoc, ← List.take_add_one]) hheads
  have hstart : { c 0 with state := some (.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      change tapeOf (v 0 i) = cfg.workTapes i
      dsimp only [v]
      rw [show counterWord 0 = [] from rfl, ← hQ, Function.update_eq_self,
        show (w[0]?).toList = σ R from hR.symm, Function.update_eq_self, hσ]
    · rfl
    · simp [c]
  rw [hstart] at hr
  refine ⟨(hB.update (by
    rw [length_counterWord]
    exact (size_le_size (hlen input σ hp)).trans (hsize _))).update (Nat.zero_le _),
    t, ht.trans ?_, ?_⟩
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hlen input σ hp)) 1
  · refine ⟨?_, ?_, rfl⟩
    · simpa only [emitReaderLoop, c, v, after, List.getElem?_length,
        Option.toList_none, List.take_length] using hr
    · apply List.append_cancel_left (as := cfg.output)
      dsimp only [emitReaderLoop]
      rw [← runFrom_output, hr.runFrom_eq]
      change cfg.output ++ w.take w.length = cfg.output ++ w
      rw [List.take_length]

/-- Initialize the query and stream a word through its digit reader. -/
@[expose] def emitReader {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (Q R : Fin k) :=
  seq (seq (const [] Q) P) (emitReaderLoop P Q R)

/-- Digit readers suffice for streaming. Only the query and result registers
change, and every subcall obeys the original physical-input space bound. -/
theorem emitReader_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (Q R : Fin k) (hQR : Q ≠ R)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : ReadsAt P Q R Pre W T B)
    (hpre : ∀ input σ q r, Pre input σ →
      Pre input (Function.update (Function.update σ Q q) R r))
    (hword : ∀ input σ q r,
      W input (Function.update (Function.update σ Q q) R r) = W input σ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (emitReader P Q R) Pre
      (fun input σ ↦ Function.update
        (Function.update σ Q (counterWord (W input σ).length)) R []) W
      (fun n ↦ 4 * B n + 9 + T n + (N n * (T n + 2 * B n + 6) + 1)) B := by
  have hpQ input σ q (hp : Pre input σ) : Pre input (Function.update σ Q q) := by
    simpa only [Function.update_eq_self] using
      hpre input σ q (Function.update σ Q q R) hp
  have hwQ input σ q : W input (Function.update σ Q q) = W input σ := by
    simpa only [Function.update_eq_self] using
      hword input σ q (Function.update σ Q q R)
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] Q (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hi : TransformsIn (seq (const [] Q) P) Pre
      (fun input σ ↦ Function.update (Function.update σ Q []) R ((W input σ)[0]?).toList)
      (fun n ↦ 4 * B n + 9 + T n) B := by
    refine ((hc.seq hP).mono_pre ?_).congr ?_
    · intro input σ _ hp
      exact ⟨trivial, hpQ input σ [] hp, 0, Function.update_self .., Nat.zero_le _⟩
    · intro input σ _
      simp only [Function.update_self, hwQ, show counterValue [] = 0 from rfl]
  have hl := emitReaderLoop_emitsIn Q R hQR hP hpre hword hlen hsize hB1
  intro input cfg σ hq hpark hpos hσ hp hB
  have hinit : Pre input σ ∧
      (Pre input (Function.update (Function.update σ Q []) R ((W input σ)[0]?).toList) ∧
      Function.update (Function.update σ Q []) R ((W input σ)[0]?).toList Q = [] ∧
      Function.update (Function.update σ Q []) R ((W input σ)[0]?).toList R =
        ((W input
          (Function.update (Function.update σ Q []) R ((W input σ)[0]?).toList))[0]?).toList) :=
    ⟨hp, hpre input σ _ _ hp, by simp [Function.update_of_ne hQR], by simp [hword]⟩
  obtain ⟨hFB, t, ht, he⟩ := hi.seqEmitsIn hl input cfg σ hq hpark hpos hσ hinit hB
  dsimp only at hFB he
  rw [hword, Function.update_comm hQR.symm, Function.update_idem,
    Function.update_idem] at hFB he
  exact ⟨hFB, t, ht, he⟩

end

end Geb.Oitavem.Machine
