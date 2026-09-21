/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Capture
public import Geb.Prototypes.Computability.Oitavem.Machine.Counter
public import Geb.Prototypes.Computability.Oitavem.Machine.Initial
public import Geb.Prototypes.Computability.Oitavem.Machine.Reader
public import Geb.Prototypes.Computability.Oitavem.Recursion

set_option doc.verso true in
/-!
# Retained-prefix machine loops

Each iteration calls a generator while the previous saved word is still available.
It captures a bounded prefix, replaces the saved word, and decrements a binary
countdown. The mask and capture tape are reused at every iteration. An indexed
invariant relates the saved register to the semantic recursion; the number of work
tapes and nested calls is independent of the iteration count.

## Main definitions

* {lit}`retainedLoop` iterates a generator with bounded saved output.
* {lit}`concatRecGenerator` streams indexed step digits, followed by its base result.
* {lit}`emitPrefix` streams a binary-counted prefix through repeated digit queries.
* {lit}`retainedVal` describes the countdown and saved word between calls.
* {lit}`lengthRecLoop` computes recursive length through generated digit queries.

## Main statements

* {lit}`retainedLoop_transformsIn` realizes an indexed saved-word invariant.
* {lit}`lengthRecLoop_transformsIn` instantiates the invariant with
  {name}`Geb.Oitavem.prefixLoop` for {name}`Geb.Oitavem.lengthByRec`.

## Implementation notes

The caller initializes the countdown, saved word, and mask. The step generator
restores its own registers before the captured prefix replaces the saved register.
The contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, safe recursion, output prefix
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- An iteration stores a prefix, then decrements its remaining-call counter. -/
@[expose] def retainedLoop {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (R C : Fin k) :=
  whileNonblank (some (oldTape C)) (seq (generatedPrefix P R) (dec (oldTape C)))

/-- The old registers between iterations: saved word and remaining-call counter. -/
@[expose] def retainedVal {k : ℕ} (σ : Fin k → List Bool) (R C : Fin k)
    (c : ℕ) (v : List Bool) : Fin k → List Bool :=
  Function.update (Function.update σ R v) C (counterWord c)

/-- A retained-prefix loop realizes any bounded indexed invariant whose next value
is the captured output of its step generator. Only two extra tapes are needed. -/
theorem retainedLoop_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (R C : Fin k) (hRC : R ≠ C)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : EmitsIn P Pre (fun _ σ ↦ σ) W T B)
    (Pre₀ : List Bool → (Fin k → List Bool) → ℕ → Prop)
    (Count : List Bool → (Fin k → List Bool) → ℕ)
    (Value : List Bool → (Fin k → List Bool) → ℕ → ℕ → List Bool)
    (hN : ∀ input σ K, Pre₀ input σ K → Count input σ ≤ N input.length)
    (hV : ∀ input σ K, Pre₀ input σ K → ∀ j ≤ Count input σ,
      (Value input σ K j).length ≤ K)
    (hcall : ∀ input σ K, Pre₀ input σ K → ∀ j < Count input σ,
      let τ := retainedVal σ R C (Count input σ - j) (Value input σ K j)
      Pre input τ ∧ (W input τ).take K = Value input σ K (j + 1)) :
    TransformsIn (retainedLoop P R C)
      (fun input σ ↦
        let τ := fun i ↦ σ (oldTape i)
        Pre₀ input τ (σ countTape).length ∧ σ resultTape = [] ∧
          τ C = counterWord (Count input τ) ∧
          τ R = Value input τ (σ countTape).length 0)
      (fun input σ ↦
        let τ := fun i ↦ σ (oldTape i)
        tapeCase (σ countTape) []
          (retainedVal τ R C 0 (Value input τ (σ countTape).length (Count input τ))))
      (fun n ↦ N n * (((4 * B n + 9) + ((T n + 2 * B n + 4) +
        ((5 * B n + 12) + (4 * B n + 9)))) + (2 * B n + 6) + 1) + 1) B := by
  intro input cfg σ hq hpark hpos hσ hp hB
  let τ := fun i ↦ σ (oldTape i)
  let K := (σ countTape).length
  let c := Count input τ
  let v := Value input τ K
  let vals := fun j ↦ tapeCase (σ countTape) [] (retainedVal τ R C (c - j) (v j))
  have hvals₀ : vals 0 = σ := by
    funext i
    rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
    · rfl
    · exact hp.2.1.symm
    · change retainedVal τ R C (c - 0) (v 0) i = τ i
      have hC : counterWord c = τ C := hp.2.2.1.symm
      have hR : v 0 = τ R := hp.2.2.2.symm
      simp only [retainedVal, Nat.sub_zero, hC, hR,
        Function.update_eq_self]
  have hvB (j : ℕ) (hj : j ≤ c) : Bounded (vals j) (B input.length) := by
    intro i
    rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
    · exact hB countTape
    · exact Nat.zero_le _
    · change (retainedVal τ R C (c - j) (v j) i).length ≤ _
      apply Bounded.update
      · apply Bounded.update (fun i ↦ hB (oldTape i))
        exact (hV input τ K hp.1 j hj).trans (hB countTape)
      · rw [length_counterWord]
        have hc : c.size ≤ B input.length := by
          simpa only [hp.2.2.1, length_counterWord] using hB (oldTape C)
        exact (size_le_size (Nat.sub_le _ _)).trans hc
  have hd := Transforms.toIn_of (fun n ↦ dec_transforms (oldTape C) (B n))
    (fun _ _ ↦ True) (fun _ ρ hb _ ↦ hb.update (by
      rw [List.length_reverse]
      exact (length_decL_le _).trans (by simpa only [List.length_reverse] using hb (oldTape C))))
  have hb := (generatedPrefix_transformsIn hP R).seq hd
  let body := seq (generatedPrefix P R) (dec (oldTape C))
  let f := fun j ↦ after { cfg with state := some body.q₀ } (vals j)
  have hprobe (j : ℕ) : probeOf (some (oldTape C)) (f j) = tapeOf (counterWord (c - j)) 0 := by
    change tapeOf (retainedVal τ R C (c - j) (v j) C) (cfg.workTapePos (oldTape C)) = _
    rw [hpark, retainedVal, Function.update_self]
  have hposB (i : Fin (k + 2)) :
      -1 ≤ (f 0).workTapePos i ∧ (f 0).workTapePos i ≤ B input.length := by
    change -1 ≤ cfg.workTapePos i ∧ cfg.workTapePos i ≤ B input.length
    rw [hpark i]
    constructor <;> omega
  obtain ⟨t, ht, hl⟩ := RunsTo.whileNonblank (some (oldTape C)) body (B input.length)
    (((4 * B input.length + 9) + ((T input.length + 2 * B input.length + 4) +
      ((5 * B input.length + 12) + (4 * B input.length + 9)))) + (2 * B input.length + 6))
    c f
    (by
      intro j hj
      rw [hprobe]
      intro hz
      have := (counterWord_eq_nil_iff _).mp ((tapeOf_zero_eq_none_iff _).mp hz)
      omega)
    (by rw [hprobe, Nat.sub_self]; rfl)
    (by
      intro j hj
      obtain ⟨hpre, hnext⟩ := hcall input τ K hp.1 j hj
      obtain ⟨_, t, ht, hb⟩ := hb input { f j with state := some body.q₀ }
        (vals j) rfl hpark hpos (fun _ ↦ rfl) ⟨hpre, trivial⟩ (hvB j (by omega))
      refine ⟨t, ht, hb.congr_target ?_⟩
      apply Cfg.ext
      · rfl
      · rfl
      · funext i
        apply congrArg tapeOf
        rcases tapeCase_cases i with rfl | rfl | ⟨i, rfl⟩
        · simp [vals, Function.update_of_ne (oldTape_ne_countTape C).symm]
        · simp [vals, Function.update_of_ne (oldTape_ne_resultTape C).symm]
        · change Function.update (tapeCase (σ countTape) []
            (Function.update (retainedVal τ R C (c - j) (v j)) R
              ((W input (retainedVal τ R C (c - j) (v j))).take K)))
            (oldTape C) _ (oldTape i) = retainedVal τ R C (c - (j + 1)) (v (j + 1)) i
          rw [hnext]
          by_cases hi : i = C
          · subst i
            simp only [Function.update_self, tapeCase_oldTape,
              Function.update_of_ne hRC.symm, retainedVal]
            simp only [vals, tapeCase_oldTape, retainedVal, Function.update_self,
              decL_counterWord, Nat.sub_sub]
          · have hi' : oldTape i ≠ oldTape C := fun h ↦
              hi (Fin.succ_injective _ (Fin.succ_injective _ h))
            rw [Function.update_of_ne hi']
            simp only [tapeCase_oldTape, retainedVal]
            rw [Function.update_comm hRC, Function.update_idem,
              Function.update_comm hRC.symm,
              Function.update_of_ne hi, Function.update_of_ne hi]
      · rfl
      · rfl)
    hposB
  have hstart : { f 0 with state := some (Sum.inl ()) } = cfg := by
    apply Cfg.ext
    · exact hq.symm
    · rfl
    · funext i
      change tapeOf (vals 0 i) = cfg.workTapes i
      rw [hvals₀, hσ i]
    · rfl
    · rfl
  rw [hstart] at hl
  refine ⟨?_, t, ht.trans ?_, hl.congr_target ?_⟩
  · simpa only [vals, Nat.sub_self] using hvB c le_rfl
  · exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hN input τ K hp.1)) 1
  · apply Cfg.ext
    · rfl
    · rfl
    · simp only [f, vals, Nat.sub_self, after]
      rfl
    · rfl
    · rfl

/-- Query the digit immediately before a saved countdown, then clear query and result.
This is the input-access part of a recursive length step, whose value ignores that digit. -/
@[expose] def readPrevious {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (C Q D : Fin k) :=
  seq (seq (copy C Q) (dec Q)) (seq P (seq (const [] Q) (const [] D)))

/-- A backwards query restores its initialized query and result registers. -/
theorem readPrevious_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (C Q D : Fin k) (hCQ : C ≠ Q) (hQD : Q ≠ D)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : ReadsAt P Q D Pre W T B)
    (hpre : ∀ input σ q d, Pre input σ →
      Pre input (Function.update (Function.update σ Q q) D d))
    (hword : ∀ input σ q d,
      W input (Function.update (Function.update σ Q q) D d) = W input σ) :
    TransformsIn (readPrevious P C Q D)
      (fun input σ ↦ Pre input σ ∧ σ Q = [] ∧ σ D = [] ∧
        ∃ c, σ C = counterWord c ∧ c ≤ (W input σ).length)
      (fun _ σ ↦ σ)
      (fun n ↦ ((5 * B n + 12) + (2 * B n + 6)) +
        (T n + ((4 * B n + 9) + (4 * B n + 9)))) B := by
  have hc := Transforms.toIn_of (fun n ↦ copy_transforms C Q hCQ (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (hb C))
  have hd := Transforms.toIn_of (fun n ↦ dec_transforms Q (B n))
    (fun _ _ ↦ True) (fun _ σ hb _ ↦ hb.update (by
      rw [List.length_reverse]
      exact (length_decL_le _).trans (by simpa only [List.length_reverse] using hb Q)))
  have hz (i : Fin k) := Transforms.toIn_of (fun n ↦ const_transforms [] i (B n))
    (fun _ _ ↦ True) (fun _ _ hb _ ↦ hb.update (Nat.zero_le _))
  have hs := ((hc.seq hd).seq (hP.seq ((hz Q).seq (hz D)))).mono_pre
    (Pre' := fun input σ ↦ Pre input σ ∧ σ Q = [] ∧ σ D = [] ∧
      ∃ c, σ C = counterWord c ∧ c ≤ (W input σ).length) (by
      intro input σ _ hp
      obtain ⟨c, hc, hcW⟩ := hp.2.2.2
      refine ⟨⟨trivial, trivial⟩, ⟨?_, trivial, trivial⟩⟩
      rw [Function.update_self, Function.update_idem, hc, decL_counterWord]
      have hp' := hpre input σ (counterWord (c - 1)) (σ D) hp.1
      have hw' := hword input σ (counterWord (c - 1)) (σ D)
      rw [Function.update_comm hQD, Function.update_eq_self] at hp' hw'
      refine ⟨hp', c - 1, Function.update_self .., ?_⟩
      rw [hw']
      omega)
  refine hs.congr ?_
  intro input σ hp
  rw [Function.update_comm hQD.symm, Function.update_idem, Function.update_idem,
    Function.update_idem, Function.update_comm hQD]
  have hD : Function.update σ D [] = σ := by rw [← hp.2.2.1, Function.update_eq_self]
  rw [hD, ← hp.2.1, Function.update_eq_self]

/-- Read the next recursion digit and emit the successor of the saved recursive value. -/
@[expose] def lengthRecStep {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S)
    (C R Q D : Fin k) :=
  seq (readPrevious P C Q D) (numericSuccGenerator (emitStored R))

/-- The length step reads its generated recursion input, preserves its environment,
and emits the successor of the saved shortlex word. -/
theorem lengthRecStep_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (C R Q D : Fin k) (hCQ : C ≠ Q) (hQD : Q ≠ D)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B : ℕ → ℕ}
    (hP : ReadsAt P Q D Pre W T B)
    (hpre : ∀ input σ q d, Pre input σ →
      Pre input (Function.update (Function.update σ Q q) D d))
    (hword : ∀ input σ q d,
      W input (Function.update (Function.update σ Q q) D d) = W input σ) :
    EmitsIn (lengthRecStep P C R Q D)
      (fun input σ ↦ Pre input σ ∧ σ Q = [] ∧ σ D = [] ∧
        ∃ c, σ C = counterWord c ∧ c ≤ (W input σ).length)
      (fun _ σ ↦ σ) (fun _ σ ↦ numericSucc (σ R))
      (fun n ↦ (((5 * B n + 12) + (2 * B n + 6)) +
        (T n + ((4 * B n + 9) + (4 * B n + 9)))) + ((2 * B n + 4) + 1)) B := by
  exact ((readPrevious_transformsIn C Q D hCQ hQD hP hpre hword).seqEmitsIn
    (numericSuccGenerator_emitsIn (emitStored_emitsIn R B))).mono_pre
      (fun _ _ _ hp ↦ ⟨hp, trivial⟩)

/-- The recursive length loop over a digit reader.
The layout is countdown, saved word, query, and digit result. -/
@[expose] def lengthRecLoop {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S)
    (r : Fin 4 → Fin k) :=
  retainedLoop (lengthRecStep P (r 0) (r 1) (r 2) (r 3)) (r 1) (r 0)

/-- Recursive length through generated digit queries and a retained shortlex value.
Every iteration reads the next digit, computes the numerical successor of the old
saved value, and captures its bounded prefix before replacing that value. -/
theorem lengthRecLoop_transformsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (r : Fin 4 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : ReadsAt P (r 2) (r 3) Pre W T B)
    (hpre : ∀ input σ q d, Pre input σ →
      Pre input (Function.update (Function.update σ (r 2) q) (r 3) d))
    (hword : ∀ input σ q d,
      W input (Function.update (Function.update σ (r 2) q) (r 3) d) = W input σ)
    (hpreRC : ∀ input σ c v, Pre input σ → Pre input (retainedVal σ (r 1) (r 0) c v))
    (hwordRC : ∀ input σ c v, W input (retainedVal σ (r 1) (r 0) c v) = W input σ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length) :
    TransformsIn (lengthRecLoop P r)
      (fun input σ ↦
        let τ := fun i ↦ σ (oldTape i)
        Pre input τ ∧ τ (r 2) = [] ∧ τ (r 3) = [] ∧
          (unrank (W input τ).length).length ≤ (σ countTape).length ∧
          σ resultTape = [] ∧ τ (r 0) = counterWord (W input τ).length ∧ τ (r 1) = [])
      (fun input σ ↦ tapeCase (σ countTape) []
        (retainedVal (fun i ↦ σ (oldTape i)) (r 1) (r 0) 0
          (unrank (W input (fun i ↦ σ (oldTape i))).length)))
      (fun n ↦ N n * (T n + 34 * B n + 82) + 1) B := by
  let Value := fun (input : List Bool) (σ : Fin k → List Bool) (K j : ℕ) ↦
    prefixLoop K (Expr.initial (.zero 0)).eval (fun _ ↦ lengthByRecStep.eval)
      (W input σ) Fin.elim0 j
  have hs := lengthRecStep_emitsIn (r 0) (r 1) (r 2) (r 3)
    (hr.ne (by decide)) (hr.ne (by decide)) hP hpre hword
  have hl := retainedLoop_transformsIn (r 1) (r 0) (hr.ne (by decide)) hs
    (fun input σ K ↦ Pre input σ ∧ σ (r 2) = [] ∧ σ (r 3) = [] ∧
      (unrank (W input σ).length).length ≤ K)
    (fun input σ ↦ (W input σ).length) Value
    (fun input σ _ hp ↦ hlen input σ hp.1)
    (fun input σ K _ j _ ↦ prefixLoop_length_le K _ _ (W input σ) Fin.elim0 j)
    (by
      intro input σ K hp j hj
      refine ⟨⟨hpreRC input σ _ _ hp.1, ?_, ?_, ?_⟩, ?_⟩
      · simpa [retainedVal, Function.update_of_ne, hr.eq_iff] using hp.2.1
      · simpa [retainedVal, Function.update_of_ne, hr.eq_iff] using hp.2.2.1
      · refine ⟨(W input σ).length - j, by simp [retainedVal], ?_⟩
        rw [hwordRC]
        exact Nat.sub_le _ _
      · rw [retainedVal, Function.update_of_ne (hr.ne (by decide : (1 : Fin 4) ≠ 0)),
          Function.update_self]
        dsimp only [Value]
        rw [prefixLoop_lengthByRec K _ hp.2.2.2 j (by omega),
          prefixLoop_lengthByRec K _ hp.2.2.2 (j + 1) (by omega)]
        simp only [numericSucc, rank_unrank]
        exact List.take_of_length_le ((length_unrank_mono (by omega)).trans hp.2.2.2))
  have hm := hl.mono_pre (Pre' := fun input σ ↦
    let τ := fun i ↦ σ (oldTape i)
    Pre input τ ∧ τ (r 2) = [] ∧ τ (r 3) = [] ∧
      (unrank (W input τ).length).length ≤ (σ countTape).length ∧
      σ resultTape = [] ∧ τ (r 0) = counterWord (W input τ).length ∧ τ (r 1) = []) (by
      intro input σ _ hp
      refine ⟨⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩,
        hp.2.2.2.2.1, hp.2.2.2.2.2.1, ?_⟩
      simpa [Value, prefixLoop, Expr.eval_initial, Initial.eval] using hp.2.2.2.2.2.2)
  refine (hm.mono_time (fun _ ↦ Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (by omega)) 1)).congr ?_
  intro input σ hp
  dsimp only [Value]
  rw [prefixLoop_lengthByRec _ _ hp.2.2.2.1 _ le_rfl]

/-- The countdown and forward index during a streaming recursion. -/
@[expose] def concatVal {k : ℕ} (σ : Fin k → List Bool) (C Q : Fin k) (c j : ℕ) :=
  Function.update (Function.update σ C (counterWord (c - j))) Q (counterWord j)

/-- Emit the current indexed digit, advance the index, and consume one iteration. -/
@[expose] def concatLoop {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (C Q : Fin k) :=
  whileNonblank (some C) (seq P (seq (inc Q) (dec C)))

/-- A generator for each indexed digit gives a streaming word generator.
Only the two counters change between calls; the generated prefix is never stored. -/
theorem concatLoop_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (C Q : Fin k) (hCQ : C ≠ Q)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : EmitsIn P Pre (fun _ σ ↦ σ) W T B)
    (Pre₀ : List Bool → (Fin k → List Bool) → Prop)
    (D : List Bool → (Fin k → List Bool) → List Bool)
    (hlen : ∀ input σ, Pre₀ input σ → (D input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n)
    (hcall : ∀ input σ, Pre₀ input σ → ∀ j < (D input σ).length,
      Pre input (concatVal σ C Q (D input σ).length j) ∧
        W input (concatVal σ C Q (D input σ).length j) = [(D input σ)[j]?.getD false]) :
    EmitsIn (concatLoop P C Q)
      (fun input σ ↦ Pre₀ input σ ∧ σ C = counterWord (D input σ).length ∧ σ Q = [])
      (fun input σ ↦ concatVal σ C Q (D input σ).length (D input σ).length) D
      (fun n ↦ N n * (T n + ((2 * B n + 4) + (2 * B n + 6)) + 1) + 1) B := by
  have hi := Transforms.toIn_of (fun n ↦ inc_transforms Q (B n))
    (fun input σ ↦ ∃ q, σ Q = counterWord q ∧ q < N input.length) (by
      intro input σ hB hp
      obtain ⟨q, hq, hqn⟩ := hp
      refine hB.update ?_
      rw [hq, incL_counterWord, length_counterWord]
      exact (size_le_size (by omega : q + 1 ≤ N input.length)).trans (hsize _))
  have hd := Transforms.toIn_of (fun n ↦ dec_transforms C (B n))
    (fun _ _ ↦ True) (fun _ σ hb _ ↦ hb.update (by
      rw [List.length_reverse]
      exact (length_decL_le _).trans (by simpa only [List.length_reverse] using hb C)))
  have hs := (hP.seqTransformsIn (hi.seq hd)).whileReg C
    (fun input σ ↦ Pre₀ input σ ∧ σ C = counterWord (D input σ).length ∧ σ Q = [])
    (fun input σ ↦ (D input σ).length) N
    (fun input σ j ↦ concatVal σ C Q (D input σ).length j)
    (fun input σ j ↦ (D input σ).take j)
    (fun input σ hp ↦ hlen input σ hp.1)
    (by
      intro input σ hp
      refine ⟨?_, rfl⟩
      dsimp only [concatVal]
      rw [Nat.sub_zero, ← hp.2.1, Function.update_eq_self]
      have hz : Function.update σ Q [] = σ := by rw [← hp.2.2, Function.update_eq_self]
      exact hz)
    (by
      intro input σ hp j hj
      have hN := hlen input σ hp.1
      have hvC : concatVal σ C Q (D input σ).length j C =
          counterWord ((D input σ).length - j) := by simp [concatVal, hCQ]
      have hvQ : concatVal σ C Q (D input σ).length j Q = counterWord j := by
        simp [concatVal]
      refine ⟨?_, ⟨(hcall input σ hp.1 j hj).1, ⟨j, hvQ, by omega⟩, trivial⟩, ?_, ?_⟩
      · rw [hvC, ne_eq, counterWord_eq_nil_iff]
        omega
      · rw [hvQ, incL_counterWord, Function.update_of_ne hCQ, hvC, decL_counterWord]
        dsimp only [concatVal]
        rw [Function.update_idem, Function.update_comm hCQ, Function.update_idem,
          Nat.sub_sub, Nat.add_comm j 1, Function.update_comm hCQ.symm]
      · rw [(hcall input σ hp.1 j hj).2, List.take_add_one, List.getElem?_eq_getElem hj]
        rfl)
    (by
      intro input σ _
      simp [concatVal, hCQ, show counterWord 0 = [] from rfl])
  simpa only [concatLoop, List.take_length] using hs

/-- Stream a saved number of digits through a reader, then clear both loop counters. -/
@[expose] def emitPrefix {k : ℕ} {S : Type}
    (P : MultiTapeTM k Bool S) (C Q R : Fin k) :=
  seq (concatLoop (readDigitGenerator P R) C Q) (const [] Q)

/-- A virtual prefix is emitted without storing it. Its saved length may be polynomially large. -/
theorem emitPrefix_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (C Q R : Fin k) (hCQ : C ≠ Q) (hRC : R ≠ C) (hRQ : R ≠ Q)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : ReadsAt P Q R Pre W T B)
    (hpre : ∀ input σ c q, Pre input σ →
      Pre input (Function.update (Function.update σ C c) Q q))
    (hword : ∀ input σ c q,
      W input (Function.update (Function.update σ C c) Q q) = W input σ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) :
    EmitsIn (emitPrefix P C Q R)
      (fun input σ ↦ Pre input σ ∧ σ R = [] ∧ σ Q = [] ∧
        ∃ c, σ C = counterWord c ∧ c ≤ (W input σ).length)
      (fun _ σ ↦ Function.update (Function.update σ C []) Q [])
      (fun input σ ↦ (W input σ).take (counterValue (σ C)))
      (fun n ↦ (N n * ((T n + (1 + (4 * B n + 9))) +
        ((2 * B n + 4) + (2 * B n + 6)) + 1) + 1) + (4 * B n + 9)) B := by
  let Pre₀ := fun input σ ↦ Pre input σ ∧ σ R = [] ∧
    ∃ c, σ C = counterWord c ∧ c ≤ (W input σ).length
  let D := fun input σ ↦ (W input σ).take (counterValue (σ C))
  have hl := concatLoop_emitsIn C Q hCQ (readDigitGenerator_emitsIn Q R hP) Pre₀ D
    (by
      intro input σ hp
      dsimp only [D]
      rw [List.length_take]
      exact (min_le_right ..).trans (hlen input σ hp.1)) hsize (by
      intro input σ hp j hj
      obtain ⟨hp, hR, c, hc, hcW⟩ := hp
      have hD : D input σ = (W input σ).take c := by simp only [D, hc, counterValue_counterWord]
      have hDl : (D input σ).length = c := by rw [hD, List.length_take, Nat.min_eq_left hcW]
      rw [hDl] at hj ⊢
      have hjW : j < (W input σ).length := hj.trans_le hcW
      refine ⟨⟨⟨hpre input σ _ _ hp, j, by simp [concatVal], ?_⟩, ?_⟩, ?_⟩
      · rw [concatVal, hword]
        exact hjW.le
      · simpa [concatVal, hRC, hRQ] using hR
      · simp only [concatVal, hword, Function.update_self, counterValue_counterWord, hD,
          List.getElem?_take, hj, ite_true, List.getElem?_eq_getElem hjW]
        rfl)
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] Q (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hs := (hl.seqTransformsIn hc).mono_pre (Pre' := fun input σ ↦
    Pre input σ ∧ σ R = [] ∧ σ Q = [] ∧
      ∃ c, σ C = counterWord c ∧ c ≤ (W input σ).length) (by
    intro input σ _ hp
    obtain ⟨c, hC, hcW⟩ := hp.2.2.2
    refine ⟨⟨⟨hp.1, hp.2.1, c, hC, hcW⟩, ?_, hp.2.2.1⟩, trivial⟩
    simp only [D, hC, counterValue_counterWord, List.length_take, Nat.min_eq_left hcW])
  refine hs.congr ?_
  intro input σ _
  simp only [concatVal, Nat.sub_self, Function.update_idem]
  rfl

/-- Stream the step digits of concatenation recursion, clear the index, then emit its base. -/
@[expose] def concatRecGenerator {k : ℕ} {S A : Type}
    (P : MultiTapeTM k Bool S) (G : MultiTapeTM k Bool A) (C Q : Fin k) :=
  seq (concatLoop P C Q) (seq (const [] Q) G)

/-- Concatenation recursion realizes the semantic constructor from its indexed step and base.
The step receives the suffix after the current digit. No accumulated result is passed to it. -/
theorem concatRecGenerator_emitsIn {k n : ℕ} {S A : Type}
    {P : MultiTapeTM k Bool S} {G : MultiTapeTM k Bool A}
    (C Q : Fin k) (hCQ : C ≠ Q)
    {Pre PreG : List Bool → (Fin k → List Bool) → Prop}
    {W WG : List Bool → (Fin k → List Bool) → List Bool} {T TG B N : ℕ → ℕ}
    (hP : EmitsIn P Pre (fun _ σ ↦ σ) W T B)
    (hG : EmitsIn G PreG (fun _ σ ↦ σ) WG TG B)
    (Pre₀ : List Bool → (Fin k → List Bool) → Prop)
    (U : List Bool → (Fin k → List Bool) → List Bool)
    (X : List Bool → (Fin k → List Bool) → Fin n → List Bool)
    (g : BellantoniCook.Sem (n, 0)) (h : Bool → BellantoniCook.Sem (n + 1, 0))
    (hlen : ∀ input σ, Pre₀ input σ → (U input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n)
    (hcall : ∀ input σ, Pre₀ input σ → ∀ j < (U input σ).length,
      Pre input (concatVal σ C Q (U input σ).length j) ∧
        W input (concatVal σ C Q (U input σ).length j) =
          [(h ((U input σ)[j]?.getD false)
            (Fin.cons ((U input σ).drop (j + 1)) (X input σ)) Fin.elim0).headD false])
    (hbase : ∀ input σ, Pre₀ input σ →
      PreG input (Function.update (Function.update σ C []) Q []) ∧
        WG input (Function.update (Function.update σ C []) Q []) = g (X input σ) Fin.elim0) :
    EmitsIn (concatRecGenerator P G C Q)
      (fun input σ ↦ Pre₀ input σ ∧ σ C = counterWord (U input σ).length ∧ σ Q = [])
      (fun _ σ ↦ Function.update (Function.update σ C []) Q [])
      (fun input σ ↦ concatRec g h (U input σ) (X input σ) Fin.elim0)
      (fun n ↦ (N n * (T n + ((2 * B n + 4) + (2 * B n + 6)) + 1) + 1) +
        ((4 * B n + 9) + TG n)) B := by
  have hdlen (input σ) : (concatDigits h (U input σ) (X input σ)).length =
      (U input σ).length := length_concatDigits ..
  have hl := concatLoop_emitsIn C Q hCQ hP Pre₀
    (fun input σ ↦ concatDigits h (U input σ) (X input σ))
    (fun input σ hp ↦ (hdlen input σ) ▸ hlen input σ hp) hsize (by
      intro input σ hp j hj
      rw [hdlen] at hj ⊢
      refine ⟨(hcall input σ hp j hj).1, ?_⟩
      rw [(hcall input σ hp j hj).2]
      simp only [getElem?_concatDigits, List.getElem?_eq_getElem hj,
        Option.getD_some, Option.map_some])
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] Q (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hf (input σ) : Function.update
      (concatVal σ C Q (U input σ).length (U input σ).length) Q [] =
        Function.update (Function.update σ C []) Q [] := by
    simp only [concatVal, Function.update_idem, Nat.sub_self]
    rfl
  have hs := (hl.seqEmitsIn (hc.seqEmitsIn hG)).mono_pre
    (Pre' := fun input σ ↦ Pre₀ input σ ∧ σ C = counterWord (U input σ).length ∧ σ Q = [])
    (by
      intro input σ _ hp
      refine ⟨?_, trivial, ?_⟩
      · simpa only [hdlen] using hp
      · simpa only [hdlen, hf] using (hbase input σ hp.1).1)
  refine (hs.congr (fun input σ _ ↦ by simpa only [hdlen] using hf input σ)).congr_output ?_
  intro input σ hp
  simp only [hdlen, hf, (hbase input σ hp.1).2,
    concatRec_eq_concatDigits]

end

end Geb.Oitavem.Machine
