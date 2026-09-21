/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Machine.Counter
public import Geb.Prototypes.Computability.Oitavem.Machine.Reader

set_option doc.verso true in
/-!
# Readers for segments of virtual words

A segment reader adds a saved offset to the caller's query before invoking the
underlying word reader. The offset and caller query survive; two temporary counters
are cleared on return. Neither the word nor its segment is stored on a work tape.

## Main definitions

* {lit}`dropReader` reads the suffix after a saved number of list positions.
* {lit}`iterPredGenerator` reads two lengths and streams their iterated predecessor.

## Main statements

* {lit}`dropReader_readsAt` gives the segment's digit contract, including the first
  out-of-range query and preservation of the source environment.
* {lit}`iterPredGenerator_emitsIn` also handles offsets beyond the source length.

## Implementation notes

The offset lies within the source word. Consequently every permitted segment query
translates to a permitted source query, and its binary size is bounded by the source
length. The contracts inherit CSLib's {lit}`Classical.choice` dependency.

## Tags

Turing machine, logarithmic space, word reader, segment, recursion
-/

set_option doc.verso true

namespace Geb.Oitavem.Machine

open Turing MultiTapeTM
open Geb.SizeBounded.Machine
open Geb.SizeBounded.Logspace
open Geb.SizeBounded.Logspace.Machine

public section

/-- Read through a saved offset. The layout is offset, caller query, child query,
addition scratch, and result. The child reads its query from the third register. -/
@[expose] def dropReader {k : ℕ} {S : Type} (P : MultiTapeTM k Bool S) (r : Fin 5 → Fin k) :=
  seq (seq (copy (r 1) (r 2)) (seq (copy (r 0) (r 3)) (addCounter (r 2) (r 3))))
    (seq P (const [] (r 2)))

/-- Time for a segment query, including copying, addition, and scratch cleanup. -/
@[expose] def dropReaderTime (T B N : ℕ → ℕ) (n : ℕ) : ℕ :=
  (5 * B n + 12) + ((5 * B n + 12) + (N n * (4 * B n + 11) + 1)) +
    (T n + (4 * B n + 9))

/-- Segment queries preserve the offset, caller query, and all source registers.
Both temporary counters are initialized to the contents restored by each call. -/
theorem dropReader_readsAt {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (r : Fin 5 → Fin k) (hr : Function.Injective r)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : ReadsAt P (r 2) (r 4) Pre W T B)
    (hpre : ∀ input σ a c, Pre input σ →
      Pre input (Function.update (Function.update σ (r 2) a) (r 3) c))
    (hword : ∀ input σ a c,
      W input (Function.update (Function.update σ (r 2) a) (r 3) c) = W input σ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) :
    ReadsAt (dropReader P r) (r 1) (r 4)
      (fun input σ ↦ Pre input σ ∧ σ (r 2) = [] ∧ σ (r 3) = [] ∧
        ∃ d, σ (r 0) = counterWord d ∧ d ≤ (W input σ).length)
      (fun input σ ↦ (W input σ).drop (counterValue (σ (r 0))))
      (dropReaderTime T B N) B := by
  have h23 : r 2 ≠ r 3 := hr.ne (by decide)
  have hcopy (i j : Fin 5) (hij : i ≠ j) :=
    Transforms.toIn_of (fun n ↦ copy_transforms (r i) (r j) (hr.ne hij) (B n))
      (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (hB (r i)))
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] (r 2) (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hi := (hcopy 1 2 (by decide)).seq
    ((hcopy 0 3 (by decide)).seq (addCounter_transformsIn (r 2) (r 3) h23 N B))
  let Invariant := fun (input : List Bool) (σ : Fin k → List Bool) ↦
    (Pre input σ ∧ σ (r 2) = [] ∧ σ (r 3) = [] ∧
      ∃ d, σ (r 0) = counterWord d ∧ d ≤ (W input σ).length) ∧
    ∃ q, σ (r 1) = counterWord q ∧
      q ≤ ((W input σ).drop (counterValue (σ (r 0)))).length
  have hs : TransformsIn (seq (seq (copy (r 1) (r 2))
      (seq (copy (r 0) (r 3)) (addCounter (r 2) (r 3)))) (seq P (const [] (r 2))))
      Invariant
      (fun input σ ↦ Function.update (Function.update
        (Function.update (Function.update
          σ (r 2) (counterWord (counterValue (σ (r 1)) + counterValue (σ (r 0))))) (r 3) [])
        (r 4) ((W input σ)[counterValue (σ (r 1)) + counterValue (σ (r 0))]?).toList) (r 2) [])
      (fun n ↦ (5 * B n + 12) + ((5 * B n + 12) + (N n * (4 * B n + 11) + 1)) +
        (T n + (4 * B n + 9))) B := by
    refine ((hi.seq (hP.seq hc)).mono_pre ?_).congr ?_
    · intro input σ _ hp
      obtain ⟨⟨hp, hA, hC, d, hd, hdW⟩, q, hq, hqW⟩ := hp
      rw [hd, counterValue_counterWord, List.length_drop] at hqW
      have hqd : q + d ≤ (W input σ).length := by omega
      refine ⟨⟨trivial, trivial, ?_⟩, ?_, trivial⟩
      · refine ⟨q, d, ?_, ?_, hdW.trans (hlen input σ hp),
          (size_le_size (hqd.trans (hlen input σ hp))).trans (hsize _)⟩ <;>
          simp [hr.eq_iff, hq, hd]
      · simp only [Function.update_of_ne (hr.ne (by decide : (0 : Fin 5) ≠ 2)),
          Function.update_of_ne h23, Function.update_self, hq, hd, counterValue_counterWord]
        rw [Function.update_comm h23, Function.update_idem,
          Function.update_comm h23.symm, Function.update_idem]
        exact ⟨hpre input σ _ _ hp, q + d, by simp,
          by simpa only [hword] using hqd⟩
    · intro input σ _
      simp only [Function.update_of_ne (hr.ne (by decide : (0 : Fin 5) ≠ 2)),
        Function.update_of_ne h23, Function.update_self, counterValue_counterWord]
      rw [Function.update_comm h23, Function.update_idem,
        Function.update_comm h23.symm, Function.update_idem, hword]
  refine hs.congr ?_
  intro input σ hp
  obtain ⟨⟨_, hA, hC, _⟩, _⟩ := hp
  rw [List.getElem?_drop, Nat.add_comm (counterValue (σ (r 0)))]
  funext i
  by_cases hi2 : i = r 2
  · subst i
    simp [hr.eq_iff, hA]
  · by_cases hi3 : i = r 3
    · subst i
      simp [hr.eq_iff, hC]
    · simp [Function.update_apply, hi2, hi3]

/-- Stream a suffix after clamping its saved offset to the source length.
The separate length register is preserved; the five reader ports are cleared. -/
@[expose] def dropGenerator {k : ℕ} {S : Type}
    (P : MultiTapeTM k Bool S) (r : Fin 5 → Fin k) (L : Fin k) :=
  seq (minCounter (r 0) L (r 3))
    (seq (emitReaderClean (dropReader P r) (r 1) (r 4)) (const [] (r 0)))

/-- Time for a suffix generator, including offset clamping and port cleanup. -/
@[expose] def dropGeneratorTime (T B N : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * ((5 * B n + 12) + (N n * (4 * B n + 13) + 1)) +
    ((4 * B n + 9 + dropReaderTime T B N n +
      (N n * (dropReaderTime T B N n + 2 * B n + 6) + 1) + (4 * B n + 9)) +
      (4 * B n + 9))

/-- Iterated string predecessor needs only its iteration count and a source reader.
Offsets beyond the end yield the empty word. The source environment is preserved. -/
theorem dropGenerator_emitsIn {k : ℕ} {S : Type} {P : MultiTapeTM k Bool S}
    (r : Fin 5 → Fin k) (hr : Function.Injective r) (L : Fin k)
    (hL : ∀ j, L ≠ r j)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {W : List Bool → (Fin k → List Bool) → List Bool} {T B N : ℕ → ℕ}
    (hP : ReadsAt P (r 2) (r 4) Pre W T B)
    (hpre : ∀ input σ j v, Pre input σ → Pre input (Function.update σ (r j) v))
    (hword : ∀ input σ j v, W input (Function.update σ (r j) v) = W input σ)
    (hlen : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (dropGenerator P r L)
      (fun input σ ↦ Pre input σ ∧ σ (r 2) = [] ∧
        (∃ d, σ (r 0) = counterWord d ∧ d ≤ N input.length) ∧
        σ L = counterWord (W input σ).length)
      (fun _ σ ↦ Function.update (Function.update
        (Function.update (Function.update σ (r 3) []) (r 1) []) (r 4) []) (r 0) [])
      (fun input σ ↦ (W input σ).drop (counterValue (σ (r 0))))
      (dropGeneratorTime T B N) B := by
  have hd := dropReader_readsAt r hr hP
    (fun input σ a c hp ↦ hpre input _ 3 c (hpre input σ 2 a hp))
    (fun input σ a c ↦ by rw [hword, hword]) hlen hsize
  have he := emitReaderClean_emitsIn (r 1) (r 4) (hr.ne (by decide)) hd
    (by
      intro input σ q v hp
      obtain ⟨hp, h2, h3, d, hd, hdn⟩ := hp
      refine ⟨hpre input _ 4 v (hpre input σ 1 q hp), ?_, ?_, d, ?_, ?_⟩
      · simpa [hr.eq_iff] using h2
      · simpa [hr.eq_iff] using h3
      · simpa [hr.eq_iff] using hd
      · simpa only [hword] using hdn)
    (by
      intro input σ q v
      simp only [hword, Function.update_of_ne (hr.ne (by decide : (0 : Fin 5) ≠ 4)),
        Function.update_of_ne (hr.ne (by decide : (0 : Fin 5) ≠ 1))])
    (by
      intro input σ hp
      rw [List.length_drop]
      exact (Nat.sub_le ..).trans (hlen input σ hp.1)) hsize hB1
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] (r 0) (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hs := ((minCounter_transformsIn (r 0) L (r 3) (hL 0).symm
      (hr.ne (by decide)) (hL 3) N B).seqEmitsIn (he.seqTransformsIn hc)).mono_pre
    (Pre' := fun input σ ↦ Pre input σ ∧ σ (r 2) = [] ∧
      (∃ d, σ (r 0) = counterWord d ∧ d ≤ N input.length) ∧
      σ L = counterWord (W input σ).length) (by
    intro input σ _ hp
    obtain ⟨hp, h2, ⟨d, hd, hdn⟩, hl⟩ := hp
    refine ⟨⟨d, (W input σ).length, hd, hl, hdn, hlen input σ hp⟩, ?_, trivial⟩
    refine ⟨hpre input _ 3 [] (hpre input σ 0 _ hp), ?_, Function.update_self ..,
      min d (W input σ).length, ?_, ?_⟩
    · simpa [hr.eq_iff] using h2
    · simp [hr.eq_iff, hd, hl, counterValue_counterWord]
    · simpa only [hword] using (min_le_right d (W input σ).length))
  refine (hs.congr ?_).congr_output ?_
  · intro input σ _
    funext i
    by_cases hi : i = r 0
    · subst i
      simp
    · simp only [Function.update_apply, hi, ite_false]
  · intro input σ hp
    obtain ⟨_, _, ⟨d, hd, _⟩, hl⟩ := hp
    simp only [hword, Function.update_of_ne (hr.ne (by decide : (0 : Fin 5) ≠ 3)),
      Function.update_self, hd, hl, counterValue_counterWord]
    exact List.drop_eq_drop_min.symm

/-- Read both argument lengths, stream the iterated predecessor, and clear its ports. -/
@[expose] def iterPredGenerator {k : ℕ} {S₁ S₂ S : Type}
    (P₁ : MultiTapeTM k Bool S₁) (P₂ : MultiTapeTM k Bool S₂)
    (P : MultiTapeTM k Bool S) (r : Fin 5 → Fin k) (L : Fin k) :=
  seq P₁ (seq P₂ (seq (dropGenerator P r L) (const [] L)))

/-- Iterated predecessor has finite control whenever its readers do. -/
theorem iterPredGenerator_finite {k : ℕ} {S₁ S₂ S : Type}
    [Finite S₁] [Finite S₂] [Finite S]
    (P₁ : MultiTapeTM k Bool S₁) (P₂ : MultiTapeTM k Bool S₂)
    (P : MultiTapeTM k Bool S) (r : Fin 5 → Fin k) (L : Fin k) :
    Finite (StateOf (iterPredGenerator P₁ P₂ P r L)) := by
  let := Fintype.ofFinite S₁
  let := Fintype.ofFinite S₂
  let := Fintype.ofFinite S
  let : Fintype (StateOf (dropReader P r)) := by
    unfold dropReader
    infer_instance
  let : Fintype (StateOf (emitReaderClean (dropReader P r) (r 1) (r 4))) := by
    unfold emitReaderClean emitReader emitReaderLoop
    infer_instance
  let : Fintype (StateOf (dropGenerator P r L)) := by
    unfold dropGenerator minCounter
    infer_instance
  unfold iterPredGenerator
  infer_instance

/-- Iterated predecessor composes two length readers with a digit reader.
The represented arguments remain virtual throughout execution. -/
theorem iterPredGenerator_emitsIn {k : ℕ} {S₁ S₂ S : Type}
    {P₁ : MultiTapeTM k Bool S₁} {P₂ : MultiTapeTM k Bool S₂}
    {P : MultiTapeTM k Bool S}
    (r : Fin 5 → Fin k) (hr : Function.Injective r) (L : Fin k) (hL : ∀ j, L ≠ r j)
    {Pre : List Bool → (Fin k → List Bool) → Prop}
    {V W : List Bool → (Fin k → List Bool) → List Bool} {T₁ T₂ T B N : ℕ → ℕ}
    (hP₁ : ReadsLength P₁ (r 0) Pre V T₁ B) (hP₂ : ReadsLength P₂ L Pre W T₂ B)
    (hP : ReadsAt P (r 2) (r 4) Pre W T B)
    (hpre : ∀ input σ j v, Pre input σ → Pre input (Function.update σ (r j) v))
    (hpreL : ∀ input σ v, Pre input σ → Pre input (Function.update σ L v))
    (hword : ∀ input σ j v, W input (Function.update σ (r j) v) = W input σ)
    (hwordL : ∀ input σ v, W input (Function.update σ L v) = W input σ)
    (hlenV : ∀ input σ, Pre input σ → (V input σ).length ≤ N input.length)
    (hlenW : ∀ input σ, Pre input σ → (W input σ).length ≤ N input.length)
    (hsize : ∀ n, (N n).size ≤ B n) (hB1 : ∀ n, 1 ≤ B n) :
    EmitsIn (iterPredGenerator P₁ P₂ P r L)
      (fun input σ ↦ Pre input σ ∧ σ (r 2) = [])
      (fun _ σ ↦ Function.update (Function.update (Function.update
        (Function.update (Function.update σ (r 3) []) (r 1) []) (r 4) []) (r 0) []) L [])
      (fun input σ ↦ (W input σ).drop (V input σ).length)
      (fun n ↦ T₁ n + (T₂ n + (dropGeneratorTime T B N n + (4 * B n + 9)))) B := by
  have hc := Transforms.toIn_of (fun n ↦ const_transforms [] L (B n))
    (fun _ _ ↦ True) (fun _ _ hB _ ↦ hB.update (Nat.zero_le _))
  have hd := dropGenerator_emitsIn r hr L hL hP hpre hword hlenW hsize hB1
  have hs := (hP₁.seqEmitsIn (hP₂.seqEmitsIn (hd.seqTransformsIn hc))).mono_pre
    (Pre' := fun input σ ↦ Pre input σ ∧ σ (r 2) = []) (by
    intro input σ _ hp
    refine ⟨hp.1, hpre input σ 0 _ hp.1, ?_, trivial⟩
    refine ⟨hpreL input _ _ (hpre input σ 0 _ hp.1), ?_,
      ⟨(V input σ).length, ?_, hlenV input σ hp.1⟩, ?_⟩
    · simpa [Function.update_of_ne (hL 2).symm, hr.eq_iff] using hp.2
    · simp [Function.update_of_ne (hL 0).symm]
    · simp only [Function.update_self, hwordL])
  refine (hs.congr ?_).congr_output ?_
  · intro input σ _
    funext i
    by_cases hiL : i = L
    · subst i
      simp
    · by_cases hi0 : i = r 0
      · subst i
        simp [hiL]
      · simp only [Function.update_apply, hiL, hi0, ite_false]
  · intro input σ _
    simp only [hwordL, hword, Function.update_of_ne (hL 0).symm,
      Function.update_self, counterValue_counterWord]

end

end Geb.Oitavem.Machine
