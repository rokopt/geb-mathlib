/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypePasses
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypePasses -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, at the passes the kernel evaluates

The soundness of a whole program of the datatype language's stage-1 compiler, read in the topos
of types and functional relations ({lit}`DatatypeProgramReading.program_reads`), has among its
hypotheses the formulas of the passes' successes. Those formulas represent the passes'
successes as the values of the globals the kernel loads compute them
({lit}`DatatypePasses.passes_rep`), so their readings hold of a list of trees of bitstrings
exactly when the passes succeed on the kernel's list of trees it represents
({lit}`DatatypeProgramReading.Reads.iff_of_repC`). The soundness then reads: where the
compilers the kernel loads succeed on a program's forms, and the remaining hypotheses hold of
the forms' representation, the conclusion holds of it.

## Main statements

* {lit}`hyps_eq` — the formulas of the passes' successes are the first of the soundness's
  hypotheses.
* {lit}`program_passes` — where the loaded compilers' passes succeed on a program's forms and
  the remaining hypotheses hold, the soundness's conclusion holds.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramPasses

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading
open Kernel (tT tList)
open Sorts

/-- Where one list is related element by element to two others, and a property of an element
of the third gives one of the element of the second related to the same element, the property
of every element of the third gives that of every element of the second. -/
theorem forall_of_forall₂ {α β γ : Type} {R : α → β → Prop} {R' : α → γ → Prop} {P : β → Prop}
    {Q : γ → Prop} (hPQ : ∀ x y z, R x y → R' x z → Q z → P y) {l : List α} {l₁ : List β}
    (h : List.Forall₂ R l l₁) :
    ∀ l₂ : List γ, List.Forall₂ R' l l₂ → (∀ z ∈ l₂, Q z) → ∀ y ∈ l₁, P y :=
  h.rec (motive := fun (l : List α) (l₁ : List β) _ ↦
      ∀ l₂ : List γ, List.Forall₂ R' l l₂ → (∀ z ∈ l₂, Q z) → ∀ y ∈ l₁, P y)
    (fun _ _ _ _ hy ↦ nomatch hy)
    fun hxy _ ih l₂ h' hQ y' hy' ↦ by
      cases h' with
      | cons hxz h'' =>
        rcases List.mem_cons.mp hy' with rfl | hy'
        · exact hPQ _ _ _ hxy hxz (hQ _ List.mem_cons_self)
        · exact ih _ h'' (fun z hz ↦ hQ z (List.mem_cons_of_mem _ hz)) y' hy'

/-- A chain of implications from properties that all hold gives its conclusion. -/
theorem of_foldr_imp {α : Type} {P : α → Prop} {Q : Prop} :
    ∀ l : List α, (∀ x ∈ l, P x) → l.foldr (fun x acc ↦ P x → acc) Q → Q :=
  List.rec (fun _ h ↦ h) fun x _ ih hP h ↦
    ih (fun y hy ↦ hP y (List.mem_cons_of_mem _ hy)) (h (hP x List.mem_cons_self))

/-- The formulas of the passes' successes ({name}`passHyps`) are the first of the hypotheses
of the soundness of a whole program ({name}`programFormsThm`), in the context of the forms. -/
theorem hyps_eq {P : Prog} {S : Defs} {T : Defs3} {a : Internal.Thm}
    (ha : programFormsThm P S T = some a) :
    ∃ hs rest, passHyps P = some hs ∧ hs.length = 5 ∧ a.hyps = hs ++ rest ∧
      a.ctx = [list treeTy] := by
  simp only [programFormsThm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨⟨hs, concl⟩, hpp, rfl⟩ := ha
  simp only [programParts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hpp
  obtain ⟨childT, hch, rfl, rfl⟩ := hpp
  refine ⟨_, _, ?_, rfl, List.append_assoc _ _ _, rfl⟩
  simp only [passHyps, hch, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)

include h

/-- The soundness of a whole program of the datatype language's stage-1 compiler, at the passes
the kernel evaluates: the hypotheses after the passes' successes and the conclusion read as
predicates of the lists of trees of bitstrings ({name}`Reads`), and at every such list that
represents a kernel list of forms on which the passes of the loaded compilers succeed
({name}`PassFns.passes`), where the remaining hypotheses hold, the conclusion holds. -/
theorem program_passes {a : Internal.Thm}
    (ha : programFormsThm PST.1 PST.2.1 PST.2.2 = some a) (L : Translated PST) {f : PassFns}
    (hf : f.Loaded L.Gk PST.1.idx) :
    ∃ (Hs : List (Forms → Prop)) (C : Forms → Prop),
      List.Forall₂ (Reads PST.1.G (L.cds₀ ++ L.ext) a.ctx) (a.hyps.drop 5) Hs ∧
      Reads PST.1.G (L.cds₀ ++ L.ext) a.ctx a.concl C ∧
      ∀ (ks : List Kernel.Tree) (es : Forms), KRel (tList tT) ks es → (∀ p ∈ f.passes, p ks) →
        Hs.foldr (fun (H : Forms → Prop) (acc : Prop) ↦ H es → acc) (C es) := by
  obtain ⟨cds, Hs, C, hc, hHs, hC, hall⟩ := program_reads h ha
  obtain rfl : cds = L.cds₀ ++ L.ext := Option.some.inj (hc.symm.trans L.ctx.compiles)
  obtain ⟨hs, rest, hp, hlen, hhyps, hctx⟩ := hyps_eq ha
  have hrep := DatatypePasses.passes_rep L h hf hp
  refine ⟨Hs.drop 5, C, List.forall₂_drop 5 hHs, hC, fun ks es hke hpass ↦ ?_⟩
  -- the readings of the passes' formulas hold of the representation
  have h5 : List.Forall₂ (Reads PST.1.G (L.cds₀ ++ L.ext) [list treeTy]) hs (Hs.take 5) := by
    have ht := List.forall₂_take 5 hHs
    rwa [hhyps, List.take_left' hlen, hctx] at ht
  have hfirst : ∀ H ∈ Hs.take 5, H es :=
    forall_of_forall₂ (P := fun H : Forms → Prop ↦ H es)
      (Q := fun F : List Kernel.Tree → Prop ↦ F ks)
      (fun _ _ _ hr hc' hF ↦ (hr.iff_of_repC hc' hke).mpr hF) h5 _ hrep hpass
  have hes := hall es
  rw [← List.take_append_drop 5 Hs, List.foldr_append] at hes
  exact of_foldr_imp (P := fun H : Forms → Prop ↦ H es) _ hfirst hes

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramPasses

end
