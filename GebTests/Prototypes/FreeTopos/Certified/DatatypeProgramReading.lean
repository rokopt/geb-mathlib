/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.ArrowValue
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramTheory
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramTheory -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, read in the topos of types and functional relations

The soundness of a whole program of the datatype language's stage-1 compiler, read in the topos
of types and functional relations: at every value of the type of lists of forms, where each
hypothesis of the soundness holds, its conclusion holds. A formula in the context of the forms
is read as a predicate of that type's values ({lit}`Reads`): it compiles to an arrow into the
subobject classifier, whose value there, with every definition unfolded, is a functional
relation into the propositions, and the predicate holds of the values it relates to the true
proposition. The hypotheses and the conclusion are read so, each as its own truth; the
statement follows from the soundness as one formula, true there
({lit}`DatatypeProgramTheory.programClosed_unfolded`), whose implications represent Lean's
({name}`Geb.FreeTopos.Internal.repC_imps`).

## Main definitions

* {lit}`Reads` — a formula in a context reads as a predicate of the context's values.

## Main statements

* {lit}`program_reads` — where the hypotheses of a whole program's soundness hold of a value,
  its conclusion does.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, certificate, functional relation, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open PartialHorn (Tree)
open Sorts SetRel

/-- A formula in a context reads as a predicate of the context's values: it compiles in the
context's standard environment to an arrow into the subobject classifier whose value in the
topos of types and functional relations, with every definition unfolded, relates to the true
proposition the values of which the predicate holds. -/
def Reads (G : Internal.Globals) (cds : List PartialHorn.Defn) (Γ : List Tree) {A : Type}
    (t : Internal.Term) (H : A → Prop) : Prop :=
  ∃ (f : Tree) (φ : FunRel A Prop),
    Internal.compile G 0 t (Internal.ctxObj Γ) (Internal.stdEnv Γ) = some (f, omega) ∧
      ArrVal [] (unfoldTerm sig cds f) φ ∧ H = fun es ↦ es ~[φ.rel] True

/-- A list each of whose elements is related to something is related, element by element, to a
list. -/
theorem exists_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ l : List α, (∀ x ∈ l, ∃ y, R x y) → ∃ l', List.Forall₂ R l l' :=
  List.rec (fun _ ↦ ⟨[], .nil⟩) fun x _ ih h ↦
    let ⟨y, hy⟩ := h x List.mem_cons_self
    let ⟨l', hl'⟩ := ih fun z hz ↦ h z (List.mem_cons_of_mem _ hz)
    ⟨y :: l', .cons hy hl'⟩

/-- The value of the type of lists of trees, unfolded: the lists of rose trees of lists of
bits. -/
theorem objVal_forms {cds : List PartialHorn.Defn} :
    ObjVal [] (unfoldTerm sig cds (list Translation.treeTy))
      (List (RoseTree (List (Unit ⊕ Unit)))) := by
  simp (disch := decide) only [Translation.treeTy, Translation.bitsTy, Translation.bitTy, list,
    lrose, coprod, one, Internal.unfold_op', List.map_cons, List.map_nil]
  exact eval_list (eval_lrose (eval_list (eval_coprod eval_one eval_one)))

universe v

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)

include h

/-- The soundness of a whole program of the datatype language's stage-1 compiler, read in the
topos of types and functional relations: the hypotheses and the conclusion of the soundness
({name}`programFormsThm`) read as predicates of the lists of forms ({name}`Reads`), and at
every such list of which the hypotheses hold the conclusion holds. -/
theorem program_reads {a : Internal.Thm}
    (ha : programFormsThm PST.1 PST.2.1 PST.2.2 = some a) :
    ∃ (cds : List PartialHorn.Defn) (A : Type) (Hs : List (A → Prop)) (C : A → Prop),
      Internal.compileDefs PST.1.G = some cds ∧
      ObjVal [] (unfoldTerm sig cds (Internal.ctxObj a.ctx)) A ∧
      List.Forall₂ (Reads PST.1.G cds a.ctx) a.hyps Hs ∧ Reads PST.1.G cds a.ctx a.concl C ∧
      ∀ es : A, Hs.foldr (fun (H : A → Prop) (acc : Prop) ↦ H es → acc) (C es) := by
  obtain ⟨cds, hc, hbase, hok, hwf⟩ := Internal.Globals.of_accepted (DatatypeAccepted.accepted h)
  have hbase' : PST.1.G.base = sig.length + ([] : List PartialHorn.Defn).length := by
    simpa using hbase
  have hlog := DatatypeAccepted.hasLogic h
  -- the statement's shape: no object variables, the context of the forms
  have hshape : a.arity = 0 ∧ a.ctx = [list Translation.treeTy] := by
    have ha' := ha
    simp only [programFormsThm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at ha'
    obtain ⟨_, -, rfl⟩ := ha'
    exact ⟨rfl, rfl⟩
  -- the hypotheses and the conclusion are formulas, by the validity in the one-point model
  obtain ⟨hctx, hhyps, hcon, -⟩ := DatatypeProgramSound.programForms_valid h
    ⟨[], cds, PartialHorn.pointModel (ext cds).sig,
      Internal.isModel_point_ext (pre := []) hwf, hc, hbase',
      Internal.devInv_init (Internal.isModel_point_ext (pre := []) hwf) hbase' hok hc
        (Internal.Globals.Le.refl _) hc⟩ ha
  have hX : ObjVal [] (unfoldTerm sig cds (Internal.ctxObj a.ctx))
      (List (RoseTree (List (Unit ⊕ Unit)))) := by
    rw [hshape.2, Internal.ctxObj_single]
    exact objVal_forms
  have hΩ : ObjVal [] (unfoldTerm sig cds omega) Prop := Internal.objVal_omega
  -- a formula in the context reads as its truth
  have atom : ∀ t : Internal.Term, Internal.typeIn PST.1.G a.arity a.ctx t = some omega →
      ∃ H : List (RoseTree (List (Unit ⊕ Unit))) → Prop, Reads PST.1.G cds a.ctx t H := by
    intro t ht
    obtain ⟨⟨f, ty⟩, hf, hty⟩ := Option.map_eq_some_iff.mp (Internal.typeIn_eq_some.mp ht)
    obtain rfl : ty = omega := hty
    obtain ⟨h₁, h₂⟩ := Internal.hom_unfoldAll_of_compile (pre := []) hbase' hok hc hwf hctx hf
      relTopos.model relTopos.isModel
    rw [unfoldAll_eq] at h₁ h₂
    have hd := h₁ [] (by rw [hshape.1]; rfl) (fun _ hh ↦ nomatch hh)
    have hcd := h₂ [] (by rw [hshape.1]; rfl) (fun _ hh ↦ nomatch hh)
    have hdom : unfoldTerm sig cds (FreeTopos.dom f) = FreeTopos.dom (unfoldTerm sig cds f) := by
      simp (disch := decide) only [FreeTopos.dom, Internal.unfold_op', List.map_cons,
        List.map_nil]
    have hcod : unfoldTerm sig cds (FreeTopos.cod f) = FreeTopos.cod (unfoldTerm sig cds f) := by
      simp (disch := decide) only [FreeTopos.cod, Internal.unfold_op', List.map_cons,
        List.map_nil]
    obtain ⟨φ, hφ⟩ := exists_arrVal_of_dom_cod (hdom ▸ hd) (hcod ▸ hcd) hX hΩ
    exact ⟨_, f, φ, hshape.1 ▸ hf, hφ, rfl⟩
  obtain ⟨Hs, hHs⟩ := exists_forall₂ a.hyps fun t ht ↦ atom t (hhyps t ht)
  obtain ⟨C, hC⟩ := atom a.concl hcon
  refine ⟨cds, _, Hs, C, hc, hX, hHs, hC, ?_⟩
  -- the soundness as one formula, true in the topos of types and functional relations
  have hcl : programClosedThm PST.1 PST.2.1 PST.2.2 =
      some ⟨0, a.ctx, [], a.hyps.foldr (Internal.Logic.imp PST.1.o) a.concl⟩ := by
    simp [programClosedThm, ha]
  obtain ⟨cds', Cc, hc', hCc, hM⟩ := DatatypeProgramTheory.programClosed_unfolded h hcl
  obtain rfl : cds = cds' := Option.some.inj (hc.symm.trans hc')
  have hv := hM relTopos.model relTopos.isModel
  -- implication's definition and its representation
  have hk : PST.1.G.defs[PST.1.o + 2]? = some (.language ⟨0, [omega, omega], omega,
      Internal.Term.eq (Internal.Logic.conj PST.1.o (Internal.Term.var 1) (Internal.Term.var 0))
        (Internal.Term.var 1)⟩) :=
    hlog 2 _ rfl
  obtain ⟨ft, hdt⟩ := Internal.compiled_language hc (hlog 0 _ rfl)
  obtain ⟨fc, hdc⟩ := Internal.compiled_language hc (hlog 1 _ rfl)
  obtain ⟨fi, hdi⟩ := Internal.compiled_language hc hk
  have hfi := Internal.represents_imp hbase hc hwf hlog hdt hdc hdi
  -- each formula represents its truth, and the implications Lean's
  have rep : ∀ {t : Internal.Term} {H : List (RoseTree (List (Unit ⊕ Unit))) → Prop},
      Reads PST.1.G cds a.ctx t H →
        Internal.RepC PST.1.G 0 cds [] t (Internal.ctxObj a.ctx) (Internal.stdEnv a.ctx) omega
          (fun x y : List (RoseTree (List (Unit ⊕ Unit))) ↦ x = y) Rep.prop H := by
    rintro t H ⟨f, φ, hf, hφ, rfl⟩
    exact ⟨f, hf, represents_truth hφ⟩
  obtain ⟨f', hf', hF'⟩ := Internal.repC_imps (n := 0) (ρ := []) hbase hk hwf hdi hfi (rep hC)
    (hHs.imp fun _ _ hr ↦ rep hr)
  obtain rfl : f' = Cc := by
    have e := Option.some.inj (hf'.symm.trans hCc)
    exact (Prod.mk.inj e).1
  exact fun es ↦ Internal.holds_of_represents hv hX hF' rfl

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading

end
