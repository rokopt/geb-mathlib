/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramConclusion
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, as a statement of Lean

The soundness of a whole program of the datatype language's stage-1 compiler, concluded in Lean
({lit}`DatatypeProgramConclusion.program_sound`), still reads its hypotheses after the passes'
successes as predicates of the trees of bitstrings. Each of those hypotheses represents a
statement of Lean about the values of the globals the kernel loads
({lit}`DatatypeHypotheses.plain_rep`, {lit}`DatatypeHypotheses.markers_rep`,
{lit}`DatatypeHypotheses.static_rep`, {lit}`DatatypeHypotheses.forms_rep`), and every kernel
list of trees is represented by a list of trees of bitstrings. The soundness is therefore a
statement about the kernel's lists of trees alone: where the loaded compilers' passes succeed
on a program's forms and what the soundness assumes of the program holds, each definition the
typing gives a type evaluates to a value related at the type, and each datatype's recognizer
decides membership.

## Main statements

* {lit}`hyps_rest` — the hypotheses of the soundness after the passes' successes.
* {lit}`program_sound_explicit` — the soundness of a whole program, of the kernel's lists of
  trees.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, evaluator, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramExplicit

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (PassFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements (EvalFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation
open GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion
open GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramPasses
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramConclusion
open Internal (RepC objVal_list)
open Kernel (tT tList)
open Sorts

/-- The hypotheses of the soundness of a whole program ({name}`programFormsThm`) after the
passes' successes: that the definitions' bodies are source forms, what the soundness assumes of
the markers among the kernel forms, of the markers' names and constructors and of the
numerals, and what it assumes of each form; the statement's context is that of the forms. -/
theorem hyps_rest {P : Prog} {S : Defs} {T : Defs3} {a : Internal.Thm}
    (ha : programFormsThm P S T = some a) :
    a.hyps.drop 5 = [plainTop P (v 0), S.allL (markerPred P (msT P (v 0))) (fsT P (v 0)),
      staticT P (msT P (v 0))] ++ formsOk P S (v 0) ∧ a.ctx = [list treeTy] := by
  simp only [programFormsThm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨⟨hs, concl⟩, hpp, rfl⟩ := ha
  simp only [programParts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hpp
  obtain ⟨childT, -, rfl, rfl⟩ := hpp
  exact ⟨rfl, rfl⟩

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)

include h

/-- The soundness of a whole program of the datatype language's stage-1 compiler, of the
kernel's lists of trees: at every list of forms on which the passes of the loaded compilers
succeed ({name}`PassFns.passes`), whose definitions' bodies are source forms
({name}`HypFns.PlainOk`), whose markers are those their datatypes' atoms find
({name}`HypFns.MarkersOk`) and are named and constructed as the soundness assumes, with the
numerals' digits read back and fixed ({name}`HypFns.StaticOk`), and whose forms declare no
name of the implementation's ({name}`HypFns.FormsOk`), the definitions are
related to the typing environment's and the recognizers decide membership, as the loaded
evaluator computes them ({name}`Concl`). -/
theorem program_sound_explicit {a : Internal.Thm}
    (ha : programFormsThm PST.1 PST.2.1 PST.2.2 = some a) (L : Translated PST) {f : PassFns}
    (hf : f.Loaded L.Gk PST.1.idx) {g : EvalFns} (hg : g.Loaded L.Gk PST.1.idx) {k : HypFns}
    (hk : k.Loaded L.Gk PST.1.idx) (ks : List Kernel.Tree) (hpass : ∀ p ∈ f.passes, p ks)
    (hplain : k.PlainOk ks) (hmark : k.MarkersOk ks) (hstat : k.StaticOk (k.msK ks))
    (hforms : k.FormsOk ks) : Concl f g ks := by
  obtain ⟨Hs, hHs, hall⟩ := program_sound h ha L hf hg
  obtain ⟨hrest, hctx⟩ := hyps_rest ha
  -- a list of trees of bitstrings that represents the forms
  obtain ⟨es, hke⟩ := ((order_props (tList tT)).1 rfl).1 ks
  -- the remaining hypotheses represent the statements assumed
  have c := RepCtx.single L.ctx (objVal_list (objVal_tree (ds := L.cds₀ ++ L.ext)))
    (isTy_trees _) (Rep.list RT)
  have hreps : List.Forall₂ (fun (t : Internal.Term) (F : List Kernel.Tree → Prop) ↦
      RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t (Internal.ctxObj [list treeTy])
        (Internal.stdEnv [list treeTy]) omega (KRel (tList tT)) Rep.prop F) (a.hyps.drop 5)
      [fun ks ↦ k.PlainOk ks, fun ks ↦ k.MarkersOk ks, fun ks ↦ k.StaticOk (k.msK ks),
        fun ks ↦ k.FormsOk ks] := by
    rw [hrest]
    exact .cons (plain_rep h L hk c (c.var (i := 0) rfl))
      (.cons (markers_rep h L hk) (.cons (static_rep h L hk) (forms_rep h L hk)))
  rw [hctx] at hHs
  have hHall : ∀ H ∈ Hs, H es :=
    forall_of_forall₂ (P := fun H : Forms → Prop ↦ H es)
      (Q := fun F : List Kernel.Tree → Prop ↦ F ks)
      (fun _ _ _ hr hc' hF ↦ (hr.iff_of_repC hc' hke).mpr hF) hHs _ hreps
      (List.forall_mem_cons.mpr ⟨hplain, List.forall_mem_cons.mpr ⟨hmark,
        List.forall_mem_cons.mpr ⟨hstat, List.forall_mem_cons.mpr ⟨hforms,
          fun _ hm ↦ (List.not_mem_nil hm).elim⟩⟩⟩⟩)
  exact of_foldr_imp (P := fun H : Forms → Prop ↦ H es) Hs hHall (hall ks es hke hpass)

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramExplicit

end
