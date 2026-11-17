/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramPasses
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, concluded in Lean

The soundness of a whole program of the datatype language's stage-1 compiler, at the passes the
kernel evaluates ({lit}`DatatypeProgramPasses.program_passes`), concludes a formula of the
internal language that represents a statement of Lean about the evaluator the kernel loads
({lit}`DatatypeConclusion.concl_rep`). The formula's reading therefore holds of a list of trees
of bitstrings exactly when the statement holds of the kernel's list of trees it represents, and
the soundness reads: where the loaded compilers' passes succeed on a program's forms, and the
remaining hypotheses hold of the forms' representation, each definition the typing gives a
type evaluates to a value related at the type, and each datatype's recognizer decides
membership.

## Main statements

* {lit}`concl_eq` — the soundness's conclusion is the formula {lit}`DatatypeConclusion.conclT`.
* {lit}`program_sound` — where the loaded compilers' passes succeed on a program's forms and
  the remaining hypotheses hold, the definitions are related to the typing environment's and
  the recognizers decide membership.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, evaluator, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramConclusion

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypePasses (PassFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements (EvalFns)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeConclusion
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramReading
open GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramPasses
open Kernel (tT tList)
open Sorts

/-- A chain of implications to a conclusion gives the chain to what the conclusion implies. -/
theorem foldr_imp_mono {α : Type} {P : α → Prop} {Q Q' : Prop} (hQ : Q → Q') :
    ∀ l : List α, l.foldr (fun x acc ↦ P x → acc) Q → l.foldr (fun x acc ↦ P x → acc) Q' :=
  List.rec hQ fun _ _ ih hl hx ↦ ih (hl hx)

/-- The conclusion of the soundness of a whole program ({name}`programFormsThm`) is the
formula of the conclusion at the program's forms ({name}`conclT`), by the translation of the
kernel's child primitive; the statement's context is that of the forms. -/
theorem concl_eq {P : Prog} {S : Defs} {T : Defs3} {a : Internal.Thm}
    (ha : programFormsThm P S T = some a) :
    ∃ childT, primT Kernel.Prim.child = some childT ∧ a.concl = conclT P T childT ∧
      a.ctx = [list treeTy] := by
  simp only [programFormsThm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨⟨hs, concl⟩, hpp, rfl⟩ := ha
  simp only [programParts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq] at hpp
  obtain ⟨childT, hch, rfl, rfl⟩ := hpp
  exact ⟨childT, hch, rfl, rfl⟩

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST)

include h

/-- The soundness of a whole program of the datatype language's stage-1 compiler, concluded in
Lean: the hypotheses after the passes' successes read as predicates of the lists of trees of
bitstrings ({name}`Reads`), and at every such list that represents a kernel list of forms on
which the passes of the loaded compilers succeed ({name}`PassFns.passes`), where those
hypotheses hold, the definitions are related to the typing environment's and the recognizers
decide membership, as the loaded evaluator computes them ({name}`Concl`). -/
theorem program_sound {a : Internal.Thm}
    (ha : programFormsThm PST.1 PST.2.1 PST.2.2 = some a) (L : Translated PST) {f : PassFns}
    (hf : f.Loaded L.Gk PST.1.idx) {g : EvalFns} (hg : g.Loaded L.Gk PST.1.idx) :
    ∃ Hs : List (Forms → Prop),
      List.Forall₂ (Reads PST.1.G (L.cds₀ ++ L.ext) a.ctx) (a.hyps.drop 5) Hs ∧
      ∀ (ks : List Kernel.Tree) (es : Forms), KRel (tList tT) ks es → (∀ p ∈ f.passes, p ks) →
        Hs.foldr (fun (H : Forms → Prop) (acc : Prop) ↦ H es → acc) (Concl f g ks) := by
  obtain ⟨Hs, C, hHs, hC, hall⟩ := program_passes h ha L hf
  obtain ⟨childT, hch, hcon, hctx⟩ := concl_eq ha
  have hrep := concl_rep h L hf hg hch
  rw [hcon, hctx] at hC
  exact ⟨Hs, hHs, fun ks es hke hpass ↦
    foldr_imp_mono (P := fun H : Forms → Prop ↦ H es) (hC.iff_of_repC hrep hke).mp Hs
      (hall ks es hke hpass)⟩

end GebTests.Prototypes.FreeTopos.Certified.DatatypeProgramConclusion

end
