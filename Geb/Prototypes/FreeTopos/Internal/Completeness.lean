/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Logic
public import Geb.Prototypes.FreeTopos.Internal.Proofs
public import Geb.Prototypes.PartialHorn.Completeness
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The completeness of the internal language

A theorem of the language whose hypotheses and conclusion are formulas, valid in every model of
the theory extended by the compilations of the language's definitions, is proved by a derivation
of one rule: the citation of a certificate of the sequent it compiles to
({name}`Geb.FreeTopos.Internal.Thm.seq`). The sequent is valid in every such model
({name}`Geb.FreeTopos.Internal.Thm.seq_valid`), the extended theory's axioms are in scope and
equate terms of one sort, and so the partial Horn logic's completeness
({name}`Geb.PartialHorn.derivable_of_valid`) gives the certificate, with any environment of
theorems. The citation is sound in every such model
({name}`Geb.FreeTopos.Internal.certSeq_sound`), so that the language citing certificates proves
exactly the theorems valid in every model.

## Main statements

* {lit}`theory_scoped` — the theory's axioms are in scope.
* {lit}`exists_certSeq_of_valid` — completeness: a theorem valid in every model is proved by the
  citation of a certificate.

## Tags

internal language, Mitchell–Bénabou language, completeness, proof certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open Geb.PartialHorn (Seq Model IsModel)
open Geb.FreeTopos.Internal.Logic (nd)

/-- The theory's axioms are in scope. -/
theorem theory_scoped : ∀ a ∈ theory.axioms, a.Scoped = true := by
  have h : axioms.all Seq.Scoped = true := by decide
  exact fun a ha ↦ List.all_eq_true.mp h a ha

/-- The theory extended by well-formed definitions has its axioms in scope, each equating terms
of one sort. -/
theorem ext_axioms_complete {cds : List PartialHorn.Defn} (hwf : PartialHorn.DefnsWF sig cds) :
    ∀ a ∈ (ext cds).axioms, a.Scoped = true ∧ PartialHorn.SidesSorted (ext cds).sig a :=
  fun a ha ↦ ⟨PartialHorn.scoped_extendAll cds theory theory_scoped hwf a ha,
    PartialHorn.sidesSorted_extendAll cds theory theory_sidesSorted hwf a ha⟩

/-- Completeness: a theorem whose hypotheses and conclusion are formulas, valid in every model of
the theory extended by the compilations of the definitions of {lit}`G`, is proved by the citation
of a certificate of the sequent it compiles to, with any environment. -/
theorem exists_certSeq_of_valid {G : Globals} (hG : G.WF) {cds : List PartialHorn.Defn}
    (hc : compileDefs G = some cds) (hb : G.base = sig.length)
    (hwf : PartialHorn.DefnsWF sig cds) {E : Array Entry} {a : Thm}
    (hΦ : ∀ ψ ∈ a.hyps, typeIn G a.arity a.ctx ψ = some omega)
    (hφ : typeIn G a.arity a.ctx a.concl = some omega)
    (hv : ∀ M : Model.{0} (ext cds).sig, IsModel (ext cds) M → a.Valid M G) :
    ∃ c, (check G E a.arity (nd (.certSeq c))).2 a.ctx a.hyps a.concl = true := by
  obtain ⟨c, hc'⟩ := PartialHorn.derivable_of_valid (E := E.map (Entry.seq G))
    (ext_axioms_complete hwf) (H := []) (fun _ h ↦ by simp at h)
    fun M hM ↦ Thm.seq_valid hM hG (hv M hM)
  refine ⟨c, ?_⟩
  rw [nd, check_node]
  simp only [checkStep, List.map_nil, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨hΦ, hφ⟩, ?_⟩
  simp only [certifies, hc, Option.any_some, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hb, hc'⟩

end Geb.FreeTopos.Internal

end
