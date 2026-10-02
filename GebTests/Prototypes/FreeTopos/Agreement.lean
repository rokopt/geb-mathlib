/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import GebTests.Prototypes.FreeTopos.Agreement.Load
public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import GebTests.Prototypes.FreeTopos.Agreement.Translation

set_option doc.verso true in
/-!
# The metalogic's checker, the translation and the prover written in Geb agree with Lean's

The checker of the metalogic written in Geb, {lit}`bootstrap/free-topos/`, loads, and one of its
globals is a function which, at the encodings of constants, entries and declarations, gives the
encoding of what {name}`Geb.FreeTopos.Internal.checkDev` gives at the same inputs: the state after
the development, or nothing where a declaration's proof does not prove it. The two checkers
therefore accept the same developments with the same results, in both directions, at every
input. The translation of the kernel into the internal language written in Geb,
{lit}`bootstrap/free-topos/translation.geb`, is part of the same program, and its translations of
a program's definitions, of a translated program's constants and of a theorem of Gödel's T give
the encodings of what {name}`Geb.FreeTopos.Translation.program`,
{name}`Geb.FreeTopos.Translation.globals` and {name}`Geb.FreeTopos.Translation.thm` give, at every
input. The prover of the internal language written in Geb, {lit}`bootstrap/free-topos/prove.geb`,
is part of the same program too, and each of its entry points, at encoded arguments, rules related
to the normalizer's and provers related to Lean's, gives the encoding of the derivation the Lean
prover ({name}`Geb.FreeTopos.Internal.byNorm` and the provers beside it) constructs, so that the
two provers prove the same equations with the same derivations.

Constants are encoded by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encGlobals`, entries by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encEntry`, declarations by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encDecl`, states by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Encode.encState`, translated programs by
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.encProgram` and theorems of Gödel's T by
{name}`GebTests.Prototypes.GoedelT.MirrorEquations.encThm`. The proofs compose the kernel's
evaluation of the loading ({lit}`GebTests.Prototypes.FreeTopos.Agreement.Load`) with the agreement
of the program's Lean mirror with the Lean definitions, proved definition by definition
({name}`GebTests.Prototypes.FreeTopos.Agreement.Derivation.checkDev_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.program_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.trGlobals_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Translation.thm_eq`,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Prove.byNorm_eq` and the prover's other agreements).

## Main statements

* {lit}`checkDev_agree` — the loaded checker written in Geb decides as the checker in Lean.
* {lit}`translation_agree` — the loaded translation written in Geb translates as the translation
  in Lean.
* {lit}`prover_agree` — the loaded prover written in Geb proves as the prover in Lean.

## Tags

metalogic, checker, translation, prover, development, agreement, soundness, completeness
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Load GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Translation GebTests.Prototypes.FreeTopos.Agreement.Prove

/-- The metalogic's checker written in Geb decides as the checker in Lean: its program loads to
globals among which is a function of the check's type that, at encoded constants, entries and
declarations, gives the encoding of the Lean checker's state after the development. -/
theorem checkDev_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    ∃ f : Ty.den checkDevTy, G'[372]? = some ⟨checkDevTy, f⟩ ∧
      ∀ (G : Internal.Globals) (E : Array Internal.Entry) (ds : List Internal.Decl),
        f (encGlobals G) (E.toList.map encEntry) (ds.map encDecl) =
          encOpt ((Internal.checkDev G E ds).map encState) :=
  ⟨_, metalogic.load_eq, GebMirror.Metalogic.checkDev, metalogic_checkDev, checkDev_eq⟩

/-- The translation written in Geb translates as the translation in Lean: its program loads to
globals among which are functions of their types that, at a program's definitions, at encoded
definitions of the language, and at the globals' types and an encoded theorem of Gödel's T, give
the encodings of the Lean translation's program, constants and theorem. -/
theorem translation_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den listFnTy, G'[533]? = some ⟨listFnTy, f⟩ ∧
      ∀ ds : List Tree, f ds = encOpt ((Translation.program ds).map encProgram)) ∧
    (∃ f : Ty.den listFnTy, G'[534]? = some ⟨listFnTy, f⟩ ∧
      ∀ defs : List Internal.Defn,
        f (defs.map encLDefn) = encGlobals (Translation.globals defs)) ∧
    (∃ f : Ty.den thmTy, G'[535]? = some ⟨thmTy, f⟩ ∧
      ∀ (gt : List Tree) (a : GoedelT.Thm),
        f gt (GebTests.Prototypes.GoedelT.MirrorEquations.encThm a) =
          encOpt ((Translation.thm gt a).map encThm)) :=
  ⟨_, metalogic.load_eq, ⟨GebMirror.Metalogic.program, metalogic_program, program_eq⟩,
    ⟨GebMirror.Metalogic.trGlobals, metalogic_trGlobals, trGlobals_eq⟩,
    ⟨GebMirror.Metalogic.thm, metalogic_thm, thm_eq⟩⟩

/-- The prover written in Geb proves as the prover in Lean: its program loads to globals among
which are the prover's entry points, each a function of its type. The preparation of encoded
rules, none a prepared theorem, gives rules related to the Lean preparation's; each proof, at
encoded arguments and related rules, is a prover related to the Lean proof; and each prover built
from provers, at related provers, is related to the Lean one. -/
theorem prover_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den prepareTy, G'[553]? = some ⟨prepareTy, f⟩ ∧
      ∀ (E : Array Internal.Entry) (rs : List Internal.NormRule),
        (∀ r ∈ rs, ∀ j θ root m k, r ≠ .thmAt j θ root m k) →
          List.Forall₂ RRel (f (E.toList.map encEntry) (rs.map encRule))
            (Internal.prepareRules E rs)) ∧
    (∃ f : Ty.den normTy, G'[560]? = some ⟨normTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel))
          (Internal.byNorm G E n rs fuel)) ∧
    (∃ f : Ty.den normTy, G'[582]? = some ⟨normTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel))
          (Internal.byNormW G E n rs fuel)) ∧
    (∃ f : Ty.den indTy, G'[562]? = some ⟨indTy, f⟩ ∧
      ∀ G E n kz ks s rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz) (leaf ks) (encTerm s) rs'
          (leaf fuel)) (Internal.byNatInd G E n kz ks s rs fuel)) ∧
    (∃ f : Ty.den indTy, G'[563]? = some ⟨indTy, f⟩ ∧
      ∀ G E n kn kc s rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn) (leaf kc) (encTerm s) rs'
          (leaf fuel)) (Internal.byListInd G E n kn kc s rs fuel)) ∧
    (∃ f : Ty.den indHypTy, G'[565]? = some ⟨indHypTy, f⟩ ∧
      ∀ G E n kz ks rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz) (leaf ks) rs' (leaf fuel))
          (Internal.byNatIndHyp G E n kz ks rs fuel)) ∧
    (∃ f : Ty.den indHypTy, G'[566]? = some ⟨indHypTy, f⟩ ∧
      ∀ G E n kn kc rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn) (leaf kc) rs' (leaf fuel))
          (Internal.byListIndHyp G E n kn kc rs fuel)) ∧
    (∃ f : Ty.den roseIndTy, G'[587]? = some ⟨roseIndTy, f⟩ ∧
      ∀ G E n kn kl kc s rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel Γ t u,
        f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn) (leaf kl) (leaf kc) (encTerm s)
            rs' (leaf fuel) Γ (encTerm t) (encTerm u) =
          encOpt ((Internal.byRoseInd G E n kn kl kc s rs fuel Γ t u).map encDeriv)) ∧
    (∃ f : Ty.den funExtTy, G'[584]? = some ⟨funExtTy, f⟩ ∧
      ∀ G n p' p, PRel p' p → PRel (f (encGlobals G) (leaf n) p') (Internal.byFunExt G n p)) ∧
    (∃ f : Ty.den proverFnTy, G'[585]? = some ⟨proverFnTy, f⟩ ∧
      ∀ kl kr i p' p, PRel p' p →
        PRel (f (leaf kl) (leaf kr) (leaf i) p') (Internal.bySplit kl kr i p)) ∧
    (∃ f : Ty.den listIndWithTy, G'[586]? = some ⟨listIndWithTy, f⟩ ∧
      ∀ G n kn kc p₀' p₀ p₁' p₁, PRel p₀' p₀ → PRel p₁' p₁ →
        PRel (f (encGlobals G) (leaf n) (leaf kn) (leaf kc) p₀' p₁')
          (Internal.byListIndWith G n kn kc p₀ p₁)) ∧
    (∃ f : Ty.den proverFnTy, G'[588]? = some ⟨proverFnTy, f⟩ ∧
      ∀ kn kl kc p' p, PRel p' p →
        PRel (f (leaf kn) (leaf kl) (leaf kc) p') (Internal.byRoseIndHyp kn kl kc p)) :=
  ⟨_, metalogic.load_eq,
    ⟨_, metalogic_prepareRules, fun E rs h ↦ prepareRules_eq E rs h⟩,
    ⟨_, metalogic_byNorm, fun G E n _ _ h fuel ↦ byNorm_eq G E n _ _ h fuel⟩,
    ⟨_, metalogic_byNormW, fun G E n _ _ h fuel ↦ byNormW_eq G E n _ _ h fuel⟩,
    ⟨_, metalogic_byNatInd, fun G E n kz ks s _ _ h fuel ↦ byNatInd_eq G E n kz ks s _ _ h fuel⟩,
    ⟨_, metalogic_byListInd, fun G E n kn kc s _ _ h fuel ↦ byListInd_eq G E n kn kc s _ _ h fuel⟩,
    ⟨_, metalogic_byNatIndHyp, fun G E n kz ks _ _ h fuel ↦ byNatIndHyp_eq G E n kz ks _ _ h fuel⟩,
    ⟨_, metalogic_byListIndHyp,
      fun G E n kn kc _ _ h fuel ↦ byListIndHyp_eq G E n kn kc _ _ h fuel⟩,
    ⟨_, metalogic_byRoseInd,
      fun G E n kn kl kc s _ _ h fuel ↦ byRoseInd_eq G E n kn kl kc s _ _ h fuel⟩,
    ⟨_, metalogic_byFunExt, fun G n _ _ h ↦ byFunExt_eq G n _ _ h⟩,
    ⟨_, metalogic_bySplit, fun kl kr i _ _ h ↦ bySplit_eq kl kr i _ _ h⟩,
    ⟨_, metalogic_byListIndWith,
      fun G n kn kc _ _ _ _ h₀ h₁ ↦ byListIndWith_eq G n kn kc _ _ _ _ h₀ h₁⟩,
    ⟨_, metalogic_byRoseIndHyp, fun kn kl kc _ _ h ↦ byRoseIndHyp_eq kn kl kc _ _ h⟩⟩

end GebTests.Prototypes.FreeTopos.Agreement

end
