/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Agreement.Combinator
public import GebTests.Prototypes.FreeTopos.Agreement.Derivation
public import GebTests.Prototypes.FreeTopos.Agreement.Load
public import GebTests.Prototypes.FreeTopos.Agreement.Prove
public import GebTests.Prototypes.FreeTopos.Agreement.Reader
public import GebTests.Prototypes.FreeTopos.Agreement.Tactics
public import GebTests.Prototypes.FreeTopos.Agreement.Translation

set_option doc.verso true in
/-!
# The metalogic's checker, translation, provers and tactics written in Geb agree with Lean's

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
two provers prove the same equations with the same derivations. The tactics written in Geb,
{lit}`bootstrap/free-topos/tactics.geb`, are part of the same program as well, and each entry point,
at encoded arguments, related rules and related provers, is a prover related to the Lean tactic
({lit}`Geb.FreeTopos.Tactics`) it transcribes. The combinator prover written in Geb,
{lit}`bootstrap/free-topos/combinator.geb`, is part of the same program, and each of its entry
points, at encoded arguments and related states, gives the encoding of the Lean prover's result
({name}`Geb.FreeTopos.Prover.normalize` and the provers beside it), so that the two provers prove
the same equations with the same certificates. The reader's resolution written in Geb,
{lit}`bootstrap/reader.geb`, and the printer of kernel terms written in Geb,
{lit}`bootstrap/printer.geb`, are part of the same program too: the resolution agrees with the Lean
reader's ({name}`Geb.Kernel.resolve`) at every S-expression, the partial printer with the Lean
printer ({name}`Geb.Kernel.printTerm?`) at every term, printing nothing where it prints nothing, and
so the reader written in Geb inverts the printer written in Geb without hypotheses, the Lean
retraction ({name}`Geb.Kernel.resolve_of_printTerm?`) carried across the two agreements.

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
{name}`GebTests.Prototypes.FreeTopos.Agreement.Prove.byNorm_eq` and the prover's other agreements,
{name}`GebTests.Prototypes.FreeTopos.Agreement.Tactics.byAuto_eq` and the tactics' other
agreements, {name}`GebTests.Prototypes.FreeTopos.Agreement.Combinator.normalize_rel` and the
combinator prover's other agreements).

## Main statements

* {lit}`checkDev_agree` — the loaded checker written in Geb decides as the checker in Lean.
* {lit}`translation_agree` — the loaded translation written in Geb translates as the translation
  in Lean.
* {lit}`prover_agree` — the loaded prover written in Geb proves as the prover in Lean.
* {lit}`tactics_agree` — the loaded tactics written in Geb prove as the tactics in Lean.
* {lit}`combinator_agree` — the loaded combinator prover written in Geb proves as the combinator
  prover in Lean.
* {lit}`reader_inverse_agree` — the loaded printer and resolution written in Geb agree with
  Lean's, and the resolution inverts the printer.

## Tags

metalogic, checker, translation, prover, tactic, combinator, development, agreement, soundness,
completeness
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement

open Geb Geb.Kernel Geb.FreeTopos GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Agreement.Load GebTests.Prototypes.FreeTopos.Agreement.Derivation
  GebTests.Prototypes.FreeTopos.Agreement.Translation GebTests.Prototypes.FreeTopos.Agreement.Prove
  GebTests.Prototypes.FreeTopos.Agreement.Tactics
open Geb.Kernel.ModulesTests (sexpTree)
open GebMirror (metalogic)

/-- The metalogic's checker written in Geb decides as the checker in Lean: its program loads to
globals among which is a function of the check's type that, at encoded constants, entries and
declarations, gives the encoding of the Lean checker's state after the development. -/
theorem checkDev_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    ∃ f : Ty.den checkDevTy, G'[372]? = some ⟨checkDevTy, f⟩ ∧
      ∀ (G : Internal.Globals) (E : Array Internal.Entry) (ds : List Internal.Decl),
        f (encGlobals G) (E.toList.map encEntry) (ds.map encDecl) =
          encOpt ((Internal.checkDev G E ds).map encState) :=
  ⟨_, metalogic.load_globals, «Derivation.checkDev», metalogic_checkDev, checkDev_eq⟩

/-- The translation written in Geb translates as the translation in Lean: its program loads to
globals among which are functions of their types that, at a program's definitions, at encoded
definitions of the language, and at the globals' types and an encoded theorem of Gödel's T, give
the encodings of the Lean translation's program, constants and theorem. -/
theorem translation_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den listFnTy, G'[558]? = some ⟨listFnTy, f⟩ ∧
      ∀ ds : List Tree, f ds = encOpt ((Translation.program ds).map encProgram)) ∧
    (∃ f : Ty.den listFnTy, G'[559]? = some ⟨listFnTy, f⟩ ∧
      ∀ defs : List Internal.Defn,
        f (defs.map encLDefn) = encGlobals (Translation.globals defs)) ∧
    (∃ f : Ty.den thmTy, G'[560]? = some ⟨thmTy, f⟩ ∧
      ∀ (gt : List Tree) (a : GoedelT.Thm),
        f gt (GebTests.Prototypes.GoedelT.MirrorEquations.encThm a) =
          encOpt ((Translation.thm gt a).map encThm)) :=
  ⟨_, metalogic.load_globals, ⟨«Translation.program», metalogic_program, program_eq⟩,
    ⟨«Translation.trGlobals», metalogic_trGlobals, trGlobals_eq⟩,
    ⟨«Translation.thm», metalogic_thm, thm_eq⟩⟩

/-- The prover written in Geb proves as the prover in Lean: its program loads to globals among
which are the prover's entry points, each a function of its type. The preparation of encoded
rules, none a prepared theorem, gives rules related to the Lean preparation's; each proof, at
encoded arguments and related rules, is a prover related to the Lean proof; and each prover built
from provers, at related provers, is related to the Lean one. -/
theorem prover_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den prepareTy, G'[578]? = some ⟨prepareTy, f⟩ ∧
      ∀ (E : Array Internal.Entry) (rs : List Internal.NormRule),
        (∀ r ∈ rs, ∀ j θ root m k, r ≠ .thmAt j θ root m k) →
          List.Forall₂ RRel (f (E.toList.map encEntry) (rs.map encRule))
            (Internal.prepareRules E rs)) ∧
    (∃ f : Ty.den normTy, G'[585]? = some ⟨normTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel))
          (Internal.byNorm G E n rs fuel)) ∧
    (∃ f : Ty.den normTy, G'[607]? = some ⟨normTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf fuel))
          (Internal.byNormW G E n rs fuel)) ∧
    (∃ f : Ty.den indTy, G'[587]? = some ⟨indTy, f⟩ ∧
      ∀ G E n kz ks s rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz) (leaf ks) (encTerm s) rs'
          (leaf fuel)) (Internal.byNatInd G E n kz ks s rs fuel)) ∧
    (∃ f : Ty.den indTy, G'[588]? = some ⟨indTy, f⟩ ∧
      ∀ G E n kn kc s rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn) (leaf kc) (encTerm s) rs'
          (leaf fuel)) (Internal.byListInd G E n kn kc s rs fuel)) ∧
    (∃ f : Ty.den indHypTy, G'[590]? = some ⟨indHypTy, f⟩ ∧
      ∀ G E n kz ks rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kz) (leaf ks) rs' (leaf fuel))
          (Internal.byNatIndHyp G E n kz ks rs fuel)) ∧
    (∃ f : Ty.den indHypTy, G'[591]? = some ⟨indHypTy, f⟩ ∧
      ∀ G E n kn kc rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn) (leaf kc) rs' (leaf fuel))
          (Internal.byListIndHyp G E n kn kc rs fuel)) ∧
    (∃ f : Ty.den roseIndTy, G'[612]? = some ⟨roseIndTy, f⟩ ∧
      ∀ G E n kn kl kc s rs' rs, List.Forall₂ RRel rs' rs → ∀ fuel Γ t u,
        f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf kn) (leaf kl) (leaf kc) (encTerm s)
            rs' (leaf fuel) Γ (encTerm t) (encTerm u) =
          encOpt ((Internal.byRoseInd G E n kn kl kc s rs fuel Γ t u).map encDeriv)) ∧
    (∃ f : Ty.den funExtTy, G'[609]? = some ⟨funExtTy, f⟩ ∧
      ∀ G n p' p, PRel p' p → PRel (f (encGlobals G) (leaf n) p') (Internal.byFunExt G n p)) ∧
    (∃ f : Ty.den proverFnTy, G'[610]? = some ⟨proverFnTy, f⟩ ∧
      ∀ kl kr i p' p, PRel p' p →
        PRel (f (leaf kl) (leaf kr) (leaf i) p') (Internal.bySplit kl kr i p)) ∧
    (∃ f : Ty.den listIndWithTy, G'[611]? = some ⟨listIndWithTy, f⟩ ∧
      ∀ G n kn kc p₀' p₀ p₁' p₁, PRel p₀' p₀ → PRel p₁' p₁ →
        PRel (f (encGlobals G) (leaf n) (leaf kn) (leaf kc) p₀' p₁')
          (Internal.byListIndWith G n kn kc p₀ p₁)) ∧
    (∃ f : Ty.den proverFnTy, G'[613]? = some ⟨proverFnTy, f⟩ ∧
      ∀ kn kl kc p' p, PRel p' p →
        PRel (f (leaf kn) (leaf kl) (leaf kc) p') (Internal.byRoseIndHyp kn kl kc p)) :=
  ⟨_, metalogic.load_globals,
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

/-- The tactics written in Geb prove as the tactics in Lean: the program loads to globals among
which are the tactics' entry points, each a function of its type that, at encoded arguments,
related rules, related provers and related provers from rules, is a prover related to the Lean
tactic, and the derivation of a rewriting under a mask is the encoding of Lean's. -/
theorem tactics_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den modeTy, G'[619]? = some ⟨modeTy, f⟩ ∧
      ∀ m G E n rs' rs, List.Forall₂ RRel rs' rs →
        PRel (f (leaf (encDepth m)) (encGlobals G) (E.toList.map encEntry) (leaf n) rs')
          (Tactics.byMode m G E n rs)) ∧
    (∃ f : Ty.den rulesProverTy, G'[620]? = some ⟨rulesProverTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs') (Tactics.byWeak G E n rs)) ∧
    (∃ f : Ty.den nfTy, G'[621]? = some ⟨nfTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ m p' p, PRel p' p →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf (encDepth m)) p')
          (Tactics.byNF G E n rs m p)) ∧
    (∃ f : Ty.den normHTy, G'[625]? = some ⟨normHTy, f⟩ ∧
      ∀ G E rs' rs, List.Forall₂ RRel rs' rs →
        PRel (f (encGlobals G) (E.toList.map encEntry) rs') (Tactics.normH G E rs)) ∧
    (∃ f : Ty.den funExtTy, G'[626]? = some ⟨funExtTy, f⟩ ∧
      ∀ k G p' p, PRel p' p → PRel (f (leaf k) (encGlobals G) p') (Tactics.funExts k G p)) ∧
    (∃ f : Ty.den listIndWeakTy, G'[627]? = some ⟨listIndWeakTy, f⟩ ∧
      ∀ G E n s rs' rs, List.Forall₂ RRel rs' rs →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (encTerm s) rs')
          (Tactics.byListIndWeak G E n s rs)) ∧
    (∃ f : Ty.den proverFnTy, G'[628]? = some ⟨proverFnTy, f⟩ ∧
      ∀ G n s p' p, PRel p' p →
        PRel (f (encGlobals G) (leaf n) (encTerm s) p') (Tactics.byRoseIndWith G n s p)) ∧
    (∃ f : Ty.den splitTy, G'[630]? = some ⟨splitTy, f⟩ ∧
      ∀ G n i p₀' p₁' p₀ p₁, PRel p₀' p₀ → PRel p₁' p₁ →
        PRel (f (encGlobals G) (leaf n) (leaf i) p₀' p₁') (Tactics.byListSplit G n i p₀ p₁)) ∧
    (∃ f : Ty.den splitTy, G'[631]? = some ⟨splitTy, f⟩ ∧
      ∀ kl kr i p₀' p₁' p₀ p₁, PRel p₀' p₀ → PRel p₁' p₁ →
        PRel (f (leaf kl) (leaf kr) (leaf i) p₀' p₁') (Tactics.bySplit2 kl kr i p₀ p₁)) ∧
    (∃ f : Ty.den funExtTy, G'[632]? = some ⟨funExtTy, f⟩ ∧
      ∀ G n p' p, PRel p' p → PRel (f (encGlobals G) (leaf n) p') (Tactics.byListCases G n p)) ∧
    (∃ f : Ty.den twoProverTy, G'[633]? = some ⟨twoProverTy, f⟩ ∧
      ∀ G n p₀' p₁' p₀ p₁, PRel p₀' p₀ → PRel p₁' p₁ →
        PRel (f (encGlobals G) (leaf n) p₀' p₁') (Tactics.bitsInd G n p₀ p₁)) ∧
    (∃ f : Ty.den funExtTy, G'[634]? = some ⟨funExtTy, f⟩ ∧
      ∀ G n p' p, PRel p' p → PRel (f (encGlobals G) (leaf n) p') (Tactics.bitsCases G n p)) ∧
    (∃ f : Ty.den byBitsTy, G'[635]? = some ⟨byBitsTy, f⟩ ∧
      ∀ G p' p, PRel p' p → ∀ d i,
        PRel (f (encGlobals G) p' (leaf d) (leaf i)) (Tactics.byBits G p d i)) ∧
    (∃ f : Ty.den twoProverTy, G'[636]? = some ⟨twoProverTy, f⟩ ∧
      ∀ G i p' q' p q, PRel p' p → PRel q' q →
        PRel (f (encGlobals G) (leaf i) p' q') (Tactics.byLength3 G i p q)) ∧
    (∃ f : Ty.den weakHypsTy, G'[637]? = some ⟨weakHypsTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ (is : List ℕ) k' k, KRel k' k → ∀ m,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (is.map leaf) k'
          (leaf (encDepth m))) (Tactics.withWeakHyps G E n rs is k m)) ∧
    (∃ f : Ty.den rulesProverTy, G'[638]? = some ⟨rulesProverTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs')
          (Tactics.byListIndHypWeak G E n rs)) ∧
    (∃ f : Ty.den bitsIndHypTy, G'[639]? = some ⟨bitsIndHypTy, f⟩ ∧
      ∀ G E rs' rs, List.Forall₂ RRel rs' rs → ∀ m,
        PRel (f (encGlobals G) (E.toList.map encEntry) rs' (leaf (encDepth m)))
          (Tactics.byBitsIndHyp G E rs m)) ∧
    (∃ f : Ty.den instsTy, G'[643]? = some ⟨instsTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ h (αs : List (List Internal.Term)) k' k,
        KRel k' k → ∀ m, PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf h)
          (αs.map (·.map encTerm)) k' (leaf (encDepth m))) (Tactics.withInsts G E n rs h αs k m)) ∧
    (∃ f : Ty.den childHypsTy, G'[645]? = some ⟨childHypsTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ h (kids : List ℕ)
        (args' : Tree → List (List Tree)) (args : ℕ → List (List Internal.Term)),
        (∀ p, args' (leaf p) = (args p).map (·.map encTerm)) →
        ∀ (k' : List Tree → List Tree → List Tree → Tree → Tree → Tree)
          (k : List ℕ → Internal.Prover), (∀ is : List ℕ, PRel (k' (is.map leaf)) (k is)) →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf h) (kids.map leaf) args'
          k') (Tactics.withChildHyps G E n rs h kids args k)) ∧
    (∃ f : Ty.den revertTy, G'[647]? = some ⟨revertTy, f⟩ ∧
      ∀ G n o lb i h pNil' pCons' pNil pCons, PRel pNil' pNil → PRel pCons' pCons →
        PRel (f (encGlobals G) (leaf n) (leaf o) (leaf lb) (leaf i) (leaf h) pNil' pCons')
          (Tactics.revertCase G n o lb i h pNil pCons)) ∧
    (∃ f : Ty.den impITy, G'[649]? = some ⟨impITy, f⟩ ∧
      ∀ G E o lb p' p, PRel p' p →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf o) (leaf lb) p')
          (Tactics.byImpI G E o lb p)) ∧
    (∃ f : Ty.den impElimTy, G'[650]? = some ⟨impElimTy, f⟩ ∧
      ∀ o lb h (is : List ℕ) k' k, KRel k' k →
        PRel (f (leaf o) (leaf lb) (leaf h) (is.map leaf) k') (Tactics.withImpElim o lb h is k)) ∧
    (∃ f : Ty.den succPredTy, G'[653]? = some ⟨succPredTy, f⟩ ∧
      ∀ E j p' p, PRel p' p →
        PRel (f (E.toList.map encEntry) (leaf j) p') (Tactics.bySuccPred E j p)) ∧
    (∃ f : Ty.den instsSearchTy, G'[672]? = some ⟨instsSearchTy, f⟩ ∧
      ∀ m G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ hs,
        PRel (f (leaf (encDepth m)) (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf hs))
          (Tactics.byInsts m G E n rs hs)) ∧
    (∃ f : Ty.den autoTy, G'[674]? = some ⟨autoTy, f⟩ ∧
      ∀ G E n rs' rs, List.Forall₂ RRel rs' rs → ∀ d m,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) rs' (leaf d) (leaf (encDepth m)))
          (Tactics.byAuto G E n rs d m)) ∧
    (∃ f : Ty.den funExtTy, G'[686]? = some ⟨funExtTy, f⟩ ∧
      ∀ lk i p' p, PRel p' p → PRel (f (leaf lk) (leaf i) p') (Tactics.byTreeSplit lk i p)) ∧
    (∃ f : Ty.den autoTTy, G'[688]? = some ⟨autoTTy, f⟩ ∧
      ∀ G E n lk rs' rs, List.Forall₂ RRel rs' rs → ∀ d m,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf lk) rs' (leaf d)
          (leaf (encDepth m))) (Tactics.byAutoT G E n lk rs d m)) ∧
    (∃ f : Ty.den autoCTy, G'[689]? = some ⟨autoCTy, f⟩ ∧
      ∀ G E n lk rs' rs, List.Forall₂ RRel rs' rs → ∀ d,
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf n) (leaf lk) rs' (leaf d))
          (Tactics.byAutoC G E n lk rs d)) ∧
    (∃ f : Ty.den maskRwTy, G'[693]? = some ⟨maskRwTy, f⟩ ∧
      ∀ a b ab j θ (σ : List Internal.Term) c d x x' z y,
        f a b (leaf ab) (leaf j) θ (σ.map encTerm) (encTerm c) (encTerm d) (encTerm x)
            (encTerm x') (encTerm z) (encTerm y) =
          encDeriv (Tactics.maskRw a b ab j θ σ c d x x' z y)) ∧
    (∃ f : Ty.den maskSubsTy, G'[696]? = some ⟨maskSubsTy, f⟩ ∧
      ∀ G E ab cs rs' rs, List.Forall₂ RRel rs' rs → ∀ n p' p, KRel p' p →
        PRel (f (encGlobals G) (E.toList.map encEntry) (leaf ab) (leaf cs) rs' (leaf n) p')
          (Tactics.byMaskSubs G E ab cs rs n p)) ∧
    (∃ f : Ty.den funExtTy, G'[697]? = some ⟨funExtTy, f⟩ ∧
      ∀ a c p' p, PRel p' p → PRel (f a (encTerm c) p') (Tactics.byGeneralize a c p)) :=
  ⟨_, metalogic.load_globals, ⟨_, metalogic_byMode, byMode_eq⟩, ⟨_, metalogic_byWeak, byWeak_eq⟩,
    ⟨_, metalogic_byNF, byNF_eq⟩, ⟨_, metalogic_normH, normH_eq⟩,
    ⟨_, metalogic_funExts, funExts_eq⟩, ⟨_, metalogic_byListIndWeak, byListIndWeak_eq⟩,
    ⟨_, metalogic_byRoseIndWith, byRoseIndWith_eq⟩, ⟨_, metalogic_byListSplit, byListSplit_eq⟩,
    ⟨_, metalogic_bySplit2, bySplit2_eq⟩, ⟨_, metalogic_byListCases, byListCases_eq⟩,
    ⟨_, metalogic_bitsInd, bitsInd_eq⟩, ⟨_, metalogic_bitsCases, bitsCases_eq⟩,
    ⟨_, metalogic_byBits, byBits_eq⟩, ⟨_, metalogic_byLength3, byLength3_eq⟩,
    ⟨_, metalogic_withWeakHyps, withWeakHyps_eq⟩,
    ⟨_, metalogic_byListIndHypWeak, byListIndHypWeak_eq⟩,
    ⟨_, metalogic_byBitsIndHyp, byBitsIndHyp_eq⟩, ⟨_, metalogic_withInsts, withInsts_eq⟩,
    ⟨_, metalogic_withChildHyps, withChildHyps_eq⟩, ⟨_, metalogic_revertCase, revertCase_eq⟩,
    ⟨_, metalogic_byImpI, byImpI_eq⟩, ⟨_, metalogic_withImpElim, withImpElim_eq⟩,
    ⟨_, metalogic_bySuccPred, bySuccPred_eq⟩, ⟨_, metalogic_byInsts, byInsts_eq⟩,
    ⟨_, metalogic_byAuto, byAuto_eq⟩, ⟨_, metalogic_byTreeSplit, byTreeSplit_eq⟩,
    ⟨_, metalogic_byAutoT, byAutoT_eq⟩, ⟨_, metalogic_byAutoC, byAutoC_eq⟩,
    ⟨_, metalogic_maskRw, maskRw_eq⟩, ⟨_, metalogic_byMaskSubs, byMaskSubs_eq⟩,
    ⟨_, metalogic_byGeneralize, byGeneralize_eq⟩⟩

set_option maxRecDepth 100000 in
/-- The combinator prover written in Geb proves as the combinator prover in Lean: the program
loads to globals among which are the prover's entry points, each a function of its type that, at
encoded arguments and related states, gives the encoding of the Lean prover's result, and the
library written in Geb and its rules are the encodings of the Lean library and its rules. -/
theorem combinator_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    (∃ f : Ty.den termPMTy, G'[761]? = some ⟨termPMTy, f⟩ ∧
      ∀ t, Combinator.PMRel Combinator.encTy (f t) (Prover.typeTerm t)) ∧
    (∃ f : Ty.den rulesPMTy, G'[790]? = some ⟨rulesPMTy, f⟩ ∧
      ∀ rules t, Combinator.PMRel encPair (f (rules.map encRw) t) (Prover.normalize rules t)) ∧
    (∃ f : Ty.den instPMTy, G'[796]? = some ⟨instPMTy, f⟩ ∧
      ∀ s σ, Combinator.PMRel Combinator.encEqC (f (encSrc s) σ) (Prover.inst s σ)) ∧
    (∃ f : Ty.den termPMTy, G'[797]? = some ⟨termPMTy, f⟩ ∧
      ∀ t, Combinator.PMRel encPair (f t) (Prover.etaExpand t)) ∧
    (∃ f : Ty.den treeFnTy, G'[800]? = some ⟨treeFnTy, f⟩ ∧
      ∀ i, f (leaf i) = encRw (Prover.deltaRule i)) ∧
    (∃ f : Ty.den rulesPMTy, G'[801]? = some ⟨rulesPMTy, f⟩ ∧
      ∀ rules q, Combinator.PMRel id (f (rules.map encRw) (encEqn q)) (Prover.byNorm rules q)) ∧
    (∃ f : Ty.den proveSeqTy, G'[802]? = some ⟨proveSeqTy, f⟩ ∧
      ∀ a m' m, Combinator.PMRel id m' m → ∀ defs infer dev,
        f (encSeq a) m' (defs.map encDefn) (ofBool infer) (dev.map encDevEntry) =
          encOpt ((Prover.proveSeq a m defs infer dev).map Combinator.encIdxDev)) ∧
    (∃ f : Ty.den normalizeThmTy, G'[803]? = some ⟨normalizeThmTy, f⟩ ∧
      ∀ rules j defs infer dev,
        f (rules.map encRw) (leaf j) (defs.map encDefn) (ofBool infer) (dev.map encDevEntry) =
          encOpt ((Prover.normalizeThm rules j defs infer dev).map Combinator.encIdxDev)) ∧
    (∃ f : Ty.den instByTy, G'[804]? = some ⟨instByTy, f⟩ ∧
      ∀ rules s σ, Combinator.PMRel Combinator.encEqC (f (rules.map encRw) (encSrc s) σ)
        (Prover.instBy rules s σ)) ∧
    (∃ f : Ty.den natIndPMTy, G'[809]? = some ⟨natIndPMTy, f⟩ ∧
      ∀ rules z s q, Combinator.PMRel id (f (rules.map encRw) z s (encEqn q))
        (Prover.byNatInduction rules z s q)) ∧
    (∃ f : Ty.den listIndPMTy, G'[810]? = some ⟨listIndPMTy, f⟩ ∧
      ∀ rules a z s q, Combinator.PMRel id (f (rules.map encRw) a z s (encEqn q))
        (Prover.byListInduction rules a z s q)) ∧
    (∃ f : Ty.den listIndPMTy, G'[811]? = some ⟨listIndPMTy, f⟩ ∧
      ∀ rules a z s q, Combinator.PMRel id (f (rules.map encRw) a z s (encEqn q))
        (Prover.byListParamInduction rules a z s q)) ∧
    (∃ f : Ty.den treeFnTy, G'[827]? = some ⟨treeFnTy, f⟩ ∧
      ∀ infer, f (ofBool infer) = encLib (Prover.libraryWith infer)) ∧
    (∃ f : Ty.den libRulesTy, G'[828]? = some ⟨libRulesTy, f⟩ ∧
      ∀ i, f (encIdx i) = (Prover.rules i).map encRw) :=
  ⟨_, metalogic.load_globals, ⟨_, metalogic_typeTerm, Combinator.typeTerm_rel⟩,
    ⟨_, metalogic_pNormalize, Combinator.normalize_rel⟩,
    ⟨_, metalogic_pInst, Combinator.inst_rel⟩, ⟨_, metalogic_etaExpand, Combinator.etaExpand_rel⟩,
    ⟨_, metalogic_deltaRule, Combinator.deltaRule_eq⟩,
    ⟨_, metalogic_pByNorm, Combinator.byNorm_rel⟩,
    ⟨_, metalogic_proveSeq, Combinator.proveSeq_eq⟩,
    ⟨_, metalogic_normalizeThm, Combinator.normalizeThm_eq⟩,
    ⟨_, metalogic_instBy, Combinator.instBy_rel⟩,
    ⟨_, metalogic_byNatInduction, Combinator.byNatInduction_rel⟩,
    ⟨_, metalogic_byListInduction, Combinator.byListInduction_rel⟩,
    ⟨_, metalogic_byListParamInduction, Combinator.byListParamInduction_rel⟩,
    ⟨_, metalogic_libraryWith, Combinator.libraryWith_eq⟩,
    ⟨_, metalogic_libRules, Combinator.libRules_eq⟩⟩

/-- The reader written in Geb inverts the printer written in Geb: the program loads to globals
among which are the partial printer of kernel terms and the reader's resolution with no type
abbreviations, at their types; the printer gives the encoding of what the Lean printer gives at
every term, names of definitions and depth; the resolution, at encoded names of definitions and
names in scope, gives the encoding of the Lean reader's resolution of every S-expression; and
whatever the printer writes for a term under binders to a depth resolves, in the scope of those
binders, to the term. -/
theorem reader_inverse_agree : ∃ G' : List Glob, load metalogic = some G' ∧
    ∃ pr : Ty.den printTermTy, G'[946]? = some ⟨printTermTy, pr⟩ ∧
    ∃ rb : Ty.den readBackTy, G'[936]? = some ⟨readBackTy, rb⟩ ∧
      (∀ (defs : List (List Char)) (t : Tree) (d : ℕ),
        pr (defs.map nameTree) t (leaf d) = encOpt ((printTerm? defs t d).map sexpTree)) ∧
      (∀ (defs : List (List Char)) (e : SExp) (scope : List (List Char)),
        rb (defs.map nameTree) (sexpTree e) (scope.map nameTree) =
          encOpt (resolve [] defs e scope)) ∧
      (∀ (defs : List (List Char)) (t : Tree) (d : ℕ) (e : Tree),
        pr (defs.map nameTree) t (leaf d) = encOpt (some e) →
          rb (defs.map nameTree) e ((scopeOf d).map nameTree) = encOpt (some t)) :=
  ⟨_, metalogic.load_globals, «Printer.printTermOpt», metalogic_printTermOpt, «Printer.readBack»,
    metalogic_readBack, Reader.printTermOpt_eq, Reader.readBack_eq,
    Reader.readBack_printTermOpt_eq⟩

end GebTests.Prototypes.FreeTopos.Agreement

end
