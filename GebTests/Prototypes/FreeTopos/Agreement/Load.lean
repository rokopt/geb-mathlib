/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic.Load
public import GebTests.Prototypes.ProgramCommand
public import GebTests.Prototypes.CheckMirror

set_option doc.verso true in
/-!
# The metalogic's checker, translation, provers and tactics written in Geb, loaded by the kernel

The bootstrap compiler's Lean backend emits the checker of the metalogic written in Geb,
{lit}`bootstrap/free-topos/`, with the kernel's checker it translates the kernel's terms by, the
translation of the kernel into the internal language, the prover of the internal language, its
tactics and the combinator prover, as Lean definitions, one for each of the program's
definitions: the program's mirror, {lit}`GebMirror.Metalogic`. This module states, and in the
loading mode {lit}`rfl` the kernel checks, that loading the program with {name}`Geb.Kernel.load`
gives globals whose denotations are the mirror's definitions; in the mode {lit}`native` the steps
of the loading are axioms ({lit}`docs/rules/ci-and-workflow.md` § Loading modes).

The command {lit}`geb_program` of {lit}`GebTests.Prototypes.ProgramCommand` declares the
program's definitions, globals and loading, one definition at a time. Among the globals are the
check of a development, at the type of the function from constants, entries and declarations to a
state; the translations of a program, of its constants and of a theorem of Gödel's T; and the
prover's entry points, the preparation of rules, the proofs by normalization and by induction and
the provers built from provers; the tactics' entry points, the proofs by reduction, case
analysis, induction, hypotheses and search; and the combinator prover's entry points, the typing,
normalization, the proofs by normalization and by induction, the proof of a sequent added to a
development and the library; the partial printer of kernel terms and the reader's resolution
of what it prints; and the checker's functions the checker of a development is built from, the
partial Horn checker of the combinators' certificates, the theory, the inference of typings and
the step of a development, with the tactics' functions of terms. Each
type is read from the definition, whose abstractions carry their types and whose body the front end
applies the identity at the result type to, by inverting the checker-evaluator: for the tactics,
the combinator prover, the printer and the checker's functions, by one lemma over the list of the
abstractions' annotations, {lit}`infer_lams`. The theory, a definition without a declared result
type, has the type the checker-evaluator infers, which the kernel evaluates.

## Main definitions

* {lit}`checkDevTy` — the type of the check of a development written in Geb.
* {lit}`listFnTy`, {lit}`thmTy` — the types of the translations of a program and of its constants,
  and of a theorem.
* {lit}`rulesTy`, {lit}`proverTy` — the types of the normalizer's rules with their matchings and
  of a prover of equations, and the types of the prover's entry points built from them.
* {lit}`krTy`, {lit}`modeTy` and the tactics' other types — the types of a prover from rules and of
  the tactics' entry points.
* {lit}`pmTy`, {lit}`proveSeqTy` and the combinator prover's other types — the types of a
  computation of the combinator prover and of its entry points.
* {lit}`printTermTy`, {lit}`readBackTy` — the types of the printer of kernel terms and of the
  reader's resolution of what it prints.
* {lit}`pcheckTy`, {lit}`infersTy` — the types of the checker of a certificate and of the
  inferences at a fuel.

## Main statements

* {lit}`metalogic.load_globals` — the program loads to its globals, listed one by one, so that
  the kernel reaches each of them in as many steps as its index.
* {lit}`infer_lams` — the type inferred for a definition is the arrows from its parameters'
  annotations to its result type.
* {lit}`checkDev_type`, {lit}`program_type`, {lit}`trGlobals_type`, {lit}`thm_type`, and
  {lit}`byNorm_type` with the prover's other entry points — the types the kernel computes for
  those definitions, read from the definitions' annotations by inverting the checker-evaluator,
  without evaluating it.
* {lit}`metalogic_checkDev`, {lit}`metalogic_program`, {lit}`metalogic_trGlobals`,
  {lit}`metalogic_thm`, {lit}`metalogic_byNorm` with the prover's other entry points, and
  {lit}`metalogic_byMode` with the tactics' other entry points, and {lit}`metalogic_proveSeq`
  with the combinator prover's other entry points, and {lit}`metalogic_printTermOpt` and
  {lit}`metalogic_readBack`, and {lit}`metalogic_pcheck` with the checker's other functions and
  {lit}`metalogic_openSubterms` with the tactics' other functions of terms — those globals are the
  mirror's definitions, at those types.

## Tags

metalogic, checker, translation, prover, tactic, combinator, development, denotation, mirror,
kernel reduction
-/

set_option doc.verso true

@[expose] public section

open GebMirror.Metalogic

namespace GebTests.Prototypes.FreeTopos.Agreement.Load

open Geb Geb.Kernel GebTests.Prototypes.CheckMirror

/-- A global at a type and a denotation, from its type and its denotation's equality to the
denotation given, which the expected type names, so that no definition is unfolded to compare it
with itself. -/
theorem glob_ext {g : Glob} {A : Tree} {f : Ty.den A} (h : g.1 = A) (hf : HEq g.2 f) :
    g = ⟨A, f⟩ :=
  Sigma.ext h hf

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
-- the generated modules of GebMirror.Metalogic.Load declare the program's definitions and the
-- steps of its loading; the kernel evaluates the checker-evaluator on each exported definition
set_option Elab.async false in
geb_program _root_.GebMirror.metalogic from "bootstrap/prelude.geb" "bootstrap/seq.geb"
  "bootstrap/free-topos/base.geb"
  "bootstrap/free-topos/partial-horn.geb" "bootstrap/free-topos/theory.geb"
  "bootstrap/free-topos/infer.geb" "bootstrap/free-topos/language.geb"
  "bootstrap/free-topos/derivation.geb" "bootstrap/reader.geb" "bootstrap/check.geb"
  "bootstrap/free-topos/translation.geb" "bootstrap/free-topos/prove.geb"
  "bootstrap/free-topos/tactics.geb" "bootstrap/free-topos/combinator.geb" "bootstrap/datatype.geb"
  "bootstrap/printer.geb"
  mirror GebMirror.Metalogic
  exports «Derivation.checkDev» «Translation.program» «Translation.trGlobals» «Translation.thm»
    «Prover.prepareRules» «Prover.byNorm» «Prover.byNatInd» «Prover.byListInd» «Prover.byNatIndHyp»
    «Prover.byListIndHyp» «Prover.byNormW» «Prover.byFunExt» «Prover.bySplit» «Prover.byListIndWith»
    «Prover.byRoseInd» «Prover.byRoseIndHyp» «Tactics.byMode» «Tactics.byWeak» «Tactics.byNF»
    «Tactics.normH» «Tactics.funExts» «Tactics.byListIndWeak» «Tactics.byRoseIndWith»
    «Tactics.byListSplit» «Tactics.bySplit2» «Tactics.byListCases» «Tactics.bitsInd»
    «Tactics.bitsCases» «Tactics.byBits» «Tactics.byLength3» «Tactics.withWeakHyps»
    «Tactics.byListIndHypWeak» «Tactics.byBitsIndHyp» «Tactics.withInsts» «Tactics.withChildHyps»
    «Tactics.revertCase» «Tactics.byImpI» «Tactics.withImpElim» «Tactics.bySuccPred»
    «Tactics.byInsts» «Tactics.byAuto» «Tactics.byTreeSplit» «Tactics.byAutoT» «Tactics.byAutoC»
    «Tactics.maskRw» «Tactics.byMaskSubs» «Tactics.byGeneralize» «Combinator.typeTerm»
    «Combinator.pNormalize» «Combinator.pInst» «Combinator.etaExpand» «Combinator.deltaRule»
    «Combinator.pByNorm» «Combinator.proveSeq» «Combinator.normalizeThm» «Combinator.instBy»
    «Combinator.byNatInduction» «Combinator.byListInduction» «Combinator.byListParamInduction»
    «Combinator.libraryWith» «Combinator.libRules» «Printer.printTermOpt» «Printer.readBack»
    «PartialHorn.sortOf» «PartialHorn.scoped» «PartialHorn.phSubst» «PartialHorn.pcheck»
    «PartialHorn.thyExtendAll» «Theory.toposTheory» «Infer.envOfDefs» «Infer.infers»
    «Derivation.declStep» «Tactics.openSubterms» «Tactics.stuckVar» «Tactics.mentions»
    «Tactics.matchesOf» «Tactics.condParts» «Tactics.stuckVarC» «Tactics.appsOf»
    «Tactics.unnodeU» «Tactics.occRewrite» «Tactics.abstractTerm»

open GebMirror (metalogic)

/-- The type of the check of a development written in Geb: from the constants, the entries and
the declarations, to the optional state after them. -/
def checkDevTy : Tree := tArrow tT (tArrow (tList tT) (tArrow (tList tT) tT))

/-- The type the kernel computes for the check's definition is the check's type: the three
abstractions' annotations, over the declared result type, at which the front end applies the
identity to the definition's body. -/
theorem checkDev_type : metalogic.g872.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step872
  generalize metalogic.g872.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global of index 872
kernel_rfl metalogic_g872 : metalogic.globals[872]? = some metalogic.g872

/-- The program's global of index 872 is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.globals[872]? = some (⟨checkDevTy, «Derivation.checkDev»⟩ : Glob) :=
  metalogic_g872.trans
    (congrArg some (glob_ext checkDev_type metalogic.«Derivation.checkDev_heq»))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g1104.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1104
  generalize metalogic.g1104.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g1105.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1105
  generalize metalogic.g1105.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g1122.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step1122
  generalize metalogic.g1122.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 1104, 1105 and 1122
kernel_rfl metalogic_g1104 : metalogic.globals[1104]? = some metalogic.g1104
kernel_rfl metalogic_g1105 : metalogic.globals[1105]? = some metalogic.g1105
kernel_rfl metalogic_g1122 : metalogic.globals[1122]? = some metalogic.g1122

/-- The program's global of index 1104 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[1104]? = some (⟨listFnTy, «Translation.program»⟩ : Glob) :=
  metalogic_g1104.trans
    (congrArg some (glob_ext program_type metalogic.«Translation.program_heq»))

/-- The program's global of index 1105 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[1105]? = some (⟨listFnTy, «Translation.trGlobals»⟩ : Glob) :=
  metalogic_g1105.trans
    (congrArg some (glob_ext trGlobals_type metalogic.«Translation.trGlobals_heq»))

/-- The program's global of index 1122 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[1122]? = some (⟨thmTy, «Translation.thm»⟩ : Glob) :=
  metalogic_g1122.trans
    (congrArg some (glob_ext thm_type metalogic.«Translation.thm_heq»))

/-- The type of the normalizer's rules. -/
def rulesTy : Tree := tList tT

/-- The type of a prover of equations: from a context, hypotheses and two sides to an optional
derivation. -/
def proverTy : Tree := tArrow (tList tT) (tArrow (tList tT) (tArrow tT (tArrow tT tT)))

/-- The type of the preparation of rules: from the entries and the encoded rules to the rules
with their matchings. -/
def prepareTy : Tree := tArrow (tList tT) (tArrow (tList tT) rulesTy)

/-- The type of a proof by normalization: from the constants, the entries, the number of
definitions, the rules and the fuel to a prover. -/
def normTy : Tree := tArrow tT (tArrow (tList tT) (tArrow tT (tArrow rulesTy (tArrow tT proverTy))))

/-- The type of a proof by induction with a step: from the constants, the entries, the number
of definitions, the two primitives, the step, the rules and the fuel to a prover. -/
def indTy : Tree :=
  tArrow tT (tArrow (tList tT) (tArrow tT (tArrow tT (tArrow tT (tArrow tT (tArrow rulesTy
    (tArrow tT proverTy)))))))

/-- The type of a proof by induction with the induction hypothesis: from the constants, the
entries, the number of definitions, the two primitives, the rules and the fuel to a prover. -/
def indHypTy : Tree :=
  tArrow tT (tArrow (tList tT) (tArrow tT (tArrow tT (tArrow tT (tArrow rulesTy
    (tArrow tT proverTy))))))

/-- The type of a proof by extensionality: from the constants, the number of definitions and a
prover to a prover. -/
def funExtTy : Tree := tArrow tT (tArrow tT (tArrow proverTy proverTy))

/-- The type of a prover from three numbers and a prover: the case analysis on a variable, and
the induction on a rose tree with the induction hypothesis. -/
def proverFnTy : Tree := tArrow tT (tArrow tT (tArrow tT (tArrow proverTy proverTy)))

/-- The type of a proof by induction on a list with the premises' provers: from the constants,
the number of definitions, the two primitives and two provers to a prover. -/
def listIndWithTy : Tree :=
  tArrow tT (tArrow tT (tArrow tT (tArrow tT (tArrow proverTy (tArrow proverTy proverTy)))))

/-- The type of a proof by the uniqueness of the fold of a rose tree: from the constants, the
entries, the number of definitions, the three primitives, the step, the rules, the fuel, the
context and the two sides to an optional derivation. -/
def roseIndTy : Tree :=
  tArrow tT (tArrow (tList tT) (tArrow tT (tArrow tT (tArrow tT (tArrow tT (tArrow tT
    (tArrow rulesTy (tArrow tT (tArrow (tList tT) (tArrow tT (tArrow tT tT)))))))))))

/-- The type the kernel computes for the preparation of rules is its type, read from the
definition's annotations. -/
theorem prepareRules_type : metalogic.g1176.1 = prepareTy := by
  have h := infer_of_loadStep metalogic.step1176
  generalize metalogic.g1176.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by normalization is its type, read from the
definition's annotations. -/
theorem byNorm_type : metalogic.g1255.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1255
  generalize metalogic.g1255.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, _, h10, -, -⟩ := infer_app_inv h9
  obtain ⟨_, _, hB, h11⟩ := infer_lam_inv h10
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h11.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by induction on a natural number with a step is its
type, read from the definition's annotations. -/
theorem byNatInd_type : metalogic.g1257.1 = indTy := by
  have h := infer_of_loadStep metalogic.step1257
  generalize metalogic.g1257.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, rfl, h10⟩ := infer_lam_inv h9
  obtain ⟨_, _, rfl, h11⟩ := infer_lam_inv h10
  obtain ⟨_, _, rfl, h12⟩ := infer_lam_inv h11
  obtain ⟨_, _, _, h13, -, -⟩ := infer_app_inv h12
  obtain ⟨_, _, hB, h14⟩ := infer_lam_inv h13
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h14.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by induction on a list with a step is its type, read
from the definition's annotations. -/
theorem byListInd_type : metalogic.g1258.1 = indTy := by
  have h := infer_of_loadStep metalogic.step1258
  generalize metalogic.g1258.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, rfl, h10⟩ := infer_lam_inv h9
  obtain ⟨_, _, rfl, h11⟩ := infer_lam_inv h10
  obtain ⟨_, _, rfl, h12⟩ := infer_lam_inv h11
  obtain ⟨_, _, _, h13, -, -⟩ := infer_app_inv h12
  obtain ⟨_, _, hB, h14⟩ := infer_lam_inv h13
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h14.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by induction on a natural number with the induction
hypothesis is its type, read from the definition's annotations. -/
theorem byNatIndHyp_type : metalogic.g1260.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step1260
  generalize metalogic.g1260.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, rfl, h10⟩ := infer_lam_inv h9
  obtain ⟨_, _, rfl, h11⟩ := infer_lam_inv h10
  obtain ⟨_, _, _, h12, -, -⟩ := infer_app_inv h11
  obtain ⟨_, _, hB, h13⟩ := infer_lam_inv h12
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h13.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by induction on a list with the induction hypothesis
is its type, read from the definition's annotations. -/
theorem byListIndHyp_type : metalogic.g1261.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step1261
  generalize metalogic.g1261.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, rfl, h10⟩ := infer_lam_inv h9
  obtain ⟨_, _, rfl, h11⟩ := infer_lam_inv h10
  obtain ⟨_, _, _, h12, -, -⟩ := infer_app_inv h11
  obtain ⟨_, _, hB, h13⟩ := infer_lam_inv h12
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h13.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by normalization through weak head normal forms is
its type, read from the definition's annotations. -/
theorem byNormW_type : metalogic.g1311.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1311
  generalize metalogic.g1311.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, _, h10, -, -⟩ := infer_app_inv h9
  obtain ⟨_, _, hB, h11⟩ := infer_lam_inv h10
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h11.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by extensionality is its type, read from the
definition's annotations. -/
theorem byFunExt_type : metalogic.g1313.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step1313
  generalize metalogic.g1313.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by case analysis is its type, read from the
definition's annotations. -/
theorem bySplit_type : metalogic.g1314.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1314
  generalize metalogic.g1314.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, _, h5, -, -⟩ := infer_app_inv h4
  obtain ⟨_, _, hB, h6⟩ := infer_lam_inv h5
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h6.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by induction on a list with the premises' provers is
its type, read from the definition's annotations. -/
theorem byListIndWith_type : metalogic.g1315.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step1315
  generalize metalogic.g1315.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, _, h7, -, -⟩ := infer_app_inv h6
  obtain ⟨_, _, hB, h8⟩ := infer_lam_inv h7
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h8.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by the uniqueness of the fold of a rose tree is its
type, read from the definition's annotations. -/
theorem byRoseInd_type : metalogic.g1316.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step1316
  generalize metalogic.g1316.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, rfl, h5⟩ := infer_lam_inv h4
  obtain ⟨_, _, rfl, h6⟩ := infer_lam_inv h5
  obtain ⟨_, _, rfl, h7⟩ := infer_lam_inv h6
  obtain ⟨_, _, rfl, h8⟩ := infer_lam_inv h7
  obtain ⟨_, _, rfl, h9⟩ := infer_lam_inv h8
  obtain ⟨_, _, rfl, h10⟩ := infer_lam_inv h9
  obtain ⟨_, _, rfl, h11⟩ := infer_lam_inv h10
  obtain ⟨_, _, rfl, h12⟩ := infer_lam_inv h11
  obtain ⟨_, _, _, h13, -, -⟩ := infer_app_inv h12
  obtain ⟨_, _, hB, h14⟩ := infer_lam_inv h13
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h14.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by induction on a rose tree with the induction
hypothesis is its type, read from the definition's annotations. -/
theorem byRoseIndHyp_type : metalogic.g1317.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1317
  generalize metalogic.g1317.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, rfl, h4⟩ := infer_lam_inv h3
  obtain ⟨_, _, _, h5, -, -⟩ := infer_app_inv h4
  obtain ⟨_, _, hB, h6⟩ := infer_lam_inv h5
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h6.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the prover's entry points are the program's globals of indices 1176 to 1312
kernel_rfl metalogic_g1176 : metalogic.globals[1176]? = some metalogic.g1176
kernel_rfl metalogic_g1255 : metalogic.globals[1255]? = some metalogic.g1255
kernel_rfl metalogic_g1257 : metalogic.globals[1257]? = some metalogic.g1257
kernel_rfl metalogic_g1258 : metalogic.globals[1258]? = some metalogic.g1258
kernel_rfl metalogic_g1260 : metalogic.globals[1260]? = some metalogic.g1260
kernel_rfl metalogic_g1261 : metalogic.globals[1261]? = some metalogic.g1261
kernel_rfl metalogic_g1311 : metalogic.globals[1311]? = some metalogic.g1311
kernel_rfl metalogic_g1313 : metalogic.globals[1313]? = some metalogic.g1313
kernel_rfl metalogic_g1314 : metalogic.globals[1314]? = some metalogic.g1314
kernel_rfl metalogic_g1315 : metalogic.globals[1315]? = some metalogic.g1315
kernel_rfl metalogic_g1316 : metalogic.globals[1316]? = some metalogic.g1316
kernel_rfl metalogic_g1317 : metalogic.globals[1317]? = some metalogic.g1317

/-- The program's global of index 1176 is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[1176]? = some (⟨prepareTy, «Prover.prepareRules»⟩ : Glob) :=
  metalogic_g1176.trans (congrArg some (glob_ext
    prepareRules_type metalogic.«Prover.prepareRules_heq»))

/-- The program's global of index 1255 is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[1255]? = some (⟨normTy, «Prover.byNorm»⟩ : Glob) :=
  metalogic_g1255.trans (congrArg some (glob_ext
    byNorm_type metalogic.«Prover.byNorm_heq»))

/-- The program's global of index 1257 is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[1257]? = some (⟨indTy, «Prover.byNatInd»⟩ : Glob) :=
  metalogic_g1257.trans (congrArg some (glob_ext
    byNatInd_type metalogic.«Prover.byNatInd_heq»))

/-- The program's global of index 1258 is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[1258]? = some (⟨indTy, «Prover.byListInd»⟩ : Glob) :=
  metalogic_g1258.trans (congrArg some (glob_ext
    byListInd_type metalogic.«Prover.byListInd_heq»))

/-- The program's global of index 1260 is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[1260]? = some (⟨indHypTy, «Prover.byNatIndHyp»⟩ : Glob) :=
  metalogic_g1260.trans (congrArg some (glob_ext
    byNatIndHyp_type metalogic.«Prover.byNatIndHyp_heq»))

/-- The program's global of index 1261 is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[1261]? = some (⟨indHypTy, «Prover.byListIndHyp»⟩ : Glob) :=
  metalogic_g1261.trans (congrArg some (glob_ext
    byListIndHyp_type metalogic.«Prover.byListIndHyp_heq»))

/-- The program's global of index 1311 is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[1311]? = some (⟨normTy, «Prover.byNormW»⟩ : Glob) :=
  metalogic_g1311.trans (congrArg some (glob_ext
    byNormW_type metalogic.«Prover.byNormW_heq»))

/-- The program's global of index 1313 is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[1313]? = some (⟨funExtTy, «Prover.byFunExt»⟩ : Glob) :=
  metalogic_g1313.trans (congrArg some (glob_ext
    byFunExt_type metalogic.«Prover.byFunExt_heq»))

/-- The program's global of index 1314 is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[1314]? = some (⟨proverFnTy, «Prover.bySplit»⟩ : Glob) :=
  metalogic_g1314.trans (congrArg some (glob_ext
    bySplit_type metalogic.«Prover.bySplit_heq»))

/-- The program's global of index 1315 is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[1315]? = some (⟨listIndWithTy, «Prover.byListIndWith»⟩ : Glob) :=
  metalogic_g1315.trans (congrArg some (glob_ext
    byListIndWith_type metalogic.«Prover.byListIndWith_heq»))

/-- The program's global of index 1316 is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[1316]? = some (⟨roseIndTy, «Prover.byRoseInd»⟩ : Glob) :=
  metalogic_g1316.trans (congrArg some (glob_ext
    byRoseInd_type metalogic.«Prover.byRoseInd_heq»))

/-- The program's global of index 1317 is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[1317]? = some (⟨proverFnTy, «Prover.byRoseIndHyp»⟩ : Glob) :=
  metalogic_g1317.trans (congrArg some (glob_ext
    byRoseIndHyp_type metalogic.«Prover.byRoseIndHyp_heq»))

/-! The tactics. -/

/-- The type an abstraction over annotations of the identity at a type applied to a body is
inferred: the arrows from the annotations to that type. The front end gives each definition that
form, over its parameters' annotations and its declared result type. -/
theorem infer_lams {G : List Glob} (B x : Tree) (as : List Tree) :
    ∀ {Γ : Ctx} {T : Tree} {f : Γ.den → Ty.den T},
      infer G Γ (as.foldr (fun a b ↦ mk Label.lam [a, b])
        (mk Label.app [mk Label.lam [B, Tm.var 0], x])) = some ⟨T, f⟩ →
        T = as.foldr tArrow B := by
  refine List.rec (motive := fun as ↦ ∀ {Γ : Ctx} {T : Tree} {f : Γ.den → Ty.den T},
      infer G Γ (as.foldr (fun a b ↦ mk Label.lam [a, b])
        (mk Label.app [mk Label.lam [B, Tm.var 0], x])) = some ⟨T, f⟩ →
        T = as.foldr tArrow B) (fun h ↦ ?_) (fun a as ih ↦ fun h ↦ ?_) as
  · obtain ⟨_, _, _, h1, -, -⟩ := infer_app_inv h
    obtain ⟨_, _, hB, h2⟩ := infer_lam_inv h1
    rw [(tArrow_inj hB).2,
      (Sigma.mk.inj_iff.mp (Option.some.inj (h2.symm.trans (infer_var0 _ _ _)))).1]
    rfl
  · obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h
    rw [ih h1]
    rfl

/-- The type of a prover from rules: from the rules to a prover. -/
def krTy : Tree := tArrow rulesTy proverTy

/-- The type of lists of lists of trees. -/
def tssTy : Tree := tList (tList tT)

/-- The type of a proof by reduction at a depth: from the depth, the constants, the entries, the
number of definitions and the rules to a prover. -/
def modeTy : Tree := [tT, tT, tList tT, tT, rulesTy].foldr tArrow proverTy

/-- The type of a proof from the constants, the entries, the number of definitions and the rules. -/
def rulesProverTy : Tree := [tT, tList tT, tT, rulesTy].foldr tArrow proverTy

/-- The type of a proof by the proof of the sides' normal forms at a depth, a prover. -/
def nfTy : Tree := [tT, tList tT, tT, rulesTy, tT, proverTy].foldr tArrow proverTy

/-- The type of a proof from the constants, the entries and the rules. -/
def normHTy : Tree := [tT, tList tT, rulesTy].foldr tArrow proverTy

/-- The type of a proof by induction with a step: from the constants, the entries, the number of
definitions, the step and the rules. -/
def listIndWeakTy : Tree := [tT, tList tT, tT, tT, rulesTy].foldr tArrow proverTy

/-- The type of a proof by case analysis of a variable: from three numbers and a prover for each
case. -/
def splitTy : Tree := [tT, tT, tT, proverTy, proverTy].foldr tArrow proverTy

/-- The type of a prover from two numbers and two provers. -/
def twoProverTy : Tree := [tT, tT, proverTy, proverTy].foldr tArrow proverTy

/-- The type of a proof by case analysis of bitstrings to a depth: from the constants, a prover, the
depth and a variable. -/
def byBitsTy : Tree := [tT, proverTy, tT].foldr tArrow (tArrow tT proverTy)

/-- The type of a proof with hypotheses cut in in normal form, the rules added given to a prover
from rules. -/
def weakHypsTy : Tree := [tT, tList tT, tT, rulesTy, tList tT, krTy, tT].foldr tArrow proverTy

/-- The type of a proof by induction on a bitstring with the induction hypothesis as a rule. -/
def bitsIndHypTy : Tree := [tT, tList tT, rulesTy, tT].foldr tArrow proverTy

/-- The type of a proof with a hypothesis's instances at lists of arguments cut in. -/
def instsTy : Tree := [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT].foldr tArrow proverTy

/-- The type of a proof with the hypotheses at the children of an induction on rose trees. -/
def childHypsTy : Tree :=
  [tT, tList tT, tT, rulesTy,
    tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy].foldr tArrow proverTy

/-- The type of a proof by case analysis of a list variable with a hypothesis reverted. -/
def revertTy : Tree := [tT, tT, tT, tT, tT, tT, proverTy, proverTy].foldr tArrow proverTy

/-- The type of a proof of an implication by its introduction. -/
def impITy : Tree := [tT, tList tT, tT, tT, proverTy].foldr tArrow proverTy

/-- The type of a proof with implications eliminated. -/
def impElimTy : Tree := [tT, tT, tT, tList tT, krTy].foldr tArrow proverTy

/-- The type of a proof by rewriting a predecessor's successor. -/
def succPredTy : Tree := [tList tT, tT, proverTy].foldr tArrow proverTy

/-- The type of a proof by the instance search: from the depth, the constants, the entries, the
number of definitions, the rules and the number of hypotheses searched. -/
def instsSearchTy : Tree := [tT, tT, tList tT, tT, rulesTy, tT].foldr tArrow proverTy

/-- The type of a proof by search to a depth: from the constants, the entries, the number of
definitions, the rules, the depth and the depth of reduction. -/
def autoTy : Tree := [tT, tList tT, tT, rulesTy, tT, tT].foldr tArrow proverTy

/-- The type of a proof by search splitting trees: the arguments of {name}`autoTy` with Lambek's
lemma's index. -/
def autoTTy : Tree := [tT, tList tT, tT, tT, rulesTy, tT, tT].foldr tArrow proverTy

/-- The type of a proof by search splitting folded conditionals' tests: from the constants, the
entries, the number of definitions, Lambek's lemma's index, the rules and the depth. -/
def autoCTy : Tree := [tT, tList tT, tT, tT, rulesTy, tT].foldr tArrow proverTy

/-- The type of a derivation of a rewriting under a conditional's mask by a masked lemma. -/
def maskRwTy : Tree := [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT].foldr tArrow tT

/-- The type of a proof by rewriting under masks: from the constants, the entries, two lemmas'
indices, the rules and the number of rounds to a prover from a prover from rules. -/
def maskSubsTy : Tree := [tT, tList tT, tT, tT, rulesTy, tT].foldr tArrow (tArrow krTy proverTy)

-- the tactics' entry points are the program's globals of indices 1334 to 1443
kernel_rfl metalogic_g1334 : metalogic.globals[1334]? = some metalogic.g1334
kernel_rfl metalogic_g1335 : metalogic.globals[1335]? = some metalogic.g1335
kernel_rfl metalogic_g1336 : metalogic.globals[1336]? = some metalogic.g1336
kernel_rfl metalogic_g1340 : metalogic.globals[1340]? = some metalogic.g1340
kernel_rfl metalogic_g1341 : metalogic.globals[1341]? = some metalogic.g1341
kernel_rfl metalogic_g1342 : metalogic.globals[1342]? = some metalogic.g1342
kernel_rfl metalogic_g1343 : metalogic.globals[1343]? = some metalogic.g1343
kernel_rfl metalogic_g1345 : metalogic.globals[1345]? = some metalogic.g1345
kernel_rfl metalogic_g1346 : metalogic.globals[1346]? = some metalogic.g1346
kernel_rfl metalogic_g1347 : metalogic.globals[1347]? = some metalogic.g1347
kernel_rfl metalogic_g1348 : metalogic.globals[1348]? = some metalogic.g1348
kernel_rfl metalogic_g1349 : metalogic.globals[1349]? = some metalogic.g1349
kernel_rfl metalogic_g1350 : metalogic.globals[1350]? = some metalogic.g1350
kernel_rfl metalogic_g1351 : metalogic.globals[1351]? = some metalogic.g1351
kernel_rfl metalogic_g1364 : metalogic.globals[1364]? = some metalogic.g1364
kernel_rfl metalogic_g1365 : metalogic.globals[1365]? = some metalogic.g1365
kernel_rfl metalogic_g1366 : metalogic.globals[1366]? = some metalogic.g1366
kernel_rfl metalogic_g1370 : metalogic.globals[1370]? = some metalogic.g1370
kernel_rfl metalogic_g1372 : metalogic.globals[1372]? = some metalogic.g1372
kernel_rfl metalogic_g1374 : metalogic.globals[1374]? = some metalogic.g1374
kernel_rfl metalogic_g1376 : metalogic.globals[1376]? = some metalogic.g1376
kernel_rfl metalogic_g1377 : metalogic.globals[1377]? = some metalogic.g1377
kernel_rfl metalogic_g1380 : metalogic.globals[1380]? = some metalogic.g1380
kernel_rfl metalogic_g1399 : metalogic.globals[1399]? = some metalogic.g1399
kernel_rfl metalogic_g1401 : metalogic.globals[1401]? = some metalogic.g1401
kernel_rfl metalogic_g1423 : metalogic.globals[1423]? = some metalogic.g1423
kernel_rfl metalogic_g1425 : metalogic.globals[1425]? = some metalogic.g1425
kernel_rfl metalogic_g1426 : metalogic.globals[1426]? = some metalogic.g1426
kernel_rfl metalogic_g1430 : metalogic.globals[1430]? = some metalogic.g1430
kernel_rfl metalogic_g1447 : metalogic.globals[1447]? = some metalogic.g1447
kernel_rfl metalogic_g1448 : metalogic.globals[1448]? = some metalogic.g1448

/-- The program's global of index 1334 is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[1334]? = some (⟨modeTy, «Tactics.byMode»⟩ : Glob) :=
  metalogic_g1334.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1334).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byMode_heq»))

/-- The program's global of index 1335 is the mirror's proof by reduction to one weak normal form,
at its type. -/
theorem metalogic_byWeak :
    metalogic.globals[1335]? = some (⟨rulesProverTy, «Tactics.byWeak»⟩ : Glob) :=
  metalogic_g1335.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1335).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byWeak_heq»))

/-- The program's global of index 1336 is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[1336]? = some (⟨nfTy, «Tactics.byNF»⟩ : Glob) :=
  metalogic_g1336.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1336).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    metalogic.«Tactics.byNF_heq»))

/-- The program's global of index 1340 is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[1340]? = some (⟨normHTy, «Tactics.normH»⟩ : Glob) :=
  metalogic_g1340.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1340).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    metalogic.«Tactics.normH_heq»))

/-- The program's global of index 1341 is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[1341]? = some (⟨funExtTy, «Tactics.funExts»⟩ : Glob) :=
  metalogic_g1341.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1341).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.funExts_heq»))

/-- The program's global of index 1342 is the mirror's proof by induction on a list with a step,
both cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[1342]? = some (⟨listIndWeakTy, «Tactics.byListIndWeak»⟩ : Glob) :=
  metalogic_g1342.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1342).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    metalogic.«Tactics.byListIndWeak_heq»))

/-- The program's global of index 1343 is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[1343]? = some (⟨proverFnTy, «Tactics.byRoseIndWith»⟩ : Glob) :=
  metalogic_g1343.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1343).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    metalogic.«Tactics.byRoseIndWith_heq»))

/-- The program's global of index 1345 is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[1345]? = some (⟨splitTy, «Tactics.byListSplit»⟩ : Glob) :=
  metalogic_g1345.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1345).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.byListSplit_heq»))

/-- The program's global of index 1346 is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[1346]? = some (⟨splitTy, «Tactics.bySplit2»⟩ : Glob) :=
  metalogic_g1346.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1346).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.bySplit2_heq»))

/-- The program's global of index 1347 is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[1347]? = some (⟨funExtTy, «Tactics.byListCases»⟩ : Glob) :=
  metalogic_g1347.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1347).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byListCases_heq»))

/-- The program's global of index 1348 is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[1348]? = some (⟨twoProverTy, «Tactics.bitsInd»⟩ : Glob) :=
  metalogic_g1348.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1348).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.bitsInd_heq»))

/-- The program's global of index 1349 is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[1349]? = some (⟨funExtTy, «Tactics.bitsCases»⟩ : Glob) :=
  metalogic_g1349.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1349).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.bitsCases_heq»))

/-- The program's global of index 1350 is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[1350]? = some (⟨byBitsTy, «Tactics.byBits»⟩ : Glob) :=
  metalogic_g1350.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1350).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    metalogic.«Tactics.byBits_heq»))

/-- The program's global of index 1351 is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[1351]? = some (⟨twoProverTy, «Tactics.byLength3»⟩ : Glob) :=
  metalogic_g1351.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1351).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.byLength3_heq»))

/-- The program's global of index 1364 is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[1364]? = some (⟨weakHypsTy, «Tactics.withWeakHyps»⟩ : Glob) :=
  metalogic_g1364.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1364).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    metalogic.«Tactics.withWeakHyps_heq»))

/-- The program's global of index 1365 is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[1365]? = some (⟨rulesProverTy, «Tactics.byListIndHypWeak»⟩ : Glob) :=
  metalogic_g1365.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1365).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byListIndHypWeak_heq»))

/-- The program's global of index 1366 is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[1366]? = some (⟨bitsIndHypTy, «Tactics.byBitsIndHyp»⟩ : Glob) :=
  metalogic_g1366.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1366).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    metalogic.«Tactics.byBitsIndHyp_heq»))

/-- The program's global of index 1370 is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[1370]? = some (⟨instsTy, «Tactics.withInsts»⟩ : Glob) :=
  metalogic_g1370.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1370).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    metalogic.«Tactics.withInsts_heq»))

/-- The program's global of index 1372 is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[1372]? = some (⟨childHypsTy, «Tactics.withChildHyps»⟩ : Glob) :=
  metalogic_g1372.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1372).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    metalogic.«Tactics.withChildHyps_heq»))

/-- The program's global of index 1374 is the mirror's proof by case analysis of a list variable
with a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[1374]? = some (⟨revertTy, «Tactics.revertCase»⟩ : Glob) :=
  metalogic_g1374.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1374).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.revertCase_heq»))

/-- The program's global of index 1376 is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[1376]? = some (⟨impITy, «Tactics.byImpI»⟩ : Glob) :=
  metalogic_g1376.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1376).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    metalogic.«Tactics.byImpI_heq»))

/-- The program's global of index 1377 is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[1377]? = some (⟨impElimTy, «Tactics.withImpElim»⟩ : Glob) :=
  metalogic_g1377.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1377).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    metalogic.«Tactics.withImpElim_heq»))

/-- The program's global of index 1380 is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[1380]? = some (⟨succPredTy, «Tactics.bySuccPred»⟩ : Glob) :=
  metalogic_g1380.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1380).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    metalogic.«Tactics.bySuccPred_heq»))

/-- The program's global of index 1399 is the mirror's proof by rounds of the instance search, at
its type. -/
theorem metalogic_byInsts :
    metalogic.globals[1399]? = some (⟨instsSearchTy, «Tactics.byInsts»⟩ : Glob) :=
  metalogic_g1399.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1399).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byInsts_heq»))

/-- The program's global of index 1401 is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[1401]? = some (⟨autoTy, «Tactics.byAuto»⟩ : Glob) :=
  metalogic_g1401.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1401).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    metalogic.«Tactics.byAuto_heq»))

/-- The program's global of index 1423 is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[1423]? = some (⟨funExtTy, «Tactics.byTreeSplit»⟩ : Glob) :=
  metalogic_g1423.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1423).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byTreeSplit_heq»))

/-- The program's global of index 1425 is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[1425]? = some (⟨autoTTy, «Tactics.byAutoT»⟩ : Glob) :=
  metalogic_g1425.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1425).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    metalogic.«Tactics.byAutoT_heq»))

/-- The program's global of index 1426 is the mirror's proof by reduction or by case analysis,
folded conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[1426]? = some (⟨autoCTy, «Tactics.byAutoC»⟩ : Glob) :=
  metalogic_g1426.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1426).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byAutoC_heq»))

/-- The program's global of index 1430 is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[1430]? = some (⟨maskRwTy, «Tactics.maskRw»⟩ : Glob) :=
  metalogic_g1430.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1430).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    metalogic.«Tactics.maskRw_heq»))

/-- The program's global of index 1447 is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[1447]? = some (⟨maskSubsTy, «Tactics.byMaskSubs»⟩ : Glob) :=
  metalogic_g1447.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1447).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byMaskSubs_heq»))

/-- The program's global of index 1448 is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[1448]? = some (⟨funExtTy, «Tactics.byGeneralize»⟩ : Glob) :=
  metalogic_g1448.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1448).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byGeneralize_heq»))

/-- The type of a computation of the combinator prover: from the scope and the state to the optional
value with the state. -/
def pmTy : Tree := tArrow tT (tArrow tT tT)

/-- The type of a computation of the combinator prover from a term. -/
def termPMTy : Tree := [tT].foldr tArrow pmTy

/-- The type of a computation of the combinator prover from rules and a term. -/
def rulesPMTy : Tree := [tList tT, tT].foldr tArrow pmTy

/-- The type of a computation of the combinator prover from a source and terms. -/
def instPMTy : Tree := [tT, tList tT].foldr tArrow pmTy

/-- The type of a function of trees. -/
def treeFnTy : Tree := [tT].foldr tArrow tT

/-- The type of the proof of a sequent added to a development: from the sequent, the computation of
its certificate, the definitions, whether the typing is inferred and the development to the optional
index and development. -/
def proveSeqTy : Tree := [tT, pmTy, tList tT, tT, tList tT].foldr tArrow tT

/-- The type of the normalization of a theorem added to a development: from the rules, the theorem's
index, the definitions, whether the typing is inferred and the development to the optional index and
development. -/
def normalizeThmTy : Tree := [tList tT, tT, tList tT, tT, tList tT].foldr tArrow tT

/-- The type of a computation of the combinator prover from rules, a source and terms. -/
def instByTy : Tree := [tList tT, tT, tList tT].foldr tArrow pmTy

/-- The type of a proof by induction on the natural numbers object: from the rules, the start, the
step and the equation. -/
def natIndPMTy : Tree := [tList tT, tT, tT, tT].foldr tArrow pmTy

/-- The type of a proof by induction on a list object: from the rules, the type of elements, the
start, the step and the equation. -/
def listIndPMTy : Tree := [tList tT, tT, tT, tT, tT].foldr tArrow pmTy

/-- The type of the rules of a library's indices. -/
def libRulesTy : Tree := [tT].foldr tArrow (tList tT)

kernel_rfl metalogic_g1698 : metalogic.globals[1698]? = some metalogic.g1698
kernel_rfl metalogic_g1752 : metalogic.globals[1752]? = some metalogic.g1752
kernel_rfl metalogic_g1758 : metalogic.globals[1758]? = some metalogic.g1758
kernel_rfl metalogic_g1759 : metalogic.globals[1759]? = some metalogic.g1759
kernel_rfl metalogic_g1762 : metalogic.globals[1762]? = some metalogic.g1762
kernel_rfl metalogic_g1763 : metalogic.globals[1763]? = some metalogic.g1763
kernel_rfl metalogic_g1773 : metalogic.globals[1773]? = some metalogic.g1773
kernel_rfl metalogic_g1774 : metalogic.globals[1774]? = some metalogic.g1774
kernel_rfl metalogic_g1775 : metalogic.globals[1775]? = some metalogic.g1775
kernel_rfl metalogic_g1780 : metalogic.globals[1780]? = some metalogic.g1780
kernel_rfl metalogic_g1781 : metalogic.globals[1781]? = some metalogic.g1781
kernel_rfl metalogic_g1782 : metalogic.globals[1782]? = some metalogic.g1782
kernel_rfl metalogic_g1807 : metalogic.globals[1807]? = some metalogic.g1807
kernel_rfl metalogic_g1808 : metalogic.globals[1808]? = some metalogic.g1808

set_option maxRecDepth 100000 in
/-- The program's global of index 1698 is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[1698]? = some (⟨termPMTy, «Combinator.typeTerm»⟩ : Glob) :=
  metalogic_g1698.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1698).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    metalogic.«Combinator.typeTerm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1752 is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[1752]? = some (⟨rulesPMTy, «Combinator.pNormalize»⟩ : Glob) :=
  metalogic_g1752.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1752).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    metalogic.«Combinator.pNormalize_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1758 is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[1758]? = some (⟨instPMTy, «Combinator.pInst»⟩ : Glob) :=
  metalogic_g1758.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1758).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    metalogic.«Combinator.pInst_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1759 is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[1759]? = some (⟨termPMTy, «Combinator.etaExpand»⟩ : Glob) :=
  metalogic_g1759.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1759).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    metalogic.«Combinator.etaExpand_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1762 is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[1762]? = some (⟨treeFnTy, «Combinator.deltaRule»⟩ : Glob) :=
  metalogic_g1762.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1762).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    metalogic.«Combinator.deltaRule_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1763 is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[1763]? = some (⟨rulesPMTy, «Combinator.pByNorm»⟩ : Glob) :=
  metalogic_g1763.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1763).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    metalogic.«Combinator.pByNorm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1773 is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[1773]? = some (⟨proveSeqTy, «Combinator.proveSeq»⟩ : Glob) :=
  metalogic_g1773.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1773).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    metalogic.«Combinator.proveSeq_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1774 is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[1774]? = some (⟨normalizeThmTy, «Combinator.normalizeThm»⟩ : Glob) :=
  metalogic_g1774.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1774).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    metalogic.«Combinator.normalizeThm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1775 is the mirror's instance of a source's sequent, its
hypotheses proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[1775]? = some (⟨instByTy, «Combinator.instBy»⟩ : Glob) :=
  metalogic_g1775.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1775).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    metalogic.«Combinator.instBy_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1780 is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[1780]? = some (⟨natIndPMTy, «Combinator.byNatInduction»⟩ : Glob) :=
  metalogic_g1780.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1780).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    metalogic.«Combinator.byNatInduction_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1781 is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[1781]? = some (⟨listIndPMTy, «Combinator.byListInduction»⟩ : Glob) :=
  metalogic_g1781.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1781).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    metalogic.«Combinator.byListInduction_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1782 is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[1782]? =
      some (⟨listIndPMTy, «Combinator.byListParamInduction»⟩ : Glob) :=
  metalogic_g1782.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1782).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    metalogic.«Combinator.byListParamInduction_heq»))

/-- A global is the pair of a type and a value when its type is that type and its value is
heterogeneously equal to that value. The value is an argument, rather than the second projection
of a pair, so that elaboration assigns it rather than unfolding it. -/
theorem glob_eq_mk {g : Glob} {T : Tree} {x : Ty.den T} (hT : g.1 = T) (hx : HEq g.2 x) :
    g = ⟨T, x⟩ :=
  Sigma.ext hT hx

set_option maxRecDepth 100000 in
/-- The program's global of index 1807 is the mirror's library of derived equations and its
development, at its type. -/
theorem metalogic_libraryWith :
    metalogic.globals[1807]? = some (⟨treeFnTy, «Combinator.libraryWith»⟩ : Glob) :=
  metalogic_g1807.trans (congrArg some (glob_eq_mk
    ((infer_of_loadStep metalogic.step1807).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Combinator.libraryWith_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1808 is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[1808]? = some (⟨libRulesTy, «Combinator.libRules»⟩ : Glob) :=
  metalogic_g1808.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1808).elim fun _ h ↦
      infer_lams (tList tT) _ [tT] h)
    metalogic.«Combinator.libRules_heq»))

/-! The partial printer of kernel terms and the reader's resolution of what it prints. -/

/-- The type of the partial printer of kernel terms: from the names of the definitions, a term and
a depth to an optional S-expression. -/
def printTermTy : Tree := [tList tT, tT, tT].foldr tArrow tT

/-- The type of the reader's resolution with no type abbreviations: from the names of the
definitions, an S-expression and the names in scope to an optional term. -/
def readBackTy : Tree := [tList tT, tT, tList tT].foldr tArrow tT

-- the reader's resolution of what the printer prints and the partial printer are the program's
-- globals of indices 1925 and 1935
kernel_rfl metalogic_g1925 : metalogic.globals[1925]? = some metalogic.g1925
kernel_rfl metalogic_g1935 : metalogic.globals[1935]? = some metalogic.g1935

set_option maxRecDepth 100000 in
/-- The program's global of index 1925 is the mirror's resolution of what the printer writes, at its
type. -/
theorem metalogic_readBack :
    metalogic.globals[1925]? = some (⟨readBackTy, «Printer.readBack»⟩ : Glob) :=
  metalogic_g1925.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1925).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT] h)
    metalogic.«Printer.readBack_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1935 is the mirror's partial printer of kernel terms, at its
type. -/
theorem metalogic_printTermOpt :
    metalogic.globals[1935]? = some (⟨printTermTy, «Printer.printTermOpt»⟩ : Glob) :=
  metalogic_g1935.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1935).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tT] h)
    metalogic.«Printer.printTermOpt_heq»))

/-! The checker's functions: the partial Horn checker, the theory, the inference of typings and
the step of a development. -/

/-- The type of the inferences at a fuel: from an environment, a context, hypotheses and the fuel
to the inference of a pattern's instance at arguments of given typings and the inference of a
term. -/
def infersTy : Tree :=
  [tT, tList tT, tList tT, tT].foldr tArrow
    (tProd (tArrow (tList tT) (tArrow tT tT)) (tArrow tT tT))

/-- The type of the checker of a certificate: from a theory, an environment of theorems and a
certificate to its conclusion as a function of the context and the hypotheses. -/
def pcheckTy : Tree :=
  [tT, tList tT, tT].foldr tArrow (tArrow (tList tT) (tArrow (tList tT) tT))

-- the checker's functions are the program's globals of indices 44 to 859
kernel_rfl metalogic_g44 : metalogic.globals[44]? = some metalogic.g44
kernel_rfl metalogic_g45 : metalogic.globals[45]? = some metalogic.g45
kernel_rfl metalogic_g46 : metalogic.globals[46]? = some metalogic.g46
kernel_rfl metalogic_g118 : metalogic.globals[118]? = some metalogic.g118
kernel_rfl metalogic_g160 : metalogic.globals[160]? = some metalogic.g160
kernel_rfl metalogic_g387 : metalogic.globals[387]? = some metalogic.g387
kernel_rfl metalogic_g434 : metalogic.globals[434]? = some metalogic.g434
kernel_rfl metalogic_g864 : metalogic.globals[864]? = some metalogic.g864

/-- The program's global of index 44 is the mirror's sort of a term in a context of sorts, at its
type. -/
theorem metalogic_sortOf :
    metalogic.globals[44]? =
      some (⟨[tList tT, tList tT, tT].foldr tArrow tT, «PartialHorn.sortOf»⟩ : Glob) :=
  metalogic_g44.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step44).elim fun _ h ↦
      infer_lams tT _ [tList tT, tList tT, tT] h)
    metalogic.«PartialHorn.sortOf_heq»))

/-- The program's global of index 45 is the mirror's test that every variable of a term has an
index below a bound, at its type. -/
theorem metalogic_scoped :
    metalogic.globals[45]? = some (⟨[tT, tT].foldr tArrow tT, «PartialHorn.scoped»⟩ : Glob) :=
  metalogic_g45.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step45).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    metalogic.«PartialHorn.scoped_heq»))

/-- The program's global of index 46 is the mirror's substitution of terms for the variables of a
term, at its type. -/
theorem metalogic_phSubst :
    metalogic.globals[46]? =
      some (⟨[tList tT, tT].foldr tArrow tT, «PartialHorn.phSubst»⟩ : Glob) :=
  metalogic_g46.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step46).elim fun _ h ↦ infer_lams tT _ [tList tT, tT] h)
    metalogic.«PartialHorn.phSubst_heq»))

/-- The program's global of index 118 is the mirror's checker of a certificate in a theory and an
environment of theorems, at its type. -/
theorem metalogic_pcheck :
    metalogic.globals[118]? =
      some (⟨pcheckTy, «PartialHorn.pcheck»⟩ : Glob) :=
  metalogic_g118.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step118).elim fun _ h ↦
      infer_lams (tArrow (tList tT) (tArrow (tList tT) tT)) _ [tT, tList tT, tT] h)
    metalogic.«PartialHorn.pcheck_heq»))

/-- The program's global of index 160 is the mirror's extension of a theory by definitions, at its
type. -/
theorem metalogic_thyExtendAll :
    metalogic.globals[160]? =
      some (⟨[tT, tList tT].foldr tArrow tT, «PartialHorn.thyExtendAll»⟩ : Glob) :=
  metalogic_g160.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step160).elim fun _ h ↦ infer_lams tT _ [tT, tList tT] h)
    metalogic.«PartialHorn.thyExtendAll_heq»))

-- The program's global of index 285 is the mirror's theory of an elementary topos, a tree, checked
-- by the kernel: elaborating the global's equality with its mirror makes the elaborator evaluate
-- the checker-evaluator on the definition.
set_option maxRecDepth 100000 in
kernel_rfl metalogic_toposTheory :
    metalogic.globals[285]? = some (⟨tT, «Theory.toposTheory»⟩ : Glob)

/-- The program's global of index 387 is the mirror's environment of a list of definitions, at its
type. -/
theorem metalogic_envOfDefs :
    metalogic.globals[387]? = some (⟨listFnTy, «Infer.envOfDefs»⟩ : Glob) :=
  metalogic_g387.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step387).elim fun _ h ↦ infer_lams tT _ [tList tT] h)
    metalogic.«Infer.envOfDefs_heq»))

/-- The program's global of index 434 is the mirror's inferences at a fuel, at its type. -/
theorem metalogic_infers :
    metalogic.globals[434]? = some (⟨infersTy, «Infer.infers»⟩ : Glob) :=
  metalogic_g434.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step434).elim fun _ h ↦
      infer_lams (tProd (tArrow (tList tT) (tArrow tT tT)) (tArrow tT tT)) _
        [tT, tList tT, tList tT, tT] h)
    metalogic.«Infer.infers_heq»))

/-- The program's global of index 864 is the mirror's constants and environment after a
declaration, at its type. -/
theorem metalogic_declStep :
    metalogic.globals[864]? =
      some (⟨[tT, tList tT, tT].foldr tArrow tT, «Derivation.declStep»⟩ : Glob) :=
  metalogic_g864.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step864).elim fun _ h ↦ infer_lams tT _ [tT, tList tT, tT] h)
    metalogic.«Derivation.declStep_heq»))

/-! The tactics' functions of terms. -/

-- the tactics' functions of terms are the program's globals of indices 1384 to 1423
kernel_rfl metalogic_g1384 : metalogic.globals[1384]? = some metalogic.g1384
kernel_rfl metalogic_g1389 : metalogic.globals[1389]? = some metalogic.g1389
kernel_rfl metalogic_g1390 : metalogic.globals[1390]? = some metalogic.g1390
kernel_rfl metalogic_g1393 : metalogic.globals[1393]? = some metalogic.g1393
kernel_rfl metalogic_g1410 : metalogic.globals[1410]? = some metalogic.g1410
kernel_rfl metalogic_g1412 : metalogic.globals[1412]? = some metalogic.g1412
kernel_rfl metalogic_g1414 : metalogic.globals[1414]? = some metalogic.g1414
kernel_rfl metalogic_g1418 : metalogic.globals[1418]? = some metalogic.g1418
kernel_rfl metalogic_g1422 : metalogic.globals[1422]? = some metalogic.g1422
kernel_rfl metalogic_g1428 : metalogic.globals[1428]? = some metalogic.g1428

set_option maxRecDepth 100000 in
/-- The program's global of index 1384 is the mirror's subterms of a term outside binders and
folds' starts and steps, at its type. -/
theorem metalogic_openSubterms :
    metalogic.globals[1384]? =
      some (⟨[tT].foldr tArrow (tList tT), «Tactics.openSubterms»⟩ : Glob) :=
  metalogic_g1384.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1384).elim fun _ h ↦ infer_lams (tList tT) _ [tT] h)
    metalogic.«Tactics.openSubterms_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1389 is the mirror's variable a weak normal form is stuck on, at
its type. -/
theorem metalogic_stuckVar :
    metalogic.globals[1389]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVar»⟩ : Glob) :=
  metalogic_g1389.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1389).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    metalogic.«Tactics.stuckVar_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1390 is the mirror's test that a term mentions a variable, at
its type. -/
theorem metalogic_mentions :
    metalogic.globals[1390]? = some (⟨[tT, tT].foldr tArrow tT, «Tactics.mentions»⟩ : Glob) :=
  metalogic_g1390.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1390).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    metalogic.«Tactics.mentions_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1393 is the mirror's arguments at which the body of an
abstraction matches the subterms of a term, at its type. -/
theorem metalogic_matchesOf :
    metalogic.globals[1393]? =
      some (⟨[tT, tT, tT].foldr tArrow (tList (tList tT)), «Tactics.matchesOf»⟩ : Glob) :=
  metalogic_g1393.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1393).elim fun _ h ↦
      infer_lams (tList (tList tT)) _ [tT, tT, tT] h)
    metalogic.«Tactics.matchesOf_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1410 is the mirror's type, test and branches of a conditional of
the library, at its type. -/
theorem metalogic_condParts :
    metalogic.globals[1410]? = some (⟨[tT].foldr tArrow tT, «Tactics.condParts»⟩ : Glob) :=
  metalogic_g1410.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1410).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Tactics.condParts_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1412 is the mirror's variable a weak normal form is stuck on,
including the test of a folded conditional, at its type. -/
theorem metalogic_stuckVarC :
    metalogic.globals[1412]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVarC»⟩ : Glob) :=
  metalogic_g1412.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1412).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    metalogic.«Tactics.stuckVarC_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1414 is the mirror's applications of a definition to two
arguments among a term's subterms, at its type. -/
theorem metalogic_appsOf :
    metalogic.globals[1414]? =
      some (⟨[tT, tT].foldr tArrow (tList tT), «Tactics.appsOf»⟩ : Glob) :=
  metalogic_g1414.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1414).elim fun _ h ↦ infer_lams (tList tT) _ [tT, tT] h)
    metalogic.«Tactics.appsOf_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1418 is the mirror's unfolding of a tree term, at its type. -/
theorem metalogic_unnodeU :
    metalogic.globals[1418]? = some (⟨[tT].foldr tArrow tT, «Tactics.unnodeU»⟩ : Glob) :=
  metalogic_g1418.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1418).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Tactics.unnodeU_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1422 is the mirror's rewriting of a term in which a tree rebuilt
from the unfolding of a variable stands for the variable, back to the term, at its type. -/
theorem metalogic_occRewrite :
    metalogic.globals[1422]? =
      some (⟨[tT, tT, tT, tT].foldr tArrow tT, «Tactics.occRewrite»⟩ : Glob) :=
  metalogic_g1422.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1422).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT, tT] h)
    metalogic.«Tactics.occRewrite_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1428 is the mirror's abstraction of a term's occurrences of a
term, at its type. -/
theorem metalogic_abstractTerm :
    metalogic.globals[1428]? =
      some (⟨[tT, tT, tT].foldr tArrow tT, «Tactics.abstractTerm»⟩ : Glob) :=
  metalogic_g1428.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1428).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT] h)
    metalogic.«Tactics.abstractTerm_heq»))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
