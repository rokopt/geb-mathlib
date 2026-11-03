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
theorem checkDev_type : metalogic.g875.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step875
  generalize metalogic.g875.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global of index 875
kernel_rfl metalogic_g875 : metalogic.globals[875]? = some metalogic.g875

/-- The program's global of index 875 is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.globals[875]? = some (⟨checkDevTy, «Derivation.checkDev»⟩ : Glob) :=
  metalogic_g875.trans
    (congrArg some (Sigma.ext checkDev_type (metalogic.«Derivation.checkDev_heq».trans HEq.rfl)))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g1105.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1105
  generalize metalogic.g1105.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g1106.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1106
  generalize metalogic.g1106.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g1123.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step1123
  generalize metalogic.g1123.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 1105, 1106 and 1123
kernel_rfl metalogic_g1105 : metalogic.globals[1105]? = some metalogic.g1105
kernel_rfl metalogic_g1106 : metalogic.globals[1106]? = some metalogic.g1106
kernel_rfl metalogic_g1123 : metalogic.globals[1123]? = some metalogic.g1123

/-- The program's global of index 1105 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[1105]? = some (⟨listFnTy, «Translation.program»⟩ : Glob) :=
  metalogic_g1105.trans
    (congrArg some (Sigma.ext program_type (metalogic.«Translation.program_heq».trans HEq.rfl)))

/-- The program's global of index 1106 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[1106]? = some (⟨listFnTy, «Translation.trGlobals»⟩ : Glob) :=
  metalogic_g1106.trans
    (congrArg some (Sigma.ext trGlobals_type (metalogic.«Translation.trGlobals_heq».trans HEq.rfl)))

/-- The program's global of index 1123 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[1123]? = some (⟨thmTy, «Translation.thm»⟩ : Glob) :=
  metalogic_g1123.trans
    (congrArg some (Sigma.ext thm_type (metalogic.«Translation.thm_heq».trans HEq.rfl)))

/-- The type of the normalizer's rules, each with its matching. -/
def rulesTy : Tree := tList (tProd tT (tArrow tT (tArrow tT (tArrow (tList tT) tT))))

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
theorem prepareRules_type : metalogic.g1179.1 = prepareTy := by
  have h := infer_of_loadStep metalogic.step1179
  generalize metalogic.g1179.1 = T at h ⊢
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
theorem byNorm_type : metalogic.g1228.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1228
  generalize metalogic.g1228.1 = T at h ⊢
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
theorem byNatInd_type : metalogic.g1230.1 = indTy := by
  have h := infer_of_loadStep metalogic.step1230
  generalize metalogic.g1230.1 = T at h ⊢
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
theorem byListInd_type : metalogic.g1231.1 = indTy := by
  have h := infer_of_loadStep metalogic.step1231
  generalize metalogic.g1231.1 = T at h ⊢
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
theorem byNatIndHyp_type : metalogic.g1233.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step1233
  generalize metalogic.g1233.1 = T at h ⊢
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
theorem byListIndHyp_type : metalogic.g1234.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step1234
  generalize metalogic.g1234.1 = T at h ⊢
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
theorem byNormW_type : metalogic.g1272.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1272
  generalize metalogic.g1272.1 = T at h ⊢
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
theorem byFunExt_type : metalogic.g1274.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step1274
  generalize metalogic.g1274.1 = T at h ⊢
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
theorem bySplit_type : metalogic.g1275.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1275
  generalize metalogic.g1275.1 = T at h ⊢
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
theorem byListIndWith_type : metalogic.g1276.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step1276
  generalize metalogic.g1276.1 = T at h ⊢
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
theorem byRoseInd_type : metalogic.g1277.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step1277
  generalize metalogic.g1277.1 = T at h ⊢
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
theorem byRoseIndHyp_type : metalogic.g1278.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1278
  generalize metalogic.g1278.1 = T at h ⊢
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

-- the prover's entry points are the program's globals of indices 1179 to 1273
kernel_rfl metalogic_g1179 : metalogic.globals[1179]? = some metalogic.g1179
kernel_rfl metalogic_g1228 : metalogic.globals[1228]? = some metalogic.g1228
kernel_rfl metalogic_g1230 : metalogic.globals[1230]? = some metalogic.g1230
kernel_rfl metalogic_g1231 : metalogic.globals[1231]? = some metalogic.g1231
kernel_rfl metalogic_g1233 : metalogic.globals[1233]? = some metalogic.g1233
kernel_rfl metalogic_g1234 : metalogic.globals[1234]? = some metalogic.g1234
kernel_rfl metalogic_g1272 : metalogic.globals[1272]? = some metalogic.g1272
kernel_rfl metalogic_g1274 : metalogic.globals[1274]? = some metalogic.g1274
kernel_rfl metalogic_g1275 : metalogic.globals[1275]? = some metalogic.g1275
kernel_rfl metalogic_g1276 : metalogic.globals[1276]? = some metalogic.g1276
kernel_rfl metalogic_g1277 : metalogic.globals[1277]? = some metalogic.g1277
kernel_rfl metalogic_g1278 : metalogic.globals[1278]? = some metalogic.g1278

/-- The program's global of index 1179 is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[1179]? = some (⟨prepareTy, «Prover.prepareRules»⟩ : Glob) :=
  metalogic_g1179.trans (congrArg some (Sigma.ext
    prepareRules_type (metalogic.«Prover.prepareRules_heq».trans HEq.rfl)))

/-- The program's global of index 1228 is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[1228]? = some (⟨normTy, «Prover.byNorm»⟩ : Glob) :=
  metalogic_g1228.trans (congrArg some (Sigma.ext
    byNorm_type (metalogic.«Prover.byNorm_heq».trans HEq.rfl)))

/-- The program's global of index 1230 is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[1230]? = some (⟨indTy, «Prover.byNatInd»⟩ : Glob) :=
  metalogic_g1230.trans (congrArg some (Sigma.ext
    byNatInd_type (metalogic.«Prover.byNatInd_heq».trans HEq.rfl)))

/-- The program's global of index 1231 is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[1231]? = some (⟨indTy, «Prover.byListInd»⟩ : Glob) :=
  metalogic_g1231.trans (congrArg some (Sigma.ext
    byListInd_type (metalogic.«Prover.byListInd_heq».trans HEq.rfl)))

/-- The program's global of index 1233 is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[1233]? = some (⟨indHypTy, «Prover.byNatIndHyp»⟩ : Glob) :=
  metalogic_g1233.trans (congrArg some (Sigma.ext
    byNatIndHyp_type (metalogic.«Prover.byNatIndHyp_heq».trans HEq.rfl)))

/-- The program's global of index 1234 is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[1234]? = some (⟨indHypTy, «Prover.byListIndHyp»⟩ : Glob) :=
  metalogic_g1234.trans (congrArg some (Sigma.ext
    byListIndHyp_type (metalogic.«Prover.byListIndHyp_heq».trans HEq.rfl)))

/-- The program's global of index 1272 is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[1272]? = some (⟨normTy, «Prover.byNormW»⟩ : Glob) :=
  metalogic_g1272.trans (congrArg some (Sigma.ext
    byNormW_type (metalogic.«Prover.byNormW_heq».trans HEq.rfl)))

/-- The program's global of index 1274 is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[1274]? = some (⟨funExtTy, «Prover.byFunExt»⟩ : Glob) :=
  metalogic_g1274.trans (congrArg some (Sigma.ext
    byFunExt_type (metalogic.«Prover.byFunExt_heq».trans HEq.rfl)))

/-- The program's global of index 1275 is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[1275]? = some (⟨proverFnTy, «Prover.bySplit»⟩ : Glob) :=
  metalogic_g1275.trans (congrArg some (Sigma.ext
    bySplit_type (metalogic.«Prover.bySplit_heq».trans HEq.rfl)))

/-- The program's global of index 1276 is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[1276]? = some (⟨listIndWithTy, «Prover.byListIndWith»⟩ : Glob) :=
  metalogic_g1276.trans (congrArg some (Sigma.ext
    byListIndWith_type (metalogic.«Prover.byListIndWith_heq».trans HEq.rfl)))

/-- The program's global of index 1277 is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[1277]? = some (⟨roseIndTy, «Prover.byRoseInd»⟩ : Glob) :=
  metalogic_g1277.trans (congrArg some (Sigma.ext
    byRoseInd_type (metalogic.«Prover.byRoseInd_heq».trans HEq.rfl)))

/-- The program's global of index 1278 is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[1278]? = some (⟨proverFnTy, «Prover.byRoseIndHyp»⟩ : Glob) :=
  metalogic_g1278.trans (congrArg some (Sigma.ext
    byRoseIndHyp_type (metalogic.«Prover.byRoseIndHyp_heq».trans HEq.rfl)))

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

-- the tactics' entry points are the program's globals of indices 1295 to 1391
kernel_rfl metalogic_g1295 : metalogic.globals[1295]? = some metalogic.g1295
kernel_rfl metalogic_g1296 : metalogic.globals[1296]? = some metalogic.g1296
kernel_rfl metalogic_g1297 : metalogic.globals[1297]? = some metalogic.g1297
kernel_rfl metalogic_g1301 : metalogic.globals[1301]? = some metalogic.g1301
kernel_rfl metalogic_g1302 : metalogic.globals[1302]? = some metalogic.g1302
kernel_rfl metalogic_g1303 : metalogic.globals[1303]? = some metalogic.g1303
kernel_rfl metalogic_g1304 : metalogic.globals[1304]? = some metalogic.g1304
kernel_rfl metalogic_g1306 : metalogic.globals[1306]? = some metalogic.g1306
kernel_rfl metalogic_g1307 : metalogic.globals[1307]? = some metalogic.g1307
kernel_rfl metalogic_g1308 : metalogic.globals[1308]? = some metalogic.g1308
kernel_rfl metalogic_g1309 : metalogic.globals[1309]? = some metalogic.g1309
kernel_rfl metalogic_g1310 : metalogic.globals[1310]? = some metalogic.g1310
kernel_rfl metalogic_g1311 : metalogic.globals[1311]? = some metalogic.g1311
kernel_rfl metalogic_g1312 : metalogic.globals[1312]? = some metalogic.g1312
kernel_rfl metalogic_g1313 : metalogic.globals[1313]? = some metalogic.g1313
kernel_rfl metalogic_g1314 : metalogic.globals[1314]? = some metalogic.g1314
kernel_rfl metalogic_g1315 : metalogic.globals[1315]? = some metalogic.g1315
kernel_rfl metalogic_g1319 : metalogic.globals[1319]? = some metalogic.g1319
kernel_rfl metalogic_g1321 : metalogic.globals[1321]? = some metalogic.g1321
kernel_rfl metalogic_g1323 : metalogic.globals[1323]? = some metalogic.g1323
kernel_rfl metalogic_g1325 : metalogic.globals[1325]? = some metalogic.g1325
kernel_rfl metalogic_g1326 : metalogic.globals[1326]? = some metalogic.g1326
kernel_rfl metalogic_g1329 : metalogic.globals[1329]? = some metalogic.g1329
kernel_rfl metalogic_g1348 : metalogic.globals[1348]? = some metalogic.g1348
kernel_rfl metalogic_g1350 : metalogic.globals[1350]? = some metalogic.g1350
kernel_rfl metalogic_g1371 : metalogic.globals[1371]? = some metalogic.g1371
kernel_rfl metalogic_g1373 : metalogic.globals[1373]? = some metalogic.g1373
kernel_rfl metalogic_g1374 : metalogic.globals[1374]? = some metalogic.g1374
kernel_rfl metalogic_g1378 : metalogic.globals[1378]? = some metalogic.g1378
kernel_rfl metalogic_g1395 : metalogic.globals[1395]? = some metalogic.g1395
kernel_rfl metalogic_g1396 : metalogic.globals[1396]? = some metalogic.g1396

/-- The program's global of index 1295 is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[1295]? = some (⟨modeTy, «Tactics.byMode»⟩ : Glob) :=
  metalogic_g1295.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1295).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    (metalogic.«Tactics.byMode_heq».trans HEq.rfl)))

/-- The program's global of index 1296 is the mirror's proof by reduction to one weak normal form,
at its type. -/
theorem metalogic_byWeak :
    metalogic.globals[1296]? = some (⟨rulesProverTy, «Tactics.byWeak»⟩ : Glob) :=
  metalogic_g1296.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1296).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.«Tactics.byWeak_heq».trans HEq.rfl)))

/-- The program's global of index 1297 is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[1297]? = some (⟨nfTy, «Tactics.byNF»⟩ : Glob) :=
  metalogic_g1297.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1297).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    (metalogic.«Tactics.byNF_heq».trans HEq.rfl)))

/-- The program's global of index 1301 is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[1301]? = some (⟨normHTy, «Tactics.normH»⟩ : Glob) :=
  metalogic_g1301.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1301).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    (metalogic.«Tactics.normH_heq».trans HEq.rfl)))

/-- The program's global of index 1302 is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[1302]? = some (⟨funExtTy, «Tactics.funExts»⟩ : Glob) :=
  metalogic_g1302.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1302).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.funExts_heq».trans HEq.rfl)))

/-- The program's global of index 1303 is the mirror's proof by induction on a list with a step,
both cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[1303]? = some (⟨listIndWeakTy, «Tactics.byListIndWeak»⟩ : Glob) :=
  metalogic_g1303.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1303).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    (metalogic.«Tactics.byListIndWeak_heq».trans HEq.rfl)))

/-- The program's global of index 1304 is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[1304]? = some (⟨proverFnTy, «Tactics.byRoseIndWith»⟩ : Glob) :=
  metalogic_g1304.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1304).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    (metalogic.«Tactics.byRoseIndWith_heq».trans HEq.rfl)))

/-- The program's global of index 1306 is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[1306]? = some (⟨splitTy, «Tactics.byListSplit»⟩ : Glob) :=
  metalogic_g1306.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1306).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.byListSplit_heq».trans HEq.rfl)))

/-- The program's global of index 1307 is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[1307]? = some (⟨splitTy, «Tactics.bySplit2»⟩ : Glob) :=
  metalogic_g1307.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1307).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.bySplit2_heq».trans HEq.rfl)))

/-- The program's global of index 1308 is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[1308]? = some (⟨funExtTy, «Tactics.byListCases»⟩ : Glob) :=
  metalogic_g1308.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1308).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.byListCases_heq».trans HEq.rfl)))

/-- The program's global of index 1309 is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[1309]? = some (⟨twoProverTy, «Tactics.bitsInd»⟩ : Glob) :=
  metalogic_g1309.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1309).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.bitsInd_heq».trans HEq.rfl)))

/-- The program's global of index 1310 is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[1310]? = some (⟨funExtTy, «Tactics.bitsCases»⟩ : Glob) :=
  metalogic_g1310.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1310).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.bitsCases_heq».trans HEq.rfl)))

/-- The program's global of index 1311 is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[1311]? = some (⟨byBitsTy, «Tactics.byBits»⟩ : Glob) :=
  metalogic_g1311.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1311).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    (metalogic.«Tactics.byBits_heq».trans HEq.rfl)))

/-- The program's global of index 1312 is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[1312]? = some (⟨twoProverTy, «Tactics.byLength3»⟩ : Glob) :=
  metalogic_g1312.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1312).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.byLength3_heq».trans HEq.rfl)))

/-- The program's global of index 1313 is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[1313]? = some (⟨weakHypsTy, «Tactics.withWeakHyps»⟩ : Glob) :=
  metalogic_g1313.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1313).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    (metalogic.«Tactics.withWeakHyps_heq».trans HEq.rfl)))

/-- The program's global of index 1314 is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[1314]? = some (⟨rulesProverTy, «Tactics.byListIndHypWeak»⟩ : Glob) :=
  metalogic_g1314.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1314).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.«Tactics.byListIndHypWeak_heq».trans HEq.rfl)))

/-- The program's global of index 1315 is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[1315]? = some (⟨bitsIndHypTy, «Tactics.byBitsIndHyp»⟩ : Glob) :=
  metalogic_g1315.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1315).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    (metalogic.«Tactics.byBitsIndHyp_heq».trans HEq.rfl)))

/-- The program's global of index 1319 is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[1319]? = some (⟨instsTy, «Tactics.withInsts»⟩ : Glob) :=
  metalogic_g1319.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1319).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    (metalogic.«Tactics.withInsts_heq».trans HEq.rfl)))

/-- The program's global of index 1321 is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[1321]? = some (⟨childHypsTy, «Tactics.withChildHyps»⟩ : Glob) :=
  metalogic_g1321.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1321).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    (metalogic.«Tactics.withChildHyps_heq».trans HEq.rfl)))

/-- The program's global of index 1323 is the mirror's proof by case analysis of a list variable
with a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[1323]? = some (⟨revertTy, «Tactics.revertCase»⟩ : Glob) :=
  metalogic_g1323.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1323).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.revertCase_heq».trans HEq.rfl)))

/-- The program's global of index 1325 is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[1325]? = some (⟨impITy, «Tactics.byImpI»⟩ : Glob) :=
  metalogic_g1325.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1325).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    (metalogic.«Tactics.byImpI_heq».trans HEq.rfl)))

/-- The program's global of index 1326 is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[1326]? = some (⟨impElimTy, «Tactics.withImpElim»⟩ : Glob) :=
  metalogic_g1326.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1326).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    (metalogic.«Tactics.withImpElim_heq».trans HEq.rfl)))

/-- The program's global of index 1329 is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[1329]? = some (⟨succPredTy, «Tactics.bySuccPred»⟩ : Glob) :=
  metalogic_g1329.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1329).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    (metalogic.«Tactics.bySuccPred_heq».trans HEq.rfl)))

/-- The program's global of index 1348 is the mirror's proof by rounds of the instance search, at
its type. -/
theorem metalogic_byInsts :
    metalogic.globals[1348]? = some (⟨instsSearchTy, «Tactics.byInsts»⟩ : Glob) :=
  metalogic_g1348.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1348).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    (metalogic.«Tactics.byInsts_heq».trans HEq.rfl)))

/-- The program's global of index 1350 is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[1350]? = some (⟨autoTy, «Tactics.byAuto»⟩ : Glob) :=
  metalogic_g1350.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1350).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    (metalogic.«Tactics.byAuto_heq».trans HEq.rfl)))

/-- The program's global of index 1371 is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[1371]? = some (⟨funExtTy, «Tactics.byTreeSplit»⟩ : Glob) :=
  metalogic_g1371.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1371).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.byTreeSplit_heq».trans HEq.rfl)))

/-- The program's global of index 1373 is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[1373]? = some (⟨autoTTy, «Tactics.byAutoT»⟩ : Glob) :=
  metalogic_g1373.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1373).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    (metalogic.«Tactics.byAutoT_heq».trans HEq.rfl)))

/-- The program's global of index 1374 is the mirror's proof by reduction or by case analysis,
folded conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[1374]? = some (⟨autoCTy, «Tactics.byAutoC»⟩ : Glob) :=
  metalogic_g1374.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1374).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.«Tactics.byAutoC_heq».trans HEq.rfl)))

/-- The program's global of index 1378 is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[1378]? = some (⟨maskRwTy, «Tactics.maskRw»⟩ : Glob) :=
  metalogic_g1378.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1378).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    (metalogic.«Tactics.maskRw_heq».trans HEq.rfl)))

/-- The program's global of index 1395 is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[1395]? = some (⟨maskSubsTy, «Tactics.byMaskSubs»⟩ : Glob) :=
  metalogic_g1395.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1395).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.«Tactics.byMaskSubs_heq».trans HEq.rfl)))

/-- The program's global of index 1396 is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[1396]? = some (⟨funExtTy, «Tactics.byGeneralize»⟩ : Glob) :=
  metalogic_g1396.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1396).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.byGeneralize_heq».trans HEq.rfl)))

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

kernel_rfl metalogic_g1646 : metalogic.globals[1646]? = some metalogic.g1646
kernel_rfl metalogic_g1700 : metalogic.globals[1700]? = some metalogic.g1700
kernel_rfl metalogic_g1706 : metalogic.globals[1706]? = some metalogic.g1706
kernel_rfl metalogic_g1707 : metalogic.globals[1707]? = some metalogic.g1707
kernel_rfl metalogic_g1710 : metalogic.globals[1710]? = some metalogic.g1710
kernel_rfl metalogic_g1711 : metalogic.globals[1711]? = some metalogic.g1711
kernel_rfl metalogic_g1721 : metalogic.globals[1721]? = some metalogic.g1721
kernel_rfl metalogic_g1722 : metalogic.globals[1722]? = some metalogic.g1722
kernel_rfl metalogic_g1723 : metalogic.globals[1723]? = some metalogic.g1723
kernel_rfl metalogic_g1728 : metalogic.globals[1728]? = some metalogic.g1728
kernel_rfl metalogic_g1729 : metalogic.globals[1729]? = some metalogic.g1729
kernel_rfl metalogic_g1730 : metalogic.globals[1730]? = some metalogic.g1730
kernel_rfl metalogic_g1755 : metalogic.globals[1755]? = some metalogic.g1755
kernel_rfl metalogic_g1756 : metalogic.globals[1756]? = some metalogic.g1756

set_option maxRecDepth 100000 in
/-- The program's global of index 1646 is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[1646]? = some (⟨termPMTy, «Combinator.typeTerm»⟩ : Glob) :=
  metalogic_g1646.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1646).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.«Combinator.typeTerm_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1700 is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[1700]? = some (⟨rulesPMTy, «Combinator.pNormalize»⟩ : Glob) :=
  metalogic_g1700.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1700).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.«Combinator.pNormalize_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1706 is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[1706]? = some (⟨instPMTy, «Combinator.pInst»⟩ : Glob) :=
  metalogic_g1706.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1706).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    (metalogic.«Combinator.pInst_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1707 is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[1707]? = some (⟨termPMTy, «Combinator.etaExpand»⟩ : Glob) :=
  metalogic_g1707.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1707).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.«Combinator.etaExpand_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1710 is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[1710]? = some (⟨treeFnTy, «Combinator.deltaRule»⟩ : Glob) :=
  metalogic_g1710.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1710).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    (metalogic.«Combinator.deltaRule_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1711 is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[1711]? = some (⟨rulesPMTy, «Combinator.pByNorm»⟩ : Glob) :=
  metalogic_g1711.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1711).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.«Combinator.pByNorm_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1721 is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[1721]? = some (⟨proveSeqTy, «Combinator.proveSeq»⟩ : Glob) :=
  metalogic_g1721.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1721).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    (metalogic.«Combinator.proveSeq_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1722 is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[1722]? = some (⟨normalizeThmTy, «Combinator.normalizeThm»⟩ : Glob) :=
  metalogic_g1722.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1722).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    (metalogic.«Combinator.normalizeThm_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1723 is the mirror's instance of a source's sequent, its
hypotheses proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[1723]? = some (⟨instByTy, «Combinator.instBy»⟩ : Glob) :=
  metalogic_g1723.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1723).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    (metalogic.«Combinator.instBy_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1728 is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[1728]? = some (⟨natIndPMTy, «Combinator.byNatInduction»⟩ : Glob) :=
  metalogic_g1728.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1728).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    (metalogic.«Combinator.byNatInduction_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1729 is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[1729]? = some (⟨listIndPMTy, «Combinator.byListInduction»⟩ : Glob) :=
  metalogic_g1729.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1729).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.«Combinator.byListInduction_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1730 is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[1730]? =
      some (⟨listIndPMTy, «Combinator.byListParamInduction»⟩ : Glob) :=
  metalogic_g1730.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1730).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.«Combinator.byListParamInduction_heq».trans HEq.rfl)))

/-- A global is the pair of a type and a value when its type is that type and its value is
heterogeneously equal to that value. The value is an argument, rather than the second projection
of a pair, so that elaboration assigns it rather than unfolding it. -/
theorem glob_eq_mk {g : Glob} {T : Tree} {x : Ty.den T} (hT : g.1 = T) (hx : HEq g.2 x) :
    g = ⟨T, x⟩ :=
  Sigma.ext hT hx

set_option maxRecDepth 100000 in
/-- The program's global of index 1755 is the mirror's library of derived equations and its
development, at its type. -/
theorem metalogic_libraryWith :
    metalogic.globals[1755]? = some (⟨treeFnTy, «Combinator.libraryWith»⟩ : Glob) :=
  metalogic_g1755.trans (congrArg some (glob_eq_mk
    ((infer_of_loadStep metalogic.step1755).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Combinator.libraryWith_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1756 is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[1756]? = some (⟨libRulesTy, «Combinator.libRules»⟩ : Glob) :=
  metalogic_g1756.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1756).elim fun _ h ↦
      infer_lams (tList tT) _ [tT] h)
    (metalogic.«Combinator.libRules_heq».trans HEq.rfl)))

/-! The partial printer of kernel terms and the reader's resolution of what it prints. -/

/-- The type of the partial printer of kernel terms: from the names of the definitions, a term and
a depth to an optional S-expression. -/
def printTermTy : Tree := [tList tT, tT, tT].foldr tArrow tT

/-- The type of the reader's resolution with no type abbreviations: from the names of the
definitions, an S-expression and the names in scope to an optional term. -/
def readBackTy : Tree := [tList tT, tT, tList tT].foldr tArrow tT

-- the reader's resolution of what the printer prints and the partial printer are the program's
-- globals of indices 1875 and 1885
kernel_rfl metalogic_g1875 : metalogic.globals[1875]? = some metalogic.g1875
kernel_rfl metalogic_g1885 : metalogic.globals[1885]? = some metalogic.g1885

set_option maxRecDepth 100000 in
/-- The program's global of index 1875 is the mirror's resolution of what the printer writes, at its
type. -/
theorem metalogic_readBack :
    metalogic.globals[1875]? = some (⟨readBackTy, «Printer.readBack»⟩ : Glob) :=
  metalogic_g1875.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1875).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT] h)
    (metalogic.«Printer.readBack_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1885 is the mirror's partial printer of kernel terms, at its
type. -/
theorem metalogic_printTermOpt :
    metalogic.globals[1885]? = some (⟨printTermTy, «Printer.printTermOpt»⟩ : Glob) :=
  metalogic_g1885.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1885).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tT] h)
    (metalogic.«Printer.printTermOpt_heq».trans HEq.rfl)))

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

-- the checker's functions are the program's globals of indices 44 to 862
kernel_rfl metalogic_g44 : metalogic.globals[44]? = some metalogic.g44
kernel_rfl metalogic_g45 : metalogic.globals[45]? = some metalogic.g45
kernel_rfl metalogic_g46 : metalogic.globals[46]? = some metalogic.g46
kernel_rfl metalogic_g118 : metalogic.globals[118]? = some metalogic.g118
kernel_rfl metalogic_g160 : metalogic.globals[160]? = some metalogic.g160
kernel_rfl metalogic_g387 : metalogic.globals[387]? = some metalogic.g387
kernel_rfl metalogic_g434 : metalogic.globals[434]? = some metalogic.g434
kernel_rfl metalogic_g867 : metalogic.globals[867]? = some metalogic.g867

/-- The program's global of index 44 is the mirror's sort of a term in a context of sorts, at its
type. -/
theorem metalogic_sortOf :
    metalogic.globals[44]? =
      some (⟨[tList tT, tList tT, tT].foldr tArrow tT, «PartialHorn.sortOf»⟩ : Glob) :=
  metalogic_g44.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step44).elim fun _ h ↦
      infer_lams tT _ [tList tT, tList tT, tT] h)
    (metalogic.«PartialHorn.sortOf_heq».trans HEq.rfl)))

/-- The program's global of index 45 is the mirror's test that every variable of a term has an
index below a bound, at its type. -/
theorem metalogic_scoped :
    metalogic.globals[45]? = some (⟨[tT, tT].foldr tArrow tT, «PartialHorn.scoped»⟩ : Glob) :=
  metalogic_g45.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step45).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    (metalogic.«PartialHorn.scoped_heq».trans HEq.rfl)))

/-- The program's global of index 46 is the mirror's substitution of terms for the variables of a
term, at its type. -/
theorem metalogic_phSubst :
    metalogic.globals[46]? =
      some (⟨[tList tT, tT].foldr tArrow tT, «PartialHorn.phSubst»⟩ : Glob) :=
  metalogic_g46.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step46).elim fun _ h ↦ infer_lams tT _ [tList tT, tT] h)
    (metalogic.«PartialHorn.phSubst_heq».trans HEq.rfl)))

/-- The program's global of index 118 is the mirror's checker of a certificate in a theory and an
environment of theorems, at its type. -/
theorem metalogic_pcheck :
    metalogic.globals[118]? =
      some (⟨pcheckTy, «PartialHorn.pcheck»⟩ : Glob) :=
  metalogic_g118.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step118).elim fun _ h ↦
      infer_lams (tArrow (tList tT) (tArrow (tList tT) tT)) _ [tT, tList tT, tT] h)
    (metalogic.«PartialHorn.pcheck_heq».trans HEq.rfl)))

/-- The program's global of index 160 is the mirror's extension of a theory by definitions, at its
type. -/
theorem metalogic_thyExtendAll :
    metalogic.globals[160]? =
      some (⟨[tT, tList tT].foldr tArrow tT, «PartialHorn.thyExtendAll»⟩ : Glob) :=
  metalogic_g160.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step160).elim fun _ h ↦ infer_lams tT _ [tT, tList tT] h)
    (metalogic.«PartialHorn.thyExtendAll_heq».trans HEq.rfl)))

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
  metalogic_g387.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step387).elim fun _ h ↦ infer_lams tT _ [tList tT] h)
    (metalogic.«Infer.envOfDefs_heq».trans HEq.rfl)))

/-- The program's global of index 434 is the mirror's inferences at a fuel, at its type. -/
theorem metalogic_infers :
    metalogic.globals[434]? = some (⟨infersTy, «Infer.infers»⟩ : Glob) :=
  metalogic_g434.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step434).elim fun _ h ↦
      infer_lams (tProd (tArrow (tList tT) (tArrow tT tT)) (tArrow tT tT)) _
        [tT, tList tT, tList tT, tT] h)
    (metalogic.«Infer.infers_heq».trans HEq.rfl)))

/-- The program's global of index 867 is the mirror's constants and environment after a
declaration, at its type. -/
theorem metalogic_declStep :
    metalogic.globals[867]? =
      some (⟨[tT, tList tT, tT].foldr tArrow tT, «Derivation.declStep»⟩ : Glob) :=
  metalogic_g867.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step867).elim fun _ h ↦ infer_lams tT _ [tT, tList tT, tT] h)
    (metalogic.«Derivation.declStep_heq».trans HEq.rfl)))

/-! The tactics' functions of terms. -/

-- the tactics' functions of terms are the program's globals of indices 1333 to 1371
kernel_rfl metalogic_g1333 : metalogic.globals[1333]? = some metalogic.g1333
kernel_rfl metalogic_g1338 : metalogic.globals[1338]? = some metalogic.g1338
kernel_rfl metalogic_g1339 : metalogic.globals[1339]? = some metalogic.g1339
kernel_rfl metalogic_g1342 : metalogic.globals[1342]? = some metalogic.g1342
kernel_rfl metalogic_g1359 : metalogic.globals[1359]? = some metalogic.g1359
kernel_rfl metalogic_g1361 : metalogic.globals[1361]? = some metalogic.g1361
kernel_rfl metalogic_g1363 : metalogic.globals[1363]? = some metalogic.g1363
kernel_rfl metalogic_g1367 : metalogic.globals[1367]? = some metalogic.g1367
kernel_rfl metalogic_g1370 : metalogic.globals[1370]? = some metalogic.g1370
kernel_rfl metalogic_g1376 : metalogic.globals[1376]? = some metalogic.g1376

set_option maxRecDepth 100000 in
/-- The program's global of index 1333 is the mirror's subterms of a term outside binders and
folds' starts and steps, at its type. -/
theorem metalogic_openSubterms :
    metalogic.globals[1333]? =
      some (⟨[tT].foldr tArrow (tList tT), «Tactics.openSubterms»⟩ : Glob) :=
  metalogic_g1333.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1333).elim fun _ h ↦ infer_lams (tList tT) _ [tT] h)
    (metalogic.«Tactics.openSubterms_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1338 is the mirror's variable a weak normal form is stuck on, at
its type. -/
theorem metalogic_stuckVar :
    metalogic.globals[1338]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVar»⟩ : Glob) :=
  metalogic_g1338.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1338).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    (metalogic.«Tactics.stuckVar_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1339 is the mirror's test that a term mentions a variable, at
its type. -/
theorem metalogic_mentions :
    metalogic.globals[1339]? = some (⟨[tT, tT].foldr tArrow tT, «Tactics.mentions»⟩ : Glob) :=
  metalogic_g1339.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1339).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    (metalogic.«Tactics.mentions_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1342 is the mirror's arguments at which the body of an
abstraction matches the subterms of a term, at its type. -/
theorem metalogic_matchesOf :
    metalogic.globals[1342]? =
      some (⟨[tT, tT, tT].foldr tArrow (tList (tList tT)), «Tactics.matchesOf»⟩ : Glob) :=
  metalogic_g1342.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1342).elim fun _ h ↦
      infer_lams (tList (tList tT)) _ [tT, tT, tT] h)
    (metalogic.«Tactics.matchesOf_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1359 is the mirror's type, test and branches of a conditional of
the library, at its type. -/
theorem metalogic_condParts :
    metalogic.globals[1359]? = some (⟨[tT].foldr tArrow tT, «Tactics.condParts»⟩ : Glob) :=
  metalogic_g1359.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1359).elim fun _ h ↦ infer_lams tT _ [tT] h)
    (metalogic.«Tactics.condParts_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1361 is the mirror's variable a weak normal form is stuck on,
including the test of a folded conditional, at its type. -/
theorem metalogic_stuckVarC :
    metalogic.globals[1361]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVarC»⟩ : Glob) :=
  metalogic_g1361.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1361).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    (metalogic.«Tactics.stuckVarC_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1363 is the mirror's applications of a definition to two
arguments among a term's subterms, at its type. -/
theorem metalogic_appsOf :
    metalogic.globals[1363]? =
      some (⟨[tT, tT].foldr tArrow (tList tT), «Tactics.appsOf»⟩ : Glob) :=
  metalogic_g1363.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1363).elim fun _ h ↦ infer_lams (tList tT) _ [tT, tT] h)
    (metalogic.«Tactics.appsOf_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1367 is the mirror's unfolding of a tree term, at its type. -/
theorem metalogic_unnodeU :
    metalogic.globals[1367]? = some (⟨[tT].foldr tArrow tT, «Tactics.unnodeU»⟩ : Glob) :=
  metalogic_g1367.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1367).elim fun _ h ↦ infer_lams tT _ [tT] h)
    (metalogic.«Tactics.unnodeU_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1370 is the mirror's rewriting of a term in which a tree rebuilt
from the unfolding of a variable stands for the variable, back to the term, at its type. -/
theorem metalogic_occRewrite :
    metalogic.globals[1370]? =
      some (⟨[tT, tT, tT, tT].foldr tArrow tT, «Tactics.occRewrite»⟩ : Glob) :=
  metalogic_g1370.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1370).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT, tT] h)
    (metalogic.«Tactics.occRewrite_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1376 is the mirror's abstraction of a term's occurrences of a
term, at its type. -/
theorem metalogic_abstractTerm :
    metalogic.globals[1376]? =
      some (⟨[tT, tT, tT].foldr tArrow tT, «Tactics.abstractTerm»⟩ : Glob) :=
  metalogic_g1376.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1376).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT] h)
    (metalogic.«Tactics.abstractTerm_heq».trans HEq.rfl)))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
