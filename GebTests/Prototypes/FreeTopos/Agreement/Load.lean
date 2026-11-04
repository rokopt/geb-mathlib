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
theorem checkDev_type : metalogic.g874.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step874
  generalize metalogic.g874.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global of index 874
kernel_rfl metalogic_g874 : metalogic.globals[874]? = some metalogic.g874

/-- The program's global of index 874 is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.globals[874]? = some (⟨checkDevTy, «Derivation.checkDev»⟩ : Glob) :=
  metalogic_g874.trans
    (congrArg some (glob_ext checkDev_type metalogic.«Derivation.checkDev_heq»))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g1106.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1106
  generalize metalogic.g1106.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g1107.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1107
  generalize metalogic.g1107.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g1124.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step1124
  generalize metalogic.g1124.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 1106, 1107 and 1124
kernel_rfl metalogic_g1106 : metalogic.globals[1106]? = some metalogic.g1106
kernel_rfl metalogic_g1107 : metalogic.globals[1107]? = some metalogic.g1107
kernel_rfl metalogic_g1124 : metalogic.globals[1124]? = some metalogic.g1124

/-- The program's global of index 1106 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[1106]? = some (⟨listFnTy, «Translation.program»⟩ : Glob) :=
  metalogic_g1106.trans
    (congrArg some (glob_ext program_type metalogic.«Translation.program_heq»))

/-- The program's global of index 1107 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[1107]? = some (⟨listFnTy, «Translation.trGlobals»⟩ : Glob) :=
  metalogic_g1107.trans
    (congrArg some (glob_ext trGlobals_type metalogic.«Translation.trGlobals_heq»))

/-- The program's global of index 1124 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[1124]? = some (⟨thmTy, «Translation.thm»⟩ : Glob) :=
  metalogic_g1124.trans
    (congrArg some (glob_ext thm_type metalogic.«Translation.thm_heq»))

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
theorem byNormW_type : metalogic.g1303.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1303
  generalize metalogic.g1303.1 = T at h ⊢
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
theorem byFunExt_type : metalogic.g1305.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step1305
  generalize metalogic.g1305.1 = T at h ⊢
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
theorem bySplit_type : metalogic.g1306.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1306
  generalize metalogic.g1306.1 = T at h ⊢
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
theorem byListIndWith_type : metalogic.g1307.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step1307
  generalize metalogic.g1307.1 = T at h ⊢
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
theorem byRoseInd_type : metalogic.g1308.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step1308
  generalize metalogic.g1308.1 = T at h ⊢
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
theorem byRoseIndHyp_type : metalogic.g1309.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1309
  generalize metalogic.g1309.1 = T at h ⊢
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

-- the prover's entry points are the program's globals of indices 1179 to 1304
kernel_rfl metalogic_g1179 : metalogic.globals[1179]? = some metalogic.g1179
kernel_rfl metalogic_g1228 : metalogic.globals[1228]? = some metalogic.g1228
kernel_rfl metalogic_g1230 : metalogic.globals[1230]? = some metalogic.g1230
kernel_rfl metalogic_g1231 : metalogic.globals[1231]? = some metalogic.g1231
kernel_rfl metalogic_g1233 : metalogic.globals[1233]? = some metalogic.g1233
kernel_rfl metalogic_g1234 : metalogic.globals[1234]? = some metalogic.g1234
kernel_rfl metalogic_g1303 : metalogic.globals[1303]? = some metalogic.g1303
kernel_rfl metalogic_g1305 : metalogic.globals[1305]? = some metalogic.g1305
kernel_rfl metalogic_g1306 : metalogic.globals[1306]? = some metalogic.g1306
kernel_rfl metalogic_g1307 : metalogic.globals[1307]? = some metalogic.g1307
kernel_rfl metalogic_g1308 : metalogic.globals[1308]? = some metalogic.g1308
kernel_rfl metalogic_g1309 : metalogic.globals[1309]? = some metalogic.g1309

/-- The program's global of index 1179 is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[1179]? = some (⟨prepareTy, «Prover.prepareRules»⟩ : Glob) :=
  metalogic_g1179.trans (congrArg some (glob_ext
    prepareRules_type metalogic.«Prover.prepareRules_heq»))

/-- The program's global of index 1228 is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[1228]? = some (⟨normTy, «Prover.byNorm»⟩ : Glob) :=
  metalogic_g1228.trans (congrArg some (glob_ext
    byNorm_type metalogic.«Prover.byNorm_heq»))

/-- The program's global of index 1230 is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[1230]? = some (⟨indTy, «Prover.byNatInd»⟩ : Glob) :=
  metalogic_g1230.trans (congrArg some (glob_ext
    byNatInd_type metalogic.«Prover.byNatInd_heq»))

/-- The program's global of index 1231 is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[1231]? = some (⟨indTy, «Prover.byListInd»⟩ : Glob) :=
  metalogic_g1231.trans (congrArg some (glob_ext
    byListInd_type metalogic.«Prover.byListInd_heq»))

/-- The program's global of index 1233 is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[1233]? = some (⟨indHypTy, «Prover.byNatIndHyp»⟩ : Glob) :=
  metalogic_g1233.trans (congrArg some (glob_ext
    byNatIndHyp_type metalogic.«Prover.byNatIndHyp_heq»))

/-- The program's global of index 1234 is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[1234]? = some (⟨indHypTy, «Prover.byListIndHyp»⟩ : Glob) :=
  metalogic_g1234.trans (congrArg some (glob_ext
    byListIndHyp_type metalogic.«Prover.byListIndHyp_heq»))

/-- The program's global of index 1303 is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[1303]? = some (⟨normTy, «Prover.byNormW»⟩ : Glob) :=
  metalogic_g1303.trans (congrArg some (glob_ext
    byNormW_type metalogic.«Prover.byNormW_heq»))

/-- The program's global of index 1305 is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[1305]? = some (⟨funExtTy, «Prover.byFunExt»⟩ : Glob) :=
  metalogic_g1305.trans (congrArg some (glob_ext
    byFunExt_type metalogic.«Prover.byFunExt_heq»))

/-- The program's global of index 1306 is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[1306]? = some (⟨proverFnTy, «Prover.bySplit»⟩ : Glob) :=
  metalogic_g1306.trans (congrArg some (glob_ext
    bySplit_type metalogic.«Prover.bySplit_heq»))

/-- The program's global of index 1307 is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[1307]? = some (⟨listIndWithTy, «Prover.byListIndWith»⟩ : Glob) :=
  metalogic_g1307.trans (congrArg some (glob_ext
    byListIndWith_type metalogic.«Prover.byListIndWith_heq»))

/-- The program's global of index 1308 is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[1308]? = some (⟨roseIndTy, «Prover.byRoseInd»⟩ : Glob) :=
  metalogic_g1308.trans (congrArg some (glob_ext
    byRoseInd_type metalogic.«Prover.byRoseInd_heq»))

/-- The program's global of index 1309 is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[1309]? = some (⟨proverFnTy, «Prover.byRoseIndHyp»⟩ : Glob) :=
  metalogic_g1309.trans (congrArg some (glob_ext
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

-- the tactics' entry points are the program's globals of indices 1326 to 1423
kernel_rfl metalogic_g1326 : metalogic.globals[1326]? = some metalogic.g1326
kernel_rfl metalogic_g1327 : metalogic.globals[1327]? = some metalogic.g1327
kernel_rfl metalogic_g1328 : metalogic.globals[1328]? = some metalogic.g1328
kernel_rfl metalogic_g1332 : metalogic.globals[1332]? = some metalogic.g1332
kernel_rfl metalogic_g1333 : metalogic.globals[1333]? = some metalogic.g1333
kernel_rfl metalogic_g1334 : metalogic.globals[1334]? = some metalogic.g1334
kernel_rfl metalogic_g1335 : metalogic.globals[1335]? = some metalogic.g1335
kernel_rfl metalogic_g1337 : metalogic.globals[1337]? = some metalogic.g1337
kernel_rfl metalogic_g1338 : metalogic.globals[1338]? = some metalogic.g1338
kernel_rfl metalogic_g1339 : metalogic.globals[1339]? = some metalogic.g1339
kernel_rfl metalogic_g1340 : metalogic.globals[1340]? = some metalogic.g1340
kernel_rfl metalogic_g1341 : metalogic.globals[1341]? = some metalogic.g1341
kernel_rfl metalogic_g1342 : metalogic.globals[1342]? = some metalogic.g1342
kernel_rfl metalogic_g1343 : metalogic.globals[1343]? = some metalogic.g1343
kernel_rfl metalogic_g1344 : metalogic.globals[1344]? = some metalogic.g1344
kernel_rfl metalogic_g1345 : metalogic.globals[1345]? = some metalogic.g1345
kernel_rfl metalogic_g1346 : metalogic.globals[1346]? = some metalogic.g1346
kernel_rfl metalogic_g1350 : metalogic.globals[1350]? = some metalogic.g1350
kernel_rfl metalogic_g1352 : metalogic.globals[1352]? = some metalogic.g1352
kernel_rfl metalogic_g1354 : metalogic.globals[1354]? = some metalogic.g1354
kernel_rfl metalogic_g1356 : metalogic.globals[1356]? = some metalogic.g1356
kernel_rfl metalogic_g1357 : metalogic.globals[1357]? = some metalogic.g1357
kernel_rfl metalogic_g1360 : metalogic.globals[1360]? = some metalogic.g1360
kernel_rfl metalogic_g1379 : metalogic.globals[1379]? = some metalogic.g1379
kernel_rfl metalogic_g1381 : metalogic.globals[1381]? = some metalogic.g1381
kernel_rfl metalogic_g1403 : metalogic.globals[1403]? = some metalogic.g1403
kernel_rfl metalogic_g1405 : metalogic.globals[1405]? = some metalogic.g1405
kernel_rfl metalogic_g1406 : metalogic.globals[1406]? = some metalogic.g1406
kernel_rfl metalogic_g1410 : metalogic.globals[1410]? = some metalogic.g1410
kernel_rfl metalogic_g1427 : metalogic.globals[1427]? = some metalogic.g1427
kernel_rfl metalogic_g1428 : metalogic.globals[1428]? = some metalogic.g1428

/-- The program's global of index 1326 is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[1326]? = some (⟨modeTy, «Tactics.byMode»⟩ : Glob) :=
  metalogic_g1326.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1326).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byMode_heq»))

/-- The program's global of index 1327 is the mirror's proof by reduction to one weak normal form,
at its type. -/
theorem metalogic_byWeak :
    metalogic.globals[1327]? = some (⟨rulesProverTy, «Tactics.byWeak»⟩ : Glob) :=
  metalogic_g1327.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1327).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byWeak_heq»))

/-- The program's global of index 1328 is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[1328]? = some (⟨nfTy, «Tactics.byNF»⟩ : Glob) :=
  metalogic_g1328.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1328).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    metalogic.«Tactics.byNF_heq»))

/-- The program's global of index 1332 is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[1332]? = some (⟨normHTy, «Tactics.normH»⟩ : Glob) :=
  metalogic_g1332.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1332).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    metalogic.«Tactics.normH_heq»))

/-- The program's global of index 1333 is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[1333]? = some (⟨funExtTy, «Tactics.funExts»⟩ : Glob) :=
  metalogic_g1333.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1333).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.funExts_heq»))

/-- The program's global of index 1334 is the mirror's proof by induction on a list with a step,
both cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[1334]? = some (⟨listIndWeakTy, «Tactics.byListIndWeak»⟩ : Glob) :=
  metalogic_g1334.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1334).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    metalogic.«Tactics.byListIndWeak_heq»))

/-- The program's global of index 1335 is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[1335]? = some (⟨proverFnTy, «Tactics.byRoseIndWith»⟩ : Glob) :=
  metalogic_g1335.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1335).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    metalogic.«Tactics.byRoseIndWith_heq»))

/-- The program's global of index 1337 is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[1337]? = some (⟨splitTy, «Tactics.byListSplit»⟩ : Glob) :=
  metalogic_g1337.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1337).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.byListSplit_heq»))

/-- The program's global of index 1338 is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[1338]? = some (⟨splitTy, «Tactics.bySplit2»⟩ : Glob) :=
  metalogic_g1338.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1338).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.bySplit2_heq»))

/-- The program's global of index 1339 is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[1339]? = some (⟨funExtTy, «Tactics.byListCases»⟩ : Glob) :=
  metalogic_g1339.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1339).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byListCases_heq»))

/-- The program's global of index 1340 is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[1340]? = some (⟨twoProverTy, «Tactics.bitsInd»⟩ : Glob) :=
  metalogic_g1340.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1340).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.bitsInd_heq»))

/-- The program's global of index 1341 is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[1341]? = some (⟨funExtTy, «Tactics.bitsCases»⟩ : Glob) :=
  metalogic_g1341.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1341).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.bitsCases_heq»))

/-- The program's global of index 1342 is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[1342]? = some (⟨byBitsTy, «Tactics.byBits»⟩ : Glob) :=
  metalogic_g1342.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1342).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    metalogic.«Tactics.byBits_heq»))

/-- The program's global of index 1343 is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[1343]? = some (⟨twoProverTy, «Tactics.byLength3»⟩ : Glob) :=
  metalogic_g1343.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1343).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.byLength3_heq»))

/-- The program's global of index 1344 is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[1344]? = some (⟨weakHypsTy, «Tactics.withWeakHyps»⟩ : Glob) :=
  metalogic_g1344.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1344).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    metalogic.«Tactics.withWeakHyps_heq»))

/-- The program's global of index 1345 is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[1345]? = some (⟨rulesProverTy, «Tactics.byListIndHypWeak»⟩ : Glob) :=
  metalogic_g1345.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1345).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byListIndHypWeak_heq»))

/-- The program's global of index 1346 is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[1346]? = some (⟨bitsIndHypTy, «Tactics.byBitsIndHyp»⟩ : Glob) :=
  metalogic_g1346.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1346).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    metalogic.«Tactics.byBitsIndHyp_heq»))

/-- The program's global of index 1350 is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[1350]? = some (⟨instsTy, «Tactics.withInsts»⟩ : Glob) :=
  metalogic_g1350.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1350).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    metalogic.«Tactics.withInsts_heq»))

/-- The program's global of index 1352 is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[1352]? = some (⟨childHypsTy, «Tactics.withChildHyps»⟩ : Glob) :=
  metalogic_g1352.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1352).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    metalogic.«Tactics.withChildHyps_heq»))

/-- The program's global of index 1354 is the mirror's proof by case analysis of a list variable
with a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[1354]? = some (⟨revertTy, «Tactics.revertCase»⟩ : Glob) :=
  metalogic_g1354.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1354).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.revertCase_heq»))

/-- The program's global of index 1356 is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[1356]? = some (⟨impITy, «Tactics.byImpI»⟩ : Glob) :=
  metalogic_g1356.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1356).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    metalogic.«Tactics.byImpI_heq»))

/-- The program's global of index 1357 is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[1357]? = some (⟨impElimTy, «Tactics.withImpElim»⟩ : Glob) :=
  metalogic_g1357.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1357).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    metalogic.«Tactics.withImpElim_heq»))

/-- The program's global of index 1360 is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[1360]? = some (⟨succPredTy, «Tactics.bySuccPred»⟩ : Glob) :=
  metalogic_g1360.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1360).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    metalogic.«Tactics.bySuccPred_heq»))

/-- The program's global of index 1379 is the mirror's proof by rounds of the instance search, at
its type. -/
theorem metalogic_byInsts :
    metalogic.globals[1379]? = some (⟨instsSearchTy, «Tactics.byInsts»⟩ : Glob) :=
  metalogic_g1379.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1379).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byInsts_heq»))

/-- The program's global of index 1381 is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[1381]? = some (⟨autoTy, «Tactics.byAuto»⟩ : Glob) :=
  metalogic_g1381.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1381).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    metalogic.«Tactics.byAuto_heq»))

/-- The program's global of index 1403 is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[1403]? = some (⟨funExtTy, «Tactics.byTreeSplit»⟩ : Glob) :=
  metalogic_g1403.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1403).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byTreeSplit_heq»))

/-- The program's global of index 1405 is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[1405]? = some (⟨autoTTy, «Tactics.byAutoT»⟩ : Glob) :=
  metalogic_g1405.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1405).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    metalogic.«Tactics.byAutoT_heq»))

/-- The program's global of index 1406 is the mirror's proof by reduction or by case analysis,
folded conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[1406]? = some (⟨autoCTy, «Tactics.byAutoC»⟩ : Glob) :=
  metalogic_g1406.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1406).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byAutoC_heq»))

/-- The program's global of index 1410 is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[1410]? = some (⟨maskRwTy, «Tactics.maskRw»⟩ : Glob) :=
  metalogic_g1410.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1410).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    metalogic.«Tactics.maskRw_heq»))

/-- The program's global of index 1427 is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[1427]? = some (⟨maskSubsTy, «Tactics.byMaskSubs»⟩ : Glob) :=
  metalogic_g1427.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1427).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byMaskSubs_heq»))

/-- The program's global of index 1428 is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[1428]? = some (⟨funExtTy, «Tactics.byGeneralize»⟩ : Glob) :=
  metalogic_g1428.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1428).elim fun _ h ↦
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

kernel_rfl metalogic_g1678 : metalogic.globals[1678]? = some metalogic.g1678
kernel_rfl metalogic_g1732 : metalogic.globals[1732]? = some metalogic.g1732
kernel_rfl metalogic_g1738 : metalogic.globals[1738]? = some metalogic.g1738
kernel_rfl metalogic_g1739 : metalogic.globals[1739]? = some metalogic.g1739
kernel_rfl metalogic_g1742 : metalogic.globals[1742]? = some metalogic.g1742
kernel_rfl metalogic_g1743 : metalogic.globals[1743]? = some metalogic.g1743
kernel_rfl metalogic_g1753 : metalogic.globals[1753]? = some metalogic.g1753
kernel_rfl metalogic_g1754 : metalogic.globals[1754]? = some metalogic.g1754
kernel_rfl metalogic_g1755 : metalogic.globals[1755]? = some metalogic.g1755
kernel_rfl metalogic_g1760 : metalogic.globals[1760]? = some metalogic.g1760
kernel_rfl metalogic_g1761 : metalogic.globals[1761]? = some metalogic.g1761
kernel_rfl metalogic_g1762 : metalogic.globals[1762]? = some metalogic.g1762
kernel_rfl metalogic_g1787 : metalogic.globals[1787]? = some metalogic.g1787
kernel_rfl metalogic_g1788 : metalogic.globals[1788]? = some metalogic.g1788

set_option maxRecDepth 100000 in
/-- The program's global of index 1678 is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[1678]? = some (⟨termPMTy, «Combinator.typeTerm»⟩ : Glob) :=
  metalogic_g1678.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1678).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    metalogic.«Combinator.typeTerm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1732 is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[1732]? = some (⟨rulesPMTy, «Combinator.pNormalize»⟩ : Glob) :=
  metalogic_g1732.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1732).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    metalogic.«Combinator.pNormalize_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1738 is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[1738]? = some (⟨instPMTy, «Combinator.pInst»⟩ : Glob) :=
  metalogic_g1738.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1738).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    metalogic.«Combinator.pInst_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1739 is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[1739]? = some (⟨termPMTy, «Combinator.etaExpand»⟩ : Glob) :=
  metalogic_g1739.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1739).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    metalogic.«Combinator.etaExpand_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1742 is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[1742]? = some (⟨treeFnTy, «Combinator.deltaRule»⟩ : Glob) :=
  metalogic_g1742.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1742).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    metalogic.«Combinator.deltaRule_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1743 is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[1743]? = some (⟨rulesPMTy, «Combinator.pByNorm»⟩ : Glob) :=
  metalogic_g1743.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1743).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    metalogic.«Combinator.pByNorm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1753 is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[1753]? = some (⟨proveSeqTy, «Combinator.proveSeq»⟩ : Glob) :=
  metalogic_g1753.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1753).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    metalogic.«Combinator.proveSeq_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1754 is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[1754]? = some (⟨normalizeThmTy, «Combinator.normalizeThm»⟩ : Glob) :=
  metalogic_g1754.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1754).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    metalogic.«Combinator.normalizeThm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1755 is the mirror's instance of a source's sequent, its
hypotheses proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[1755]? = some (⟨instByTy, «Combinator.instBy»⟩ : Glob) :=
  metalogic_g1755.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1755).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    metalogic.«Combinator.instBy_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1760 is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[1760]? = some (⟨natIndPMTy, «Combinator.byNatInduction»⟩ : Glob) :=
  metalogic_g1760.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1760).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    metalogic.«Combinator.byNatInduction_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1761 is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[1761]? = some (⟨listIndPMTy, «Combinator.byListInduction»⟩ : Glob) :=
  metalogic_g1761.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1761).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    metalogic.«Combinator.byListInduction_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1762 is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[1762]? =
      some (⟨listIndPMTy, «Combinator.byListParamInduction»⟩ : Glob) :=
  metalogic_g1762.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1762).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    metalogic.«Combinator.byListParamInduction_heq»))

/-- A global is the pair of a type and a value when its type is that type and its value is
heterogeneously equal to that value. The value is an argument, rather than the second projection
of a pair, so that elaboration assigns it rather than unfolding it. -/
theorem glob_eq_mk {g : Glob} {T : Tree} {x : Ty.den T} (hT : g.1 = T) (hx : HEq g.2 x) :
    g = ⟨T, x⟩ :=
  Sigma.ext hT hx

set_option maxRecDepth 100000 in
/-- The program's global of index 1787 is the mirror's library of derived equations and its
development, at its type. -/
theorem metalogic_libraryWith :
    metalogic.globals[1787]? = some (⟨treeFnTy, «Combinator.libraryWith»⟩ : Glob) :=
  metalogic_g1787.trans (congrArg some (glob_eq_mk
    ((infer_of_loadStep metalogic.step1787).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Combinator.libraryWith_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1788 is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[1788]? = some (⟨libRulesTy, «Combinator.libRules»⟩ : Glob) :=
  metalogic_g1788.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1788).elim fun _ h ↦
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
-- globals of indices 1907 and 1917
kernel_rfl metalogic_g1907 : metalogic.globals[1907]? = some metalogic.g1907
kernel_rfl metalogic_g1917 : metalogic.globals[1917]? = some metalogic.g1917

set_option maxRecDepth 100000 in
/-- The program's global of index 1907 is the mirror's resolution of what the printer writes, at its
type. -/
theorem metalogic_readBack :
    metalogic.globals[1907]? = some (⟨readBackTy, «Printer.readBack»⟩ : Glob) :=
  metalogic_g1907.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1907).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT] h)
    metalogic.«Printer.readBack_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1917 is the mirror's partial printer of kernel terms, at its
type. -/
theorem metalogic_printTermOpt :
    metalogic.globals[1917]? = some (⟨printTermTy, «Printer.printTermOpt»⟩ : Glob) :=
  metalogic_g1917.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1917).elim fun _ h ↦
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

-- the checker's functions are the program's globals of indices 44 to 861
kernel_rfl metalogic_g44 : metalogic.globals[44]? = some metalogic.g44
kernel_rfl metalogic_g45 : metalogic.globals[45]? = some metalogic.g45
kernel_rfl metalogic_g46 : metalogic.globals[46]? = some metalogic.g46
kernel_rfl metalogic_g118 : metalogic.globals[118]? = some metalogic.g118
kernel_rfl metalogic_g160 : metalogic.globals[160]? = some metalogic.g160
kernel_rfl metalogic_g387 : metalogic.globals[387]? = some metalogic.g387
kernel_rfl metalogic_g434 : metalogic.globals[434]? = some metalogic.g434
kernel_rfl metalogic_g866 : metalogic.globals[866]? = some metalogic.g866

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

/-- The program's global of index 866 is the mirror's constants and environment after a
declaration, at its type. -/
theorem metalogic_declStep :
    metalogic.globals[866]? =
      some (⟨[tT, tList tT, tT].foldr tArrow tT, «Derivation.declStep»⟩ : Glob) :=
  metalogic_g866.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step866).elim fun _ h ↦ infer_lams tT _ [tT, tList tT, tT] h)
    metalogic.«Derivation.declStep_heq»))

/-! The tactics' functions of terms. -/

-- the tactics' functions of terms are the program's globals of indices 1364 to 1403
kernel_rfl metalogic_g1364 : metalogic.globals[1364]? = some metalogic.g1364
kernel_rfl metalogic_g1369 : metalogic.globals[1369]? = some metalogic.g1369
kernel_rfl metalogic_g1370 : metalogic.globals[1370]? = some metalogic.g1370
kernel_rfl metalogic_g1373 : metalogic.globals[1373]? = some metalogic.g1373
kernel_rfl metalogic_g1390 : metalogic.globals[1390]? = some metalogic.g1390
kernel_rfl metalogic_g1392 : metalogic.globals[1392]? = some metalogic.g1392
kernel_rfl metalogic_g1394 : metalogic.globals[1394]? = some metalogic.g1394
kernel_rfl metalogic_g1398 : metalogic.globals[1398]? = some metalogic.g1398
kernel_rfl metalogic_g1402 : metalogic.globals[1402]? = some metalogic.g1402
kernel_rfl metalogic_g1408 : metalogic.globals[1408]? = some metalogic.g1408

set_option maxRecDepth 100000 in
/-- The program's global of index 1364 is the mirror's subterms of a term outside binders and
folds' starts and steps, at its type. -/
theorem metalogic_openSubterms :
    metalogic.globals[1364]? =
      some (⟨[tT].foldr tArrow (tList tT), «Tactics.openSubterms»⟩ : Glob) :=
  metalogic_g1364.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1364).elim fun _ h ↦ infer_lams (tList tT) _ [tT] h)
    metalogic.«Tactics.openSubterms_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1369 is the mirror's variable a weak normal form is stuck on, at
its type. -/
theorem metalogic_stuckVar :
    metalogic.globals[1369]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVar»⟩ : Glob) :=
  metalogic_g1369.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1369).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    metalogic.«Tactics.stuckVar_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1370 is the mirror's test that a term mentions a variable, at
its type. -/
theorem metalogic_mentions :
    metalogic.globals[1370]? = some (⟨[tT, tT].foldr tArrow tT, «Tactics.mentions»⟩ : Glob) :=
  metalogic_g1370.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1370).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    metalogic.«Tactics.mentions_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1373 is the mirror's arguments at which the body of an
abstraction matches the subterms of a term, at its type. -/
theorem metalogic_matchesOf :
    metalogic.globals[1373]? =
      some (⟨[tT, tT, tT].foldr tArrow (tList (tList tT)), «Tactics.matchesOf»⟩ : Glob) :=
  metalogic_g1373.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1373).elim fun _ h ↦
      infer_lams (tList (tList tT)) _ [tT, tT, tT] h)
    metalogic.«Tactics.matchesOf_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1390 is the mirror's type, test and branches of a conditional of
the library, at its type. -/
theorem metalogic_condParts :
    metalogic.globals[1390]? = some (⟨[tT].foldr tArrow tT, «Tactics.condParts»⟩ : Glob) :=
  metalogic_g1390.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1390).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Tactics.condParts_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1392 is the mirror's variable a weak normal form is stuck on,
including the test of a folded conditional, at its type. -/
theorem metalogic_stuckVarC :
    metalogic.globals[1392]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVarC»⟩ : Glob) :=
  metalogic_g1392.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1392).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    metalogic.«Tactics.stuckVarC_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1394 is the mirror's applications of a definition to two
arguments among a term's subterms, at its type. -/
theorem metalogic_appsOf :
    metalogic.globals[1394]? =
      some (⟨[tT, tT].foldr tArrow (tList tT), «Tactics.appsOf»⟩ : Glob) :=
  metalogic_g1394.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1394).elim fun _ h ↦ infer_lams (tList tT) _ [tT, tT] h)
    metalogic.«Tactics.appsOf_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1398 is the mirror's unfolding of a tree term, at its type. -/
theorem metalogic_unnodeU :
    metalogic.globals[1398]? = some (⟨[tT].foldr tArrow tT, «Tactics.unnodeU»⟩ : Glob) :=
  metalogic_g1398.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1398).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Tactics.unnodeU_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1402 is the mirror's rewriting of a term in which a tree rebuilt
from the unfolding of a variable stands for the variable, back to the term, at its type. -/
theorem metalogic_occRewrite :
    metalogic.globals[1402]? =
      some (⟨[tT, tT, tT, tT].foldr tArrow tT, «Tactics.occRewrite»⟩ : Glob) :=
  metalogic_g1402.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1402).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT, tT] h)
    metalogic.«Tactics.occRewrite_heq»))

set_option maxRecDepth 100000 in
/-- The program's global of index 1408 is the mirror's abstraction of a term's occurrences of a
term, at its type. -/
theorem metalogic_abstractTerm :
    metalogic.globals[1408]? =
      some (⟨[tT, tT, tT].foldr tArrow tT, «Tactics.abstractTerm»⟩ : Glob) :=
  metalogic_g1408.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1408).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT] h)
    metalogic.«Tactics.abstractTerm_heq»))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
