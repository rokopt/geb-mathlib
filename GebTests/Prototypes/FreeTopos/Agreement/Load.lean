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
development and the library; and the partial printer of kernel terms and the reader's resolution
of what it prints. Each
type is read from the definition, whose abstractions carry their types and whose body the front end
applies the identity at the result type to, by inverting the checker-evaluator: for the tactics,
the combinator prover and the printer, by one lemma over the list of the abstractions'
annotations, {lit}`infer_lams`. The library, a definition without a declared result type, has the
type the checker-evaluator infers, which the kernel evaluates.

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
  {lit}`metalogic_readBack` — those globals are the mirror's definitions, at those types.

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

open GebMirror (metalogic)

/-- The type of the check of a development written in Geb: from the constants, the entries and
the declarations, to the optional state after them. -/
def checkDevTy : Tree := tArrow tT (tArrow (tList tT) (tArrow (tList tT) tT))

/-- The type the kernel computes for the check's definition is the check's type: the three
abstractions' annotations, over the declared result type, at which the front end applies the
identity to the definition's body. -/
theorem checkDev_type : metalogic.g809.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step809
  generalize metalogic.g809.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global of index 809
kernel_rfl metalogic_g809 : metalogic.globals[809]? = some metalogic.g809

/-- The program's global of index 809 is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.globals[809]? = some (⟨checkDevTy, «Derivation.checkDev»⟩ : Glob) :=
  metalogic_g809.trans
    (congrArg some (Sigma.ext checkDev_type (metalogic.«Derivation.checkDev_heq».trans HEq.rfl)))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g1039.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1039
  generalize metalogic.g1039.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g1040.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step1040
  generalize metalogic.g1040.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g1057.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step1057
  generalize metalogic.g1057.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 1039, 1040 and 1057
kernel_rfl metalogic_g1039 : metalogic.globals[1039]? = some metalogic.g1039
kernel_rfl metalogic_g1040 : metalogic.globals[1040]? = some metalogic.g1040
kernel_rfl metalogic_g1057 : metalogic.globals[1057]? = some metalogic.g1057

/-- The program's global of index 1039 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[1039]? = some (⟨listFnTy, «Translation.program»⟩ : Glob) :=
  metalogic_g1039.trans
    (congrArg some (Sigma.ext program_type (metalogic.«Translation.program_heq».trans HEq.rfl)))

/-- The program's global of index 1040 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[1040]? = some (⟨listFnTy, «Translation.trGlobals»⟩ : Glob) :=
  metalogic_g1040.trans
    (congrArg some (Sigma.ext trGlobals_type (metalogic.«Translation.trGlobals_heq».trans HEq.rfl)))

/-- The program's global of index 1057 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[1057]? = some (⟨thmTy, «Translation.thm»⟩ : Glob) :=
  metalogic_g1057.trans
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
theorem prepareRules_type : metalogic.g1113.1 = prepareTy := by
  have h := infer_of_loadStep metalogic.step1113
  generalize metalogic.g1113.1 = T at h ⊢
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
theorem byNorm_type : metalogic.g1162.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1162
  generalize metalogic.g1162.1 = T at h ⊢
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
theorem byNatInd_type : metalogic.g1164.1 = indTy := by
  have h := infer_of_loadStep metalogic.step1164
  generalize metalogic.g1164.1 = T at h ⊢
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
theorem byListInd_type : metalogic.g1165.1 = indTy := by
  have h := infer_of_loadStep metalogic.step1165
  generalize metalogic.g1165.1 = T at h ⊢
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
theorem byNatIndHyp_type : metalogic.g1167.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step1167
  generalize metalogic.g1167.1 = T at h ⊢
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
theorem byListIndHyp_type : metalogic.g1168.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step1168
  generalize metalogic.g1168.1 = T at h ⊢
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
theorem byNormW_type : metalogic.g1185.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1185
  generalize metalogic.g1185.1 = T at h ⊢
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
theorem byFunExt_type : metalogic.g1187.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step1187
  generalize metalogic.g1187.1 = T at h ⊢
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
theorem bySplit_type : metalogic.g1188.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1188
  generalize metalogic.g1188.1 = T at h ⊢
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
theorem byListIndWith_type : metalogic.g1189.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step1189
  generalize metalogic.g1189.1 = T at h ⊢
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
theorem byRoseInd_type : metalogic.g1190.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step1190
  generalize metalogic.g1190.1 = T at h ⊢
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
theorem byRoseIndHyp_type : metalogic.g1191.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1191
  generalize metalogic.g1191.1 = T at h ⊢
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

-- the prover's entry points are the program's globals of indices 1113 to 1191
kernel_rfl metalogic_g1113 : metalogic.globals[1113]? = some metalogic.g1113
kernel_rfl metalogic_g1162 : metalogic.globals[1162]? = some metalogic.g1162
kernel_rfl metalogic_g1164 : metalogic.globals[1164]? = some metalogic.g1164
kernel_rfl metalogic_g1165 : metalogic.globals[1165]? = some metalogic.g1165
kernel_rfl metalogic_g1167 : metalogic.globals[1167]? = some metalogic.g1167
kernel_rfl metalogic_g1168 : metalogic.globals[1168]? = some metalogic.g1168
kernel_rfl metalogic_g1185 : metalogic.globals[1185]? = some metalogic.g1185
kernel_rfl metalogic_g1187 : metalogic.globals[1187]? = some metalogic.g1187
kernel_rfl metalogic_g1188 : metalogic.globals[1188]? = some metalogic.g1188
kernel_rfl metalogic_g1189 : metalogic.globals[1189]? = some metalogic.g1189
kernel_rfl metalogic_g1190 : metalogic.globals[1190]? = some metalogic.g1190
kernel_rfl metalogic_g1191 : metalogic.globals[1191]? = some metalogic.g1191

/-- The program's global of index 1113 is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[1113]? = some (⟨prepareTy, «Prover.prepareRules»⟩ : Glob) :=
  metalogic_g1113.trans (congrArg some (Sigma.ext
    prepareRules_type (metalogic.«Prover.prepareRules_heq».trans HEq.rfl)))

/-- The program's global of index 1162 is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[1162]? = some (⟨normTy, «Prover.byNorm»⟩ : Glob) :=
  metalogic_g1162.trans (congrArg some (Sigma.ext
    byNorm_type (metalogic.«Prover.byNorm_heq».trans HEq.rfl)))

/-- The program's global of index 1164 is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[1164]? = some (⟨indTy, «Prover.byNatInd»⟩ : Glob) :=
  metalogic_g1164.trans (congrArg some (Sigma.ext
    byNatInd_type (metalogic.«Prover.byNatInd_heq».trans HEq.rfl)))

/-- The program's global of index 1165 is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[1165]? = some (⟨indTy, «Prover.byListInd»⟩ : Glob) :=
  metalogic_g1165.trans (congrArg some (Sigma.ext
    byListInd_type (metalogic.«Prover.byListInd_heq».trans HEq.rfl)))

/-- The program's global of index 1167 is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[1167]? = some (⟨indHypTy, «Prover.byNatIndHyp»⟩ : Glob) :=
  metalogic_g1167.trans (congrArg some (Sigma.ext
    byNatIndHyp_type (metalogic.«Prover.byNatIndHyp_heq».trans HEq.rfl)))

/-- The program's global of index 1168 is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[1168]? = some (⟨indHypTy, «Prover.byListIndHyp»⟩ : Glob) :=
  metalogic_g1168.trans (congrArg some (Sigma.ext
    byListIndHyp_type (metalogic.«Prover.byListIndHyp_heq».trans HEq.rfl)))

/-- The program's global of index 1185 is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[1185]? = some (⟨normTy, «Prover.byNormW»⟩ : Glob) :=
  metalogic_g1185.trans (congrArg some (Sigma.ext
    byNormW_type (metalogic.«Prover.byNormW_heq».trans HEq.rfl)))

/-- The program's global of index 1187 is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[1187]? = some (⟨funExtTy, «Prover.byFunExt»⟩ : Glob) :=
  metalogic_g1187.trans (congrArg some (Sigma.ext
    byFunExt_type (metalogic.«Prover.byFunExt_heq».trans HEq.rfl)))

/-- The program's global of index 1188 is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[1188]? = some (⟨proverFnTy, «Prover.bySplit»⟩ : Glob) :=
  metalogic_g1188.trans (congrArg some (Sigma.ext
    bySplit_type (metalogic.«Prover.bySplit_heq».trans HEq.rfl)))

/-- The program's global of index 1189 is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[1189]? = some (⟨listIndWithTy, «Prover.byListIndWith»⟩ : Glob) :=
  metalogic_g1189.trans (congrArg some (Sigma.ext
    byListIndWith_type (metalogic.«Prover.byListIndWith_heq».trans HEq.rfl)))

/-- The program's global of index 1190 is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[1190]? = some (⟨roseIndTy, «Prover.byRoseInd»⟩ : Glob) :=
  metalogic_g1190.trans (congrArg some (Sigma.ext
    byRoseInd_type (metalogic.«Prover.byRoseInd_heq».trans HEq.rfl)))

/-- The program's global of index 1191 is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[1191]? = some (⟨proverFnTy, «Prover.byRoseIndHyp»⟩ : Glob) :=
  metalogic_g1191.trans (congrArg some (Sigma.ext
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

-- the tactics' entry points are the program's globals of indices 1208 to 1309
kernel_rfl metalogic_g1208 : metalogic.globals[1208]? = some metalogic.g1208
kernel_rfl metalogic_g1209 : metalogic.globals[1209]? = some metalogic.g1209
kernel_rfl metalogic_g1210 : metalogic.globals[1210]? = some metalogic.g1210
kernel_rfl metalogic_g1214 : metalogic.globals[1214]? = some metalogic.g1214
kernel_rfl metalogic_g1215 : metalogic.globals[1215]? = some metalogic.g1215
kernel_rfl metalogic_g1216 : metalogic.globals[1216]? = some metalogic.g1216
kernel_rfl metalogic_g1217 : metalogic.globals[1217]? = some metalogic.g1217
kernel_rfl metalogic_g1219 : metalogic.globals[1219]? = some metalogic.g1219
kernel_rfl metalogic_g1220 : metalogic.globals[1220]? = some metalogic.g1220
kernel_rfl metalogic_g1221 : metalogic.globals[1221]? = some metalogic.g1221
kernel_rfl metalogic_g1222 : metalogic.globals[1222]? = some metalogic.g1222
kernel_rfl metalogic_g1223 : metalogic.globals[1223]? = some metalogic.g1223
kernel_rfl metalogic_g1224 : metalogic.globals[1224]? = some metalogic.g1224
kernel_rfl metalogic_g1225 : metalogic.globals[1225]? = some metalogic.g1225
kernel_rfl metalogic_g1226 : metalogic.globals[1226]? = some metalogic.g1226
kernel_rfl metalogic_g1227 : metalogic.globals[1227]? = some metalogic.g1227
kernel_rfl metalogic_g1228 : metalogic.globals[1228]? = some metalogic.g1228
kernel_rfl metalogic_g1232 : metalogic.globals[1232]? = some metalogic.g1232
kernel_rfl metalogic_g1234 : metalogic.globals[1234]? = some metalogic.g1234
kernel_rfl metalogic_g1236 : metalogic.globals[1236]? = some metalogic.g1236
kernel_rfl metalogic_g1238 : metalogic.globals[1238]? = some metalogic.g1238
kernel_rfl metalogic_g1239 : metalogic.globals[1239]? = some metalogic.g1239
kernel_rfl metalogic_g1242 : metalogic.globals[1242]? = some metalogic.g1242
kernel_rfl metalogic_g1261 : metalogic.globals[1261]? = some metalogic.g1261
kernel_rfl metalogic_g1263 : metalogic.globals[1263]? = some metalogic.g1263
kernel_rfl metalogic_g1284 : metalogic.globals[1284]? = some metalogic.g1284
kernel_rfl metalogic_g1286 : metalogic.globals[1286]? = some metalogic.g1286
kernel_rfl metalogic_g1287 : metalogic.globals[1287]? = some metalogic.g1287
kernel_rfl metalogic_g1291 : metalogic.globals[1291]? = some metalogic.g1291
kernel_rfl metalogic_g1308 : metalogic.globals[1308]? = some metalogic.g1308
kernel_rfl metalogic_g1309 : metalogic.globals[1309]? = some metalogic.g1309

/-- The program's global of index 1208 is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[1208]? = some (⟨modeTy, «Tactics.byMode»⟩ : Glob) :=
  metalogic_g1208.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1208).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    (metalogic.«Tactics.byMode_heq».trans HEq.rfl)))

/-- The program's global of index 1209 is the mirror's proof by reduction to one weak normal form,
at its type. -/
theorem metalogic_byWeak :
    metalogic.globals[1209]? = some (⟨rulesProverTy, «Tactics.byWeak»⟩ : Glob) :=
  metalogic_g1209.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1209).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.«Tactics.byWeak_heq».trans HEq.rfl)))

/-- The program's global of index 1210 is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[1210]? = some (⟨nfTy, «Tactics.byNF»⟩ : Glob) :=
  metalogic_g1210.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1210).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    (metalogic.«Tactics.byNF_heq».trans HEq.rfl)))

/-- The program's global of index 1214 is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[1214]? = some (⟨normHTy, «Tactics.normH»⟩ : Glob) :=
  metalogic_g1214.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1214).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    (metalogic.«Tactics.normH_heq».trans HEq.rfl)))

/-- The program's global of index 1215 is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[1215]? = some (⟨funExtTy, «Tactics.funExts»⟩ : Glob) :=
  metalogic_g1215.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1215).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.funExts_heq».trans HEq.rfl)))

/-- The program's global of index 1216 is the mirror's proof by induction on a list with a step,
both cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[1216]? = some (⟨listIndWeakTy, «Tactics.byListIndWeak»⟩ : Glob) :=
  metalogic_g1216.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1216).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    (metalogic.«Tactics.byListIndWeak_heq».trans HEq.rfl)))

/-- The program's global of index 1217 is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[1217]? = some (⟨proverFnTy, «Tactics.byRoseIndWith»⟩ : Glob) :=
  metalogic_g1217.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1217).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    (metalogic.«Tactics.byRoseIndWith_heq».trans HEq.rfl)))

/-- The program's global of index 1219 is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[1219]? = some (⟨splitTy, «Tactics.byListSplit»⟩ : Glob) :=
  metalogic_g1219.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1219).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.byListSplit_heq».trans HEq.rfl)))

/-- The program's global of index 1220 is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[1220]? = some (⟨splitTy, «Tactics.bySplit2»⟩ : Glob) :=
  metalogic_g1220.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1220).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.bySplit2_heq».trans HEq.rfl)))

/-- The program's global of index 1221 is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[1221]? = some (⟨funExtTy, «Tactics.byListCases»⟩ : Glob) :=
  metalogic_g1221.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1221).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.byListCases_heq».trans HEq.rfl)))

/-- The program's global of index 1222 is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[1222]? = some (⟨twoProverTy, «Tactics.bitsInd»⟩ : Glob) :=
  metalogic_g1222.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1222).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.bitsInd_heq».trans HEq.rfl)))

/-- The program's global of index 1223 is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[1223]? = some (⟨funExtTy, «Tactics.bitsCases»⟩ : Glob) :=
  metalogic_g1223.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1223).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.bitsCases_heq».trans HEq.rfl)))

/-- The program's global of index 1224 is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[1224]? = some (⟨byBitsTy, «Tactics.byBits»⟩ : Glob) :=
  metalogic_g1224.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1224).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    (metalogic.«Tactics.byBits_heq».trans HEq.rfl)))

/-- The program's global of index 1225 is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[1225]? = some (⟨twoProverTy, «Tactics.byLength3»⟩ : Glob) :=
  metalogic_g1225.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1225).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.byLength3_heq».trans HEq.rfl)))

/-- The program's global of index 1226 is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[1226]? = some (⟨weakHypsTy, «Tactics.withWeakHyps»⟩ : Glob) :=
  metalogic_g1226.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1226).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    (metalogic.«Tactics.withWeakHyps_heq».trans HEq.rfl)))

/-- The program's global of index 1227 is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[1227]? = some (⟨rulesProverTy, «Tactics.byListIndHypWeak»⟩ : Glob) :=
  metalogic_g1227.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1227).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.«Tactics.byListIndHypWeak_heq».trans HEq.rfl)))

/-- The program's global of index 1228 is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[1228]? = some (⟨bitsIndHypTy, «Tactics.byBitsIndHyp»⟩ : Glob) :=
  metalogic_g1228.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1228).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    (metalogic.«Tactics.byBitsIndHyp_heq».trans HEq.rfl)))

/-- The program's global of index 1232 is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[1232]? = some (⟨instsTy, «Tactics.withInsts»⟩ : Glob) :=
  metalogic_g1232.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1232).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    (metalogic.«Tactics.withInsts_heq».trans HEq.rfl)))

/-- The program's global of index 1234 is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[1234]? = some (⟨childHypsTy, «Tactics.withChildHyps»⟩ : Glob) :=
  metalogic_g1234.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1234).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    (metalogic.«Tactics.withChildHyps_heq».trans HEq.rfl)))

/-- The program's global of index 1236 is the mirror's proof by case analysis of a list variable
with a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[1236]? = some (⟨revertTy, «Tactics.revertCase»⟩ : Glob) :=
  metalogic_g1236.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1236).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    (metalogic.«Tactics.revertCase_heq».trans HEq.rfl)))

/-- The program's global of index 1238 is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[1238]? = some (⟨impITy, «Tactics.byImpI»⟩ : Glob) :=
  metalogic_g1238.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1238).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    (metalogic.«Tactics.byImpI_heq».trans HEq.rfl)))

/-- The program's global of index 1239 is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[1239]? = some (⟨impElimTy, «Tactics.withImpElim»⟩ : Glob) :=
  metalogic_g1239.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1239).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    (metalogic.«Tactics.withImpElim_heq».trans HEq.rfl)))

/-- The program's global of index 1242 is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[1242]? = some (⟨succPredTy, «Tactics.bySuccPred»⟩ : Glob) :=
  metalogic_g1242.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1242).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    (metalogic.«Tactics.bySuccPred_heq».trans HEq.rfl)))

/-- The program's global of index 1261 is the mirror's proof by rounds of the instance search, at
its type. -/
theorem metalogic_byInsts :
    metalogic.globals[1261]? = some (⟨instsSearchTy, «Tactics.byInsts»⟩ : Glob) :=
  metalogic_g1261.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1261).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    (metalogic.«Tactics.byInsts_heq».trans HEq.rfl)))

/-- The program's global of index 1263 is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[1263]? = some (⟨autoTy, «Tactics.byAuto»⟩ : Glob) :=
  metalogic_g1263.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1263).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    (metalogic.«Tactics.byAuto_heq».trans HEq.rfl)))

/-- The program's global of index 1284 is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[1284]? = some (⟨funExtTy, «Tactics.byTreeSplit»⟩ : Glob) :=
  metalogic_g1284.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1284).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.«Tactics.byTreeSplit_heq».trans HEq.rfl)))

/-- The program's global of index 1286 is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[1286]? = some (⟨autoTTy, «Tactics.byAutoT»⟩ : Glob) :=
  metalogic_g1286.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1286).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    (metalogic.«Tactics.byAutoT_heq».trans HEq.rfl)))

/-- The program's global of index 1287 is the mirror's proof by reduction or by case analysis,
folded conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[1287]? = some (⟨autoCTy, «Tactics.byAutoC»⟩ : Glob) :=
  metalogic_g1287.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1287).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.«Tactics.byAutoC_heq».trans HEq.rfl)))

/-- The program's global of index 1291 is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[1291]? = some (⟨maskRwTy, «Tactics.maskRw»⟩ : Glob) :=
  metalogic_g1291.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1291).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    (metalogic.«Tactics.maskRw_heq».trans HEq.rfl)))

/-- The program's global of index 1308 is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[1308]? = some (⟨maskSubsTy, «Tactics.byMaskSubs»⟩ : Glob) :=
  metalogic_g1308.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1308).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.«Tactics.byMaskSubs_heq».trans HEq.rfl)))

/-- The program's global of index 1309 is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[1309]? = some (⟨funExtTy, «Tactics.byGeneralize»⟩ : Glob) :=
  metalogic_g1309.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1309).elim fun _ h ↦
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

kernel_rfl metalogic_g1559 : metalogic.globals[1559]? = some metalogic.g1559
kernel_rfl metalogic_g1613 : metalogic.globals[1613]? = some metalogic.g1613
kernel_rfl metalogic_g1619 : metalogic.globals[1619]? = some metalogic.g1619
kernel_rfl metalogic_g1620 : metalogic.globals[1620]? = some metalogic.g1620
kernel_rfl metalogic_g1623 : metalogic.globals[1623]? = some metalogic.g1623
kernel_rfl metalogic_g1624 : metalogic.globals[1624]? = some metalogic.g1624
kernel_rfl metalogic_g1634 : metalogic.globals[1634]? = some metalogic.g1634
kernel_rfl metalogic_g1635 : metalogic.globals[1635]? = some metalogic.g1635
kernel_rfl metalogic_g1636 : metalogic.globals[1636]? = some metalogic.g1636
kernel_rfl metalogic_g1641 : metalogic.globals[1641]? = some metalogic.g1641
kernel_rfl metalogic_g1642 : metalogic.globals[1642]? = some metalogic.g1642
kernel_rfl metalogic_g1643 : metalogic.globals[1643]? = some metalogic.g1643
kernel_rfl metalogic_g1669 : metalogic.globals[1669]? = some metalogic.g1669

set_option maxRecDepth 100000 in
/-- The program's global of index 1559 is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[1559]? = some (⟨termPMTy, «Combinator.typeTerm»⟩ : Glob) :=
  metalogic_g1559.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1559).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.«Combinator.typeTerm_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1613 is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[1613]? = some (⟨rulesPMTy, «Combinator.pNormalize»⟩ : Glob) :=
  metalogic_g1613.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1613).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.«Combinator.pNormalize_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1619 is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[1619]? = some (⟨instPMTy, «Combinator.pInst»⟩ : Glob) :=
  metalogic_g1619.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1619).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    (metalogic.«Combinator.pInst_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1620 is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[1620]? = some (⟨termPMTy, «Combinator.etaExpand»⟩ : Glob) :=
  metalogic_g1620.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1620).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.«Combinator.etaExpand_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1623 is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[1623]? = some (⟨treeFnTy, «Combinator.deltaRule»⟩ : Glob) :=
  metalogic_g1623.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1623).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    (metalogic.«Combinator.deltaRule_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1624 is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[1624]? = some (⟨rulesPMTy, «Combinator.pByNorm»⟩ : Glob) :=
  metalogic_g1624.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1624).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.«Combinator.pByNorm_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1634 is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[1634]? = some (⟨proveSeqTy, «Combinator.proveSeq»⟩ : Glob) :=
  metalogic_g1634.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1634).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    (metalogic.«Combinator.proveSeq_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1635 is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[1635]? = some (⟨normalizeThmTy, «Combinator.normalizeThm»⟩ : Glob) :=
  metalogic_g1635.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1635).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    (metalogic.«Combinator.normalizeThm_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1636 is the mirror's instance of a source's sequent, its
hypotheses proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[1636]? = some (⟨instByTy, «Combinator.instBy»⟩ : Glob) :=
  metalogic_g1636.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1636).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    (metalogic.«Combinator.instBy_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1641 is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[1641]? = some (⟨natIndPMTy, «Combinator.byNatInduction»⟩ : Glob) :=
  metalogic_g1641.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1641).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    (metalogic.«Combinator.byNatInduction_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1642 is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[1642]? = some (⟨listIndPMTy, «Combinator.byListInduction»⟩ : Glob) :=
  metalogic_g1642.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1642).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.«Combinator.byListInduction_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1643 is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[1643]? =
      some (⟨listIndPMTy, «Combinator.byListParamInduction»⟩ : Glob) :=
  metalogic_g1643.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1643).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.«Combinator.byListParamInduction_heq».trans HEq.rfl)))

-- The program's global of index 1668 is the mirror's library of derived equations and its
-- development, at its type, checked by the kernel: elaborating the global's equality with its
-- mirror makes the elaborator evaluate the checker-evaluator on the definition.
set_option maxRecDepth 100000 in
kernel_rfl metalogic_libraryWith :
    metalogic.globals[1668]? = some (⟨treeFnTy, «Combinator.libraryWith»⟩ : Glob)

set_option maxRecDepth 100000 in
/-- The program's global of index 1669 is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[1669]? = some (⟨libRulesTy, «Combinator.libRules»⟩ : Glob) :=
  metalogic_g1669.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1669).elim fun _ h ↦
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
-- globals of indices 1787 and 1797
kernel_rfl metalogic_g1787 : metalogic.globals[1787]? = some metalogic.g1787
kernel_rfl metalogic_g1797 : metalogic.globals[1797]? = some metalogic.g1797

set_option maxRecDepth 100000 in
/-- The program's global of index 1787 is the mirror's resolution of what the printer writes, at its
type. -/
theorem metalogic_readBack :
    metalogic.globals[1787]? = some (⟨readBackTy, «Printer.readBack»⟩ : Glob) :=
  metalogic_g1787.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1787).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT] h)
    (metalogic.«Printer.readBack_heq».trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 1797 is the mirror's partial printer of kernel terms, at its
type. -/
theorem metalogic_printTermOpt :
    metalogic.globals[1797]? = some (⟨printTermTy, «Printer.printTermOpt»⟩ : Glob) :=
  metalogic_g1797.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step1797).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tT] h)
    (metalogic.«Printer.printTermOpt_heq».trans HEq.rfl)))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
