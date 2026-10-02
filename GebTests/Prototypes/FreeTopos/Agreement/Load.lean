/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic.Load
public import GebTests.Prototypes.GoedelT.LoadCommand
public import GebTests.Prototypes.GoedelT.MirrorDelta

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

The command {lit}`geb_program` of {lit}`GebTests.Prototypes.GoedelT.LoadCommand` declares the
program's definitions, globals and loading, one definition at a time. Among the globals are the
check of a development, at the type of the function from constants, entries and declarations to a
state; the translations of a program, of its constants and of a theorem of Gödel's T; and the
prover's entry points, the preparation of rules, the proofs by normalization and by induction and
the provers built from provers; the tactics' entry points, the proofs by reduction, case
analysis, induction, hypotheses and search; and the combinator prover's entry points, the typing,
normalization, the proofs by normalization and by induction, the proof of a sequent added to a
development and the library. Each type is read from the definition, whose
abstractions carry their types and whose body the front end applies the identity at the result
type to, by inverting the checker-evaluator: for the tactics and the combinator prover, by one
lemma over the list of the abstractions' annotations, {lit}`infer_lams`.

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
  with the combinator prover's other entry points — those globals are the mirror's definitions, at
  those types.

## Tags

metalogic, checker, translation, prover, tactic, combinator, development, denotation, mirror,
kernel reduction
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Agreement.Load

open Geb Geb.Kernel GebTests.Prototypes.GoedelT.MirrorDelta

set_option maxHeartbeats 20000000 in
-- the generated modules of GebMirror.Metalogic.Load declare the program's definitions and the
-- steps of its loading; the kernel evaluates the checker-evaluator on each exported definition
set_option Elab.async false in
geb_program _root_.GebMirror.metalogic from "bootstrap/prelude.geb" "bootstrap/free-topos/base.geb"
  "bootstrap/free-topos/partial-horn.geb" "bootstrap/free-topos/theory.geb"
  "bootstrap/free-topos/infer.geb" "bootstrap/free-topos/language.geb"
  "bootstrap/free-topos/derivation.geb" "bootstrap/reader.geb" "bootstrap/check.geb"
  "bootstrap/free-topos/translation.geb" "bootstrap/free-topos/prove.geb"
  "bootstrap/free-topos/tactics.geb" "bootstrap/free-topos/combinator.geb"
  mirror GebMirror.Metalogic
  exports checkDev program trGlobals thm prepareRules byNorm byNatInd byListInd byNatIndHyp
    byListIndHyp byNormW byFunExt bySplit byListIndWith byRoseInd byRoseIndHyp byMode byWeak
    byNF normH funExts byListIndWeak byRoseIndWith byListSplit bySplit2 byListCases bitsInd
    bitsCases byBits byLength3 withWeakHyps byListIndHypWeak byBitsIndHyp withInsts withChildHyps
    revertCase byImpI withImpElim bySuccPred byInsts byAuto byTreeSplit byAutoT byAutoC maskRw
    byMaskSubs byGeneralize typeTerm pNormalize pInst etaExpand deltaRule pByNorm proveSeq
    normalizeThm instBy byNatInduction byListInduction byListParamInduction libraryWith libRules

open GebMirror (metalogic)

/-- The type of the check of a development written in Geb: from the constants, the entries and
the declarations, to the optional state after them. -/
def checkDevTy : Tree := tArrow tT (tArrow (tList tT) (tArrow (tList tT) tT))

/-- The type the kernel computes for the check's definition is the check's type: the three
abstractions' annotations, over the declared result type, at which the front end applies the
identity to the definition's body. -/
theorem checkDev_type : metalogic.g372.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step372
  generalize metalogic.g372.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global of index 372
kernel_rfl metalogic_g372 : metalogic.globals[372]? = some metalogic.g372

/-- The program's global of index 372 is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.globals[372]? = some (⟨checkDevTy, GebMirror.Metalogic.checkDev⟩ : Glob) :=
  metalogic_g372.trans
    (congrArg some (Sigma.ext checkDev_type (metalogic.checkDev_heq.trans HEq.rfl)))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g550.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step550
  generalize metalogic.g550.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g551.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step551
  generalize metalogic.g551.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g552.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step552
  generalize metalogic.g552.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 550, 551 and 552
kernel_rfl metalogic_g550 : metalogic.globals[550]? = some metalogic.g550
kernel_rfl metalogic_g551 : metalogic.globals[551]? = some metalogic.g551
kernel_rfl metalogic_g552 : metalogic.globals[552]? = some metalogic.g552

/-- The program's global of index 550 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[550]? = some (⟨listFnTy, GebMirror.Metalogic.program⟩ : Glob) :=
  metalogic_g550.trans
    (congrArg some (Sigma.ext program_type (metalogic.program_heq.trans HEq.rfl)))

/-- The program's global of index 551 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[551]? = some (⟨listFnTy, GebMirror.Metalogic.trGlobals⟩ : Glob) :=
  metalogic_g551.trans
    (congrArg some (Sigma.ext trGlobals_type (metalogic.trGlobals_heq.trans HEq.rfl)))

/-- The program's global of index 552 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[552]? = some (⟨thmTy, GebMirror.Metalogic.thm⟩ : Glob) :=
  metalogic_g552.trans
    (congrArg some (Sigma.ext thm_type (metalogic.thm_heq.trans HEq.rfl)))

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
theorem prepareRules_type : metalogic.g570.1 = prepareTy := by
  have h := infer_of_loadStep metalogic.step570
  generalize metalogic.g570.1 = T at h ⊢
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
theorem byNorm_type : metalogic.g577.1 = normTy := by
  have h := infer_of_loadStep metalogic.step577
  generalize metalogic.g577.1 = T at h ⊢
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
theorem byNatInd_type : metalogic.g579.1 = indTy := by
  have h := infer_of_loadStep metalogic.step579
  generalize metalogic.g579.1 = T at h ⊢
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
theorem byListInd_type : metalogic.g580.1 = indTy := by
  have h := infer_of_loadStep metalogic.step580
  generalize metalogic.g580.1 = T at h ⊢
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
theorem byNatIndHyp_type : metalogic.g582.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step582
  generalize metalogic.g582.1 = T at h ⊢
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
theorem byListIndHyp_type : metalogic.g583.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step583
  generalize metalogic.g583.1 = T at h ⊢
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
theorem byNormW_type : metalogic.g599.1 = normTy := by
  have h := infer_of_loadStep metalogic.step599
  generalize metalogic.g599.1 = T at h ⊢
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
theorem byFunExt_type : metalogic.g601.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step601
  generalize metalogic.g601.1 = T at h ⊢
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
theorem bySplit_type : metalogic.g602.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step602
  generalize metalogic.g602.1 = T at h ⊢
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
theorem byListIndWith_type : metalogic.g603.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step603
  generalize metalogic.g603.1 = T at h ⊢
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
theorem byRoseInd_type : metalogic.g604.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step604
  generalize metalogic.g604.1 = T at h ⊢
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
theorem byRoseIndHyp_type : metalogic.g605.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step605
  generalize metalogic.g605.1 = T at h ⊢
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

-- the prover's entry points are the program's globals of indices 570 to 605
kernel_rfl metalogic_g570 : metalogic.globals[570]? = some metalogic.g570
kernel_rfl metalogic_g577 : metalogic.globals[577]? = some metalogic.g577
kernel_rfl metalogic_g579 : metalogic.globals[579]? = some metalogic.g579
kernel_rfl metalogic_g580 : metalogic.globals[580]? = some metalogic.g580
kernel_rfl metalogic_g582 : metalogic.globals[582]? = some metalogic.g582
kernel_rfl metalogic_g583 : metalogic.globals[583]? = some metalogic.g583
kernel_rfl metalogic_g599 : metalogic.globals[599]? = some metalogic.g599
kernel_rfl metalogic_g601 : metalogic.globals[601]? = some metalogic.g601
kernel_rfl metalogic_g602 : metalogic.globals[602]? = some metalogic.g602
kernel_rfl metalogic_g603 : metalogic.globals[603]? = some metalogic.g603
kernel_rfl metalogic_g604 : metalogic.globals[604]? = some metalogic.g604
kernel_rfl metalogic_g605 : metalogic.globals[605]? = some metalogic.g605

/-- The program's global of index 570 is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[570]? = some (⟨prepareTy, GebMirror.Metalogic.prepareRules⟩ : Glob) :=
  metalogic_g570.trans (congrArg some (Sigma.ext
    prepareRules_type (metalogic.prepareRules_heq.trans HEq.rfl)))

/-- The program's global of index 577 is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[577]? = some (⟨normTy, GebMirror.Metalogic.byNorm⟩ : Glob) :=
  metalogic_g577.trans (congrArg some (Sigma.ext
    byNorm_type (metalogic.byNorm_heq.trans HEq.rfl)))

/-- The program's global of index 579 is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[579]? = some (⟨indTy, GebMirror.Metalogic.byNatInd⟩ : Glob) :=
  metalogic_g579.trans (congrArg some (Sigma.ext
    byNatInd_type (metalogic.byNatInd_heq.trans HEq.rfl)))

/-- The program's global of index 580 is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[580]? = some (⟨indTy, GebMirror.Metalogic.byListInd⟩ : Glob) :=
  metalogic_g580.trans (congrArg some (Sigma.ext
    byListInd_type (metalogic.byListInd_heq.trans HEq.rfl)))

/-- The program's global of index 582 is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[582]? = some (⟨indHypTy, GebMirror.Metalogic.byNatIndHyp⟩ : Glob) :=
  metalogic_g582.trans (congrArg some (Sigma.ext
    byNatIndHyp_type (metalogic.byNatIndHyp_heq.trans HEq.rfl)))

/-- The program's global of index 583 is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[583]? = some (⟨indHypTy, GebMirror.Metalogic.byListIndHyp⟩ : Glob) :=
  metalogic_g583.trans (congrArg some (Sigma.ext
    byListIndHyp_type (metalogic.byListIndHyp_heq.trans HEq.rfl)))

/-- The program's global of index 599 is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[599]? = some (⟨normTy, GebMirror.Metalogic.byNormW⟩ : Glob) :=
  metalogic_g599.trans (congrArg some (Sigma.ext
    byNormW_type (metalogic.byNormW_heq.trans HEq.rfl)))

/-- The program's global of index 601 is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[601]? = some (⟨funExtTy, GebMirror.Metalogic.byFunExt⟩ : Glob) :=
  metalogic_g601.trans (congrArg some (Sigma.ext
    byFunExt_type (metalogic.byFunExt_heq.trans HEq.rfl)))

/-- The program's global of index 602 is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[602]? = some (⟨proverFnTy, GebMirror.Metalogic.bySplit⟩ : Glob) :=
  metalogic_g602.trans (congrArg some (Sigma.ext
    bySplit_type (metalogic.bySplit_heq.trans HEq.rfl)))

/-- The program's global of index 603 is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[603]? = some (⟨listIndWithTy, GebMirror.Metalogic.byListIndWith⟩ : Glob) :=
  metalogic_g603.trans (congrArg some (Sigma.ext
    byListIndWith_type (metalogic.byListIndWith_heq.trans HEq.rfl)))

/-- The program's global of index 604 is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[604]? = some (⟨roseIndTy, GebMirror.Metalogic.byRoseInd⟩ : Glob) :=
  metalogic_g604.trans (congrArg some (Sigma.ext
    byRoseInd_type (metalogic.byRoseInd_heq.trans HEq.rfl)))

/-- The program's global of index 605 is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[605]? = some (⟨proverFnTy, GebMirror.Metalogic.byRoseIndHyp⟩ : Glob) :=
  metalogic_g605.trans (congrArg some (Sigma.ext
    byRoseIndHyp_type (metalogic.byRoseIndHyp_heq.trans HEq.rfl)))

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

-- the tactics' entry points are the program's globals of indices 611 to 689
kernel_rfl metalogic_g611 : metalogic.globals[611]? = some metalogic.g611
kernel_rfl metalogic_g612 : metalogic.globals[612]? = some metalogic.g612
kernel_rfl metalogic_g613 : metalogic.globals[613]? = some metalogic.g613
kernel_rfl metalogic_g617 : metalogic.globals[617]? = some metalogic.g617
kernel_rfl metalogic_g618 : metalogic.globals[618]? = some metalogic.g618
kernel_rfl metalogic_g619 : metalogic.globals[619]? = some metalogic.g619
kernel_rfl metalogic_g620 : metalogic.globals[620]? = some metalogic.g620
kernel_rfl metalogic_g622 : metalogic.globals[622]? = some metalogic.g622
kernel_rfl metalogic_g623 : metalogic.globals[623]? = some metalogic.g623
kernel_rfl metalogic_g624 : metalogic.globals[624]? = some metalogic.g624
kernel_rfl metalogic_g625 : metalogic.globals[625]? = some metalogic.g625
kernel_rfl metalogic_g626 : metalogic.globals[626]? = some metalogic.g626
kernel_rfl metalogic_g627 : metalogic.globals[627]? = some metalogic.g627
kernel_rfl metalogic_g628 : metalogic.globals[628]? = some metalogic.g628
kernel_rfl metalogic_g629 : metalogic.globals[629]? = some metalogic.g629
kernel_rfl metalogic_g630 : metalogic.globals[630]? = some metalogic.g630
kernel_rfl metalogic_g631 : metalogic.globals[631]? = some metalogic.g631
kernel_rfl metalogic_g635 : metalogic.globals[635]? = some metalogic.g635
kernel_rfl metalogic_g637 : metalogic.globals[637]? = some metalogic.g637
kernel_rfl metalogic_g639 : metalogic.globals[639]? = some metalogic.g639
kernel_rfl metalogic_g641 : metalogic.globals[641]? = some metalogic.g641
kernel_rfl metalogic_g642 : metalogic.globals[642]? = some metalogic.g642
kernel_rfl metalogic_g645 : metalogic.globals[645]? = some metalogic.g645
kernel_rfl metalogic_g664 : metalogic.globals[664]? = some metalogic.g664
kernel_rfl metalogic_g666 : metalogic.globals[666]? = some metalogic.g666
kernel_rfl metalogic_g678 : metalogic.globals[678]? = some metalogic.g678
kernel_rfl metalogic_g680 : metalogic.globals[680]? = some metalogic.g680
kernel_rfl metalogic_g681 : metalogic.globals[681]? = some metalogic.g681
kernel_rfl metalogic_g685 : metalogic.globals[685]? = some metalogic.g685
kernel_rfl metalogic_g688 : metalogic.globals[688]? = some metalogic.g688
kernel_rfl metalogic_g689 : metalogic.globals[689]? = some metalogic.g689

/-- The program's global of index 611 is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[611]? = some (⟨modeTy, GebMirror.Metalogic.byMode⟩ : Glob) :=
  metalogic_g611.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step611).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    (metalogic.byMode_heq.trans HEq.rfl)))

/-- The program's global of index 612 is the mirror's proof by reduction to one weak normal form, at
its type. -/
theorem metalogic_byWeak :
    metalogic.globals[612]? = some (⟨rulesProverTy, GebMirror.Metalogic.byWeak⟩ : Glob) :=
  metalogic_g612.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step612).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.byWeak_heq.trans HEq.rfl)))

/-- The program's global of index 613 is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[613]? = some (⟨nfTy, GebMirror.Metalogic.byNF⟩ : Glob) :=
  metalogic_g613.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step613).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    (metalogic.byNF_heq.trans HEq.rfl)))

/-- The program's global of index 617 is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[617]? = some (⟨normHTy, GebMirror.Metalogic.normH⟩ : Glob) :=
  metalogic_g617.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step617).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    (metalogic.normH_heq.trans HEq.rfl)))

/-- The program's global of index 618 is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[618]? = some (⟨funExtTy, GebMirror.Metalogic.funExts⟩ : Glob) :=
  metalogic_g618.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step618).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.funExts_heq.trans HEq.rfl)))

/-- The program's global of index 619 is the mirror's proof by induction on a list with a step, both
cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[619]? = some (⟨listIndWeakTy, GebMirror.Metalogic.byListIndWeak⟩ : Glob) :=
  metalogic_g619.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step619).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    (metalogic.byListIndWeak_heq.trans HEq.rfl)))

/-- The program's global of index 620 is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[620]? = some (⟨proverFnTy, GebMirror.Metalogic.byRoseIndWith⟩ : Glob) :=
  metalogic_g620.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step620).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    (metalogic.byRoseIndWith_heq.trans HEq.rfl)))

/-- The program's global of index 622 is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[622]? = some (⟨splitTy, GebMirror.Metalogic.byListSplit⟩ : Glob) :=
  metalogic_g622.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step622).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.byListSplit_heq.trans HEq.rfl)))

/-- The program's global of index 623 is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[623]? = some (⟨splitTy, GebMirror.Metalogic.bySplit2⟩ : Glob) :=
  metalogic_g623.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step623).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.bySplit2_heq.trans HEq.rfl)))

/-- The program's global of index 624 is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[624]? = some (⟨funExtTy, GebMirror.Metalogic.byListCases⟩ : Glob) :=
  metalogic_g624.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step624).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.byListCases_heq.trans HEq.rfl)))

/-- The program's global of index 625 is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[625]? = some (⟨twoProverTy, GebMirror.Metalogic.bitsInd⟩ : Glob) :=
  metalogic_g625.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step625).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.bitsInd_heq.trans HEq.rfl)))

/-- The program's global of index 626 is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[626]? = some (⟨funExtTy, GebMirror.Metalogic.bitsCases⟩ : Glob) :=
  metalogic_g626.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step626).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.bitsCases_heq.trans HEq.rfl)))

/-- The program's global of index 627 is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[627]? = some (⟨byBitsTy, GebMirror.Metalogic.byBits⟩ : Glob) :=
  metalogic_g627.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step627).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    (metalogic.byBits_heq.trans HEq.rfl)))

/-- The program's global of index 628 is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[628]? = some (⟨twoProverTy, GebMirror.Metalogic.byLength3⟩ : Glob) :=
  metalogic_g628.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step628).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.byLength3_heq.trans HEq.rfl)))

/-- The program's global of index 629 is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[629]? = some (⟨weakHypsTy, GebMirror.Metalogic.withWeakHyps⟩ : Glob) :=
  metalogic_g629.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step629).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    (metalogic.withWeakHyps_heq.trans HEq.rfl)))

/-- The program's global of index 630 is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[630]? = some (⟨rulesProverTy, GebMirror.Metalogic.byListIndHypWeak⟩ : Glob) :=
  metalogic_g630.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step630).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.byListIndHypWeak_heq.trans HEq.rfl)))

/-- The program's global of index 631 is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[631]? = some (⟨bitsIndHypTy, GebMirror.Metalogic.byBitsIndHyp⟩ : Glob) :=
  metalogic_g631.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step631).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    (metalogic.byBitsIndHyp_heq.trans HEq.rfl)))

/-- The program's global of index 635 is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[635]? = some (⟨instsTy, GebMirror.Metalogic.withInsts⟩ : Glob) :=
  metalogic_g635.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step635).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    (metalogic.withInsts_heq.trans HEq.rfl)))

/-- The program's global of index 637 is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[637]? = some (⟨childHypsTy, GebMirror.Metalogic.withChildHyps⟩ : Glob) :=
  metalogic_g637.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step637).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    (metalogic.withChildHyps_heq.trans HEq.rfl)))

/-- The program's global of index 639 is the mirror's proof by case analysis of a list variable with
a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[639]? = some (⟨revertTy, GebMirror.Metalogic.revertCase⟩ : Glob) :=
  metalogic_g639.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step639).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    (metalogic.revertCase_heq.trans HEq.rfl)))

/-- The program's global of index 641 is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[641]? = some (⟨impITy, GebMirror.Metalogic.byImpI⟩ : Glob) :=
  metalogic_g641.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step641).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    (metalogic.byImpI_heq.trans HEq.rfl)))

/-- The program's global of index 642 is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[642]? = some (⟨impElimTy, GebMirror.Metalogic.withImpElim⟩ : Glob) :=
  metalogic_g642.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step642).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    (metalogic.withImpElim_heq.trans HEq.rfl)))

/-- The program's global of index 645 is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[645]? = some (⟨succPredTy, GebMirror.Metalogic.bySuccPred⟩ : Glob) :=
  metalogic_g645.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step645).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    (metalogic.bySuccPred_heq.trans HEq.rfl)))

/-- The program's global of index 664 is the mirror's proof by rounds of the instance search, at its
type. -/
theorem metalogic_byInsts :
    metalogic.globals[664]? = some (⟨instsSearchTy, GebMirror.Metalogic.byInsts⟩ : Glob) :=
  metalogic_g664.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step664).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    (metalogic.byInsts_heq.trans HEq.rfl)))

/-- The program's global of index 666 is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[666]? = some (⟨autoTy, GebMirror.Metalogic.byAuto⟩ : Glob) :=
  metalogic_g666.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step666).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    (metalogic.byAuto_heq.trans HEq.rfl)))

/-- The program's global of index 678 is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[678]? = some (⟨funExtTy, GebMirror.Metalogic.byTreeSplit⟩ : Glob) :=
  metalogic_g678.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step678).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.byTreeSplit_heq.trans HEq.rfl)))

/-- The program's global of index 680 is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[680]? = some (⟨autoTTy, GebMirror.Metalogic.byAutoT⟩ : Glob) :=
  metalogic_g680.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step680).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    (metalogic.byAutoT_heq.trans HEq.rfl)))

/-- The program's global of index 681 is the mirror's proof by reduction or by case analysis, folded
conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[681]? = some (⟨autoCTy, GebMirror.Metalogic.byAutoC⟩ : Glob) :=
  metalogic_g681.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step681).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.byAutoC_heq.trans HEq.rfl)))

/-- The program's global of index 685 is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[685]? = some (⟨maskRwTy, GebMirror.Metalogic.maskRw⟩ : Glob) :=
  metalogic_g685.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step685).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    (metalogic.maskRw_heq.trans HEq.rfl)))

/-- The program's global of index 688 is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[688]? = some (⟨maskSubsTy, GebMirror.Metalogic.byMaskSubs⟩ : Glob) :=
  metalogic_g688.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step688).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.byMaskSubs_heq.trans HEq.rfl)))

/-- The program's global of index 689 is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[689]? = some (⟨funExtTy, GebMirror.Metalogic.byGeneralize⟩ : Glob) :=
  metalogic_g689.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step689).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.byGeneralize_heq.trans HEq.rfl)))

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

kernel_rfl metalogic_g753 : metalogic.globals[753]? = some metalogic.g753
kernel_rfl metalogic_g782 : metalogic.globals[782]? = some metalogic.g782
kernel_rfl metalogic_g788 : metalogic.globals[788]? = some metalogic.g788
kernel_rfl metalogic_g789 : metalogic.globals[789]? = some metalogic.g789
kernel_rfl metalogic_g792 : metalogic.globals[792]? = some metalogic.g792
kernel_rfl metalogic_g793 : metalogic.globals[793]? = some metalogic.g793
kernel_rfl metalogic_g794 : metalogic.globals[794]? = some metalogic.g794
kernel_rfl metalogic_g795 : metalogic.globals[795]? = some metalogic.g795
kernel_rfl metalogic_g796 : metalogic.globals[796]? = some metalogic.g796
kernel_rfl metalogic_g801 : metalogic.globals[801]? = some metalogic.g801
kernel_rfl metalogic_g802 : metalogic.globals[802]? = some metalogic.g802
kernel_rfl metalogic_g803 : metalogic.globals[803]? = some metalogic.g803
kernel_rfl metalogic_g820 : metalogic.globals[820]? = some metalogic.g820

set_option maxRecDepth 100000 in
/-- The program's global of index 753 is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[753]? = some (⟨termPMTy, GebMirror.Metalogic.typeTerm⟩ : Glob) :=
  metalogic_g753.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step753).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.typeTerm_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 782 is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[782]? = some (⟨rulesPMTy, GebMirror.Metalogic.pNormalize⟩ : Glob) :=
  metalogic_g782.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step782).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.pNormalize_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 788 is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[788]? = some (⟨instPMTy, GebMirror.Metalogic.pInst⟩ : Glob) :=
  metalogic_g788.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step788).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    (metalogic.pInst_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 789 is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[789]? = some (⟨termPMTy, GebMirror.Metalogic.etaExpand⟩ : Glob) :=
  metalogic_g789.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step789).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.etaExpand_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 792 is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[792]? = some (⟨treeFnTy, GebMirror.Metalogic.deltaRule⟩ : Glob) :=
  metalogic_g792.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step792).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    (metalogic.deltaRule_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 793 is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[793]? = some (⟨rulesPMTy, GebMirror.Metalogic.pByNorm⟩ : Glob) :=
  metalogic_g793.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step793).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.pByNorm_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 794 is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[794]? = some (⟨proveSeqTy, GebMirror.Metalogic.proveSeq⟩ : Glob) :=
  metalogic_g794.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step794).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    (metalogic.proveSeq_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 795 is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[795]? = some (⟨normalizeThmTy, GebMirror.Metalogic.normalizeThm⟩ : Glob) :=
  metalogic_g795.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step795).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    (metalogic.normalizeThm_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 796 is the mirror's instance of a source's sequent, its hypotheses
proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[796]? = some (⟨instByTy, GebMirror.Metalogic.instBy⟩ : Glob) :=
  metalogic_g796.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step796).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    (metalogic.instBy_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 801 is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[801]? = some (⟨natIndPMTy, GebMirror.Metalogic.byNatInduction⟩ : Glob) :=
  metalogic_g801.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step801).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    (metalogic.byNatInduction_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 802 is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[802]? = some (⟨listIndPMTy, GebMirror.Metalogic.byListInduction⟩ : Glob) :=
  metalogic_g802.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step802).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.byListInduction_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 803 is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[803]? =
      some (⟨listIndPMTy, GebMirror.Metalogic.byListParamInduction⟩ : Glob) :=
  metalogic_g803.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step803).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.byListParamInduction_heq.trans HEq.rfl)))

-- The program's global of index 819 is the mirror's library of derived equations and its
-- development, at its type, checked by the kernel: elaborating the global's equality with its
-- mirror makes the elaborator evaluate the checker-evaluator on the definition.
kernel_rfl metalogic_libraryWith :
    metalogic.globals[819]? = some (⟨treeFnTy, GebMirror.Metalogic.libraryWith⟩ : Glob)

set_option maxRecDepth 100000 in
/-- The program's global of index 820 is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[820]? = some (⟨libRulesTy, GebMirror.Metalogic.libRules⟩ : Glob) :=
  metalogic_g820.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step820).elim fun _ h ↦
      infer_lams (tList tT) _ [tT] h)
    (metalogic.libRules_heq.trans HEq.rfl)))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
