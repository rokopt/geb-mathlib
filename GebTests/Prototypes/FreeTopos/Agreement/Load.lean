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
definitions: the program's mirror, {lit}`GebMirror.Metalogic`. This module states, and the kernel
checks, that loading the program with {name}`Geb.Kernel.load` gives globals whose denotations are
the mirror's definitions.

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
theorem program_type : metalogic.g533.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step533
  generalize metalogic.g533.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g534.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step534
  generalize metalogic.g534.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g535.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step535
  generalize metalogic.g535.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
-- indices 533, 534 and 535
kernel_rfl metalogic_g533 : metalogic.globals[533]? = some metalogic.g533
kernel_rfl metalogic_g534 : metalogic.globals[534]? = some metalogic.g534
kernel_rfl metalogic_g535 : metalogic.globals[535]? = some metalogic.g535

/-- The program's global of index 533 is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[533]? = some (⟨listFnTy, GebMirror.Metalogic.program⟩ : Glob) :=
  metalogic_g533.trans
    (congrArg some (Sigma.ext program_type (metalogic.program_heq.trans HEq.rfl)))

/-- The program's global of index 534 is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[534]? = some (⟨listFnTy, GebMirror.Metalogic.trGlobals⟩ : Glob) :=
  metalogic_g534.trans
    (congrArg some (Sigma.ext trGlobals_type (metalogic.trGlobals_heq.trans HEq.rfl)))

/-- The program's global of index 535 is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[535]? = some (⟨thmTy, GebMirror.Metalogic.thm⟩ : Glob) :=
  metalogic_g535.trans
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
theorem prepareRules_type : metalogic.g553.1 = prepareTy := by
  have h := infer_of_loadStep metalogic.step553
  generalize metalogic.g553.1 = T at h ⊢
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
theorem byNorm_type : metalogic.g560.1 = normTy := by
  have h := infer_of_loadStep metalogic.step560
  generalize metalogic.g560.1 = T at h ⊢
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
theorem byNatInd_type : metalogic.g562.1 = indTy := by
  have h := infer_of_loadStep metalogic.step562
  generalize metalogic.g562.1 = T at h ⊢
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
theorem byListInd_type : metalogic.g563.1 = indTy := by
  have h := infer_of_loadStep metalogic.step563
  generalize metalogic.g563.1 = T at h ⊢
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
theorem byNatIndHyp_type : metalogic.g565.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step565
  generalize metalogic.g565.1 = T at h ⊢
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
theorem byListIndHyp_type : metalogic.g566.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step566
  generalize metalogic.g566.1 = T at h ⊢
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
theorem byNormW_type : metalogic.g582.1 = normTy := by
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
  obtain ⟨_, _, _, h10, -, -⟩ := infer_app_inv h9
  obtain ⟨_, _, hB, h11⟩ := infer_lam_inv h10
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h11.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the proof by extensionality is its type, read from the
definition's annotations. -/
theorem byFunExt_type : metalogic.g584.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step584
  generalize metalogic.g584.1 = T at h ⊢
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
theorem bySplit_type : metalogic.g585.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step585
  generalize metalogic.g585.1 = T at h ⊢
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
theorem byListIndWith_type : metalogic.g586.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step586
  generalize metalogic.g586.1 = T at h ⊢
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
theorem byRoseInd_type : metalogic.g587.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step587
  generalize metalogic.g587.1 = T at h ⊢
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
theorem byRoseIndHyp_type : metalogic.g588.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step588
  generalize metalogic.g588.1 = T at h ⊢
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

-- the prover's entry points are the program's globals of indices 553 to 588
kernel_rfl metalogic_g553 : metalogic.globals[553]? = some metalogic.g553
kernel_rfl metalogic_g560 : metalogic.globals[560]? = some metalogic.g560
kernel_rfl metalogic_g562 : metalogic.globals[562]? = some metalogic.g562
kernel_rfl metalogic_g563 : metalogic.globals[563]? = some metalogic.g563
kernel_rfl metalogic_g565 : metalogic.globals[565]? = some metalogic.g565
kernel_rfl metalogic_g566 : metalogic.globals[566]? = some metalogic.g566
kernel_rfl metalogic_g582 : metalogic.globals[582]? = some metalogic.g582
kernel_rfl metalogic_g584 : metalogic.globals[584]? = some metalogic.g584
kernel_rfl metalogic_g585 : metalogic.globals[585]? = some metalogic.g585
kernel_rfl metalogic_g586 : metalogic.globals[586]? = some metalogic.g586
kernel_rfl metalogic_g587 : metalogic.globals[587]? = some metalogic.g587
kernel_rfl metalogic_g588 : metalogic.globals[588]? = some metalogic.g588

/-- The program's global of index 553 is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[553]? = some (⟨prepareTy, GebMirror.Metalogic.prepareRules⟩ : Glob) :=
  metalogic_g553.trans (congrArg some (Sigma.ext
    prepareRules_type (metalogic.prepareRules_heq.trans HEq.rfl)))

/-- The program's global of index 560 is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[560]? = some (⟨normTy, GebMirror.Metalogic.byNorm⟩ : Glob) :=
  metalogic_g560.trans (congrArg some (Sigma.ext
    byNorm_type (metalogic.byNorm_heq.trans HEq.rfl)))

/-- The program's global of index 562 is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[562]? = some (⟨indTy, GebMirror.Metalogic.byNatInd⟩ : Glob) :=
  metalogic_g562.trans (congrArg some (Sigma.ext
    byNatInd_type (metalogic.byNatInd_heq.trans HEq.rfl)))

/-- The program's global of index 563 is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[563]? = some (⟨indTy, GebMirror.Metalogic.byListInd⟩ : Glob) :=
  metalogic_g563.trans (congrArg some (Sigma.ext
    byListInd_type (metalogic.byListInd_heq.trans HEq.rfl)))

/-- The program's global of index 565 is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[565]? = some (⟨indHypTy, GebMirror.Metalogic.byNatIndHyp⟩ : Glob) :=
  metalogic_g565.trans (congrArg some (Sigma.ext
    byNatIndHyp_type (metalogic.byNatIndHyp_heq.trans HEq.rfl)))

/-- The program's global of index 566 is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[566]? = some (⟨indHypTy, GebMirror.Metalogic.byListIndHyp⟩ : Glob) :=
  metalogic_g566.trans (congrArg some (Sigma.ext
    byListIndHyp_type (metalogic.byListIndHyp_heq.trans HEq.rfl)))

/-- The program's global of index 582 is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[582]? = some (⟨normTy, GebMirror.Metalogic.byNormW⟩ : Glob) :=
  metalogic_g582.trans (congrArg some (Sigma.ext
    byNormW_type (metalogic.byNormW_heq.trans HEq.rfl)))

/-- The program's global of index 584 is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[584]? = some (⟨funExtTy, GebMirror.Metalogic.byFunExt⟩ : Glob) :=
  metalogic_g584.trans (congrArg some (Sigma.ext
    byFunExt_type (metalogic.byFunExt_heq.trans HEq.rfl)))

/-- The program's global of index 585 is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[585]? = some (⟨proverFnTy, GebMirror.Metalogic.bySplit⟩ : Glob) :=
  metalogic_g585.trans (congrArg some (Sigma.ext
    bySplit_type (metalogic.bySplit_heq.trans HEq.rfl)))

/-- The program's global of index 586 is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[586]? = some (⟨listIndWithTy, GebMirror.Metalogic.byListIndWith⟩ : Glob) :=
  metalogic_g586.trans (congrArg some (Sigma.ext
    byListIndWith_type (metalogic.byListIndWith_heq.trans HEq.rfl)))

/-- The program's global of index 587 is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[587]? = some (⟨roseIndTy, GebMirror.Metalogic.byRoseInd⟩ : Glob) :=
  metalogic_g587.trans (congrArg some (Sigma.ext
    byRoseInd_type (metalogic.byRoseInd_heq.trans HEq.rfl)))

/-- The program's global of index 588 is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[588]? = some (⟨proverFnTy, GebMirror.Metalogic.byRoseIndHyp⟩ : Glob) :=
  metalogic_g588.trans (congrArg some (Sigma.ext
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

-- the tactics' entry points are the program's globals of indices 594 to 672
kernel_rfl metalogic_g594 : metalogic.globals[594]? = some metalogic.g594
kernel_rfl metalogic_g595 : metalogic.globals[595]? = some metalogic.g595
kernel_rfl metalogic_g596 : metalogic.globals[596]? = some metalogic.g596
kernel_rfl metalogic_g600 : metalogic.globals[600]? = some metalogic.g600
kernel_rfl metalogic_g601 : metalogic.globals[601]? = some metalogic.g601
kernel_rfl metalogic_g602 : metalogic.globals[602]? = some metalogic.g602
kernel_rfl metalogic_g603 : metalogic.globals[603]? = some metalogic.g603
kernel_rfl metalogic_g605 : metalogic.globals[605]? = some metalogic.g605
kernel_rfl metalogic_g606 : metalogic.globals[606]? = some metalogic.g606
kernel_rfl metalogic_g607 : metalogic.globals[607]? = some metalogic.g607
kernel_rfl metalogic_g608 : metalogic.globals[608]? = some metalogic.g608
kernel_rfl metalogic_g609 : metalogic.globals[609]? = some metalogic.g609
kernel_rfl metalogic_g610 : metalogic.globals[610]? = some metalogic.g610
kernel_rfl metalogic_g611 : metalogic.globals[611]? = some metalogic.g611
kernel_rfl metalogic_g612 : metalogic.globals[612]? = some metalogic.g612
kernel_rfl metalogic_g613 : metalogic.globals[613]? = some metalogic.g613
kernel_rfl metalogic_g614 : metalogic.globals[614]? = some metalogic.g614
kernel_rfl metalogic_g618 : metalogic.globals[618]? = some metalogic.g618
kernel_rfl metalogic_g620 : metalogic.globals[620]? = some metalogic.g620
kernel_rfl metalogic_g622 : metalogic.globals[622]? = some metalogic.g622
kernel_rfl metalogic_g624 : metalogic.globals[624]? = some metalogic.g624
kernel_rfl metalogic_g625 : metalogic.globals[625]? = some metalogic.g625
kernel_rfl metalogic_g628 : metalogic.globals[628]? = some metalogic.g628
kernel_rfl metalogic_g647 : metalogic.globals[647]? = some metalogic.g647
kernel_rfl metalogic_g649 : metalogic.globals[649]? = some metalogic.g649
kernel_rfl metalogic_g661 : metalogic.globals[661]? = some metalogic.g661
kernel_rfl metalogic_g663 : metalogic.globals[663]? = some metalogic.g663
kernel_rfl metalogic_g664 : metalogic.globals[664]? = some metalogic.g664
kernel_rfl metalogic_g668 : metalogic.globals[668]? = some metalogic.g668
kernel_rfl metalogic_g671 : metalogic.globals[671]? = some metalogic.g671
kernel_rfl metalogic_g672 : metalogic.globals[672]? = some metalogic.g672

/-- The program's global of index 594 is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[594]? = some (⟨modeTy, GebMirror.Metalogic.byMode⟩ : Glob) :=
  metalogic_g594.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step594).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    (metalogic.byMode_heq.trans HEq.rfl)))

/-- The program's global of index 595 is the mirror's proof by reduction to one weak normal form, at
its type. -/
theorem metalogic_byWeak :
    metalogic.globals[595]? = some (⟨rulesProverTy, GebMirror.Metalogic.byWeak⟩ : Glob) :=
  metalogic_g595.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step595).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.byWeak_heq.trans HEq.rfl)))

/-- The program's global of index 596 is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[596]? = some (⟨nfTy, GebMirror.Metalogic.byNF⟩ : Glob) :=
  metalogic_g596.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step596).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    (metalogic.byNF_heq.trans HEq.rfl)))

/-- The program's global of index 600 is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[600]? = some (⟨normHTy, GebMirror.Metalogic.normH⟩ : Glob) :=
  metalogic_g600.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step600).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    (metalogic.normH_heq.trans HEq.rfl)))

/-- The program's global of index 601 is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[601]? = some (⟨funExtTy, GebMirror.Metalogic.funExts⟩ : Glob) :=
  metalogic_g601.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step601).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.funExts_heq.trans HEq.rfl)))

/-- The program's global of index 602 is the mirror's proof by induction on a list with a step, both
cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[602]? = some (⟨listIndWeakTy, GebMirror.Metalogic.byListIndWeak⟩ : Glob) :=
  metalogic_g602.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step602).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    (metalogic.byListIndWeak_heq.trans HEq.rfl)))

/-- The program's global of index 603 is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[603]? = some (⟨proverFnTy, GebMirror.Metalogic.byRoseIndWith⟩ : Glob) :=
  metalogic_g603.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step603).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    (metalogic.byRoseIndWith_heq.trans HEq.rfl)))

/-- The program's global of index 605 is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[605]? = some (⟨splitTy, GebMirror.Metalogic.byListSplit⟩ : Glob) :=
  metalogic_g605.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step605).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.byListSplit_heq.trans HEq.rfl)))

/-- The program's global of index 606 is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[606]? = some (⟨splitTy, GebMirror.Metalogic.bySplit2⟩ : Glob) :=
  metalogic_g606.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step606).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    (metalogic.bySplit2_heq.trans HEq.rfl)))

/-- The program's global of index 607 is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[607]? = some (⟨funExtTy, GebMirror.Metalogic.byListCases⟩ : Glob) :=
  metalogic_g607.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step607).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.byListCases_heq.trans HEq.rfl)))

/-- The program's global of index 608 is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[608]? = some (⟨twoProverTy, GebMirror.Metalogic.bitsInd⟩ : Glob) :=
  metalogic_g608.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step608).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.bitsInd_heq.trans HEq.rfl)))

/-- The program's global of index 609 is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[609]? = some (⟨funExtTy, GebMirror.Metalogic.bitsCases⟩ : Glob) :=
  metalogic_g609.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step609).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.bitsCases_heq.trans HEq.rfl)))

/-- The program's global of index 610 is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[610]? = some (⟨byBitsTy, GebMirror.Metalogic.byBits⟩ : Glob) :=
  metalogic_g610.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step610).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    (metalogic.byBits_heq.trans HEq.rfl)))

/-- The program's global of index 611 is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[611]? = some (⟨twoProverTy, GebMirror.Metalogic.byLength3⟩ : Glob) :=
  metalogic_g611.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step611).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    (metalogic.byLength3_heq.trans HEq.rfl)))

/-- The program's global of index 612 is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[612]? = some (⟨weakHypsTy, GebMirror.Metalogic.withWeakHyps⟩ : Glob) :=
  metalogic_g612.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step612).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    (metalogic.withWeakHyps_heq.trans HEq.rfl)))

/-- The program's global of index 613 is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[613]? = some (⟨rulesProverTy, GebMirror.Metalogic.byListIndHypWeak⟩ : Glob) :=
  metalogic_g613.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step613).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    (metalogic.byListIndHypWeak_heq.trans HEq.rfl)))

/-- The program's global of index 614 is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[614]? = some (⟨bitsIndHypTy, GebMirror.Metalogic.byBitsIndHyp⟩ : Glob) :=
  metalogic_g614.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step614).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    (metalogic.byBitsIndHyp_heq.trans HEq.rfl)))

/-- The program's global of index 618 is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[618]? = some (⟨instsTy, GebMirror.Metalogic.withInsts⟩ : Glob) :=
  metalogic_g618.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step618).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    (metalogic.withInsts_heq.trans HEq.rfl)))

/-- The program's global of index 620 is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[620]? = some (⟨childHypsTy, GebMirror.Metalogic.withChildHyps⟩ : Glob) :=
  metalogic_g620.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step620).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    (metalogic.withChildHyps_heq.trans HEq.rfl)))

/-- The program's global of index 622 is the mirror's proof by case analysis of a list variable with
a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[622]? = some (⟨revertTy, GebMirror.Metalogic.revertCase⟩ : Glob) :=
  metalogic_g622.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step622).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    (metalogic.revertCase_heq.trans HEq.rfl)))

/-- The program's global of index 624 is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[624]? = some (⟨impITy, GebMirror.Metalogic.byImpI⟩ : Glob) :=
  metalogic_g624.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step624).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    (metalogic.byImpI_heq.trans HEq.rfl)))

/-- The program's global of index 625 is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[625]? = some (⟨impElimTy, GebMirror.Metalogic.withImpElim⟩ : Glob) :=
  metalogic_g625.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step625).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    (metalogic.withImpElim_heq.trans HEq.rfl)))

/-- The program's global of index 628 is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[628]? = some (⟨succPredTy, GebMirror.Metalogic.bySuccPred⟩ : Glob) :=
  metalogic_g628.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step628).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    (metalogic.bySuccPred_heq.trans HEq.rfl)))

/-- The program's global of index 647 is the mirror's proof by rounds of the instance search, at its
type. -/
theorem metalogic_byInsts :
    metalogic.globals[647]? = some (⟨instsSearchTy, GebMirror.Metalogic.byInsts⟩ : Glob) :=
  metalogic_g647.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step647).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    (metalogic.byInsts_heq.trans HEq.rfl)))

/-- The program's global of index 649 is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[649]? = some (⟨autoTy, GebMirror.Metalogic.byAuto⟩ : Glob) :=
  metalogic_g649.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step649).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    (metalogic.byAuto_heq.trans HEq.rfl)))

/-- The program's global of index 661 is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[661]? = some (⟨funExtTy, GebMirror.Metalogic.byTreeSplit⟩ : Glob) :=
  metalogic_g661.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step661).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    (metalogic.byTreeSplit_heq.trans HEq.rfl)))

/-- The program's global of index 663 is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[663]? = some (⟨autoTTy, GebMirror.Metalogic.byAutoT⟩ : Glob) :=
  metalogic_g663.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step663).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    (metalogic.byAutoT_heq.trans HEq.rfl)))

/-- The program's global of index 664 is the mirror's proof by reduction or by case analysis, folded
conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[664]? = some (⟨autoCTy, GebMirror.Metalogic.byAutoC⟩ : Glob) :=
  metalogic_g664.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step664).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.byAutoC_heq.trans HEq.rfl)))

/-- The program's global of index 668 is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[668]? = some (⟨maskRwTy, GebMirror.Metalogic.maskRw⟩ : Glob) :=
  metalogic_g668.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step668).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    (metalogic.maskRw_heq.trans HEq.rfl)))

/-- The program's global of index 671 is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[671]? = some (⟨maskSubsTy, GebMirror.Metalogic.byMaskSubs⟩ : Glob) :=
  metalogic_g671.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step671).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    (metalogic.byMaskSubs_heq.trans HEq.rfl)))

/-- The program's global of index 672 is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[672]? = some (⟨funExtTy, GebMirror.Metalogic.byGeneralize⟩ : Glob) :=
  metalogic_g672.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step672).elim fun _ h ↦
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

kernel_rfl metalogic_g736 : metalogic.globals[736]? = some metalogic.g736
kernel_rfl metalogic_g765 : metalogic.globals[765]? = some metalogic.g765
kernel_rfl metalogic_g771 : metalogic.globals[771]? = some metalogic.g771
kernel_rfl metalogic_g772 : metalogic.globals[772]? = some metalogic.g772
kernel_rfl metalogic_g775 : metalogic.globals[775]? = some metalogic.g775
kernel_rfl metalogic_g776 : metalogic.globals[776]? = some metalogic.g776
kernel_rfl metalogic_g777 : metalogic.globals[777]? = some metalogic.g777
kernel_rfl metalogic_g778 : metalogic.globals[778]? = some metalogic.g778
kernel_rfl metalogic_g779 : metalogic.globals[779]? = some metalogic.g779
kernel_rfl metalogic_g784 : metalogic.globals[784]? = some metalogic.g784
kernel_rfl metalogic_g785 : metalogic.globals[785]? = some metalogic.g785
kernel_rfl metalogic_g786 : metalogic.globals[786]? = some metalogic.g786
kernel_rfl metalogic_g803 : metalogic.globals[803]? = some metalogic.g803

set_option maxRecDepth 100000 in
/-- The program's global of index 736 is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[736]? = some (⟨termPMTy, GebMirror.Metalogic.typeTerm⟩ : Glob) :=
  metalogic_g736.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step736).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.typeTerm_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 765 is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[765]? = some (⟨rulesPMTy, GebMirror.Metalogic.pNormalize⟩ : Glob) :=
  metalogic_g765.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step765).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.pNormalize_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 771 is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[771]? = some (⟨instPMTy, GebMirror.Metalogic.pInst⟩ : Glob) :=
  metalogic_g771.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step771).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    (metalogic.pInst_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 772 is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[772]? = some (⟨termPMTy, GebMirror.Metalogic.etaExpand⟩ : Glob) :=
  metalogic_g772.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step772).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    (metalogic.etaExpand_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 775 is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[775]? = some (⟨treeFnTy, GebMirror.Metalogic.deltaRule⟩ : Glob) :=
  metalogic_g775.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step775).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    (metalogic.deltaRule_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 776 is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[776]? = some (⟨rulesPMTy, GebMirror.Metalogic.pByNorm⟩ : Glob) :=
  metalogic_g776.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step776).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    (metalogic.pByNorm_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 777 is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[777]? = some (⟨proveSeqTy, GebMirror.Metalogic.proveSeq⟩ : Glob) :=
  metalogic_g777.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step777).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    (metalogic.proveSeq_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 778 is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[778]? = some (⟨normalizeThmTy, GebMirror.Metalogic.normalizeThm⟩ : Glob) :=
  metalogic_g778.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step778).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    (metalogic.normalizeThm_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 779 is the mirror's instance of a source's sequent, its hypotheses
proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[779]? = some (⟨instByTy, GebMirror.Metalogic.instBy⟩ : Glob) :=
  metalogic_g779.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step779).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    (metalogic.instBy_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 784 is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[784]? = some (⟨natIndPMTy, GebMirror.Metalogic.byNatInduction⟩ : Glob) :=
  metalogic_g784.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step784).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    (metalogic.byNatInduction_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 785 is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[785]? = some (⟨listIndPMTy, GebMirror.Metalogic.byListInduction⟩ : Glob) :=
  metalogic_g785.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step785).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.byListInduction_heq.trans HEq.rfl)))

set_option maxRecDepth 100000 in
/-- The program's global of index 786 is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[786]? =
      some (⟨listIndPMTy, GebMirror.Metalogic.byListParamInduction⟩ : Glob) :=
  metalogic_g786.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step786).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    (metalogic.byListParamInduction_heq.trans HEq.rfl)))

-- The program's global of index 802 is the mirror's library of derived equations and its
-- development, at its type, checked by the kernel: elaborating the global's equality with its
-- mirror makes the elaborator evaluate the checker-evaluator on the definition.
kernel_rfl metalogic_libraryWith :
    metalogic.globals[802]? = some (⟨treeFnTy, GebMirror.Metalogic.libraryWith⟩ : Glob)

set_option maxRecDepth 100000 in
/-- The program's global of index 803 is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[803]? = some (⟨libRulesTy, GebMirror.Metalogic.libRules⟩ : Glob) :=
  metalogic_g803.trans (congrArg some (Sigma.ext
    ((infer_of_loadStep metalogic.step803).elim fun _ h ↦
      infer_lams (tList tT) _ [tT] h)
    (metalogic.libRules_heq.trans HEq.rfl)))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
