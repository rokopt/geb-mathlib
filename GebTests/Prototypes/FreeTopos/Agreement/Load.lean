/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Metalogic.Load
public import GebTests.Prototypes.ProgramCommand
public import GebTests.Prototypes.CheckMirror
public import Geb.Prototypes.Kernel
public meta import GebTests.Prototypes.Stage0 -- shake: keep

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
program's definitions, as the stage-0 compiler's front end reads them from the sources
({name}`Geb.Kernel.Stage0Tests.bundled`), its globals and its loading, one definition at a time.
Among the globals are the
check of a development, at the type of the function from constants, entries and declarations to a
state; the translations of a program, of its constants and of a theorem of Gödel's T; and the
prover's entry points, the preparation of rules, the proofs by normalization and by induction and
the provers built from provers; the tactics' entry points, the proofs by reduction, case
analysis, induction, hypotheses and search; and the combinator prover's entry points, the typing,
normalization, the proofs by normalization and by induction, the proof of a sequent added to a
development and the library; the partial printer of kernel terms and the reader's resolution
of what it prints; the check of elementary-affine certificates; the conversion checker with the
evaluation at literals; and the checker's functions the
checker of a development is built from, the partial Horn checker of the combinators' certificates,
the theory, the inference of typings and the step of a development, with the tactics' functions of
terms. Each
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
* {lit}`affineCheckTy` — the type of the check of an elementary-affine certificate.
* {lit}`convCheckTy`, {lit}`thmConvChecksTy`, {lit}`litEvalTy`, {lit}`readyTy`,
  {lit}`machineRunTy` — the types of the conversion checker, of its test of a theorem, of the
  evaluation at literals, of its test of readiness and of the reduction by the machine at the
  data of a step.
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
  {lit}`metalogic_readBack`, and {lit}`metalogic_affineCheck`, and {lit}`metalogic_convCheck`
  with the conversion checker's other entry points, and {lit}`metalogic_pcheck` with
  the checker's other functions and {lit}`metalogic_openSubterms` with the tactics' other functions
  of terms — those globals are the mirror's definitions, at those types.

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
geb_program _root_.GebMirror.metalogic
  of Geb.Kernel.Stage0Tests.bundled (include_manifest "bootstrap/metalogic.manifest").toList
  from "bootstrap/metalogic.manifest" mirror GebMirror.Metalogic

open GebMirror (metalogic)

/-- The type of the check of a development written in Geb: from the constants, the entries and
the declarations, to the optional state after them. -/
def checkDevTy : Tree := tArrow tT (tArrow (tList tT) (tArrow (tList tT) tT))

/-- The type the kernel computes for the check's definition is the check's type: the three
abstractions' annotations, over the declared result type, at which the front end applies the
identity to the definition's body. -/
theorem checkDev_type : metalogic.g662.1 = checkDevTy := by
  have h := infer_of_loadStep metalogic.step662
  generalize metalogic.g662.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, rfl, h3⟩ := infer_lam_inv h2
  obtain ⟨_, _, _, h4, -, -⟩ := infer_app_inv h3
  obtain ⟨_, _, hB, h5⟩ := infer_lam_inv h4
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h5.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the check of a development is the program's global
kernel_rfl metalogic_g662 : metalogic.globals[662]? = some metalogic.g662

/-- The program's global is the mirror's check of a development, at the check's
type. -/
theorem metalogic_checkDev :
    metalogic.globals[662]? = some (⟨checkDevTy, «Derivation.checkDev»⟩ : Glob) :=
  metalogic_g662.trans
    (congrArg some (glob_ext checkDev_type metalogic.«Derivation.checkDev_heq»))

/-- The type of the translation of a program's definitions and of the constants of a translated
program: from a list of trees to a tree. -/
def listFnTy : Tree := tArrow (tList tT) tT

/-- The type of the translation of a theorem of Gödel's T: from the globals' types and a theorem
to an optional theorem. -/
def thmTy : Tree := tArrow (tList tT) (tArrow tT tT)

/-- The type the kernel computes for the translation of a program is its type, read from the
definition's annotations. -/
theorem program_type : metalogic.g873.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step873
  generalize metalogic.g873.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the constants of a translated program is their type, read
from the definition's annotations. -/
theorem trGlobals_type : metalogic.g875.1 = listFnTy := by
  have h := infer_of_loadStep metalogic.step875
  generalize metalogic.g875.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, _, h2, -, -⟩ := infer_app_inv h1
  obtain ⟨_, _, hB, h3⟩ := infer_lam_inv h2
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h3.symm.trans (infer_var0 _ _ _)))).1]
  rfl

/-- The type the kernel computes for the translation of a theorem is its type, read from the
definition's annotations. -/
theorem thm_type : metalogic.g888.1 = thmTy := by
  have h := infer_of_loadStep metalogic.step888
  generalize metalogic.g888.1 = T at h ⊢
  obtain ⟨_, h0⟩ := h
  obtain ⟨_, _, rfl, h1⟩ := infer_lam_inv h0
  obtain ⟨_, _, rfl, h2⟩ := infer_lam_inv h1
  obtain ⟨_, _, _, h3, -, -⟩ := infer_app_inv h2
  obtain ⟨_, _, hB, h4⟩ := infer_lam_inv h3
  rw [(tArrow_inj hB).2,
    (Sigma.mk.inj_iff.mp (Option.some.inj (h4.symm.trans (infer_var0 _ _ _)))).1]
  rfl

-- the translations of a program, of its constants and of a theorem are the program's globals of
kernel_rfl metalogic_g873 : metalogic.globals[873]? = some metalogic.g873
kernel_rfl metalogic_g875 : metalogic.globals[875]? = some metalogic.g875
kernel_rfl metalogic_g888 : metalogic.globals[888]? = some metalogic.g888

/-- The program's global is the mirror's translation of a program. -/
theorem metalogic_program :
    metalogic.globals[873]? = some (⟨listFnTy, «Translation.program»⟩ : Glob) :=
  metalogic_g873.trans
    (congrArg some (glob_ext program_type metalogic.«Translation.program_heq»))

/-- The program's global is the mirror's constants of a translated program. -/
theorem metalogic_trGlobals :
    metalogic.globals[875]? = some (⟨listFnTy, «Translation.trGlobals»⟩ : Glob) :=
  metalogic_g875.trans
    (congrArg some (glob_ext trGlobals_type metalogic.«Translation.trGlobals_heq»))

/-- The program's global is the mirror's translation of a theorem. -/
theorem metalogic_thm :
    metalogic.globals[888]? = some (⟨thmTy, «Translation.thm»⟩ : Glob) :=
  metalogic_g888.trans
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
theorem prepareRules_type : metalogic.g929.1 = prepareTy := by
  have h := infer_of_loadStep metalogic.step929
  generalize metalogic.g929.1 = T at h ⊢
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
theorem byNorm_type : metalogic.g991.1 = normTy := by
  have h := infer_of_loadStep metalogic.step991
  generalize metalogic.g991.1 = T at h ⊢
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
theorem byNatInd_type : metalogic.g993.1 = indTy := by
  have h := infer_of_loadStep metalogic.step993
  generalize metalogic.g993.1 = T at h ⊢
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
theorem byListInd_type : metalogic.g994.1 = indTy := by
  have h := infer_of_loadStep metalogic.step994
  generalize metalogic.g994.1 = T at h ⊢
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
theorem byNatIndHyp_type : metalogic.g996.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step996
  generalize metalogic.g996.1 = T at h ⊢
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
theorem byListIndHyp_type : metalogic.g997.1 = indHypTy := by
  have h := infer_of_loadStep metalogic.step997
  generalize metalogic.g997.1 = T at h ⊢
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
theorem byNormW_type : metalogic.g1054.1 = normTy := by
  have h := infer_of_loadStep metalogic.step1054
  generalize metalogic.g1054.1 = T at h ⊢
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
theorem byFunExt_type : metalogic.g1056.1 = funExtTy := by
  have h := infer_of_loadStep metalogic.step1056
  generalize metalogic.g1056.1 = T at h ⊢
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
theorem bySplit_type : metalogic.g1057.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1057
  generalize metalogic.g1057.1 = T at h ⊢
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
theorem byListIndWith_type : metalogic.g1058.1 = listIndWithTy := by
  have h := infer_of_loadStep metalogic.step1058
  generalize metalogic.g1058.1 = T at h ⊢
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
theorem byRoseInd_type : metalogic.g1059.1 = roseIndTy := by
  have h := infer_of_loadStep metalogic.step1059
  generalize metalogic.g1059.1 = T at h ⊢
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
theorem byRoseIndHyp_type : metalogic.g1060.1 = proverFnTy := by
  have h := infer_of_loadStep metalogic.step1060
  generalize metalogic.g1060.1 = T at h ⊢
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

-- the prover's entry points in the program's globals
kernel_rfl metalogic_g929 : metalogic.globals[929]? = some metalogic.g929
kernel_rfl metalogic_g991 : metalogic.globals[991]? = some metalogic.g991
kernel_rfl metalogic_g993 : metalogic.globals[993]? = some metalogic.g993
kernel_rfl metalogic_g994 : metalogic.globals[994]? = some metalogic.g994
kernel_rfl metalogic_g996 : metalogic.globals[996]? = some metalogic.g996
kernel_rfl metalogic_g997 : metalogic.globals[997]? = some metalogic.g997
kernel_rfl metalogic_g1054 : metalogic.globals[1054]? = some metalogic.g1054
kernel_rfl metalogic_g1056 : metalogic.globals[1056]? = some metalogic.g1056
kernel_rfl metalogic_g1057 : metalogic.globals[1057]? = some metalogic.g1057
kernel_rfl metalogic_g1058 : metalogic.globals[1058]? = some metalogic.g1058
kernel_rfl metalogic_g1059 : metalogic.globals[1059]? = some metalogic.g1059
kernel_rfl metalogic_g1060 : metalogic.globals[1060]? = some metalogic.g1060

/-- The program's global is the mirror's preparation of rules, at its type. -/
theorem metalogic_prepareRules :
    metalogic.globals[929]? = some (⟨prepareTy, «Prover.prepareRules»⟩ : Glob) :=
  metalogic_g929.trans (congrArg some (glob_ext
    prepareRules_type metalogic.«Prover.prepareRules_heq»))

/-- The program's global is the mirror's proof by normalization, at its type. -/
theorem metalogic_byNorm :
    metalogic.globals[991]? = some (⟨normTy, «Prover.byNorm»⟩ : Glob) :=
  metalogic_g991.trans (congrArg some (glob_ext
    byNorm_type metalogic.«Prover.byNorm_heq»))

/-- The program's global is the mirror's proof by induction on a natural number
with a step, at its type. -/
theorem metalogic_byNatInd :
    metalogic.globals[993]? = some (⟨indTy, «Prover.byNatInd»⟩ : Glob) :=
  metalogic_g993.trans (congrArg some (glob_ext
    byNatInd_type metalogic.«Prover.byNatInd_heq»))

/-- The program's global is the mirror's proof by induction on a list with a step,
at its type. -/
theorem metalogic_byListInd :
    metalogic.globals[994]? = some (⟨indTy, «Prover.byListInd»⟩ : Glob) :=
  metalogic_g994.trans (congrArg some (glob_ext
    byListInd_type metalogic.«Prover.byListInd_heq»))

/-- The program's global is the mirror's proof by induction on a natural number
with the induction hypothesis, at its type. -/
theorem metalogic_byNatIndHyp :
    metalogic.globals[996]? = some (⟨indHypTy, «Prover.byNatIndHyp»⟩ : Glob) :=
  metalogic_g996.trans (congrArg some (glob_ext
    byNatIndHyp_type metalogic.«Prover.byNatIndHyp_heq»))

/-- The program's global is the mirror's proof by induction on a list with the
induction hypothesis, at its type. -/
theorem metalogic_byListIndHyp :
    metalogic.globals[997]? = some (⟨indHypTy, «Prover.byListIndHyp»⟩ : Glob) :=
  metalogic_g997.trans (congrArg some (glob_ext
    byListIndHyp_type metalogic.«Prover.byListIndHyp_heq»))

/-- The program's global is the mirror's proof by normalization through weak head
normal forms, at its type. -/
theorem metalogic_byNormW :
    metalogic.globals[1054]? = some (⟨normTy, «Prover.byNormW»⟩ : Glob) :=
  metalogic_g1054.trans (congrArg some (glob_ext
    byNormW_type metalogic.«Prover.byNormW_heq»))

/-- The program's global is the mirror's proof by extensionality, at its type. -/
theorem metalogic_byFunExt :
    metalogic.globals[1056]? = some (⟨funExtTy, «Prover.byFunExt»⟩ : Glob) :=
  metalogic_g1056.trans (congrArg some (glob_ext
    byFunExt_type metalogic.«Prover.byFunExt_heq»))

/-- The program's global is the mirror's proof by case analysis, at its type. -/
theorem metalogic_bySplit :
    metalogic.globals[1057]? = some (⟨proverFnTy, «Prover.bySplit»⟩ : Glob) :=
  metalogic_g1057.trans (congrArg some (glob_ext
    bySplit_type metalogic.«Prover.bySplit_heq»))

/-- The program's global is the mirror's proof by induction on a list with the
premises' provers, at its type. -/
theorem metalogic_byListIndWith :
    metalogic.globals[1058]? = some (⟨listIndWithTy, «Prover.byListIndWith»⟩ : Glob) :=
  metalogic_g1058.trans (congrArg some (glob_ext
    byListIndWith_type metalogic.«Prover.byListIndWith_heq»))

/-- The program's global is the mirror's proof by the uniqueness of the fold of a
rose tree, at its type. -/
theorem metalogic_byRoseInd :
    metalogic.globals[1059]? = some (⟨roseIndTy, «Prover.byRoseInd»⟩ : Glob) :=
  metalogic_g1059.trans (congrArg some (glob_ext
    byRoseInd_type metalogic.«Prover.byRoseInd_heq»))

/-- The program's global is the mirror's proof by induction on a rose tree with the
induction hypothesis, at its type. -/
theorem metalogic_byRoseIndHyp :
    metalogic.globals[1060]? = some (⟨proverFnTy, «Prover.byRoseIndHyp»⟩ : Glob) :=
  metalogic_g1060.trans (congrArg some (glob_ext
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

-- the tactics' entry points in the program's globals
kernel_rfl metalogic_g1228 : metalogic.globals[1228]? = some metalogic.g1228
kernel_rfl metalogic_g1229 : metalogic.globals[1229]? = some metalogic.g1229
kernel_rfl metalogic_g1230 : metalogic.globals[1230]? = some metalogic.g1230
kernel_rfl metalogic_g1234 : metalogic.globals[1234]? = some metalogic.g1234
kernel_rfl metalogic_g1235 : metalogic.globals[1235]? = some metalogic.g1235
kernel_rfl metalogic_g1236 : metalogic.globals[1236]? = some metalogic.g1236
kernel_rfl metalogic_g1237 : metalogic.globals[1237]? = some metalogic.g1237
kernel_rfl metalogic_g1239 : metalogic.globals[1239]? = some metalogic.g1239
kernel_rfl metalogic_g1240 : metalogic.globals[1240]? = some metalogic.g1240
kernel_rfl metalogic_g1241 : metalogic.globals[1241]? = some metalogic.g1241
kernel_rfl metalogic_g1242 : metalogic.globals[1242]? = some metalogic.g1242
kernel_rfl metalogic_g1243 : metalogic.globals[1243]? = some metalogic.g1243
kernel_rfl metalogic_g1244 : metalogic.globals[1244]? = some metalogic.g1244
kernel_rfl metalogic_g1245 : metalogic.globals[1245]? = some metalogic.g1245
kernel_rfl metalogic_g1254 : metalogic.globals[1254]? = some metalogic.g1254
kernel_rfl metalogic_g1255 : metalogic.globals[1255]? = some metalogic.g1255
kernel_rfl metalogic_g1256 : metalogic.globals[1256]? = some metalogic.g1256
kernel_rfl metalogic_g1260 : metalogic.globals[1260]? = some metalogic.g1260
kernel_rfl metalogic_g1262 : metalogic.globals[1262]? = some metalogic.g1262
kernel_rfl metalogic_g1264 : metalogic.globals[1264]? = some metalogic.g1264
kernel_rfl metalogic_g1266 : metalogic.globals[1266]? = some metalogic.g1266
kernel_rfl metalogic_g1267 : metalogic.globals[1267]? = some metalogic.g1267
kernel_rfl metalogic_g1270 : metalogic.globals[1270]? = some metalogic.g1270
kernel_rfl metalogic_g1291 : metalogic.globals[1291]? = some metalogic.g1291
kernel_rfl metalogic_g1293 : metalogic.globals[1293]? = some metalogic.g1293
kernel_rfl metalogic_g1314 : metalogic.globals[1314]? = some metalogic.g1314
kernel_rfl metalogic_g1316 : metalogic.globals[1316]? = some metalogic.g1316
kernel_rfl metalogic_g1317 : metalogic.globals[1317]? = some metalogic.g1317
kernel_rfl metalogic_g1321 : metalogic.globals[1321]? = some metalogic.g1321
kernel_rfl metalogic_g1338 : metalogic.globals[1338]? = some metalogic.g1338
kernel_rfl metalogic_g1339 : metalogic.globals[1339]? = some metalogic.g1339

/-- The program's global is the mirror's proof by reduction to one normal form at a
depth, at its type. -/
theorem metalogic_byMode :
    metalogic.globals[1228]? = some (⟨modeTy, «Tactics.byMode»⟩ : Glob) :=
  metalogic_g1228.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1228).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byMode_heq»))

/-- The program's global is the mirror's proof by reduction to one weak normal form,
at its type. -/
theorem metalogic_byWeak :
    metalogic.globals[1229]? = some (⟨rulesProverTy, «Tactics.byWeak»⟩ : Glob) :=
  metalogic_g1229.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1229).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byWeak_heq»))

/-- The program's global is the mirror's proof by that of the sides' normal forms at a
depth, at its type. -/
theorem metalogic_byNF :
    metalogic.globals[1230]? = some (⟨nfTy, «Tactics.byNF»⟩ : Glob) :=
  metalogic_g1230.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1230).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, proverTy] h)
    metalogic.«Tactics.byNF_heq»))

/-- The program's global is the mirror's proof by normalization with the hypotheses as
rules, at its type. -/
theorem metalogic_normH :
    metalogic.globals[1234]? = some (⟨normHTy, «Tactics.normH»⟩ : Glob) :=
  metalogic_g1234.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1234).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy] h)
    metalogic.«Tactics.normH_heq»))

/-- The program's global is the mirror's proof by extensionality a number of times, at
its type. -/
theorem metalogic_funExts :
    metalogic.globals[1235]? = some (⟨funExtTy, «Tactics.funExts»⟩ : Glob) :=
  metalogic_g1235.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1235).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.funExts_heq»))

/-- The program's global is the mirror's proof by induction on a list with a step,
both cases by weak reduction, at its type. -/
theorem metalogic_byListIndWeak :
    metalogic.globals[1236]? = some (⟨listIndWeakTy, «Tactics.byListIndWeak»⟩ : Glob) :=
  metalogic_g1236.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1236).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy] h)
    metalogic.«Tactics.byListIndWeak_heq»))

/-- The program's global is the mirror's proof by the uniqueness of the fold of a rose
tree, the step's premise by a prover, at its type. -/
theorem metalogic_byRoseIndWith :
    metalogic.globals[1237]? = some (⟨proverFnTy, «Tactics.byRoseIndWith»⟩ : Glob) :=
  metalogic_g1237.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1237).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy] h)
    metalogic.«Tactics.byRoseIndWith_heq»))

/-- The program's global is the mirror's proof by case analysis of a list variable, at
its type. -/
theorem metalogic_byListSplit :
    metalogic.globals[1239]? = some (⟨splitTy, «Tactics.byListSplit»⟩ : Glob) :=
  metalogic_g1239.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1239).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.byListSplit_heq»))

/-- The program's global is the mirror's proof by case analysis of a coproduct
variable, at its type. -/
theorem metalogic_bySplit2 :
    metalogic.globals[1240]? = some (⟨splitTy, «Tactics.bySplit2»⟩ : Glob) :=
  metalogic_g1240.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1240).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.bySplit2_heq»))

/-- The program's global is the mirror's proof by case analysis of the innermost list
variable, at its type. -/
theorem metalogic_byListCases :
    metalogic.globals[1241]? = some (⟨funExtTy, «Tactics.byListCases»⟩ : Glob) :=
  metalogic_g1241.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1241).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byListCases_heq»))

/-- The program's global is the mirror's proof by induction on a bitstring, at its
type. -/
theorem metalogic_bitsInd :
    metalogic.globals[1242]? = some (⟨twoProverTy, «Tactics.bitsInd»⟩ : Glob) :=
  metalogic_g1242.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1242).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.bitsInd_heq»))

/-- The program's global is the mirror's proof by case analysis of a bitstring, at its
type. -/
theorem metalogic_bitsCases :
    metalogic.globals[1243]? = some (⟨funExtTy, «Tactics.bitsCases»⟩ : Glob) :=
  metalogic_g1243.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1243).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.bitsCases_heq»))

/-- The program's global is the mirror's proof by case analysis of bitstrings to a
depth, at its type. -/
theorem metalogic_byBits :
    metalogic.globals[1244]? = some (⟨byBitsTy, «Tactics.byBits»⟩ : Glob) :=
  metalogic_g1244.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1244).elim fun _ h ↦
      infer_lams (tArrow tT proverTy) _ [tT, proverTy, tT] h)
    metalogic.«Tactics.byBits_heq»))

/-- The program's global is the mirror's proof by case analysis of a list to length
three, at its type. -/
theorem metalogic_byLength3 :
    metalogic.globals[1245]? = some (⟨twoProverTy, «Tactics.byLength3»⟩ : Glob) :=
  metalogic_g1245.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1245).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.byLength3_heq»))

/-- The program's global is the mirror's proof with hypotheses cut in in normal form
and used as rules, at its type. -/
theorem metalogic_withWeakHyps :
    metalogic.globals[1254]? = some (⟨weakHypsTy, «Tactics.withWeakHyps»⟩ : Glob) :=
  metalogic_g1254.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1254).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tList tT, krTy, tT] h)
    metalogic.«Tactics.withWeakHyps_heq»))

/-- The program's global is the mirror's proof by induction on a list with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byListIndHypWeak :
    metalogic.globals[1255]? = some (⟨rulesProverTy, «Tactics.byListIndHypWeak»⟩ : Glob) :=
  metalogic_g1255.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1255).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy] h)
    metalogic.«Tactics.byListIndHypWeak_heq»))

/-- The program's global is the mirror's proof by induction on a bitstring with the
induction hypothesis as a rule, at its type. -/
theorem metalogic_byBitsIndHyp :
    metalogic.globals[1256]? = some (⟨bitsIndHypTy, «Tactics.byBitsIndHyp»⟩ : Glob) :=
  metalogic_g1256.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1256).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, rulesTy, tT] h)
    metalogic.«Tactics.byBitsIndHyp_heq»))

/-- The program's global is the mirror's proof with the instances of a hypothesis
equating functions cut in, at its type. -/
theorem metalogic_withInsts :
    metalogic.globals[1260]? = some (⟨instsTy, «Tactics.withInsts»⟩ : Glob) :=
  metalogic_g1260.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1260).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tssTy, krTy, tT] h)
    metalogic.«Tactics.withInsts_heq»))

/-- The program's global is the mirror's proof with the hypotheses at the children of
an induction on rose trees, at its type. -/
theorem metalogic_withChildHyps :
    metalogic.globals[1262]? = some (⟨childHypsTy, «Tactics.withChildHyps»⟩ : Glob) :=
  metalogic_g1262.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1262).elim fun _ h ↦
      infer_lams proverTy _
        [tT, tList tT, tT, rulesTy, tT, tList tT, tArrow tT tssTy, tArrow (tList tT) proverTy] h)
    metalogic.«Tactics.withChildHyps_heq»))

/-- The program's global is the mirror's proof by case analysis of a list variable
with a hypothesis reverted, at its type. -/
theorem metalogic_revertCase :
    metalogic.globals[1264]? = some (⟨revertTy, «Tactics.revertCase»⟩ : Glob) :=
  metalogic_g1264.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1264).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tT, tT, tT, proverTy, proverTy] h)
    metalogic.«Tactics.revertCase_heq»))

/-- The program's global is the mirror's proof of an implication by its introduction,
at its type. -/
theorem metalogic_byImpI :
    metalogic.globals[1266]? = some (⟨impITy, «Tactics.byImpI»⟩ : Glob) :=
  metalogic_g1266.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1266).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, proverTy] h)
    metalogic.«Tactics.byImpI_heq»))

/-- The program's global is the mirror's proof with implications eliminated, at its
type. -/
theorem metalogic_withImpElim :
    metalogic.globals[1267]? = some (⟨impElimTy, «Tactics.withImpElim»⟩ : Glob) :=
  metalogic_g1267.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1267).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tT, tList tT, krTy] h)
    metalogic.«Tactics.withImpElim_heq»))

/-- The program's global is the mirror's proof by rewriting a predecessor's successor,
at its type. -/
theorem metalogic_bySuccPred :
    metalogic.globals[1270]? = some (⟨succPredTy, «Tactics.bySuccPred»⟩ : Glob) :=
  metalogic_g1270.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1270).elim fun _ h ↦
      infer_lams proverTy _ [tList tT, tT, proverTy] h)
    metalogic.«Tactics.bySuccPred_heq»))

/-- The program's global is the mirror's proof by rounds of the instance search, at
its type. -/
theorem metalogic_byInsts :
    metalogic.globals[1291]? = some (⟨instsSearchTy, «Tactics.byInsts»⟩ : Glob) :=
  metalogic_g1291.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1291).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, tList tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byInsts_heq»))

/-- The program's global is the mirror's proof by the instance search or by case
analysis, to a depth, at its type. -/
theorem metalogic_byAuto :
    metalogic.globals[1293]? = some (⟨autoTy, «Tactics.byAuto»⟩ : Glob) :=
  metalogic_g1293.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1293).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, rulesTy, tT, tT] h)
    metalogic.«Tactics.byAuto_heq»))

/-- The program's global is the mirror's proof by case analysis of a tree variable, at
its type. -/
theorem metalogic_byTreeSplit :
    metalogic.globals[1314]? = some (⟨funExtTy, «Tactics.byTreeSplit»⟩ : Glob) :=
  metalogic_g1314.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1314).elim fun _ h ↦
      infer_lams proverTy _ [tT, tT, proverTy] h)
    metalogic.«Tactics.byTreeSplit_heq»))

/-- The program's global is the mirror's proof by reduction, the instance search or
case analysis of lists, coproducts and trees, at its type. -/
theorem metalogic_byAutoT :
    metalogic.globals[1316]? = some (⟨autoTTy, «Tactics.byAutoT»⟩ : Glob) :=
  metalogic_g1316.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1316).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT, tT] h)
    metalogic.«Tactics.byAutoT_heq»))

/-- The program's global is the mirror's proof by reduction or by case analysis,
folded conditionals' tests among the variables, at its type. -/
theorem metalogic_byAutoC :
    metalogic.globals[1317]? = some (⟨autoCTy, «Tactics.byAutoC»⟩ : Glob) :=
  metalogic_g1317.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1317).elim fun _ h ↦
      infer_lams proverTy _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byAutoC_heq»))

/-- The program's global is the mirror's derivation of a rewriting under a
conditional's mask, at its type. -/
theorem metalogic_maskRw :
    metalogic.globals[1321]? = some (⟨maskRwTy, «Tactics.maskRw»⟩ : Glob) :=
  metalogic_g1321.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1321).elim fun _ h ↦
      infer_lams tT _ [tT, tT, tT, tT, tList tT, tList tT, tT, tT, tT, tT, tT, tT] h)
    metalogic.«Tactics.maskRw_heq»))

/-- The program's global is the mirror's proof by rewriting under masks by the
hypotheses, at its type. -/
theorem metalogic_byMaskSubs :
    metalogic.globals[1338]? = some (⟨maskSubsTy, «Tactics.byMaskSubs»⟩ : Glob) :=
  metalogic_g1338.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1338).elim fun _ h ↦
      infer_lams (tArrow krTy proverTy) _ [tT, tList tT, tT, tT, rulesTy, tT] h)
    metalogic.«Tactics.byMaskSubs_heq»))

/-- The program's global is the mirror's proof by generalizing a term, at its type. -/
theorem metalogic_byGeneralize :
    metalogic.globals[1339]? = some (⟨funExtTy, «Tactics.byGeneralize»⟩ : Glob) :=
  metalogic_g1339.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1339).elim fun _ h ↦
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

kernel_rfl metalogic_g1509 : metalogic.globals[1509]? = some metalogic.g1509
kernel_rfl metalogic_g1575 : metalogic.globals[1575]? = some metalogic.g1575
kernel_rfl metalogic_g1585 : metalogic.globals[1585]? = some metalogic.g1585
kernel_rfl metalogic_g1587 : metalogic.globals[1587]? = some metalogic.g1587
kernel_rfl metalogic_g1590 : metalogic.globals[1590]? = some metalogic.g1590
kernel_rfl metalogic_g1593 : metalogic.globals[1593]? = some metalogic.g1593
kernel_rfl metalogic_g1599 : metalogic.globals[1599]? = some metalogic.g1599
kernel_rfl metalogic_g1600 : metalogic.globals[1600]? = some metalogic.g1600
kernel_rfl metalogic_g1602 : metalogic.globals[1602]? = some metalogic.g1602
kernel_rfl metalogic_g1608 : metalogic.globals[1608]? = some metalogic.g1608
kernel_rfl metalogic_g1609 : metalogic.globals[1609]? = some metalogic.g1609
kernel_rfl metalogic_g1610 : metalogic.globals[1610]? = some metalogic.g1610
kernel_rfl metalogic_g1634 : metalogic.globals[1634]? = some metalogic.g1634
kernel_rfl metalogic_g1638 : metalogic.globals[1638]? = some metalogic.g1638

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's the typing of a term, at its type. -/
theorem metalogic_typeTerm :
    metalogic.globals[1509]? = some (⟨termPMTy, «Combinator.typeTerm»⟩ : Glob) :=
  metalogic_g1509.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1509).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    metalogic.«Combinator.typeTerm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's normal form of a term under rules, at its
type. -/
theorem metalogic_pNormalize :
    metalogic.globals[1575]? = some (⟨rulesPMTy, «Combinator.pNormalize»⟩ : Glob) :=
  metalogic_g1575.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1575).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    metalogic.«Combinator.pNormalize_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's instance of a source's sequent at terms, at
its type. -/
theorem metalogic_pInst :
    metalogic.globals[1585]? = some (⟨instPMTy, «Combinator.pInst»⟩ : Glob) :=
  metalogic_g1585.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1585).elim fun _ h ↦
      infer_lams pmTy _ [tT, tList tT] h)
    metalogic.«Combinator.pInst_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's expansion of an arrow into a product, at its
type. -/
theorem metalogic_etaExpand :
    metalogic.globals[1587]? = some (⟨termPMTy, «Combinator.etaExpand»⟩ : Glob) :=
  metalogic_g1587.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1587).elim fun _ h ↦
      infer_lams pmTy _ [tT] h)
    metalogic.«Combinator.etaExpand_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's rule unfolding a definition, at its type. -/
theorem metalogic_deltaRule :
    metalogic.globals[1590]? = some (⟨treeFnTy, «Combinator.deltaRule»⟩ : Glob) :=
  metalogic_g1590.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1590).elim fun _ h ↦
      infer_lams tT _ [tT] h)
    metalogic.«Combinator.deltaRule_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's proof of an equation by normalization, at its
type. -/
theorem metalogic_pByNorm :
    metalogic.globals[1593]? = some (⟨rulesPMTy, «Combinator.pByNorm»⟩ : Glob) :=
  metalogic_g1593.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1593).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT] h)
    metalogic.«Combinator.pByNorm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's proof of a sequent added to a development, at
its type. -/
theorem metalogic_proveSeq :
    metalogic.globals[1599]? = some (⟨proveSeqTy, «Combinator.proveSeq»⟩ : Glob) :=
  metalogic_g1599.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1599).elim fun _ h ↦
      infer_lams tT _ [tT, pmTy, tList tT, tT, tList tT] h)
    metalogic.«Combinator.proveSeq_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's normalization of a theorem's left side, added
to a development, at its type. -/
theorem metalogic_normalizeThm :
    metalogic.globals[1600]? = some (⟨normalizeThmTy, «Combinator.normalizeThm»⟩ : Glob) :=
  metalogic_g1600.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1600).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT, tT, tList tT] h)
    metalogic.«Combinator.normalizeThm_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's instance of a source's sequent, its
hypotheses proved by normalization, at its type. -/
theorem metalogic_instBy :
    metalogic.globals[1602]? = some (⟨instByTy, «Combinator.instBy»⟩ : Glob) :=
  metalogic_g1602.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1602).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tList tT] h)
    metalogic.«Combinator.instBy_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's proof by induction on the natural numbers
object, at its type. -/
theorem metalogic_byNatInduction :
    metalogic.globals[1608]? = some (⟨natIndPMTy, «Combinator.byNatInduction»⟩ : Glob) :=
  metalogic_g1608.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1608).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT] h)
    metalogic.«Combinator.byNatInduction_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's proof by induction on a list object, at its
type. -/
theorem metalogic_byListInduction :
    metalogic.globals[1609]? = some (⟨listIndPMTy, «Combinator.byListInduction»⟩ : Glob) :=
  metalogic_g1609.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1609).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    metalogic.«Combinator.byListInduction_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's proof by induction on a list object with a
parameter, at its type. -/
theorem metalogic_byListParamInduction :
    metalogic.globals[1610]? =
      some (⟨listIndPMTy, «Combinator.byListParamInduction»⟩ : Glob) :=
  metalogic_g1610.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1610).elim fun _ h ↦
      infer_lams pmTy _ [tList tT, tT, tT, tT, tT] h)
    metalogic.«Combinator.byListParamInduction_heq»))

/-- A global is the pair of a type and a value when its type is that type and its value is
heterogeneously equal to that value. The value is an argument, rather than the second projection
of a pair, so that elaboration assigns it rather than unfolding it. -/
theorem glob_eq_mk {g : Glob} {T : Tree} {x : Ty.den T} (hT : g.1 = T) (hx : HEq g.2 x) :
    g = ⟨T, x⟩ :=
  Sigma.ext hT hx

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's library of derived equations and its
development, at its type. -/
theorem metalogic_libraryWith :
    metalogic.globals[1634]? = some (⟨treeFnTy, «Combinator.libraryWith»⟩ : Glob) :=
  metalogic_g1634.trans (congrArg some (glob_eq_mk
    ((infer_of_loadStep metalogic.step1634).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Combinator.libraryWith_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's rules of the axioms and of the library's
derived equations, at its type. -/
theorem metalogic_libRules :
    metalogic.globals[1638]? = some (⟨libRulesTy, «Combinator.libRules»⟩ : Glob) :=
  metalogic_g1638.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1638).elim fun _ h ↦
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
kernel_rfl metalogic_g1756 : metalogic.globals[1756]? = some metalogic.g1756
kernel_rfl metalogic_g1766 : metalogic.globals[1766]? = some metalogic.g1766

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's resolution of what the printer writes, at its
type. -/
theorem metalogic_readBack :
    metalogic.globals[1756]? = some (⟨readBackTy, «Printer.readBack»⟩ : Glob) :=
  metalogic_g1756.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1756).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tList tT] h)
    metalogic.«Printer.readBack_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's partial printer of kernel terms, at its
type. -/
theorem metalogic_printTermOpt :
    metalogic.globals[1766]? = some (⟨printTermTy, «Printer.printTermOpt»⟩ : Glob) :=
  metalogic_g1766.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1766).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT, tT] h)
    metalogic.«Printer.printTermOpt_heq»))

/-! The check of elementary-affine certificates. -/

/-- The type of the check of a certificate: from the terms of a program's definitions and a
certificate to the optional list of the instances' definitions and decorated types. -/
def affineCheckTy : Tree := [tList tT, tT].foldr tArrow tT

-- the check of a certificate is the program's global
kernel_rfl metalogic_g1834 : metalogic.globals[1834]? = some metalogic.g1834

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's check of a certificate, at its type. -/
theorem metalogic_affineCheck :
    metalogic.globals[1834]? = some (⟨affineCheckTy, «Affine.check»⟩ : Glob) :=
  metalogic_g1834.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1834).elim fun _ h ↦
      infer_lams tT _ [tList tT, tT] h)
    metalogic.«Affine.check_heq»))

/-! The conversion checker and the evaluation at literals. -/

/-- The type of the term of a term's value by the evaluation at literals: from a term to the
optional term. -/
def litEvalTy : Tree := [tT].foldr tArrow tT

/-- The type of the test of the conditions under which the evaluation at literals is a rewriting:
from the constants, the entries and an index to a truth value. -/
def readyTy : Tree := [tT, tList tT, tT].foldr tArrow tT

/-- The type of the conversion checker: from the constants, the entries, the indices at which the
evaluation at literals is ready, the number of object variables and a certificate to the
checker's result, a function of a mode, a context, a number of variables, hypotheses and a
term. -/
def convCheckTy : Tree :=
  [tT, tList tT, tList tT, tT, tT].foldr tArrow ([tT, tList tT, tT, tList tT, tT].foldr tArrow tT)

/-- The type of the test that a certificate of the conversion checker proves a theorem: from the
constants, the entries, the indices at which the evaluation at literals is ready, a theorem and a
certificate to a truth value. -/
def thmConvChecksTy : Tree := [tT, tList tT, tList tT, tT, tT].foldr tArrow tT

/-- The type of the check of a development with certificates: from the constants, the entries
and the declarations to the optional state. -/
def checkConvDevTy : Tree := [tT, tList tT, tList tT].foldr tArrow tT

/-- The type of the reduction by the machine at the data of a step: from the constants, the
entries, the number of object variables, the data of the step, the context, the hypotheses and
the term to the optional result. -/
def machineRunTy : Tree := [tT, tList tT, tT, tList tT, tList tT, tList tT, tT].foldr tArrow tT

-- the evaluation at literals, its test of readiness, the reduction by the machine at the data
-- of a step, the conversion checker, its test of a theorem and its check of a development are
-- among the program's globals, each at the index its fact names
kernel_rfl metalogic_g1086 : metalogic.globals[1086]? = some metalogic.g1086
kernel_rfl metalogic_g1125 : metalogic.globals[1125]? = some metalogic.g1125
kernel_rfl metalogic_g1198 : metalogic.globals[1198]? = some metalogic.g1198
kernel_rfl metalogic_g1201 : metalogic.globals[1201]? = some metalogic.g1201
kernel_rfl metalogic_g1202 : metalogic.globals[1202]? = some metalogic.g1202
kernel_rfl metalogic_g1215 : metalogic.globals[1215]? = some metalogic.g1215

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's term of a term's value by the evaluation
at literals, at its type. -/
theorem metalogic_litEval :
    metalogic.globals[1086]? = some (⟨litEvalTy, «Literals.litEval»⟩ : Glob) :=
  metalogic_g1086.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1086).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Literals.litEval_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's test of the conditions under which the
evaluation at literals is a rewriting, at its type. -/
theorem metalogic_ready :
    metalogic.globals[1125]? = some (⟨readyTy, «Literals.ready»⟩ : Glob) :=
  metalogic_g1125.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1125).elim fun _ h ↦
      infer_lams tT _ [tT, tList tT, tT] h)
    metalogic.«Literals.ready_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's reduction by the machine at the data of a
step, at its type. -/
theorem metalogic_machineRun :
    metalogic.globals[1198]? = some (⟨machineRunTy, «Conversion.machineRun»⟩ : Glob) :=
  metalogic_g1198.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1198).elim fun _ h ↦
      infer_lams tT _ [tT, tList tT, tT, tList tT, tList tT, tList tT, tT] h)
    metalogic.«Conversion.machineRun_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's conversion checker, at its type. -/
theorem metalogic_convCheck :
    metalogic.globals[1201]? = some (⟨convCheckTy, «Conversion.convCheck»⟩ : Glob) :=
  metalogic_g1201.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1201).elim fun _ h ↦
      infer_lams ([tT, tList tT, tT, tList tT, tT].foldr tArrow tT) _
        [tT, tList tT, tList tT, tT, tT] h)
    metalogic.«Conversion.convCheck_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's test that a certificate of the conversion
checker proves a theorem, at its type. -/
theorem metalogic_thmConvChecks :
    metalogic.globals[1202]? = some (⟨thmConvChecksTy, «Conversion.thmConvChecks»⟩ : Glob) :=
  metalogic_g1202.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1202).elim fun _ h ↦
      infer_lams tT _ [tT, tList tT, tList tT, tT, tT] h)
    metalogic.«Conversion.thmConvChecks_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's check of a development with certificates
of the conversion checker, at its type. -/
theorem metalogic_checkConvDev :
    metalogic.globals[1215]? = some (⟨checkConvDevTy, «Conversion.checkConvDev»⟩ : Glob) :=
  metalogic_g1215.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1215).elim fun _ h ↦
      infer_lams tT _ [tT, tList tT, tList tT] h)
    metalogic.«Conversion.checkConvDev_heq»))

/-! The checker's functions: the partial Horn checker, the theory, the inference of typings and
the step of a development. -/

/-- The type of the inferences at a fuel: from an environment, a context, hypotheses and the fuel
to the inference of a pattern's instance at arguments of given typings and the inference of a
term. -/
def infersTy : Tree :=
  [tT, tList tT, tList tT].foldr tArrow (tProd (tArrow (tList tT) (tArrow tT tT)) (tArrow tT tT))

/-- The type of the checker of a certificate: from a theory, an environment of theorems and a
certificate to its conclusion as a function of the context and the hypotheses. -/
def pcheckTy : Tree :=
  [tT, tList tT, tT].foldr tArrow (tArrow (tList tT) (tArrow (tList tT) tT))

-- the checker's functions in the program's globals
kernel_rfl metalogic_g42 : metalogic.globals[42]? = some metalogic.g42
kernel_rfl metalogic_g43 : metalogic.globals[43]? = some metalogic.g43
kernel_rfl metalogic_g44 : metalogic.globals[44]? = some metalogic.g44
kernel_rfl metalogic_g92 : metalogic.globals[92]? = some metalogic.g92
kernel_rfl metalogic_g108 : metalogic.globals[108]? = some metalogic.g108
kernel_rfl metalogic_g249 : metalogic.globals[249]? = some metalogic.g249
kernel_rfl metalogic_g325 : metalogic.globals[325]? = some metalogic.g325
kernel_rfl metalogic_g660 : metalogic.globals[660]? = some metalogic.g660

/-- The program's global is the mirror's sort of a term in a context of sorts, at its
type. -/
theorem metalogic_sortOf :
    metalogic.globals[42]? =
      some (⟨[tList tT, tList tT, tT].foldr tArrow tT, «PartialHorn.sortOf»⟩ : Glob) :=
  metalogic_g42.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step42).elim fun _ h ↦
      infer_lams tT _ [tList tT, tList tT, tT] h)
    metalogic.«PartialHorn.sortOf_heq»))

/-- The program's global is the mirror's test that every variable of a term has an
index below a bound, at its type. -/
theorem metalogic_scoped :
    metalogic.globals[43]? = some (⟨[tT, tT].foldr tArrow tT, «PartialHorn.scoped»⟩ : Glob) :=
  metalogic_g43.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step43).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    metalogic.«PartialHorn.scoped_heq»))

/-- The program's global is the mirror's substitution of terms for the variables of a
term, at its type. -/
theorem metalogic_phSubst :
    metalogic.globals[44]? =
      some (⟨[tList tT, tT].foldr tArrow tT, «PartialHorn.phSubst»⟩ : Glob) :=
  metalogic_g44.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step44).elim fun _ h ↦ infer_lams tT _ [tList tT, tT] h)
    metalogic.«PartialHorn.phSubst_heq»))

/-- The program's global is the mirror's checker of a certificate in a theory and an
environment of theorems, at its type. -/
theorem metalogic_pcheck :
    metalogic.globals[92]? =
      some (⟨pcheckTy, «PartialHorn.pcheck»⟩ : Glob) :=
  metalogic_g92.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step92).elim fun _ h ↦
      infer_lams (tArrow (tList tT) (tArrow (tList tT) tT)) _ [tT, tList tT, tT] h)
    metalogic.«PartialHorn.pcheck_heq»))

/-- The program's global is the mirror's extension of a theory by definitions, at its
type. -/
theorem metalogic_thyExtendAll :
    metalogic.globals[108]? =
      some (⟨[tT, tList tT].foldr tArrow tT, «PartialHorn.thyExtendAll»⟩ : Glob) :=
  metalogic_g108.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step108).elim fun _ h ↦ infer_lams tT _ [tT, tList tT] h)
    metalogic.«PartialHorn.thyExtendAll_heq»))

-- the program's global is the mirror's theory of an elementary topos, a tree, checked
-- by the kernel: elaborating the global's equality with its mirror makes the elaborator evaluate
-- the checker-evaluator on the definition.
set_option maxRecDepth 100000 in
kernel_rfl metalogic_toposTheory :
    metalogic.globals[210]? = some (⟨tT, «Theory.toposTheory»⟩ : Glob)

/-- The program's global is the mirror's environment of a list of definitions, at its
type. -/
theorem metalogic_envOfDefs :
    metalogic.globals[249]? = some (⟨listFnTy, «Infer.envOfDefs»⟩ : Glob) :=
  metalogic_g249.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step249).elim fun _ h ↦ infer_lams tT _ [tList tT] h)
    metalogic.«Infer.envOfDefs_heq»))

/-- The program's global is the mirror's inferences, at its type. -/
theorem metalogic_infers :
    metalogic.globals[325]? = some (⟨infersTy, «Infer.infers»⟩ : Glob) :=
  metalogic_g325.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step325).elim fun _ h ↦
      infer_lams (tProd (tArrow (tList tT) (tArrow tT tT)) (tArrow tT tT)) _
        [tT, tList tT, tList tT] h)
    metalogic.«Infer.infers_heq»))

/-- The program's global is the mirror's constants and environment after a
declaration, at its type. -/
theorem metalogic_declStep :
    metalogic.globals[660]? =
      some (⟨[tT, tList tT, tT].foldr tArrow tT, «Derivation.declStep»⟩ : Glob) :=
  metalogic_g660.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step660).elim fun _ h ↦ infer_lams tT _ [tT, tList tT, tT] h)
    metalogic.«Derivation.declStep_heq»))

/-! The tactics' functions of terms. -/

-- the tactics' functions of terms in the program's globals
kernel_rfl metalogic_g1274 : metalogic.globals[1274]? = some metalogic.g1274
kernel_rfl metalogic_g1279 : metalogic.globals[1279]? = some metalogic.g1279
kernel_rfl metalogic_g1280 : metalogic.globals[1280]? = some metalogic.g1280
kernel_rfl metalogic_g1283 : metalogic.globals[1283]? = some metalogic.g1283
kernel_rfl metalogic_g1298 : metalogic.globals[1298]? = some metalogic.g1298
kernel_rfl metalogic_g1300 : metalogic.globals[1300]? = some metalogic.g1300
kernel_rfl metalogic_g1302 : metalogic.globals[1302]? = some metalogic.g1302
kernel_rfl metalogic_g1309 : metalogic.globals[1309]? = some metalogic.g1309
kernel_rfl metalogic_g1313 : metalogic.globals[1313]? = some metalogic.g1313
kernel_rfl metalogic_g1319 : metalogic.globals[1319]? = some metalogic.g1319

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's subterms of a term outside binders and
folds' starts and steps, at its type. -/
theorem metalogic_openSubterms :
    metalogic.globals[1274]? =
      some (⟨[tT].foldr tArrow (tList tT), «Tactics.openSubterms»⟩ : Glob) :=
  metalogic_g1274.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1274).elim fun _ h ↦ infer_lams (tList tT) _ [tT] h)
    metalogic.«Tactics.openSubterms_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's variable a weak normal form is stuck on, at
its type. -/
theorem metalogic_stuckVar :
    metalogic.globals[1279]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVar»⟩ : Glob) :=
  metalogic_g1279.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1279).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    metalogic.«Tactics.stuckVar_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's test that a term mentions a variable, at
its type. -/
theorem metalogic_mentions :
    metalogic.globals[1280]? = some (⟨[tT, tT].foldr tArrow tT, «Tactics.mentions»⟩ : Glob) :=
  metalogic_g1280.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1280).elim fun _ h ↦ infer_lams tT _ [tT, tT] h)
    metalogic.«Tactics.mentions_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's arguments at which the body of an
abstraction matches the subterms of a term, at its type. -/
theorem metalogic_matchesOf :
    metalogic.globals[1283]? =
      some (⟨[tT, tT, tT].foldr tArrow (tList (tList tT)), «Tactics.matchesOf»⟩ : Glob) :=
  metalogic_g1283.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1283).elim fun _ h ↦
      infer_lams (tList (tList tT)) _ [tT, tT, tT] h)
    metalogic.«Tactics.matchesOf_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's type, test and branches of a conditional of
the library, at its type. -/
theorem metalogic_condParts :
    metalogic.globals[1298]? = some (⟨[tT].foldr tArrow tT, «Tactics.condParts»⟩ : Glob) :=
  metalogic_g1298.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1298).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Tactics.condParts_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's variable a weak normal form is stuck on,
including the test of a folded conditional, at its type. -/
theorem metalogic_stuckVarC :
    metalogic.globals[1300]? =
      some (⟨[tArrow tT tT, tT].foldr tArrow tT, «Tactics.stuckVarC»⟩ : Glob) :=
  metalogic_g1300.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1300).elim fun _ h ↦ infer_lams tT _ [tArrow tT tT, tT] h)
    metalogic.«Tactics.stuckVarC_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's applications of a definition to two
arguments among a term's subterms, at its type. -/
theorem metalogic_appsOf :
    metalogic.globals[1302]? =
      some (⟨[tT, tT].foldr tArrow (tList tT), «Tactics.appsOf»⟩ : Glob) :=
  metalogic_g1302.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1302).elim fun _ h ↦ infer_lams (tList tT) _ [tT, tT] h)
    metalogic.«Tactics.appsOf_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's unfolding of a tree term, at its type. -/
theorem metalogic_unnodeU :
    metalogic.globals[1309]? = some (⟨[tT].foldr tArrow tT, «Tactics.unnodeU»⟩ : Glob) :=
  metalogic_g1309.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1309).elim fun _ h ↦ infer_lams tT _ [tT] h)
    metalogic.«Tactics.unnodeU_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's rewriting of a term in which a tree rebuilt
from the unfolding of a variable stands for the variable, back to the term, at its type. -/
theorem metalogic_occRewrite :
    metalogic.globals[1313]? =
      some (⟨[tT, tT, tT, tT].foldr tArrow tT, «Tactics.occRewrite»⟩ : Glob) :=
  metalogic_g1313.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1313).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT, tT] h)
    metalogic.«Tactics.occRewrite_heq»))

set_option maxRecDepth 100000 in
/-- The program's global is the mirror's abstraction of a term's occurrences of a
term, at its type. -/
theorem metalogic_abstractTerm :
    metalogic.globals[1319]? =
      some (⟨[tT, tT, tT].foldr tArrow tT, «Tactics.abstractTerm»⟩ : Glob) :=
  metalogic_g1319.trans (congrArg some (glob_ext
    ((infer_of_loadStep metalogic.step1319).elim fun _ h ↦ infer_lams tT _ [tT, tT, tT] h)
    metalogic.«Tactics.abstractTerm_heq»))

end GebTests.Prototypes.FreeTopos.Agreement.Load

end
