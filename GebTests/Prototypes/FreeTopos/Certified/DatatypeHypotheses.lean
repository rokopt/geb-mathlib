/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeFolds
public import GebTests.Prototypes.FreeTopos.DatatypeProgramStep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The remaining hypotheses of the datatype language's soundness, in Lean

Besides the successes of the compiler's passes, the soundness of a whole program of the
datatype language's stage-1 compiler assumes of the program: that each body the expansion
writes for a definition is a source form at the numeral abbreviations before it, which a run
over the program's forms tests; that each marker among the kernel forms is the one its
datatype's atom finds among the markers; that the markers' datatypes are named by atoms other
than the trees' type's and the unit type's, with at most one constructor of each label, and
that the digits of a label read as the label and are fixed by the expansion of numeral
abbreviations; and, of each form, that it is no declaration of a tree datatype and declares no
name of the implementation's. Each is a formula of the internal language over references to
the compilers' definitions, and represents the statement of Lean built the same way from the
values of the globals the kernel loads.

## Main definitions

* {lit}`HypFns` — the values of the compilers' definitions the hypotheses call.
* {lit}`PlainOk`, {lit}`MarkersOk`, {lit}`StaticOk`, {lit}`FormsOk` — the four hypotheses, as
  those values compute them.
* {lit}`NamesOk`, {lit}`CtorsOk`, {lit}`DigitsRead`, {lit}`DigitsFixed` — what {lit}`StaticOk`
  assumes of the markers' names, of their constructors, and of the numerals' digits.

## Main statements

* {lit}`exists_hypFns` — the loaded globals give the values.
* {lit}`repC_typedForms`, {lit}`repC_plainStep` — the expansion's run and the step of the test
  of source forms represent those the loaded compilers compute.
* {lit}`plain_rep`, {lit}`markers_rep`, {lit}`static_rep`, {lit}`forms_rep` — the four
  hypotheses represent the statements of Lean.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, kernel, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs pc truth)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted (xpK hypGlobals hypGlobalsTyped)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements
open GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation
open GebTests.Prototypes.FreeTopos.Certified.DatatypeFolds
open Internal (Term RepC repC_lam repC_app repC_pair repC_fst repC_snd repC_eq repC_nil
  repC_cons repC_star objVal_exp objVal_prod objVal_list objVal_omega isTy_exp isTy_list
  isTy_omega)
open Kernel (tT tList tProd tArrow)
open Sorts

/-- The values of the kernel type of the expansion's states: whether every form has expanded,
the declarations, and the forms written. -/
abbrev XpSt : Type := Kernel.Tree × List Kernel.Tree × List Kernel.Tree

/-- The values of the compilers' definitions the soundness's remaining hypotheses call. -/
structure HypFns where
  /-- The expansion's step at a template's instance. -/
  genericStep : XpSt → Kernel.Tree → XpSt
  /-- The expansion's step at a form. -/
  xpStep : XpSt → Kernel.Tree → XpSt
  /-- The conjunction of two truth values. -/
  and : Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The disjunction of two truth values. -/
  or : Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- Whether a form is a list. -/
  isListTx : Kernel.Tree → Kernel.Tree
  /-- Whether a form is the atom of a name. -/
  namedTx : Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The form of a list at an index. -/
  nthTx : List Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- A list form's elements. -/
  elems : Kernel.Tree → List Kernel.Tree
  /-- The templates' keyword. -/
  kwGeneric : Kernel.Tree
  /-- The datatypes' keyword. -/
  kwData : Kernel.Tree
  /-- The tree datatypes' keyword. -/
  kwTreeData : Kernel.Tree
  /-- The functions' keyword. -/
  kwDefn : Kernel.Tree
  /-- The definitions' keyword. -/
  kwDef : Kernel.Tree
  /-- The type abbreviations' keyword. -/
  kwDeftype : Kernel.Tree
  /-- The numeral abbreviations' keyword. -/
  kwDefnum : Kernel.Tree
  /-- The name of the trees' type. -/
  kwT : Kernel.Tree
  /-- The name of the unit type. -/
  kwUnit : Kernel.Tree
  /-- Whether a form is a source form, at an expansion of numeral abbreviations. -/
  srcForm : (Kernel.Tree → Kernel.Tree) → Kernel.Tree → Kernel.Tree
  /-- The expansion of numeral abbreviations in a form. -/
  expandNums : List Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The numeral a form is at numeral abbreviations, when it is one. -/
  numOf : List Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- An atom's name. -/
  nameOf : Kernel.Tree → Kernel.Tree
  /-- The node of a label over two children. -/
  node2 : Kernel.Tree → Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- The reversal of a list of forms. -/
  reverse : List Kernel.Tree → List Kernel.Tree
  /-- A list of forms after a number of them. -/
  drop : Kernel.Tree → List Kernel.Tree → List Kernel.Tree
  /-- The erasure of typed forms to kernel forms. -/
  kernelForms : List Kernel.Tree → List Kernel.Tree
  /-- The markers among kernel forms. -/
  markers : List Kernel.Tree → List Kernel.Tree
  /-- A datatype's constructors among markers, as the typing reads them. -/
  markerCtors : List Kernel.Tree → Kernel.Tree → Kernel.Tree × List Kernel.Tree
  /-- The names of the markers' datatypes. -/
  markerNames : List Kernel.Tree → List Kernel.Tree
  /-- Whether a form is an atom. -/
  isAtom : Kernel.Tree → Kernel.Tree
  /-- Whether a form is named by a name. -/
  named : Kernel.Tree → Kernel.Tree → Kernel.Tree
  /-- A list's length. -/
  length : List Kernel.Tree → Kernel.Tree
  /-- The numeral digits read as, when they read as one. -/
  numeral : List Kernel.Tree → Kernel.Tree
  /-- The digits of a tree's label. -/
  decimalChars : Kernel.Tree → List Kernel.Tree
  /-- Whether a function of forms fixes each of some characters. -/
  charsFixed : (Kernel.Tree → Kernel.Tree) → List Kernel.Tree → Kernel.Tree
  /-- Whether a name is one of the implementation's. -/
  implName : Kernel.Tree → Kernel.Tree
  /-- The name of a datatype's recognizer. -/
  memberName : Kernel.Tree → Kernel.Tree
  /-- The value of an optional tree that is present. -/
  get : Kernel.Tree → Kernel.Tree
  /-- Whether an optional tree is present. -/
  isSome : Kernel.Tree → Kernel.Tree
  /-- The presence of a tree. -/
  just : Kernel.Tree → Kernel.Tree
  /-- The index of a name among names, when it has one. -/
  indexOf : Kernel.Tree → List Kernel.Tree → Kernel.Tree

/-- The values are those of the globals the kernel loads for the definitions' names. -/
structure HypFns.Loaded (f : HypFns) (Gk : List Kernel.Glob) (idx : String → ℕ) : Prop where
  /-- The value of {lit}`Datatype.genericStep`. -/
  genericStep : DatatypeTranslated.Loaded Gk idx "Datatype.genericStep"
    (tArrow xpK (tArrow tT xpK)) f.genericStep
  /-- The value of {lit}`Datatype.xpStep`. -/
  xpStep : DatatypeTranslated.Loaded Gk idx "Datatype.xpStep" (tArrow xpK (tArrow tT xpK)) f.xpStep
  /-- The value of {lit}`Prelude.and`. -/
  and : DatatypeTranslated.Loaded Gk idx "Prelude.and" (tArrow tT (tArrow tT tT)) f.and
  /-- The value of {lit}`Prelude.or`. -/
  or : DatatypeTranslated.Loaded Gk idx "Prelude.or" (tArrow tT (tArrow tT tT)) f.or
  /-- The value of {lit}`Datatype.isListTx`. -/
  isListTx : DatatypeTranslated.Loaded Gk idx "Datatype.isListTx" (tArrow tT tT) f.isListTx
  /-- The value of {lit}`Datatype.namedTx`. -/
  namedTx : DatatypeTranslated.Loaded Gk idx "Datatype.namedTx" (tArrow tT (tArrow tT tT)) f.namedTx
  /-- The value of {lit}`Datatype.nthTx`. -/
  nthTx : DatatypeTranslated.Loaded Gk idx "Datatype.nthTx"
    (tArrow (tList tT) (tArrow tT tT)) f.nthTx
  /-- The value of {lit}`Datatype.elems`. -/
  elems : DatatypeTranslated.Loaded Gk idx "Datatype.elems" (tArrow tT (tList tT)) f.elems
  /-- The value of {lit}`Datatype.kwGeneric`. -/
  kwGeneric : DatatypeTranslated.Loaded Gk idx "Datatype.kwGeneric" tT f.kwGeneric
  /-- The value of {lit}`Datatype.kwData`. -/
  kwData : DatatypeTranslated.Loaded Gk idx "Datatype.kwData" tT f.kwData
  /-- The value of {lit}`Datatype.kwTreeData`. -/
  kwTreeData : DatatypeTranslated.Loaded Gk idx "Datatype.kwTreeData" tT f.kwTreeData
  /-- The value of {lit}`Datatype.kwDefn`. -/
  kwDefn : DatatypeTranslated.Loaded Gk idx "Datatype.kwDefn" tT f.kwDefn
  /-- The value of {lit}`Reader.kwDef`. -/
  kwDef : DatatypeTranslated.Loaded Gk idx "Reader.kwDef" tT f.kwDef
  /-- The value of {lit}`Reader.kwDeftype`. -/
  kwDeftype : DatatypeTranslated.Loaded Gk idx "Reader.kwDeftype" tT f.kwDeftype
  /-- The value of {lit}`Reader.kwDefnum`. -/
  kwDefnum : DatatypeTranslated.Loaded Gk idx "Reader.kwDefnum" tT f.kwDefnum
  /-- The value of {lit}`Reader.kwT`. -/
  kwT : DatatypeTranslated.Loaded Gk idx "Reader.kwT" tT f.kwT
  /-- The value of {lit}`Reader.kwUnit`. -/
  kwUnit : DatatypeTranslated.Loaded Gk idx "Reader.kwUnit" tT f.kwUnit
  /-- The value of {lit}`srcForm`. -/
  srcForm : DatatypeTranslated.Loaded Gk idx "srcForm"
    (tArrow (tArrow tT tT) (tArrow tT tT)) f.srcForm
  /-- The value of {lit}`Reader.expandNums`. -/
  expandNums : DatatypeTranslated.Loaded Gk idx "Reader.expandNums"
    (tArrow (tList tT) (tArrow tT tT)) f.expandNums
  /-- The value of {lit}`Reader.numOf`. -/
  numOf : DatatypeTranslated.Loaded Gk idx "Reader.numOf" (tArrow (tList tT) (tArrow tT tT)) f.numOf
  /-- The value of {lit}`Reader.nameOf`. -/
  nameOf : DatatypeTranslated.Loaded Gk idx "Reader.nameOf" (tArrow tT tT) f.nameOf
  /-- The value of {lit}`Reader.node2`. -/
  node2 : DatatypeTranslated.Loaded Gk idx "Reader.node2"
    (tArrow tT (tArrow tT (tArrow tT tT))) f.node2
  /-- The value of {lit}`Datatype/Txs.reverse`. -/
  reverse : DatatypeTranslated.Loaded Gk idx "Datatype/Txs.reverse"
    (tArrow (tList tT) (tList tT)) f.reverse
  /-- The value of {lit}`Datatype/Txs.drop`. -/
  drop : DatatypeTranslated.Loaded Gk idx "Datatype/Txs.drop"
    (tArrow tT (tArrow (tList tT) (tList tT))) f.drop
  /-- The value of {lit}`Datatype.kernelForms`. -/
  kernelForms : DatatypeTranslated.Loaded Gk idx "Datatype.kernelForms"
    (tArrow (tList tT) (tList tT)) f.kernelForms
  /-- The value of {lit}`Recognize.markers`. -/
  markers : DatatypeTranslated.Loaded Gk idx "Recognize.markers"
    (tArrow (tList tT) (tList tT)) f.markers
  /-- The value of {lit}`Typing.markerCtors`. -/
  markerCtors : DatatypeTranslated.Loaded Gk idx "Typing.markerCtors"
    (tArrow (tList tT) (tArrow tT (tProd tT (tList tT)))) f.markerCtors
  /-- The value of {lit}`Typing.markerNames`. -/
  markerNames : DatatypeTranslated.Loaded Gk idx "Typing.markerNames"
    (tArrow (tList tT) (tList tT)) f.markerNames
  /-- The value of {lit}`Reader.isAtom`. -/
  isAtom : DatatypeTranslated.Loaded Gk idx "Reader.isAtom" (tArrow tT tT) f.isAtom
  /-- The value of {lit}`Reader.named`. -/
  named : DatatypeTranslated.Loaded Gk idx "Reader.named" (tArrow tT (tArrow tT tT)) f.named
  /-- The value of {lit}`Prelude.length`. -/
  length : DatatypeTranslated.Loaded Gk idx "Prelude.length" (tArrow (tList tT) tT) f.length
  /-- The value of {lit}`Reader.numeral`. -/
  numeral : DatatypeTranslated.Loaded Gk idx "Reader.numeral" (tArrow (tList tT) tT) f.numeral
  /-- The value of {lit}`Typing.decimalChars`. -/
  decimalChars : DatatypeTranslated.Loaded Gk idx "Typing.decimalChars"
    (tArrow tT (tList tT)) f.decimalChars
  /-- The value of {lit}`charsFixed`. -/
  charsFixed : DatatypeTranslated.Loaded Gk idx "charsFixed"
    (tArrow (tArrow tT tT) (tArrow (tList tT) tT)) f.charsFixed
  /-- The value of {lit}`implName`. -/
  implName : DatatypeTranslated.Loaded Gk idx "implName" (tArrow tT tT) f.implName
  /-- The value of {lit}`Datatype.memberName`. -/
  memberName : DatatypeTranslated.Loaded Gk idx "Datatype.memberName" (tArrow tT tT) f.memberName
  /-- The value of {lit}`Prelude.get`. -/
  get : DatatypeTranslated.Loaded Gk idx "Prelude.get" (tArrow tT tT) f.get
  /-- The value of {lit}`Prelude.isSome`. -/
  isSome : DatatypeTranslated.Loaded Gk idx "Prelude.isSome" (tArrow tT tT) f.isSome
  /-- The value of {lit}`Prelude.some`. -/
  just : DatatypeTranslated.Loaded Gk idx "Prelude.some" (tArrow tT tT) f.just
  /-- The value of {lit}`Reader.indexOf`. -/
  indexOf : DatatypeTranslated.Loaded Gk idx "Reader.indexOf"
    (tArrow tT (tArrow (tList tT) tT)) f.indexOf

namespace HypFns

variable (f : HypFns)

/-- The expansion's step at a form from a state: a template's instance's, or a form's. -/
def xpStepK (s : XpSt) (e : Kernel.Tree) : XpSt :=
  if (f.and (f.isListTx e) (f.namedTx (f.nthTx (f.elems e) (Kernel.leaf 0)) f.kwGeneric)).label
      ≠ 0 then f.genericStep s e else f.xpStep s e

/-- The typed forms the expansion writes for a program's forms: its run from no declarations
and no forms written, the forms it has written reversed. -/
def typedFormsK (ks : List Kernel.Tree) : List Kernel.Tree :=
  f.reverse (ks.foldl f.xpStepK (Kernel.leaf 1, [], [])).2.2

/-- The kernel forms of a program's forms. -/
def fsK (ks : List Kernel.Tree) : List Kernel.Tree := f.kernelForms (f.typedFormsK ks)

/-- The markers among the kernel forms of a program's forms. -/
def msK (ks : List Kernel.Tree) : List Kernel.Tree := f.markers (f.fsK ks)

/-- The step at a form of the test of the definitions' bodies, from a state of whether none
has failed, the declarations and the numeral abbreviations: the expansion's step at the form
from the declarations leaves declarations and writes forms; at a template's instance or a
datatype's declaration the state has those declarations; where the form written is a
definition's, it has them where the body is a source form at the numeral abbreviations and has
failed where it is not; where it is a numeral abbreviation's, it has the abbreviation before
the others; a state that has failed is left. -/
def plainStepK (s : XpSt) (e : Kernel.Tree) : XpSt :=
  let x := f.xpStepK (Kernel.leaf 1, s.2.1, []) e
  let he := f.nthTx (f.elems e) (Kernel.leaf 0)
  let fs := f.elems (f.nthTx x.2.2 (Kernel.leaf 0))
  let hf := f.nthTx fs (Kernel.leaf 0)
  let keep : XpSt := (Kernel.leaf 1, x.2.1, s.2.2)
  if s.1.label ≠ 0 then
    if (f.and (f.isListTx e) (f.namedTx he f.kwGeneric)).label ≠ 0 then keep
    else if (f.or (f.namedTx he f.kwData) (f.namedTx he f.kwTreeData)).label ≠ 0 then keep
    else if (f.namedTx hf f.kwDef).label ≠ 0 then
      if (f.srcForm (fun y ↦ f.expandNums s.2.2 y) (f.nthTx fs (Kernel.leaf 2))).label ≠ 0
      then keep else (Kernel.leaf 0, x.2.1, s.2.2)
    else if (f.namedTx hf f.kwDeftype).label ≠ 0 then keep
    else if (f.namedTx hf f.kwDefnum).label ≠ 0 then
      (Kernel.leaf 1, x.2.1,
        f.node2 (Kernel.leaf 0) (f.nameOf (f.nthTx fs (Kernel.leaf 1)))
          (f.get (f.numOf s.2.2 (f.nthTx fs (Kernel.leaf 2)))) :: s.2.2)
    else keep
  else s

/-- Each body the expansion writes for a definition of a program is a source form at the
numeral abbreviations before it: the run of the test over the program's forms, from no
declarations and no abbreviations, ends without a failure. -/
def PlainOk (ks : List Kernel.Tree) : Prop :=
  (ks.foldl f.plainStepK (Kernel.leaf 1, [], [])).1.label ≠ 0

/-- Each kernel form of a program that is a marker is the marker its datatype's atom finds
among the markers: the typing's reading of that datatype's constructors is the marker's own. -/
def MarkersOk (ks : List Kernel.Tree) : Prop :=
  ∀ x ∈ f.fsK ks, (Kernel.Const.eq (Kernel.Const.label x) (Kernel.leaf 9)).label ≠ 0 →
    f.markerCtors (f.msK ks) (Kernel.Const.child x (Kernel.leaf 0)) =
      (Kernel.leaf 1, x.children.tail)

/-- The constructors of a list whose first child has a label. -/
def filterK (l : Kernel.Tree) (xs : List Kernel.Tree) : List Kernel.Tree :=
  xs.foldr (fun x r ↦
    if (Kernel.Const.eq (Kernel.Const.child x (Kernel.leaf 0)) l).label ≠ 0 then x :: r else r) []

/-- What the soundness assumes of the markers' names: each marker's datatype is named by an
atom, other than the trees' type's and the unit type's. -/
def NamesOk (ms : List Kernel.Tree) : Prop :=
  ∀ n, (f.isSome (f.indexOf n (f.markerNames ms))).label ≠ 0 →
    (f.isAtom n).label ≠ 0 ∧ ((f.named n f.kwT).label ≠ 0 → False) ∧
      ((f.named n f.kwUnit).label ≠ 0 → False)

/-- What the soundness assumes of the markers' constructors: each marker's constructors have at
most one of each label. -/
def CtorsOk (ms : List Kernel.Tree) : Prop :=
  ∀ dt, ∀ l, (Kernel.Const.lt (f.length (filterK l (f.markerCtors ms dt).2))
    (Kernel.leaf 2)).label ≠ 0

/-- The reader reads the digits of a tree's label as the leaf of the label. -/
def DigitsRead : Prop :=
  ∀ t : Kernel.Tree, f.numeral (f.decimalChars t) = f.just (Kernel.leaf t.label)

/-- The expansion of any numeral abbreviations fixes the digits of a tree's label. -/
def DigitsFixed : Prop :=
  ∀ (nums : List Kernel.Tree) (t : Kernel.Tree),
    (f.charsFixed (fun y ↦ f.expandNums nums y) (f.decimalChars t)).label ≠ 0

/-- What the soundness assumes of markers and of the numerals: of the markers' names
({name}`NamesOk`) and constructors ({name}`CtorsOk`), and that the digits of a tree's label read
as its leaf ({name}`DigitsRead`) and are fixed by the expansion of any numeral abbreviations
({name}`DigitsFixed`). -/
def StaticOk (ms : List Kernel.Tree) : Prop :=
  f.NamesOk ms ∧ f.CtorsOk ms ∧ f.DigitsRead ∧ f.DigitsFixed

/-- What the soundness assumes of a form: where it declares a datatype, no constructor's name
and not the recognizer's is one of the implementation's; it does not declare a tree datatype;
and where it is a numeral abbreviation's, a definition's or a function's, the name it declares
is not one of the implementation's. -/
def FormOk (e : Kernel.Tree) : Prop :=
  ((f.namedTx (f.nthTx (f.elems e) (Kernel.leaf 0)) f.kwData).label ≠ 0 →
    (∀ c ∈ f.drop (Kernel.leaf 2) (f.elems e),
      (f.implName (f.nameOf (f.nthTx (f.elems c) (Kernel.leaf 0)))).label ≠ 0 → False) ∧
    ((f.implName (f.nameOf (f.memberName (f.nthTx (f.elems e) (Kernel.leaf 1))))).label ≠ 0 →
      False)) ∧
  ((f.namedTx (f.nthTx (f.elems e) (Kernel.leaf 0)) f.kwTreeData).label ≠ 0 → False) ∧
  ((f.namedTx (f.nthTx (f.elems e) (Kernel.leaf 0)) f.kwDefnum).label ≠ 0 →
    (f.implName (f.nameOf (f.nthTx (f.elems e) (Kernel.leaf 1)))).label ≠ 0 → False) ∧
  ((f.namedTx (f.nthTx (f.elems e) (Kernel.leaf 0)) f.kwDef).label ≠ 0 →
    (f.implName (f.nameOf (f.nthTx (f.elems e) (Kernel.leaf 1)))).label ≠ 0 → False) ∧
  ((f.namedTx (f.nthTx (f.elems e) (Kernel.leaf 0)) f.kwDefn).label ≠ 0 →
    (f.implName (f.nameOf (f.nthTx (f.elems e) (Kernel.leaf 1)))).label ≠ 0 → False)

/-- What the soundness assumes of each form of a program. -/
def FormsOk (ks : List Kernel.Tree) : Prop := ∀ e ∈ ks, f.FormOk e

end HypFns

variable {PST : Prog × Defs × Defs3}

/-- The loaded globals give the values of the compilers' definitions the hypotheses call, each
at the kernel type the evaluator checked ({name}`DatatypeAccepted.hypGlobalsTyped`). -/
theorem exists_hypFns (L : Translated PST) : ∃ f : HypFns, f.Loaded L.Gk PST.1.idx := by
  have m : ∀ (i : ℕ) {name : String} {T : Kernel.Tree}, hypGlobals[i]? = some (name, T) →
      ∃ f, DatatypeTranslated.Loaded L.Gk PST.1.idx name T f := by
    intro _ _ _ hm
    exact L.loaded hypGlobalsTyped (List.mem_of_getElem? hm)
  obtain ⟨f0, h0⟩ := m 0 rfl
  obtain ⟨f1, h1⟩ := m 1 rfl
  obtain ⟨f2, h2⟩ := m 2 rfl
  obtain ⟨f3, h3⟩ := m 3 rfl
  obtain ⟨f4, h4⟩ := m 4 rfl
  obtain ⟨f5, h5⟩ := m 5 rfl
  obtain ⟨f6, h6⟩ := m 6 rfl
  obtain ⟨f7, h7⟩ := m 7 rfl
  obtain ⟨f8, h8⟩ := m 8 rfl
  obtain ⟨f9, h9⟩ := m 9 rfl
  obtain ⟨f10, h10⟩ := m 10 rfl
  obtain ⟨f11, h11⟩ := m 11 rfl
  obtain ⟨f12, h12⟩ := m 12 rfl
  obtain ⟨f13, h13⟩ := m 13 rfl
  obtain ⟨f14, h14⟩ := m 14 rfl
  obtain ⟨f15, h15⟩ := m 15 rfl
  obtain ⟨f16, h16⟩ := m 16 rfl
  obtain ⟨f17, h17⟩ := m 17 rfl
  obtain ⟨f18, h18⟩ := m 18 rfl
  obtain ⟨f19, h19⟩ := m 19 rfl
  obtain ⟨f20, h20⟩ := m 20 rfl
  obtain ⟨f21, h21⟩ := m 21 rfl
  obtain ⟨f22, h22⟩ := m 22 rfl
  obtain ⟨f23, h23⟩ := m 23 rfl
  obtain ⟨f24, h24⟩ := m 24 rfl
  obtain ⟨f25, h25⟩ := m 25 rfl
  obtain ⟨f26, h26⟩ := m 26 rfl
  obtain ⟨f27, h27⟩ := m 27 rfl
  obtain ⟨f28, h28⟩ := m 28 rfl
  obtain ⟨f29, h29⟩ := m 29 rfl
  obtain ⟨f30, h30⟩ := m 30 rfl
  obtain ⟨f31, h31⟩ := m 31 rfl
  obtain ⟨f32, h32⟩ := m 32 rfl
  obtain ⟨f33, h33⟩ := m 33 rfl
  obtain ⟨f34, h34⟩ := m 34 rfl
  obtain ⟨f35, h35⟩ := m 35 rfl
  obtain ⟨f36, h36⟩ := m 36 rfl
  obtain ⟨f37, h37⟩ := m 37 rfl
  obtain ⟨f38, h38⟩ := m 38 rfl
  obtain ⟨f39, h39⟩ := m 39 rfl
  exact ⟨⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36,
    f37, f38, f39⟩,
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37,
      h38, h39⟩⟩

/-- The kernel forms of a program's forms, as a term of the forms. -/
def fsT (P : Prog) (es : Term) : Term :=
  pc P "Datatype.kernelForms" [typedForms P es (nilT treeTy)]

/-- The markers among the kernel forms of a program's forms, as a term of the forms. -/
def msT (P : Prog) (es : Term) : Term := pc P "Recognize.markers" [fsT P es]

/-- The type of the expansion's states is a type, over every constants. -/
theorem isTy_xp (G : Internal.Globals) : Internal.IsTy G 0 xpTy = true :=
  (ty_spec (G := G) (n := 0) (ρ := []) (ds := []) xpK rfl).1

/-- The type of lists of trees is a type, over every constants. -/
theorem isTy_trees (G : Internal.Globals) : Internal.IsTy G 0 (list treeTy) = true := by
  simp [isTy_list, isTy_tree]

/-- The value of the type of the expansion's states, unfolded. -/
theorem objVal_xp {ds : List PartialHorn.Defn} :
    ObjVal [] (unfoldTerm sig ds xpTy) (MTy xpK) := objVal_ty' (T := xpK) rfl

section Readings

variable (L : Translated PST) {f : HypFns} (hf : f.Loaded L.Gk PST.1.idx)
  {X : PartialHorn.Tree} {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type}
  {R : S → A → Prop} {ents : List (Internal.RepEntry S)}
  (c : RepCtx L.defs L.cds₀ L.ext X e R ents)

include hf c

/-- The expansion's step at a form from a state represents the step the loaded compilers
compute ({name}`HypFns.xpStepK`). -/
theorem repC_xpStep {s t : Term} {Fs : S → XpSt} {Ft : S → Kernel.Tree}
    (hs : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] s X e xpTy R (KRel xpK) Fs)
    (ht : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t X e treeTy R RT Ft) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (xpStepT PST.1 s t) X e xpTy R (KRel xpK)
      fun σ ↦ f.xpStepK (Fs σ) (Ft σ) :=
  repC_condB L.ctx (isTy_xp _)
    (ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) xpK rfl).2.1
    (objVal_ty (T := xpK) rfl)
    (repC_lab L.ctx (repC_pc₂ L hf.and rfl rfl rfl c.val
      (repC_pc₁ L hf.isListTx rfl rfl c.val ht)
      (repC_pc₂ L hf.namedTx rfl rfl rfl c.val
        (repC_pc₂ L hf.nthTx rfl rfl rfl c.val (repC_pc₁ L hf.elems rfl rfl c.val ht)
          (c.quote L.ctx (Kernel.leaf 0)))
        (repC_pc₀ L hf.kwGeneric rfl c.val R))))
    (repC_pc₂ L hf.genericStep rfl rfl rfl c.val hs ht)
    (repC_pc₂ L hf.xpStep rfl rfl rfl c.val hs ht)

/-- The typed forms the expansion writes, at a term of the forms, represent those the loaded
compilers compute ({name}`HypFns.typedFormsK`). -/
theorem repC_typedForms {es : Term} {Fes : S → List Kernel.Tree}
    (hes : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] es X e (list treeTy) R (Rep.list RT) Fes) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (typedForms PST.1 es (nilT treeTy)) X e (list treeTy) R
      (Rep.list RT) fun σ ↦ f.typedFormsK (Fes σ) := by
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hXp := objVal_xp (ds := L.cds₀ ++ L.ext)
  have hkNil : PST.1.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  -- the step, in a form, a continuation and a state
  have c₃ := ((c.extend L.ctx hT (isTy_tree _) RT).extend L.ctx (objVal_exp hXp hXp)
    (by simp [isTy_exp, isTy_xp]) (Rep.exp (KRel xpK) (KRel xpK))).extend L.ctx hXp (isTy_xp _)
    (KRel xpK)
  have hstep := repC_xpStep L hf c₃ (c₃.var (i := 0) rfl) (c₃.var (i := 2) rfl)
  -- the state the run begins in: no failure, no declarations, no forms written
  have hnil := repC_nil hkNil (isTy_tree _) (repC_star (e := e) c.val R) hT RT
  have hs₀ := repC_pair (c.quote L.ctx (Kernel.leaf 1)) (repC_pair hnil hnil)
  have hrun := repC_runT (isTy_tree _) (isTy_xp _) hT hXp c.rep c.val
    (StepF := fun _ s x ↦ f.xpStepK s x) hstep hes hs₀
  exact repC_pc₁ L hf.reverse rfl rfl c.val
    (repC_snd (repC_snd hrun hT (objVal_prod hL hL)) hL hL)

/-- The kernel forms of a program's forms, at a term of the forms, represent those the loaded
compilers compute ({name}`HypFns.fsK`). -/
theorem repC_fs {es : Term} {Fes : S → List Kernel.Tree}
    (hes : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] es X e (list treeTy) R (Rep.list RT) Fes) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (fsT PST.1 es) X e (list treeTy) R (Rep.list RT)
      fun σ ↦ f.fsK (Fes σ) :=
  repC_pc₁ L hf.kernelForms rfl rfl c.val (repC_typedForms L hf c hes)

/-- The markers among the kernel forms of a program's forms, at a term of the forms, represent
those the loaded compilers compute ({name}`HypFns.msK`). -/
theorem repC_ms {es : Term} {Fes : S → List Kernel.Tree}
    (hes : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] es X e (list treeTy) R (Rep.list RT) Fes) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (msT PST.1 es) X e (list treeTy) R (Rep.list RT)
      fun σ ↦ f.msK (Fes σ) :=
  repC_pc₁ L hf.markers rfl rfl c.val (repC_fs L hf c hes)

omit hf c in
/-- The choice between two states by a test, the conditional on the test's label, represents
the choice by the label of the kernel tree the test represents. -/
theorem repC_stateTest {t a b : Term} {Ft : S → Kernel.Tree} {Fa Fb : S → XpSt}
    (ht : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t X e treeTy R RT Ft)
    (ha : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] a X e plainTy R (KRel xpK) Fa)
    (hb : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] b X e plainTy R (KRel xpK) Fb) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (condT plainTy (call D.lab [] [t]) a b) X e plainTy R
      (KRel xpK) fun σ ↦ if (Ft σ).label ≠ 0 then Fa σ else Fb σ :=
  repC_condB L.ctx (isTy_xp _)
    (ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) xpK rfl).2.1
    (objVal_ty (T := xpK) rfl) (repC_lab L.ctx ht) ha hb

/-- The step of the test of the definitions' bodies, at the state and the form a run binds,
represents the step the loaded compilers compute ({name}`HypFns.plainStepK`). -/
theorem repC_plainStep :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (plainStepT PST.1 (v 0) (v 2))
      (prod (prod (prod X treeTy) (exp plainTy plainTy)) plainTy)
      (Internal.extEnv (prod (prod X treeTy) (exp plainTy plainTy)) plainTy
        (Internal.extEnv (prod X treeTy) (exp plainTy plainTy) (Internal.extEnv X treeTy e)))
      plainTy (Rep.prod (Rep.prod (Rep.prod R RT) (Rep.exp (KRel xpK) (KRel xpK))) (KRel xpK))
      (KRel xpK) fun q ↦ f.plainStepK q.2 q.1.1.2 := by
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hLL := objVal_prod hL hL
  have hXp := objVal_xp (ds := L.cds₀ ++ L.ext)
  have hkNil : PST.1.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have hkCons : PST.1.G.prims[1]? = some Internal.consPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have c₃ := ((c.extend L.ctx hT (isTy_tree _) RT).extend L.ctx (objVal_exp hXp hXp)
    (by simp [isTy_exp, isTy_xp]) (Rep.exp (KRel xpK) (KRel xpK))).extend L.ctx hXp (isTy_xp _)
    (KRel xpK)
  have c₄ := c₃.extend L.ctx hT (isTy_tree _) RT
  -- the state's parts and the form
  have hs := c₃.var (G := PST.1.G) (i := 0) rfl
  have he := c₃.var (G := PST.1.G) (i := 2) rfl
  have hdv := repC_fst (repC_snd hs hT hLL) hL hL
  have hnums := repC_snd (repC_snd hs hT hLL) hL hL
  have hnil := repC_nil hkNil (isTy_tree _)
    (repC_star (e := Internal.extEnv (prod (prod X treeTy) (exp xpTy xpTy)) xpTy
      (Internal.extEnv (prod X treeTy) (exp xpTy xpTy) (Internal.extEnv X treeTy e))) c₃.val
      (Rep.prod (Rep.prod (Rep.prod R RT) (Rep.exp (KRel xpK) (KRel xpK))) (KRel xpK))) hT RT
  -- the expansion's step from the declarations, and the form it writes
  have hx := repC_xpStep L hf c₃
    (repC_pair (c₃.quote L.ctx (Kernel.leaf 1)) (repC_pair hdv hnil)) he
  have hdv' := repC_fst (repC_snd hx hT hLL) hL hL
  have hhe := repC_pc₂ L hf.nthTx rfl rfl rfl c₃.val (repC_pc₁ L hf.elems rfl rfl c₃.val he)
    (c₃.quote L.ctx (Kernel.leaf 0))
  have hfs := repC_pc₁ L hf.elems rfl rfl c₃.val
    (repC_pc₂ L hf.nthTx rfl rfl rfl c₃.val (repC_snd (repC_snd hx hT hLL) hL hL)
      (c₃.quote L.ctx (Kernel.leaf 0)))
  have hhf := repC_pc₂ L hf.nthTx rfl rfl rfl c₃.val hfs (c₃.quote L.ctx (Kernel.leaf 0))
  have hn := repC_pc₂ L hf.nthTx rfl rfl rfl c₃.val hfs (c₃.quote L.ctx (Kernel.leaf 1))
  have hb := repC_pc₂ L hf.nthTx rfl rfl rfl c₃.val hfs (c₃.quote L.ctx (Kernel.leaf 2))
  -- the states the step leaves
  have hkeep := repC_pair (c₃.quote L.ctx (Kernel.leaf 1)) (repC_pair hdv' hnums)
  have hfail := repC_pair (c₃.quote L.ctx (Kernel.leaf 0)) (repC_pair hdv' hnums)
  have hnums' := repC_cons hkCons (isTy_tree _)
    (repC_pair
      (repC_pc₃ L hf.node2 rfl rfl rfl rfl c₃.val (c₃.quote L.ctx (Kernel.leaf 0))
        (repC_pc₁ L hf.nameOf rfl rfl c₃.val hn)
        (repC_pc₁ L hf.get rfl rfl c₃.val (repC_pc₂ L hf.numOf rfl rfl rfl c₃.val hnums hb)))
      hnums) hT
  have hnew := repC_pair (c₃.quote L.ctx (Kernel.leaf 1)) (repC_pair hdv' hnums')
  -- the test of source forms, at the expansion of the numeral abbreviations
  have hsrc := repC_pc₂ L hf.srcForm rfl rfl rfl c₃.val
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c₃.val hT
      (repC_pc₂ L hf.expandNums rfl rfl rfl c₄.val
        (repC_snd (repC_snd (c₄.var (i := 1) rfl) hT hLL) hL hL) (c₄.var (i := 0) rfl))) hb
  exact repC_stateTest L (repC_fst hs hT hLL)
    (repC_stateTest L
      (repC_pc₂ L hf.and rfl rfl rfl c₃.val (repC_pc₁ L hf.isListTx rfl rfl c₃.val he)
        (repC_pc₂ L hf.namedTx rfl rfl rfl c₃.val hhe (repC_pc₀ L hf.kwGeneric rfl c₃.val _)))
      hkeep
      (repC_stateTest L
        (repC_pc₂ L hf.or rfl rfl rfl c₃.val
          (repC_pc₂ L hf.namedTx rfl rfl rfl c₃.val hhe (repC_pc₀ L hf.kwData rfl c₃.val _))
          (repC_pc₂ L hf.namedTx rfl rfl rfl c₃.val hhe
            (repC_pc₀ L hf.kwTreeData rfl c₃.val _)))
        hkeep
        (repC_stateTest L
          (repC_pc₂ L hf.namedTx rfl rfl rfl c₃.val hhf (repC_pc₀ L hf.kwDef rfl c₃.val _))
          (repC_stateTest L hsrc hkeep hfail)
          (repC_stateTest L
            (repC_pc₂ L hf.namedTx rfl rfl rfl c₃.val hhf
              (repC_pc₀ L hf.kwDeftype rfl c₃.val _))
            hkeep
            (repC_stateTest L
              (repC_pc₂ L hf.namedTx rfl rfl rfl c₃.val hhf
                (repC_pc₀ L hf.kwDefnum rfl c₃.val _))
              hnew hkeep)))))
    hs

end Readings

section Hypotheses

variable (h : extended3 = some PST) (L : Translated PST) {f : HypFns}
  (hf : f.Loaded L.Gk PST.1.idx)

include h hf

/-- The hypothesis that the definitions' bodies are source forms, at a term of the forms in a
represented context, represents the statement of Lean ({name}`HypFns.PlainOk`). -/
theorem plain_rep {X : PartialHorn.Tree} {e : List (PartialHorn.Tree × PartialHorn.Tree)}
    {S A : Type} {R : S → A → Prop} {ents : List (Internal.RepEntry S)}
    (c : RepCtx L.defs L.cds₀ L.ext X e R ents) {es : Term} {Fes : S → List Kernel.Tree}
    (hes : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] es X e (list treeTy) R (Rep.list RT) Fes) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (plainTop PST.1 es) X e omega R Rep.prop
      fun σ ↦ f.PlainOk (Fes σ) := by
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hXp := objVal_xp (ds := L.cds₀ ++ L.ext)
  have hkNil : PST.1.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have hnil := repC_nil hkNil (isTy_tree _) (repC_star (e := e) c.val R) hT RT
  have hs₀ := repC_pair (c.quote L.ctx (Kernel.leaf 1)) (repC_pair hnil hnil)
  exact repC_truth L.ctx (DatatypeAccepted.hasLogic h) c.val
    (repC_fst
      (repC_runT (isTy_tree _) (isTy_xp _) hT hXp c.rep c.val
        (StepF := fun _ s x ↦ f.plainStepK s x) (repC_plainStep L hf c) hes hs₀)
      hT (objVal_prod hL hL))

/-- The hypothesis on the markers among a program's kernel forms represents the statement of
Lean ({name}`HypFns.MarkersOk`), at the kernel's lists of trees. -/
theorem markers_rep :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (PST.2.1.allL (markerPred PST.1 (msT PST.1 (v 0)))
      (fsT PST.1 (v 0))) (Internal.ctxObj [list treeTy]) (Internal.stdEnv [list treeTy]) omega
      (KRel (tList tT)) Rep.prop fun ks ↦ f.MarkersOk ks := by
  have hC := connectives h L
  have hlog := DatatypeAccepted.hasLogic h
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hTT := objVal_exp hT hT
  have hops := (ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) tT rfl).2.1
  have hvT : ObjVal [] treeTy BT := objVal_ty (T := tT) rfl
  obtain ⟨-, -, hl, hr⟩ := (order_props (tProd tT (tList tT))).1 rfl
  have c := RepCtx.single L.ctx hL (isTy_trees _) (Rep.list RT)
  have c₁ := c.extend L.ctx hT (isTy_tree _) RT
  -- the kernel's primitives: the equality of labels, the label and the child
  obtain ⟨a, ha, heq⟩ := c₁.prim L.ctx (k := Kernel.Prim.eq)
    (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.eq⟩) rfl rfl
  obtain rfl : a = exp treeTy (exp treeTy treeTy) := Option.some.inj (ha.symm.trans rfl)
  obtain ⟨a, ha, hlab⟩ := c₁.prim L.ctx (k := Kernel.Prim.label)
    (g := ⟨tArrow tT tT, Kernel.Const.label⟩) rfl rfl
  obtain rfl : a = exp treeTy treeTy := Option.some.inj (ha.symm.trans rfl)
  obtain ⟨a, ha, hchild⟩ := c₁.prim L.ctx (k := Kernel.Prim.child)
    (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.child⟩) rfl rfl
  obtain rfl : a = exp treeTy (exp treeTy treeTy) := Option.some.inj (ha.symm.trans rfl)
  have hx := c₁.var (G := PST.1.G) (i := 0) rfl
  -- the form is a marker, and the marker its datatype's atom finds is the form's
  have htest := repC_truth L.ctx hlog c₁.val
    (repC_app (repC_app heq (repC_app hlab hx hT hT) hT hTT) (c₁.quote L.ctx (Kernel.leaf 9)) hT
      hT)
  have hfound := repC_eq
    (repC_pc₂ L hf.markerCtors rfl rfl rfl c₁.val (repC_ms L hf c₁ (c₁.var (i := 1) rfl))
      (repC_app (repC_app hchild hx hT hTT) (c₁.quote L.ctx (Kernel.leaf 0)) hT hT))
    (repC_pair (c₁.quote L.ctx (Kernel.leaf 1))
      (repC_tail L.ctx (isTy_tree _) hops hvT (repC_children L.ctx hx)))
    (objVal_prod hT hL) hl hr
  exact repC_allL h L (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c.val hT
    (hC.imp htest hfound)) (repC_fs L hf c (c.var (i := 0) rfl))

/-- The hypothesis on the markers' names and constructors and on the numerals represents the
statement of Lean ({name}`HypFns.StaticOk`) at the markers of a program's kernel forms, at the
kernel's lists of trees. -/
theorem static_rep :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (staticT PST.1 (msT PST.1 (v 0)))
      (Internal.ctxObj [list treeTy]) (Internal.stdEnv [list treeTy]) omega (KRel (tList tT))
      Rep.prop fun ks ↦ f.StaticOk (f.msK ks) := by
  have hC := connectives h L
  have hlog := DatatypeAccepted.hasLogic h
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have hTT := objVal_exp hT hT
  have hsT := ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) tT rfl
  have hsL := ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) (tList tT) rfl
  have hvT : ObjVal [] treeTy BT := objVal_ty (T := tT) rfl
  have hvL : ObjVal [] (list treeTy) (List BT) := objVal_ty (T := tList tT) rfl
  obtain ⟨htot, hsur, hl, hr⟩ := (order_props tT).1 rfl
  obtain ⟨htotL, hsurL, -, -⟩ := (order_props (tList tT)).1 rfl
  have hkNil : PST.1.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have hkCons : PST.1.G.prims[1]? = some Internal.consPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have c := RepCtx.single L.ctx hL (isTy_trees _) (Rep.list RT)
  have c₁ := c.extend L.ctx hT (isTy_tree _) RT
  have c₂ := c₁.extend L.ctx hT (isTy_tree _) RT
  have c₃ := c₂.extend L.ctx hT (isTy_tree _) RT
  have c₄ := c₃.extend L.ctx hL (isTy_trees _) (Rep.list RT)
  -- each marker's datatype is named by an atom, not the trees' type's nor the unit type's
  have hn := c₁.var (G := PST.1.G) (i := 0) rfl
  have hnames := hC.all htot hsur (isTy_tree _) hsT.2.1 hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c.val hT
      (hC.imp
        (repC_truth L.ctx hlog c₁.val (repC_pc₁ L hf.isSome rfl rfl c₁.val
          (repC_pc₂ L hf.indexOf rfl rfl rfl c₁.val hn
            (repC_pc₁ L hf.markerNames rfl rfl c₁.val
              (repC_ms L hf c₁ (c₁.var (i := 1) rfl))))))
        (hC.conj (repC_truth L.ctx hlog c₁.val (repC_pc₁ L hf.isAtom rfl rfl c₁.val hn))
          (hC.conj
            (hC.imp
              (repC_truth L.ctx hlog c₁.val
                (repC_pc₂ L hf.named rfl rfl rfl c₁.val hn (repC_pc₀ L hf.kwT rfl c₁.val _)))
              (hC.ff c₁.val _))
            (hC.imp
              (repC_truth L.ctx hlog c₁.val
                (repC_pc₂ L hf.named rfl rfl rfl c₁.val hn
                  (repC_pc₀ L hf.kwUnit rfl c₁.val _)))
              (hC.ff c₁.val _))))))
  -- each marker's constructors have at most one of each label
  obtain ⟨a, ha, heq⟩ := c₄.prim L.ctx (k := Kernel.Prim.eq)
    (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.eq⟩) rfl rfl
  obtain rfl : a = exp treeTy (exp treeTy treeTy) := Option.some.inj (ha.symm.trans rfl)
  obtain ⟨a, ha, hchild⟩ := c₄.prim L.ctx (k := Kernel.Prim.child)
    (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.child⟩) rfl rfl
  obtain rfl : a = exp treeTy (exp treeTy treeTy) := Option.some.inj (ha.symm.trans rfl)
  obtain ⟨a, ha, hlt⟩ := c₂.prim L.ctx (k := Kernel.Prim.lt)
    (g := ⟨tArrow tT (tArrow tT tT), Kernel.Const.lt⟩) rfl rfl
  obtain rfl : a = exp treeTy (exp treeTy treeTy) := Option.some.inj (ha.symm.trans rfl)
  have hsel := repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c₂.val hT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_trees _) c₃.val hL
      (repC_condB L.ctx (isTy_trees _) hsL.2.1 hvL
        (repC_lab L.ctx
          (repC_app
            (repC_app heq
              (repC_app (repC_app hchild (c₄.var (i := 1) rfl) hT hTT)
                (c₄.quote L.ctx (Kernel.leaf 0)) hT hT) hT hTT)
            (c₄.var (i := 2) rfl) hT hT))
        (repC_cons hkCons (isTy_tree _)
          (repC_pair (c₄.var (i := 1) rfl) (c₄.var (i := 0) rfl)) hT)
        (c₄.var (i := 0) rfl)))
  have hfilter := repC_foldrT (isTy_tree _) (isTy_trees _) hT hL hsel
    (repC_nil hkNil (isTy_tree _)
      (repC_star (e := Internal.extEnv (prod (list treeTy) treeTy) treeTy
        (Internal.extEnv (list treeTy) treeTy (Internal.stdEnv [list treeTy]))) c₂.val
        (Rep.prod (Rep.prod (Rep.list RT) RT) RT)) hT RT)
    (repC_snd
      (repC_pc₂ L hf.markerCtors rfl rfl rfl c₂.val (repC_ms L hf c₂ (c₂.var (i := 2) rfl))
        (c₂.var (i := 1) rfl)) hT hL)
  have huniqs := hC.all htot hsur (isTy_tree _) hsT.2.1 hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c.val hT
      (hC.all htot hsur (isTy_tree _) hsT.2.1 hvT
        (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c₁.val hT
          (repC_truth L.ctx hlog c₂.val
            (repC_app (repC_app hlt (repC_pc₁ L hf.length rfl rfl c₂.val hfilter) hT hTT)
              (c₂.quote L.ctx (Kernel.leaf 2)) hT hT)))))
  -- the digits of a tree's label read as its leaf
  have hdec := hC.all htot hsur (isTy_tree _) hsT.2.1 hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c.val hT
      (repC_eq
        (repC_pc₁ L hf.numeral rfl rfl c₁.val (repC_pc₁ L hf.decimalChars rfl rfl c₁.val hn))
        (repC_pc₁ L hf.just rfl rfl c₁.val (repC_leafL L.ctx c₁.val (repC_lab L.ctx hn)))
        hT hl hr))
  -- and are fixed by the expansion of any numeral abbreviations
  have cn := c.extend L.ctx hL (isTy_trees _) (Rep.list RT)
  have ct := cn.extend L.ctx hT (isTy_tree _) RT
  have cy := ct.extend L.ctx hT (isTy_tree _) RT
  have hdig := hC.all htotL hsurL (isTy_trees _) hsL.2.1 hvL
    (repC_lam (G := PST.1.G) (n := 0) (isTy_trees _) c.val hL
      (hC.all htot hsur (isTy_tree _) hsT.2.1 hvT
        (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cn.val hT
          (repC_truth L.ctx hlog ct.val
            (repC_pc₂ L hf.charsFixed rfl rfl rfl ct.val
              (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) ct.val hT
                (repC_pc₂ L hf.expandNums rfl rfl rfl cy.val (cy.var (i := 2) rfl)
                  (cy.var (i := 0) rfl)))
              (repC_pc₁ L hf.decimalChars rfl rfl ct.val (ct.var (i := 0) rfl)))))))
  exact hC.conj hnames (hC.conj huniqs (hC.conj hdec hdig))

/-- The hypothesis on the forms of a program represents the statement of Lean
({name}`HypFns.FormsOk`), at the kernel's lists of trees. -/
theorem forms_rep :
    List.Forall₂ (fun (t : Term) (F : List Kernel.Tree → Prop) ↦
      RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t (Internal.ctxObj [list treeTy])
        (Internal.stdEnv [list treeTy]) omega (KRel (tList tT)) Rep.prop F)
      (formsOk PST.1 PST.2.1 (v 0)) [fun ks ↦ f.FormsOk ks] := by
  have hC := connectives h L
  have hlog := DatatypeAccepted.hasLogic h
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hL := objVal_list hT
  have c := RepCtx.single L.ctx hL (isTy_trees _) (Rep.list RT)
  have c₁ := c.extend L.ctx hT (isTy_tree _) RT
  have c₂ := c₁.extend L.ctx hT (isTy_tree _) RT
  -- the form's elements, its head and its second element
  have helems := repC_pc₁ L hf.elems rfl rfl c₁.val (c₁.var (i := 0) rfl)
  have hhead := repC_pc₂ L hf.nthTx rfl rfl rfl c₁.val helems (c₁.quote L.ctx (Kernel.leaf 0))
  have hsecond := repC_pc₂ L hf.nthTx rfl rfl rfl c₁.val helems
    (c₁.quote L.ctx (Kernel.leaf 1))
  -- the name the form declares is none of the implementation's
  have huser := hC.imp
    (repC_truth L.ctx hlog c₁.val (repC_pc₁ L hf.implName rfl rfl c₁.val
      (repC_pc₁ L hf.nameOf rfl rfl c₁.val hsecond)))
    (hC.ff c₁.val _)
  -- a datatype's declaration: no constructor's name, and not the recognizer's
  have hctors := repC_allL h L
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c₁.val hT
      (hC.imp
        (repC_truth L.ctx hlog c₂.val (repC_pc₁ L hf.implName rfl rfl c₂.val
          (repC_pc₁ L hf.nameOf rfl rfl c₂.val
            (repC_pc₂ L hf.nthTx rfl rfl rfl c₂.val
              (repC_pc₁ L hf.elems rfl rfl c₂.val (c₂.var (i := 0) rfl))
              (c₂.quote L.ctx (Kernel.leaf 0))))))
        (hC.ff c₂.val _)))
    (repC_pc₂ L hf.drop rfl rfl rfl c₁.val (c₁.quote L.ctx (Kernel.leaf 2)) helems)
  have hrec := hC.imp
    (repC_truth L.ctx hlog c₁.val (repC_pc₁ L hf.implName rfl rfl c₁.val
      (repC_pc₁ L hf.nameOf rfl rfl c₁.val (repC_pc₁ L hf.memberName rfl rfl c₁.val hsecond))))
    (hC.ff c₁.val _)
  have hdata := hC.imp
    (repC_truth L.ctx hlog c₁.val
      (repC_pc₂ L hf.namedTx rfl rfl rfl c₁.val hhead (repC_pc₀ L hf.kwData rfl c₁.val _)))
    (hC.conj hctors hrec)
  have htree := hC.imp
    (repC_truth L.ctx hlog c₁.val
      (repC_pc₂ L hf.namedTx rfl rfl rfl c₁.val hhead (repC_pc₀ L hf.kwTreeData rfl c₁.val _)))
    (hC.ff c₁.val _)
  have hnum := hC.imp
    (repC_truth L.ctx hlog c₁.val
      (repC_pc₂ L hf.namedTx rfl rfl rfl c₁.val hhead (repC_pc₀ L hf.kwDefnum rfl c₁.val _)))
    huser
  have hdef := hC.imp
    (repC_truth L.ctx hlog c₁.val
      (repC_pc₂ L hf.namedTx rfl rfl rfl c₁.val hhead (repC_pc₀ L hf.kwDef rfl c₁.val _)))
    huser
  have hdefn := hC.imp
    (repC_truth L.ctx hlog c₁.val
      (repC_pc₂ L hf.namedTx rfl rfl rfl c₁.val hhead (repC_pc₀ L hf.kwDefn rfl c₁.val _)))
    huser
  exact .cons (repC_allL h L
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c.val hT
      (hC.conj hdata (hC.conj htree (hC.conj hnum (hC.conj hdef hdefn)))))
    (c.var (i := 0) rfl)) .nil

end Hypotheses

end GebTests.Prototypes.FreeTopos.Certified.DatatypeHypotheses

end
