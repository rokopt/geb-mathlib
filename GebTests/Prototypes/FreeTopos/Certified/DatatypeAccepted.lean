/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.RepresentLogic
public import Geb.Prototypes.FreeTopos.Internal.Unfolded
public import GebTests.Prototypes.FreeTopos.Certified.DatatypeLoad
public import GebTests.Prototypes.FreeTopos.DatatypeBase
public import GebTests.Prototypes.FreeTopos.DatatypeProgramStep
public import GebTests.Prototypes.ProgramCommand
public meta import Geb.Prototypes.FreeTopos.Internal.RepresentLogic -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Unfolded -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Certified.DatatypeLoad -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeBase -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramStep -- shake: keep

set_option doc.verso true in
/-!
# The constants of the datatype language's soundness are accepted

The constants of the program the datatype language's soundness is stated in, the translated
compilers extended by the relations' definitions, are ones the developments' soundness reads
({name}`Geb.FreeTopos.Internal.Globals.accepted`): each definition compiles over the
definitions before it, the check accepts the primitive arrows and the definitions, and the
definitions they compile to are well formed. Lean's evaluator decides it. The theory of a topos
extended by those definitions therefore has models, in each of which the constants' invariant
holds, so that the validity of a development's theorems in every model of the program is that
of each of them.

The module states the other facts about the compilers' program that Lean's evaluator decides
for the soundness's transfer to Lean: the constants of the translation alone are accepted
too, the definitions the compiler's passes call have, in the types the translation records,
the kernel types named with them, and the extended program's constants have, at their indices,
the definitions the soundness's conclusion is stated by. The compilers' program is also the one
the kernel loads to its mirror's definitions ({lit}`DatatypeLoad`): its definitions' trees are
those loaded, and the entries of its manifest are at the indices named with them.

## Main definitions

* {lit}`translatedGlobals` — the constants of the translation of the compilers' program.
* {lit}`passGlobals`, {lit}`statementGlobals`, {lit}`hypGlobals` — the definitions the
  compiler's passes, the soundness's conclusion and its remaining hypotheses call, with their
  kernel types.
* {lit}`statementDefs` — the definitions the soundness's conclusion is stated by, with their
  indices.
* {lit}`mirrorIndices` — the entries of the program's manifest, with their indices among the
  program's definitions.

## Main statements

* {lit}`accepted` — the constants of the extended program are accepted.
* {lit}`hasLogic` — they have the connectives' definitions from the index the program names.
* {lit}`translatedAccepted` — the constants of the translation alone are accepted.
* {lit}`passGlobalsTyped`, {lit}`statementGlobalsTyped`, {lit}`hypGlobalsTyped` — the
  definitions the passes, the conclusion and the remaining hypotheses call have the kernel
  types named.
* {lit}`defined`, {lit}`natPrims` — the extended program's constants have the definitions the
  conclusion is stated by, and the primitive arrows of the natural numbers.
* {lit}`envTy_eq` — the type of the typing's environments the program records is the
  translation of their kernel type.
* {lit}`mirrorTrees`, {lit}`mirrorIndexed` — the program's definitions are those the kernel
  loads to the mirror's, and the manifest's entries are at the indices named.
* {lit}`exists_programForms` — the extended program exists, and the soundness of a whole program
  is stated in it.

## Tags

internal language, datatypes, definitional extension, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

open Geb Geb.FreeTopos GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs pc truth succN fnsTy kZero kSucc)
open Geb.FreeTopos.Translation
open Internal (Term)
open Kernel (tT tList tProd tArrow)
open Sorts
open scoped FinEnum

/-- Whether the constants of a program, where one is given, are ones the check accepts that
compile to well-formed definitions ({name}`Geb.FreeTopos.Internal.Globals.accepted`). -/
def acceptedIn {α : Type} (o : Option α) (G : α → Internal.Globals) : Bool :=
  match o with
  | some P => (G P).accepted
  | none => false

set_option doc.verso false in
/-- The constants of the extended program are accepted and compile to well-formed definitions,
as Lean's evaluator decides. -/
evaluation_axiom constantsAccepted : acceptedIn extended3 (·.1.G) = true

/-- The constants of the extended program are accepted. -/
theorem accepted {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    PST.1.G.accepted = true := by
  have ha := constantsAccepted
  rw [h] at ha
  exact ha

/-- Whether the constants of a program, where one is given, have the connectives' definitions
from the index it names ({name}`Geb.FreeTopos.Internal.Globals.hasLogic`). -/
def hasLogicIn {α : Type} (o : Option α) (G : α → Internal.Globals) (i : α → ℕ) : Bool :=
  match o with
  | some P => (G P).hasLogic (i P)
  | none => false

set_option doc.verso false in
/-- The constants of the extended program have the connectives' definitions from the index the
program names, as Lean's evaluator decides. -/
evaluation_axiom logicPresent : hasLogicIn extended3 (·.1.G) (·.1.o) = true

/-- The constants of the extended program have the connectives' definitions. -/
theorem hasLogic {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    Internal.HasLogic PST.1.G PST.1.o := by
  have ha := logicPresent
  rw [h] at ha
  exact Internal.Globals.hasLogic_sound ha

/-- The constants of the translation of the bundled compilers' program, where the program
bundles and translates. -/
def translatedGlobals : Option Internal.Globals := do
  let ds ← Weakening.bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList
  let (_, defs) ← Translation.program (ds.map Prod.snd)
  pure (Translation.globals defs)

set_option doc.verso false in
/-- The constants of the translation of the bundled compilers' program are accepted and compile
to well-formed definitions, as Lean's evaluator decides. -/
evaluation_axiom translatedAccepted : acceptedIn translatedGlobals id = true

/-- The bundled definitions of the compilers' program with the kernel types the translation
records for them, where the program bundles and translates. -/
def bundledTypes : Option (List (List Char × PartialHorn.Tree) × List PartialHorn.Tree) := do
  let ds ← Weakening.bundled Geb.Kernel.Stage0Tests.bundler.toList programText.toList
  let (gt, _) ← Translation.program (ds.map Prod.snd)
  pure (ds, gt)

/-- Whether each of the named definitions, among bundled definitions with their kernel types
where given, has the kernel type given with its name. -/
def typedIn (o : Option (List (List Char × PartialHorn.Tree) × List PartialHorn.Tree))
    (l : List (String × Kernel.Tree)) : Bool :=
  match o with
  | some (ds, gt) => l.all fun p ↦
    match ds.findIdx? fun d ↦ d.1 == p.1.toList with
    | some i => decide (gt[i]? = some p.2)
    | none => false
  | none => false

/-- The kernel type of the typing environment: its lists of trees. -/
def envTy : Kernel.Tree :=
  tProd (tList tT) (tProd (tList tT) (tProd (tList tT) (tProd (tList tT)
    (tProd (tList tT) (tList tT)))))

/-- The names of the compilers' definitions the passes call, each with its kernel type. -/
def passGlobals : List (String × Kernel.Tree) :=
  [("Datatype.expandTyped", tArrow (tList tT) (tProd tT (tList tT))),
    ("Typing/OName.nothing", tT),
    ("Typing.checkAll", tArrow (tProd envTy tT) (tArrow (tList tT) (tProd envTy tT))),
    ("Typing.env0", envTy),
    ("Datatype.markersFirst", tArrow (tList tT) (tList tT)),
    ("Recognize.insertRecognizers", tArrow (tList tT) tT),
    ("Datatype.kernelForms", tArrow (tList tT) (tList tT)),
    ("Reader.readProgram", tArrow (tList tT) tT),
    ("Prelude.get", tArrow tT tT),
    ("Prelude.isSome", tArrow tT tT),
    ("Check.checkProgram", tArrow (tList tT) tT)]

set_option doc.verso false in
/-- The compilers' definitions the passes call have the kernel types named with them, in the
types the translation records, as Lean's evaluator decides. -/
evaluation_axiom passGlobalsTyped : typedIn bundledTypes passGlobals = true

/-- The kernel type of the evaluator's functions at a level: evaluation in an environment, and
application. -/
def fnsK : Kernel.Tree := tProd (tArrow (tList tT) (tArrow tT tT)) (tArrow tT (tArrow tT tT))

/-- The names of the compilers' definitions the soundness's conclusion calls, each with its
kernel type. -/
def statementGlobals : List (String × Kernel.Tree) :=
  [("Prelude.some", tArrow tT tT), ("Prelude.nth", tArrow (tList tT) (tArrow tT tT)),
    ("Prelude.get", tArrow tT tT), ("Prelude.isSome", tArrow tT tT),
    ("Eval.level", tArrow (tList tT) (tArrow tT fnsK)),
    ("Eval.next", tArrow (tList tT) (tArrow fnsK fnsK)),
    ("Eval.valQuote", tArrow tT tT), ("Eval.valUnit", tT),
    ("Eval.valPair", tArrow tT (tArrow tT tT)), ("Eval.listOf", tArrow tT tT),
    ("Typing.memberOf", tArrow (tList tT) (tArrow tT (tArrow tT tT))),
    ("Typing.lookupName", tArrow tT (tArrow (tList tT) tT)),
    ("Typing.envDefs", tArrow envTy (tList tT)),
    ("Typing.hasName", tArrow tT (tArrow (tList tT) tT)),
    ("Typing.envNoms", tArrow envTy (tList tT)), ("Typing.recognizerName", tArrow tT tT),
    ("Reader.indexOf", tArrow tT (tArrow (tList tT) tT)),
    ("Typing.envMs", tArrow envTy (tList tT))]

set_option doc.verso false in
/-- The compilers' definitions the soundness's conclusion calls have the kernel types named
with them, in the types the translation records, as Lean's evaluator decides. -/
evaluation_axiom statementGlobalsTyped : typedIn bundledTypes statementGlobals = true

/-- The kernel type of the expansion's states: whether every form has expanded, the
declarations, and the forms written. -/
def xpK : Kernel.Tree := tProd tT (tProd (tList tT) (tList tT))

/-- The names of the compilers' definitions the soundness's remaining hypotheses call, each
with its kernel type. -/
def hypGlobals : List (String × Kernel.Tree) :=
  [("Datatype.genericStep", tArrow xpK (tArrow tT xpK)),
    ("Datatype.xpStep", tArrow xpK (tArrow tT xpK)),
    ("Prelude.and", tArrow tT (tArrow tT tT)),
    ("Datatype.isListTx", tArrow tT tT), ("Datatype.namedTx", tArrow tT (tArrow tT tT)),
    ("Datatype.nthTx", tArrow (tList tT) (tArrow tT tT)), ("Datatype.elems", tArrow tT (tList tT)),
    ("Datatype.kwGeneric", tT), ("Datatype.kwData", tT),
    ("Datatype.kwDefn", tT), ("Reader.kwDef", tT), ("Reader.kwDeftype", tT),
    ("Reader.kwDefnum", tT), ("Reader.kwT", tT), ("Reader.kwUnit", tT),
    ("srcForm", tArrow (tArrow tT tT) (tArrow tT tT)),
    ("Reader.expandNums", tArrow (tList tT) (tArrow tT tT)),
    ("Reader.numOf", tArrow (tList tT) (tArrow tT tT)), ("Reader.nameOf", tArrow tT tT),
    ("Reader.node2", tArrow tT (tArrow tT (tArrow tT tT))),
    ("Datatype/Txs.reverse", tArrow (tList tT) (tList tT)),
    ("Datatype/Txs.drop", tArrow tT (tArrow (tList tT) (tList tT))),
    ("Datatype.kernelForms", tArrow (tList tT) (tList tT)),
    ("Recognize.markers", tArrow (tList tT) (tList tT)),
    ("Typing.markerCtors", tArrow (tList tT) (tArrow tT (tProd tT (tList tT)))),
    ("Typing.markerNames", tArrow (tList tT) (tList tT)), ("Reader.isAtom", tArrow tT tT),
    ("Reader.named", tArrow tT (tArrow tT tT)), ("Prelude.length", tArrow (tList tT) tT),
    ("Reader.numeral", tArrow (tList tT) tT), ("Typing.decimalChars", tArrow tT (tList tT)),
    ("charsFixed", tArrow (tArrow tT tT) (tArrow (tList tT) tT)), ("implName", tArrow tT tT),
    ("Datatype.memberName", tArrow tT tT), ("Prelude.get", tArrow tT tT),
    ("Prelude.isSome", tArrow tT tT), ("Prelude.some", tArrow tT tT),
    ("Reader.indexOf", tArrow tT (tArrow (tList tT) tT))]

set_option doc.verso false in
/-- The compilers' definitions the soundness's remaining hypotheses call have the kernel types
named with them, in the types the translation records, as Lean's evaluator decides. -/
evaluation_axiom hypGlobalsTyped : typedIn bundledTypes hypGlobals = true

/-! The definitions the soundness's conclusion is stated by. -/

/-- Addition's definition: recursion on the second summand into functions of the first. -/
def addDefn : Internal.Defn :=
  ⟨0, [nat, nat], nat, Term.app (Term.natRec (Term.lam nat (v 0))
    (Term.lam nat (succN (Term.app (v 1) (v 0)))) (v 0)) (v 1)⟩

/-- Convergence's definition: from some fuel on, the function's value is one value the
predicate holds of. -/
def convDefn (P : Prog) (S : Defs) : Internal.Defn :=
  let o := P.o
  ⟨0, [exp treeTy omega, exp nat treeTy], omega,
    Internal.Logic.ex o nat (Term.lam nat (Internal.Logic.ex o treeTy (Term.lam treeTy
      (Internal.Logic.conj o (Internal.Logic.all o nat (Term.lam nat
          (Term.eq (Term.app (v 4) (S.add (v 2) (v 0))) (pc P "Prelude.some" [v 1]))))
        (Term.app (v 2) (v 0))))))⟩

/-- The definition of a predicate's holding of every element of a list. -/
def allLDefn (P : Prog) : Internal.Defn :=
  let o := P.o
  ⟨0, [list treeTy, exp treeTy omega], omega,
    Term.app (Term.listRec (Term.lam (exp treeTy omega) (Internal.Logic.tt o))
      (Term.lam (exp treeTy omega) (Internal.Logic.conj o (Term.app (v 0) (v 2))
        (Term.app (v 1) (v 0)))) (v 0)) (v 1)⟩

/-- The definition of the evaluator's functions at a level of fuel: the fold of the level from
the level zero. -/
def levelDefn (P : Prog) : Internal.Defn :=
  ⟨0, [nat, list treeTy], fnsTy,
    Term.app (Term.natRec (Term.lam (list treeTy) (pc P "Eval.level" [v 0, leafT bnilT]))
      (Term.lam (list treeTy) (pc P "Eval.next" [v 0, Term.app (v 1) (v 0)])) (v 0)) (v 1)⟩

/-- The definition of the relation of the definitions to the typing environment's: at each
name the environment gives some type, the reader's names give an index, at which the
definitions have some term whose evaluation in the empty environment converges to a value
related at that type. -/
def globDefn (P : Prog) (S : Defs) (T : Defs3) : Internal.Defn :=
  let o := P.o
  let ex := Internal.Logic.ex o
  let conj := Internal.Logic.conj o
  ⟨0, [list treeTy, T.envTy, Defs3.ctxTy], omega,
    Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (pc P "Prelude.isSome"
        [pc P "Typing.lookupName" [v 0, pc P "Typing.envDefs" [v 2]]]))
      (ex treeTy (Term.lam treeTy (conj (Term.eq (pc P "Reader.indexOf" [v 1, v 2])
          (pc P "Prelude.some" [v 0]))
        (ex treeTy (Term.lam treeTy (conj
          (Term.eq (pc P "Prelude.nth" [Term.fst (v 5), v 1]) (pc P "Prelude.some" [v 0]))
          (S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (nilT treeTy) (v 1)))
            (T.relT (v 5) (pc P "Prelude.get"
              [pc P "Typing.lookupName" [v 2, pc P "Typing.envDefs" [v 4]]])))))))))))⟩

/-- The definition of the recognizers' agreement with membership: at each datatype of the
environment whose recognizer's name has an index, the definition there evaluates to a function
whose application to the quotation of a tree converges to the quotation of a tree true exactly
when the tree is a member of the datatype. -/
def recsDefn (P : Prog) (S : Defs) (T : Defs3) : Internal.Defn :=
  let o := P.o
  let ex := Internal.Logic.ex o
  let all := Internal.Logic.all o
  let conj := Internal.Logic.conj o
  let imp := Internal.Logic.imp o
  let member : Term := pc P "Typing.memberOf" [Term.snd (v 9),
    nodeT (Term.pair (numeral 1) (call D.children [] [v 6])), v 2]
  let agrees : Term := ex treeTy (Term.lam treeTy (conj
    (Term.eq (v 1) (pc P "Eval.valQuote" [v 0]))
    (conj (imp (truth o (v 0)) (truth o member)) (imp (truth o member) (truth o (v 0))))))
  let applied : Term := S.conv (Term.lam nat (Tactics.apps
    (Term.snd (S.levelN (Term.fst (v 8)) (v 0))) [v 2, pc P "Eval.valQuote" [v 1]]))
    (Term.lam treeTy agrees)
  let recognizer : Term := conj
    (Term.eq (pc P "Prelude.nth" [Term.fst (v 5), v 1]) (pc P "Prelude.some" [v 0]))
    (S.conv (Term.lam nat (S.evN (Term.fst (v 6)) (v 0) (nilT treeTy) (v 1)))
      (Term.lam treeTy (all treeTy (Term.lam treeTy applied))))
  ⟨0, [list treeTy, T.envTy, Defs3.ctxTy], omega,
    all treeTy (Term.lam treeTy (imp
      (truth o (pc P "Typing.hasName" [v 0, pc P "Typing.envNoms" [v 2]]))
      (imp (truth o (pc P "Prelude.isSome" [pc P "Reader.indexOf"
          [pc P "Typing.recognizerName" [v 0], v 1]]))
        (ex treeTy (Term.lam treeTy (conj
          (Term.eq (pc P "Reader.indexOf" [pc P "Typing.recognizerName" [v 1], v 2])
            (pc P "Prelude.some" [v 0]))
          (ex treeTy (Term.lam treeTy recognizer))))))))⟩

/-- The definitions the soundness's conclusion is stated by, each with its index among the
extended program's: addition, convergence, the quantification over a list and the evaluator's
levels, of the fundamental lemma's definitions; and the relation at a type, the relation of the
definitions to the typing environment's, and the recognizers' agreement with membership. -/
def statementDefs (PST : Prog × Defs × Defs3) : List (ℕ × Internal.Defn) :=
  [(PST.2.1.q, addDefn), (PST.2.1.q + 2, convDefn PST.1 PST.2.1),
    (PST.2.1.q + 3, allLDefn PST.1), (PST.2.1.q + 4, levelDefn PST.1),
    (PST.2.2.q, relDefn PST.1 PST.2.1), (PST.2.2.q + 2, globDefn PST.1 PST.2.1 PST.2.2),
    (PST.2.2.q + 6 + 2 * nFolds, recsDefn PST.1 PST.2.1 PST.2.2)]

/-- Whether the constants of a program, where one is given, have each of the definitions
listed at its index, and the primitive arrows of the natural numbers at theirs. -/
def definesIn {α : Type} (o : Option α) (G : α → Internal.Globals)
    (l : α → List (ℕ × Internal.Defn)) : Bool :=
  match o with
  | some x =>
    ((l x).all fun p ↦ match (G x).defs[p.1]? with
      | some (.language d) => decide (d.arity = p.2.arity ∧ d.params = p.2.params ∧
          d.type = p.2.type ∧ d.body = p.2.body)
      | _ => false) &&
    decide ((G x).prims[kZero]? = some Internal.zeroPrim ∧
      (G x).prims[kSucc]? = some Internal.succPrim)
  | none => false

set_option doc.verso false in
/-- The constants of the extended program have the definitions the soundness's conclusion is
stated by, and the primitive arrows of the natural numbers, as Lean's evaluator decides. -/
evaluation_axiom statementsDefined : definesIn extended3 (·.1.G) statementDefs = true

/-- The constants of the extended program have each definition the soundness's conclusion is
stated by at its index. -/
theorem defined {PST : Prog × Defs × Defs3} (h : extended3 = some PST) {k : ℕ}
    {d : Internal.Defn} (hm : (k, d) ∈ statementDefs PST) :
    PST.1.G.defs[k]? = some (.language d) := by
  have ha := statementsDefined
  rw [h] at ha
  have hp := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ha).1 (k, d) hm
  split at hp
  · next d' hd' =>
    simp only [decide_eq_true_eq] at hp
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hp
    obtain ⟨a, ps, ty, b⟩ := d'
    obtain ⟨a', ps', ty', b'⟩ := d
    obtain rfl : a = a' := h₁
    obtain rfl : ps = ps' := h₂
    obtain rfl : ty = ty' := h₃
    obtain rfl : b = b' := h₄
    exact hd'
  · exact nomatch hp

/-- The type of the typing's environments: the translation of their kernel type
({name}`envTy`). -/
def envT : PartialHorn.Tree :=
  prod (list treeTy) (prod (list treeTy) (prod (list treeTy) (prod (list treeTy)
    (prod (list treeTy) (list treeTy)))))

/-- Whether the type of the typing's environments a program's definitions record, where a
program is given, is the translation of their kernel type. -/
def envTyIn (o : Option (Prog × Defs × Defs3)) : Bool :=
  match o with
  | some PST => decide (PST.2.2.envTy = envT)
  | none => false

set_option doc.verso false in
/-- The type of the typing's environments the extended program records is the translation of
their kernel type, as Lean's evaluator decides. -/
evaluation_axiom envTyChecked : envTyIn extended3 = true

/-- The type of the typing's environments the extended program records is the translation of
their kernel type. -/
theorem envTy_eq {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    PST.2.2.envTy = envT := by
  have ha := envTyChecked
  rw [h] at ha
  exact of_decide_eq_true ha

/-- The constants of the extended program have the primitive arrows of the natural numbers,
zero and the successor, after the translation's. -/
theorem natPrims {PST : Prog × Defs × Defs3} (h : extended3 = some PST) :
    PST.1.G.prims[kZero]? = some Internal.zeroPrim ∧
      PST.1.G.prims[kSucc]? = some Internal.succPrim := by
  have ha := statementsDefined
  rw [h] at ha
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp ha).2

/-- Whether the trees of bundled definitions are the trees given. -/
def treesIn (o : Option (List (List Char × PartialHorn.Tree) × List PartialHorn.Tree))
    (ts : List Kernel.Tree) : Bool :=
  match o with
  | some (ds, _) => decide (ds.map Prod.snd = ts)
  | none => false

set_option doc.verso false in
/-- The definitions of the compilers' program are those of the program the kernel loads to its
mirror's definitions (`GebMirror.datatypeSoundness`), tree by tree, as Lean's evaluator
decides. -/
evaluation_axiom mirrorTrees : treesIn bundledTypes GebMirror.datatypeSoundness = true

/-- Whether each of the named definitions, among bundled definitions, is at the index named
with it. -/
def indexedIn (o : Option (List (List Char × PartialHorn.Tree) × List PartialHorn.Tree))
    (l : List (String × ℕ)) : Bool :=
  match o with
  | some (ds, _) => l.all fun p ↦
    decide ((ds.findIdx? fun d ↦ d.1 == p.1.toList) = some p.2)
  | none => false

/-- The entries of the manifest of the compilers' program, each with its index among the
program's definitions. -/
def mirrorIndices : List (String × ℕ) :=
  [("Prelude.length", 1), ("Prelude.some", 5), ("Prelude.isSome", 7), ("Prelude.get", 8),
    ("Prelude.and", 9), ("Prelude.nth", 12), ("Reader.isAtom", 50), ("Reader.nameOf", 52),
    ("Reader.named", 53), ("Reader.kwT", 54), ("Reader.kwUnit", 55), ("Reader.kwDef", 74),
    ("Reader.kwDeftype", 75), ("Reader.kwDefnum", 76), ("Reader.indexOf", 78),
    ("Reader.numeral", 80), ("Reader.expandNums", 81), ("Reader.numOf", 82), ("Reader.node2", 85),
    ("Reader.readProgram", 107), ("Check.checkProgram", 122), ("Typing.envDefs", 203),
    ("Typing.envNoms", 204), ("Typing.envMs", 207), ("Typing.env0", 208),
    ("Typing.lookupName", 209), ("Typing.hasName", 210), ("Typing.recognizerName", 213),
    ("Typing.markerNames", 243), ("Typing.memberOf", 247), ("Typing.decimalChars", 269),
    ("Typing.markerCtors", 286), ("Typing/OName.nothing", 299), ("Typing.checkAll", 313),
    ("Datatype/Txs.reverse", 318), ("Datatype/Txs.drop", 320), ("Datatype.isListTx", 338),
    ("Datatype.namedTx", 339), ("Datatype.elems", 340), ("Datatype.nthTx", 341),
    ("Datatype.kwData", 387), ("Datatype.kwDefn", 390), ("Datatype.kwGeneric", 395),
    ("Datatype.memberName", 400), ("Datatype.xpStep", 473), ("Datatype.genericStep", 474),
    ("Datatype.expandTyped", 475), ("Datatype.markersFirst", 483), ("Datatype.kernelForms", 484),
    ("Recognize.markers", 530), ("Recognize.insertRecognizers", 542), ("Eval.valQuote", 557),
    ("Eval.valUnit", 558), ("Eval.valPair", 559), ("Eval.listOf", 564), ("Eval.next", 580),
    ("Eval.level", 581), ("charsFixed", 590), ("srcForm", 591), ("implName", 593)]

set_option doc.verso false in
/-- The entries of the manifest of the compilers' program are at the indices named with them, as
Lean's evaluator decides. -/
evaluation_axiom mirrorIndexed : indexedIn bundledTypes mirrorIndices = true

/-- Whether the soundness of a whole program is stated in an extended program. -/
def statedIn (o : Option (Prog × Defs × Defs3)) : Bool :=
  match o with
  | some PST => (programFormsThm PST.1 PST.2.1 PST.2.2).isSome
  | none => false

set_option doc.verso false in
/-- The compilers' program extends, and the soundness of a whole program is stated in the
extended program, as Lean's evaluator decides. -/
evaluation_axiom programStated : statedIn extended3 = true

/-- The extended program exists, and the soundness of a whole program is stated in it. -/
theorem exists_programForms : ∃ (PST : Prog × Defs × Defs3) (a : Internal.Thm),
    extended3 = some PST ∧ programFormsThm PST.1 PST.2.1 PST.2.2 = some a := by
  have ha := programStated
  cases he : extended3 with
  | none => rw [he] at ha; exact nomatch ha
  | some PST =>
    rw [he] at ha
    have hs : (programFormsThm PST.1 PST.2.1 PST.2.2).isSome = true := ha
    obtain ⟨a, hs⟩ := Option.isSome_iff_exists.mp hs
    exact ⟨PST, a, rfl, hs⟩

end GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted

end
