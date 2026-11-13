/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeProgramRuns
public import GebTests.Prototypes.FreeTopos.DatatypeConstructor
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramRuns -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeConstructor -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, by induction on its forms

The soundness of a program of the datatype language, generalized over the states of the
compiler's passes: from the declarations the expansion has, the typing's environment, and the
reader's abbreviations, names and terms, where the passes over the forms that remain end without
a failure, the definitions the reader ends with are related to the typing environment the typing
ends with. It is proved by induction on the forms. A form at which the expansion's step does not
fail, and whose head the tree datatypes' keyword does not name, is of a kind: a definition, a
type or a numeral abbreviation, a function, a template's instance, or a datatype's declaration.
The step at a kind shows that the states the passes' steps leave at a form of it satisfy the
invariant, which includes the recognizers' agreement with membership: it is kept where a
definition is read because the definition's name occurs in the program's kernel forms and each
recognizer those forms refer to is among the names the reader has, so that the name, which is
fresh, is no recognizer's. A definition and a function share the step at a form at which the
expansion writes a definition, whose body is a source form sound at expanded forms; the
hypotheses at the states are preserved by a definition written before pending forms, as the
definitions a datatype's declaration writes are. The step at a datatype's declaration is that
of {lit}`GebTests.Prototypes.FreeTopos.DatatypeProgramData`; for it the invariant has that no
name is one of the implementation's, that the typing environment has no sort, that the
expansion's aliases are coherent with the environment's abbreviations and are type
abbreviations of the reader's, and that the markers are the environment's. The aliases'
coherence is kept where a type abbreviation is declared. At the states the passes begin in,
the soundness at all states is that of the program.

The soundness assumes of the program's forms that the tree datatypes' keyword names no form's
head, and that no numeral abbreviation, definition, function, constructor or recognizer takes a
name of the implementation's; that each definition's body the expansion writes is a source form
at the numeral abbreviations before it, which a run over the program's forms tests; of the
program's markers, that each is the one its datatype's atom finds among them, that its
datatype is named by an atom naming neither the trees' type nor the unit type, and that its
constructors have at most one of each label; and, of the numerals, that the digits of a tree's
label read as its leaf and are fixed by the expansion of numeral abbreviations.

## Main definitions

* {lit}`Passes` — the states of the passes and the forms that remain.
* {lit}`Passes.hyps`, {lit}`Passes.concl` — the hypotheses and the conclusion at the states.
* {lit}`staticT`, {lit}`markerPred` — what the soundness assumes of the markers and the
  numerals.
* {lit}`preOk` — what the soundness assumes of a form.
* {lit}`formOk` — the kinds of forms.

## Main statements

* {lit}`writtenInv` — the hypotheses at the states are preserved by a definition written.
* {lit}`stepDefined` — the step at a form at which the expansion writes a definition.
* {lit}`cohAt`, {lit}`aliasExtend` — a type the typing reads coheres with the expansion of its
  aliases, and the aliases' coherence is kept where a type abbreviation is declared.
* {lit}`formKind` — a form at which the expansion's step does not fail is of a kind.
* {lit}`passesForms` — the soundness at all states, by induction on the forms.
* {lit}`programFormsThm`, {lit}`programForms` — the soundness of a program, its statement
  and its proof.
* {lit}`programClosed` — the soundness of a program as one formula without hypotheses.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The forms the recognizers' insertion gives for kernel forms, each optional: the markers
{lit}`mk` and the forms {lit}`fs` of the whole program, the forms {lit}`l` mapped. -/
def recMap (P : Prog) (mk fs l : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (consT treeTy
    (pc P "Recognize.recognizersAt" [sh 2 mk, sh 2 fs, v 1]) (v 0)))) (nilT treeTy) l

/-- The reader's test that every optional tree of a list is present, with their values. -/
def optFold (P : Prog) (xs : Term) : Term :=
  let R := prod treeTy (list treeTy)
  foldrT treeTy R (Term.lam treeTy (Term.lam R (Term.pair
    (pc P "Reader.both" [v 1, Term.fst (v 0)])
    (consT treeTy (pc P "Prelude.get" [v 1]) (Term.snd (v 0))))))
    (Term.pair (leafT (numeral 1)) (nilT treeTy)) xs

/-- The concatenation of the children of the trees of a list. -/
def flatT (P : Prog) (xs : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls
    (pc P "Prelude.append" [call D.children [] [v 1], v 0]))) (nilT treeTy) xs

/-- Whether an atom occurs in a form, as the recognizers' insertion tests it. -/
def occT (P : Prog) (a g : Term) : Term := pc P "Recognize.occurs" [a, g]

/-- Whether an atom occurs in a form of a list, as the recognizers' insertion tests the program's
forms for a recognizer's atom. -/
def occInT (P : Prog) (a fs : Term) : Term := anyT P (occT P (sh 2 a) (v 1)) fs

/-- That each atom that occurs in a form occurs in a list of forms: the predicate of the form,
beneath it, at the list. -/
def occPred (P : Prog) (fs : Term) : Term :=
  Term.lam treeTy (Internal.Logic.all P.o treeTy (Term.lam treeTy (Internal.Logic.imp P.o
    (truth P.o (occT P (v 0) (v 1))) (truth P.o (occInT P (v 0) (sh 2 fs))))))

/-- The atom of a name: the node of the atoms' label over the name's characters. -/
def atomOfNameT (n : Term) : Term := nodeT (Term.pair (numeral 1) (call D.children [] [n]))

/-- The atom of a datatype's recognizer, of the recognizer's name. -/
def memberAtomT (P : Prog) (d : Term) : Term :=
  atomOfNameT (pc P "Typing.recognizerName" [d])

/-- That the recognizers the program's forms refer to are among the names: at each datatype of
the typing environment whose recognizer's atom occurs in the forms, the recognizer's name has an
index among the names. -/
def insT (P : Prog) (Ev names fs : Term) : Term :=
  let o := P.o
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
    (truth o (pc P "Typing.hasName" [v 0, pc P "Typing.envNoms" [sh 1 Ev]]))
    (Internal.Logic.imp o (truth o (occInT P (memberAtomT P (v 0)) (sh 1 fs)))
      (truth o (pc P "Prelude.isSome" [pc P "Reader.indexOf"
        [pc P "Typing.recognizerName" [v 0], sh 1 names]])))))

/-- That a name's atom occurs in the program's forms: the predicate of the name. -/
def usedPred (P : Prog) (fs : Term) : Term :=
  Term.lam treeTy (truth P.o (occInT P (atomOfNameT (v 0)) (sh 1 fs)))

/-- That a name is not one of the implementation's. -/
def userNameT (P : Prog) (x : Term) : Term := notTest P.o (pc P "implName" [x])

/-- That a name is none of the implementation's: the predicate of the name. -/
def userPred (P : Prog) : Term := Term.lam treeTy (userNameT P (v 0))

/-- The coherence of the expansion's aliases with the typing environment's abbreviations, at
the markers: at each name, the declarations have an alias exactly where the environment has an
abbreviation, and where the alias is a marker's datatype's atom the abbreviation is that
datatype. -/
def aliasT (P : Prog) (dv Ev ms : Term) : Term :=
  let o := P.o
  let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let fa := pc P "Datatype.findAlias" [v 0, sh 1 dv]
  let la := pc P "Typing.lookupName" [v 0, pc P "Typing.envAl" [sh 1 Ev]]
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.conj o
    (Internal.Logic.imp o (notTest o (isSome fa)) (notTest o (isSome la)))
    (Internal.Logic.imp o (truth o (isSome fa)) (Internal.Logic.conj o (truth o (isSome la))
      (Internal.Logic.imp o (truth o (isSome (pc P "Reader.indexOf"
          [get fa, pc P "Typing.markerNames" [sh 1 ms]])))
        (Term.eq (get la) (pc P "Typing.tyData" [atomNameT (get fa)])))))))

/-- That the declarations have no alias named as the trees' type or as the unit type, which the
typing reads before the abbreviations. -/
def aliasKwT (P : Prog) (dv : Term) : Term :=
  let no (kw : String) : Term :=
    notTest P.o (pc P "Prelude.isSome" [pc P "Datatype.findAlias" [pc P kw [], dv]])
  Internal.Logic.conj P.o (no "Reader.kwT") (no "Reader.kwUnit")

/-- That each marker's datatype is named by an atom, naming neither the trees' type nor the unit
type. -/
def markerNamesT (P : Prog) (ms : Term) : Term :=
  let o := P.o
  let no (kw : String) : Term := notTest o (pc P "Reader.named" [v 0, pc P kw []])
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
    (truth o (pc P "Prelude.isSome"
      [pc P "Reader.indexOf" [v 0, pc P "Typing.markerNames" [sh 1 ms]]]))
    (Internal.Logic.conj o (truth o (pc P "Reader.isAtom" [v 0]))
      (Internal.Logic.conj o (no "Reader.kwT") (no "Reader.kwUnit")))))

/-- That the typing environment has no sort: no name is one of its sorts'. -/
def noSortsT (P : Prog) (Ev : Term) : Term :=
  Internal.Logic.all P.o treeTy (Term.lam treeTy
    (notTest P.o (pc P "Typing.hasName" [v 0, pc P "Typing.envSorts" [sh 1 Ev]])))

/-- That each alias of the declarations is a type abbreviation of the reader's: a name with an
alias is abbreviated. -/
def aliasTysT (P : Prog) (dv tys : Term) : Term :=
  let o := P.o
  let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
  Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
    (truth o (isSome (pc P "Datatype.findAlias" [v 0, sh 1 dv])))
    (truth o (isSome (pc P "Reader.lookupAbbrev" [v 0, sh 1 tys])))))

/-- That a kernel form, where it is a marker, is the marker its datatype's atom finds among the
markers: the typing's reading of that datatype's constructors is the marker's own. The
predicate of the form. -/
def markerPred (P : Prog) (ms : Term) : Term :=
  let eqT := (primT Kernel.Prim.eq).getD Term.star
  let labelT := (primT Kernel.Prim.label).getD Term.star
  let childT := (primT Kernel.Prim.child).getD Term.star
  Term.lam treeTy (Internal.Logic.imp P.o
    (truth P.o (apps eqT [apps labelT [v 0], leafT (numeral 9)]))
    (Term.eq (pc P "Typing.markerCtors" [sh 1 ms, apps childT [v 0, leafT bnilT]])
      (Term.pair (leafT (numeral 1)) (call D.tail [treeTy] [call D.children [] [v 0]]))))

/-- That the digits of a tree's label read as the leaf of that label, at every tree. -/
def decRoundT (P : Prog) : Term :=
  Internal.Logic.all P.o treeTy (Term.lam treeTy (Term.eq
    (pc P "Reader.numeral" [pc P "Typing.decimalChars" [v 0]])
    (pc P "Prelude.some" [leafT (call D.lab [] [v 0])])))

/-- That the digits of every tree's label are fixed by the expansion of any numeral
abbreviations: no digit is an atom. -/
def digitsFixedT (P : Prog) : Term :=
  let Ls := list treeTy
  Internal.Logic.all P.o Ls (Term.lam Ls (Internal.Logic.all P.o treeTy (Term.lam treeTy
    (truth P.o (pc P "charsFixed" [Term.lam treeTy (pc P "Reader.expandNums" [v 2, v 0]),
      pc P "Typing.decimalChars" [v 0]])))))

/-- What the soundness assumes of a program's markers, and of the numerals: each marker's
datatype is named by an atom naming no type the typing reads before the abbreviations
({name}`markerNamesT`), each marker's constructors have at most one of each label, the digits
of a tree's label read as its leaf ({name}`decRoundT`), and they are fixed by the expansion of
numeral abbreviations ({name}`digitsFixedT`). -/
def staticT (P : Prog) (ms : Term) : Term :=
  Internal.Logic.conj P.o (markerNamesT P ms)
    (Internal.Logic.conj P.o (uniqsT P ms)
      (Internal.Logic.conj P.o (decRoundT P) (digitsFixedT P)))

/-- The states of the compiler's passes over a program's forms, and the forms that remain: the
expansion's declarations, the typing's environment and rejection, the reader's type and numeral
abbreviations, names and terms, and the markers and the kernel forms of the whole program, which
the recognizers' insertion reads. The partition of forms into markers and others is given as a
term of the forms, the variable of index 0. -/
structure Passes where
  /-- The forms that remain. -/
  es : Term
  /-- The expansion's declarations. -/
  dv : Term
  /-- The typing's environment. -/
  env : Term
  /-- The typing's rejection. -/
  rej : Term
  /-- The reader's type abbreviations. -/
  tys : Term
  /-- The reader's numeral abbreviations. -/
  nums : Term
  /-- The reader's names. -/
  names : Term
  /-- The reader's terms. -/
  terms : Term
  /-- The program's markers, as the recognizers' insertion reads them. -/
  ms : Term
  /-- The program's kernel forms. -/
  fs : Term
  /-- The typed forms written and not yet read, in order, before those of the forms that
  remain, where there are any. -/
  ws : Option Term := none
  /-- The environment whose datatypes' recognizers the invariant speaks of, where it is not the
  typing's: within a datatype's declaration, the environment before it. -/
  recEnv : Option Term := none

namespace Passes

variable (P : Prog) (S : Defs) (T : Defs3) (X₀ : Term) (s : Passes)

/-- The typed forms the passes after the expansion have yet to read: those written and not yet
read, where there are any, before those the expansion writes for the forms that remain. -/
def typed : Term := match s.ws with
  | none => typedForms P s.es s.dv
  | some w => txsApp P w (typedForms P s.es s.dv)

/-- The typed forms that are no markers, which the typing checks after the markers. -/
def others : Term := Term.snd (Term.subst X₀ fun _ ↦ s.typed P)

/-- The typing's run over the forms that remain. -/
def checked : Term := pc P "Typing.checkAll" [Term.pair s.env s.rej, s.others P X₀]

/-- The optional forms the recognizers' insertion gives for the forms that remain. -/
def inserted : Term :=
  optFold P (recMap P s.ms s.fs (pc P "Datatype.kernelForms" [s.typed P]))

/-- The reader's run over the forms the recognizers' insertion gives. -/
def read : Term :=
  readRun P (flatT P (Term.snd (s.inserted P))) (progState s.tys s.nums s.names s.terms)

/-- The terms the reader ends with. -/
def finalTerms : Term := termsOf (s.read P)

/-- The names the reader ends with. -/
def finalNames : Term := Term.fst (Term.snd (Term.snd (Term.snd (s.read P))))

/-- The relation's context: the terms the reader ends with and the typing environment's
markers. -/
def rel : Term := Term.pair (s.finalTerms P) (pc P "Typing.envMs" [s.env])

/-- The hypotheses at the states: the passes over the forms that remain end without a failure,
the kernel types the terms the reader ends with, and the states' invariant: no rejection, the
definitions related to the typing environment's, the numeral abbreviations coherent with the
environment's, the names those of definitions, no numeral abbreviation a keyword, as many names
as terms, and the recognizers of the environment's datatypes among the definitions decide
membership; each definition's body the expansion writes for the forms that remain is a source
form at the numeral abbreviations before it; and, of the program's kernel forms, each atom of a
kernel form that remains occurs in them, each recognizer they refer to of a datatype of the
environment is among the names, and each name's atom occurs in them. The datatypes whose
recognizers are spoken of are those of the recognizers' environment, where one is given. No name
is one of the implementation's; the environment has no sort; the expansion's aliases are
coherent with the environment's abbreviations and are type abbreviations of the reader's; the
markers are the environment's; each marker among the kernel forms that remain is the one its
datatype's atom finds; and the markers and the numerals are as the soundness assumes
({name}`staticT`). -/
def hyps : List Term :=
  let o := P.o
  let Er := s.recEnv.getD s.env
  let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
  let len (t : Term) : Term := pc P "Prelude.length" [t]
  [truth o (Term.fst (xpRun P s.es (xpState s.dv (nilT treeTy)))),
    notTest o (isSome (Term.snd (s.checked P X₀))),
    truth o (Term.fst (s.inserted P)),
    truth o (Term.fst (s.read P)),
    truth o (isSome (pc P "Check.checkProgram" [s.finalTerms P])),
    notTest o (isSome s.rej),
    T.globT (s.rel P) s.env s.names,
    T.numsT s.env s.nums,
    T.namesT s.names,
    T.kwsT s.nums,
    Term.eq (len s.names) (len s.terms),
    T.recsT (s.rel P) Er s.names,
    truth o (Term.fst (plainRun P s.es (plainState s.dv s.nums))),
    S.allL (occPred P s.fs) (pc P "Datatype.kernelForms" [s.typed P]),
    insT P Er s.names s.fs,
    S.allL (usedPred P s.fs) s.names,
    S.allL (userPred P) s.names,
    noSortsT P s.env,
    aliasT P s.dv s.env s.ms,
    aliasKwT P s.dv,
    aliasTysT P s.dv s.tys,
    Term.eq s.ms (pc P "Typing.envMs" [s.env]),
    S.allL (markerPred P s.ms) (pc P "Datatype.kernelForms" [s.typed P]),
    staticT P s.ms]

/-- The conclusion at the states: the typing environment the typing ends with has the markers
of the environment, the definitions the reader ends with are related to it by the names the
reader ends with, and its recognizers decide membership. -/
def concl : Term :=
  let Efin := Term.fst (s.checked P X₀)
  let ms (e : Term) : Term := pc P "Typing.envMs" [e]
  Internal.Logic.conj P.o (Term.eq (ms Efin) (ms s.env))
    (Internal.Logic.conj P.o (T.globT (s.rel P) Efin (s.finalNames P))
      (T.recsT (s.rel P) Efin (s.finalNames P)))

end Passes

/-- The types of the variables of the passes' states, the forms that remain last: the kernel
forms, the markers, the terms, the names, the numeral and type abbreviations, the rejection, the
environment and the declarations, the innermost first. -/
def passesCtx (T : Defs3) : List Tree :=
  let Ls := list treeTy
  [Ls, Ls, Ls, Ls, Ls, Ls, treeTy, T.envTy, Ls]

/-- The passes' states of the variables of {name}`passesCtx`, shifted by a number of variables
within them, at forms that remain. -/
def passesAt (k : ℕ) (es : Term) : Passes :=
  ⟨es, v (k + 8), v (k + 7), v (k + 6), v (k + 5), v (k + 4), v (k + 3), v (k + 2), v (k + 1), v k,
    none, none⟩

/-- The soundness at the forms that remain, the variable of index 0, at all states: the
quantification over the states' variables of the implication of the conclusion by the hypotheses
and the further hypotheses {lit}`more` of the forms. -/
def passesφ (P : Prog) (S : Defs) (T : Defs3) (X₀ : Term) (more : Term → List Term) :
    Term :=
  let s := passesAt 0 (v 9)
  (passesCtx T).foldl (fun b A ↦ Internal.Logic.all P.o A (Term.lam A b))
    ((s.hyps P S T X₀ ++ more (v 9)).foldr (Internal.Logic.imp P.o) (s.concl P T X₀))

/-- The environment's relation to the empty named context holds of the empty environment: no
position of the context has an entry. In the context of the relation's context. -/
def envNil (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("envNil", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["ltZero"]⟩
    let a : Internal.Thm := ⟨0, [Defs3.ctxTy], [],
      T.envT (v 0) (nilT treeTy) (nilT treeTy)⟩
    let some d := (linkK K "envNil: folded" <|
        dRwBy (evalRw K.G K.E [.delta (T.q + 1)] .head) <| linkK K "envNil: unfolded" <|
        dAllI K.L <|
        dImpI K.L (linkK K "envNil: an entry" (lastFalse K))) a.ctx a.hyps a.concl
      | dbgTrace "envNil: not proved" fun _ ↦ none
    pure (a, d))

/-- The empty named context's names are admitted: none has a type. In the context of the typing
environment. -/
def cxNil (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("cxNil", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let a : Internal.Thm := ⟨0, [T.envTy], [], T.cxT (v 0) (nilT treeTy)⟩
    let some d := (dRwBy (evalRw K.G K.E [.delta (T.q + 7 + 2 * nFolds)] .head) <|
        dAllI K.L <| dImpI K.L (linkK K "cxNil: a type" (lastFalse K)))
        a.ctx a.hyps a.concl
      | dbgTrace "cxNil: not proved" fun _ ↦ none
    pure (a, d))

/-- Whether a head is named by a keyword, as the expansion tests it. -/
def headNamed (P : Prog) (h : Term) (kw : String) : Term :=
  pc P "Datatype.namedTx" [h, pc P kw []]

/-- The hypotheses of a head that names a definition: no template's instance, no declaration of
a datatype, the definitions' keyword. -/
def defHead (P : Prog) (h : Term) : List Term :=
  ["Datatype.kwGeneric", "Datatype.kwData", "Datatype.kwTreeData"].map
    (fun kw ↦ notTest P.o (headNamed P h kw)) ++ [truth P.o (headNamed P h "Reader.kwDef")]

/-- The hypotheses of a head that names a type abbreviation: no template's instance, no
declaration of a datatype, no definition, the type abbreviations' keyword. -/
def deftypeHead (P : Prog) (h : Term) : List Term :=
  ["Datatype.kwGeneric", "Datatype.kwData", "Datatype.kwTreeData", "Reader.kwDef"].map
    (fun kw ↦ notTest P.o (headNamed P h kw)) ++ [truth P.o (headNamed P h "Reader.kwDeftype")]

/-- That a form is the list of a number of parts of which facts hold: the conjunction of the
form's equation and the facts, under the parts, the first, the head, the variable of the
greatest index. A list of a head, a name and a body where no number is given. -/
def kindT (P : Prog) (e : Term) (facts : List Term) (n : ℕ := 3) : Term :=
  let o := P.o
  let ex (b : Term) : Term := Internal.Logic.ex o treeTy (Term.lam treeTy b)
  let parts := [Term.eq (sh n e) (listNode ((List.range n).reverse.map v))] ++ facts
  Nat.rec (motive := fun _ ↦ Term)
    (parts.dropLast.foldr (Internal.Logic.conj o) (parts.getLastD Term.star)) (fun _ t ↦ ex t) n

/-- The hypotheses of a head that names a numeral abbreviation: no template's instance, no
declaration of a datatype, no definition, no type abbreviation, the numeral abbreviations'
keyword. -/
def defnumHead (P : Prog) (h : Term) : List Term :=
  ["Datatype.kwGeneric", "Datatype.kwData", "Datatype.kwTreeData", "Reader.kwDef",
    "Reader.kwDeftype"].map (fun kw ↦ notTest P.o (headNamed P h kw)) ++
    [truth P.o (headNamed P h "Reader.kwDefnum")]

/-- The hypotheses of a head that names a function: no template's instance, no declaration of a
datatype, the functions' keyword. -/
def defnHead (P : Prog) (h : Term) : List Term :=
  ["Datatype.kwGeneric", "Datatype.kwData", "Datatype.kwTreeData"].map
    (fun kw ↦ notTest P.o (headNamed P h kw)) ++ [truth P.o (headNamed P h "Datatype.kwDefn")]

/-- The binders the expansion reads of a function's list of binders. -/
def bindersT (P : Prog) (bs : Term) : Term := pc P "Datatype.bindersTx" [bs]

/-- Whether a form is a template's instance, as the expansion's run tests it: a list whose
head the instances' keyword names. -/
def genericTest (P : Prog) (e : Term) : List Term :=
  [pc P "Datatype.isListTx" [e], pc P "Datatype.namedTx"
    [pc P "Datatype.nthTx" [pc P "Datatype.elems" [e], leafT bnilT],
      pc P "Datatype.kwGeneric" []]]

/-- That a form is a template's instance ({name}`genericTest`). -/
def genericT (P : Prog) (e : Term) : Term :=
  Internal.Logic.conj P.o (truth P.o ((genericTest P e).headD Term.star))
    (truth P.o ((genericTest P e).getLastD Term.star))

/-- The test that a constructor's fields end with a variable field: more than one, the last but
one the variable fields' keyword. -/
def varFlagT (P : Prog) (fs : Term) : Term :=
  let ltT := (primT Kernel.Prim.lt).getD Term.star
  let subT := (primT Kernel.Prim.sub).getD Term.star
  let nr := pc P "Datatype/Txs.length" [fs]
  pc P "Prelude.and" [apps ltT [leafT (numeral 1), nr], pc P "Datatype.namedTx"
    [pc P "Datatype.nthTx" [fs, apps subT [nr, leafT (numeral 2)]], pc P "Datatype.kwAmp" []]]

/-- What the soundness assumes of a datatype's declaration, of the datatype's atom and its
constructors: each constructor is named by none of the implementation's names, as the
datatype's recognizer is. -/
def dataFacts (P : Prog) (S : Defs) (dA cs : Term) : List Term :=
  let elems := pc P "Datatype.elems" [v 0]
  [S.allL (Term.lam treeTy (userNameT P (pc P "Reader.nameOf"
      [pc P "Datatype.nthTx" [elems, leafT bnilT]]))) cs,
    userNameT P (pc P "Reader.nameOf" [pc P "Datatype.memberName" [dA]])]

/-- The hypotheses of a datatype's declaration's form, of its head, the datatype's atom and its
constructors: no template's instance, the datatypes' keyword, and what the soundness assumes
of the declaration ({name}`dataFacts`). -/
def dataHead (P : Prog) (S : Defs) (h dA cs : Term) : List Term :=
  [notTest P.o (headNamed P h "Datatype.kwGeneric"), truth P.o (headNamed P h "Datatype.kwData")] ++
    dataFacts P S dA cs

/-- That a form is a datatype's declaration: the list of a head, the datatype's atom and its
constructors, of which the declaration's hypotheses hold ({name}`dataHead`), under the
constructors, the atom and the head, the variable of the greatest index. -/
def dataKindT (P : Prog) (S : Defs) (e : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  let parts := [Term.eq (sh 3 e) (nodeT (Term.pair (numeral 2)
      (consT treeTy (v 2) (consT treeTy (v 1) (v 0)))))] ++ dataHead P S (v 2) (v 1) (v 0)
  Internal.Logic.ex o treeTy (Term.lam treeTy (Internal.Logic.ex o treeTy (Term.lam treeTy
    (Internal.Logic.ex o Ls (Term.lam Ls
      (parts.dropLast.foldr (Internal.Logic.conj o) (parts.getLastD Term.star)))))))

/-- That a form is of a kind the soundness of a whole program reads: a definition, a type
abbreviation, a numeral abbreviation, a function, the list of a head, a name, binders, a result
type and a body, a template's instance, or a datatype's declaration ({name}`dataKindT`); the
name of a definition, of a numeral abbreviation and of a function is not one of the
implementation's. -/
def formOk (P : Prog) (S : Defs) (e : Term) : Term :=
  let user (n : Term) : List Term := [userNameT P (pc P "Reader.nameOf" [n])]
  Internal.Logic.disj P.o (kindT P e (defHead P (v 2) ++ user (v 1)))
    (Internal.Logic.disj P.o (kindT P e (deftypeHead P (v 2)))
      (Internal.Logic.disj P.o (kindT P e (defnumHead P (v 2) ++ user (v 1)))
        (Internal.Logic.disj P.o (kindT P e (defnHead P (v 4) ++ user (v 3)) 5)
          (Internal.Logic.disj P.o (genericT P e) (dataKindT P S e)))))

/-- The head of a form, as the expansion reads it: the first of its elements. -/
def formHead (P : Prog) (e : Term) : Term :=
  pc P "Datatype.nthTx" [pc P "Datatype.elems" [e], leafT bnilT]

/-- What the soundness of a whole program assumes of a form: where the datatypes' keyword names
its head, what it assumes of a datatype's declaration ({name}`dataFacts`) of its second
element and of the elements after; the tree datatypes' keyword does not name its head; and
where the keyword of the numeral abbreviations, of the definitions or of the functions names
it, the name of its second element is not one of the implementation's. -/
def preOk (P : Prog) (S : Defs) (e : Term) : List Term :=
  let named (kw : String) : Term := headNamed P (formHead P e) kw
  let elems := pc P "Datatype.elems" [e]
  let second := pc P "Datatype.nthTx" [elems, leafT (numeral 1)]
  let user (kw : String) : Term := Internal.Logic.imp P.o (truth P.o (named kw))
    (userNameT P (pc P "Reader.nameOf" [second]))
  let facts := dataFacts P S second (pc P "Datatype/Txs.drop" [leafT (numeral 2), elems])
  [Internal.Logic.imp P.o (truth P.o (named "Datatype.kwData"))
      (facts.dropLast.foldr (Internal.Logic.conj P.o) (facts.getLastD Term.star)),
    notTest P.o (named "Datatype.kwTreeData"),
    user "Reader.kwDefnum", user "Reader.kwDef", user "Datatype.kwDefn"]

/-- The hypothesis on the forms of a program: what the soundness assumes of each
({name}`preOk`). -/
def formsOk (P : Prog) (S : Defs) (es : Term) : List Term :=
  let parts := preOk P S (v 0)
  [S.allL (Term.lam treeTy
    (parts.dropLast.foldr (Internal.Logic.conj P.o) (parts.getLastD Term.star))) es]

/-- The program with the passes' steps kept folded, and with them the erasure of a form and the
recognizers' insertion at a form, whose values at a definition's form are equations
({lit}`eraseDefForm`, {lit}`recAtThree`). -/
def passProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Typing.checkStep", "Datatype.xpStep", "Datatype.genericStep",
      "Reader.progStep", "Datatype.eraseForm", "Recognize.recognizersAt",
      "Recognize.occurs"] }

/-- An equation of a function kept folded at arguments, in the normal forms of the passes'
rules: the function's value there, by its unfolding. -/
def foldedEq (P : Prog) (S : Defs) (name fn : String) (Γ : List Tree) (lhs rhs : Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let nf (t : Term) : Option Term := nfE K.G K.E (K.rules []) Γ t
    let some l := nf lhs | dbgTrace s!"{name}: left" fun _ ↦ none
    let some r := nf rhs | dbgTrace s!"{name}: right" fun _ ↦ none
    let some d := byMode .full K.G K.E 0 (K.rules [] ++ [.delta (P.idx fn)]) Γ [] l r
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The erasure of a definition's form is the definition of the name as the body's erasure. In
the context of the body and the name. -/
def eraseDefForm (P : Prog) (S : Defs) : Step :=
  foldedEq P S "eraseDefForm" "Datatype.eraseForm" [treeTy, treeTy]
    (pc P "Datatype.eraseForm" [defForm P (v 1) (v 0)])
    (defForm P (v 1) (pc P "Datatype.eraseExpr" [v 0]))

/-- The recognizers' insertion at a list of three forms, which is no marker, gives the list.
In the context of the list's forms, the program's forms and its markers. -/
def recAtThree (P : Prog) (S : Defs) : Step :=
  let Ls := list treeTy
  let f := listNode [v 2, v 1, v 0]
  foldedEq P S "recAtThree" "Recognize.recognizersAt" [treeTy, treeTy, treeTy, Ls, Ls]
    (pc P "Recognize.recognizersAt" [v 4, v 3, f])
    (pc P "Prelude.some" [nodeT (Term.pair (numeral 0) (consT treeTy f (nilT treeTy)))])

/-- The erasure of a list of a head, a name and a body whose head does not name a definition is
the list: the head's test decided. In the context of the body, the name and the head. -/
def eraseOther (P : Prog) (S : Defs) : Step :=
  ("eraseOther", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let f := listNode [v 2, v 1, v 0]
    let test := headNamed P (v 2) "Reader.kwDef"
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, treeTy], [notTest P.o test],
      Term.eq (pc P "Datatype.eraseForm" [f]) f⟩
    let some d := decideIn K (fun Γ ↦ sh (Γ.length - 3) test)
        (byNormWith K [.delta (P.idx "Datatype.eraseForm")]) (refuteNot K 0)
        a.ctx a.hyps a.concl
      | dbgTrace "eraseOther: not proved" fun _ ↦ none
    pure (a, d))

/-- A deducer's failure reported with a message and the numbers of variables and hypotheses. -/
def stage (msg : String) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  (k Γ Φ ψ).orElse fun _ ↦
    dbgTrace s!"{msg}: {Γ.length} variables, {Φ.length} hypotheses" fun _ ↦ none

/-- Implications eliminated in turn from the hypothesis of index {lit}`h`: each antecedent by
its deducer, each consequent the last hypothesis, from which the next is eliminated. -/
def impEs (L : Conn) (h : ℕ) (prems : List Deducer) (k : Deducer) : Deducer :=
  match prems with
  | [] => k
  | p :: ps => dImpE L h p (ps.foldr (fun q k Γ Φ ψ ↦ dImpE L (Φ.length - 1) q k Γ Φ ψ) k)

/-- The last hypothesis, where it is the goal, else normalized as the goal is. -/
def lastOr (K : Kit) : Deducer := fun Γ Φ ψ ↦
  (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ

/-- A hypothesis, where it is the goal, else normalized as the goal is. -/
def hypOrK (K : Kit) (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ

/-- The soundness at expanded forms at a form's expansion under declarations, where it is
present by {lit}`present`: the soundness at every source form ({lit}`soundClosed`) gives that at
its expansion ({lit}`expSound`). The hypothesis's index is given to {lit}`k`. -/
def expandedOf (K : Kit) (form dv : List Tree → Term) (present : Deducer) (k : ℕ → Deducer) :
    Deducer :=
  K.cutThm "soundClosed" (fun Γ ↦ [form Γ]) <|
  applyThm K "expSound" (fun Γ ↦ [form Γ]) [lastOr K] <| K.allEΓ dv <| K.impE present <|
  fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ

/-- That a definition's body is sound at the states: where the typing gives it a type in the
empty context, the reader resolves its erasure, its numeral abbreviations expanded, in the empty
scope, and the kernel types the resolved term at the types of the terms the reader has, the term
converges, in the empty environment, to a value related at the type. -/
def soundAtT (P : Prog) (S : Defs) (T : Defs3) (s : Passes) (b : Term) : Term :=
  let o := P.o
  let nil := nilT treeTy
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let syn := pc P "Typing.synIn" [s.env, nil, b]
  let res := pc P "Reader.resolve" [s.tys, s.names,
    pc P "Reader.expandNums" [s.nums, pc P "Datatype.eraseExpr" [b]], nil]
  let kernel := pc P "Check.typeIn" [Term.snd (kcRun P s.terms kcInit), nil, get res]
  [isSomeT syn, isSomeT res, isSomeT kernel].foldr (Internal.Logic.imp o)
    (S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (s.rel P))) (v 0) (sh 1 nil) (sh 1 (get res))))
      (T.relT (s.rel P) (get syn)))

/-- The soundness at the states ({name}`soundAtT`) of a body that is a source form at the
numeral abbreviations and sound at expanded forms: that soundness at the states, whose
hypotheses are those at the states and the relations of the empty named context and
environment ({lit}`envNil`, {lit}`cxNil`). The hypotheses at the states are those from the index
{lit}`hInv`, the
body's being a source form that of index {lit}`iSrc`, and {lit}`expanded` gives the body's
soundness at expanded forms as a hypothesis, by its index. -/
def soundExpanded (K : Kit) (P : Prog) (s : List Tree → Passes) (hInv iSrc : ℕ)
    (expanded : (ℕ → Deducer) → Deducer) : Deducer :=
  let L := K.L
  let nil := nilT treeTy
  let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
  let hypOr := hypOrK K
  let at' (m : String) (k : Deducer) : Deducer := stage s!"soundExpanded: {m}" k
  dImpI L <| dImpI L <| dImpI L <| fun Γ₀ Φ₀ ψ₀ ↦
    let (iSyn, iRes, iTyped) := (Φ₀.length - 3, Φ₀.length - 2, Φ₀.length - 1)
    (expanded fun iExp Γ₁ Φ₁ ψ₁ ↦
      dAllE L K.G K.E iExp (Term.snd (kcRun P (s Γ₁).terms kcInit)) (
        K.allEΓ (fun _ ↦ nil) <| K.allEΓ (fun Γ ↦ (s Γ).dv) <| K.allEΓ (fun Γ ↦ (s Γ).env) <|
        K.allEΓ (fun _ ↦ nil) <| K.allEΓ (fun Γ ↦ (s Γ).tys) <| K.allEΓ (fun Γ ↦ (s Γ).nums) <|
        K.allEΓ (fun Γ ↦ (s Γ).names) <| K.allEΓ (fun _ ↦ nil) <|
        K.allEΓ (fun Γ ↦ (s Γ).rel P) <| last fun iS ↦ impEs L iS
          [at' "the definitions related" (hypOr (hInv + 6)),
            at' "the empty environment"
              (K.cutThm "envNil" (fun Γ ↦ [(s Γ).rel P]) (last K.byHyp)),
            at' "the numerals" (hypOr (hInv + 7)),
            at' "the names" (hypOr (hInv + 8)),
            at' "a source form" (K.byHyp iSrc),
            at' "expanded" (K.solve 3),
            at' "typed" (K.byHyp iSyn),
            at' "resolved" (K.byHyp iRes),
            at' "kernel typed" (K.byHyp iTyped),
            at' "the keywords" (hypOr (hInv + 9)),
            at' "the markers" K.byNorm,
            at' "the recognizers" (hypOr (hInv + 11)),
            at' "the empty context"
              (K.cutThm "cxNil" (fun Γ ↦ [(s Γ).env]) (last K.byHyp))] <|
        at' "the value" (last K.byHyp)) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀

/-- A number of deducer transformers applied in turn. -/
def repeatK (n : ℕ) (f : Deducer → Deducer) (k : Deducer) : Deducer :=
  Nat.rec (motive := fun _ ↦ Deducer) k (fun _ r ↦ f r) n

/-- The parts of a conjunction nested to the right ({name}`conjAll`), proved in order. -/
def conjIs (L : Conn) (ds : List Deducer) : Deducer := match ds.reverse with
  | [] => fun _ _ _ ↦ none
  | d :: rest => rest.foldl (fun acc p ↦ dConjI L p acc) d

/-- The last hypothesis, a conjunction of a number of formulas nested to the right
({name}`conjAll`), split: the continuation is given the index of each formula, by its
position. -/
def conjEs (K : Kit) (n : ℕ) (k : (ℕ → ℕ) → Deducer) : Deducer := fun Γ Φ ψ ↦
  let base := Φ.length - 1
  repeatK (n - 1) K.conjE
    (k fun i ↦ if i + 1 < n then base + 1 + 2 * i else base + 2 * (n - 1)) Γ Φ ψ

/-- A goal by a hypothesis, a defined predicate of an index unfolded at the head of both. -/
def unfoldBothK (K : Kit) (idx h : ℕ) : Deducer :=
  dRwBy (evalRw K.G K.E [.delta idx] .head) <|
    dRwHyp (evalRw K.G K.E [.delta idx] .head) h fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ

/-- The states after a definition written of a name's atom as a body is read, given the pending
forms after it: the typing environment declares the name at the body's type, without a
rejection, and the reader has the name after the names and the resolved body after the terms. -/
def Passes.written (P : Prog) (s : Passes) (n b ws : Term) : Passes :=
  let nil := nilT treeTy
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let nm := pc P "Reader.nameOf" [n]
  let syn := pc P "Typing.synIn" [s.env, nil, b]
  let res := pc P "Reader.resolve" [s.tys, s.names,
    pc P "Reader.expandNums" [s.nums, pc P "Datatype.eraseExpr" [b]], nil]
  { s with
    env := pc P "Typing.withDefs" [s.env,
      declareT P (pc P "Typing.envDefs" [s.env]) nm (get syn)]
    rej := pc P "Typing/OName.nothing" []
    names := pc P "Prelude.append" [s.names, pc P "Prelude.single" [nm]]
    terms := pc P "Prelude.append" [s.terms, pc P "Prelude.single" [get res]]
    ws := some ws }

/-- The hypotheses at the states are preserved by a definition written: a definition of a
name as a body sound at the states ({name}`soundAtT`), before pending forms, leaves states
({name}`Passes.written`) of which the hypotheses hold again, and whose conclusion gives that at
the states before. The typing's step
({lit}`checkDef`) declares the name at the body's type; the reader's ({lit}`readDef`) has the
name after the names and the resolved term after the terms. The terms the reader ends with have
the term at the index of the names' length ({lit}`readExt`, {lit}`nthLen`), with a kernel type
({lit}`kcTyped`), so that the term converges to a value related at its type, by the body's
soundness, and the invariant holds of the states the steps leave ({lit}`globExtend`,
{lit}`namesExtend`); the name, whose atom occurs in the program's forms
({lit}`occursDefName`), is no recognizer's of a datatype of the recognizers' environment, the
recognizers the forms refer to being among the names, so that the recognizers decide membership
as before ({lit}`recsExtend`, {lit}`insExtend`). In the context of the body, the name, the
pending forms after, the forms that remain, the states and the recognizers' environment. -/
def writtenInv (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("writtenInv", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"] ++ lookupEqNames⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"writtenInv @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "writtenInv: no partition" fun _ ↦ none
    let s : Passes := { passesAt 4 (v 3) with
      ws := some (consT treeTy (defForm P (v 1) (v 0)) (v 2)), recEnv := some (v 13) }
    let hyps := s.hyps P S T X₀ ++
      [soundAtT P S T s (v 0), userNameT P (pc P "Reader.nameOf" [v 1])]
    let Γ₀ := [treeTy, treeTy, Ls, Ls] ++ passesCtx T ++ [T.envTy]
    let s' := s.written P (v 1) (v 0) (v 2)
    let a : Internal.Thm := ⟨0, Γ₀, hyps, conjAll P.o (s'.hyps P S T X₀ ++
      [Internal.Logic.imp P.o (s'.concl P T X₀) (s.concl P T X₀)])⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (bA, nA, wsA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3)
    let (fsA, termsA, namesA, numsA, tysA) := (at_ 4, at_ 6, at_ 7, at_ 8, at_ 9)
    let (rA, EA, ErA) := (at_ 10, at_ 11, at_ 13)
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let fA (Γ : List Tree) : Term := defForm P (nA Γ) (bA Γ)
    -- the states before the form, and the parts of the states after it
    let sA (Γ : List Tree) : Passes := { passesAt (4 + (Γ.length - Γ₀.length)) (esA Γ) with
      ws := some (consT treeTy (fA Γ) (wsA Γ)), recEnv := some (ErA Γ) }
    let synA (Γ : List Tree) : Term := pc P "Typing.synIn" [EA Γ, nil, bA Γ]
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [nA Γ]
    let erA (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [bA Γ]
    let resA (Γ : List Tree) : Term := pc P "Reader.resolve" [tysA Γ, namesA Γ,
      pc P "Reader.expandNums" [numsA Γ, erA Γ], nil]
    let tA (Γ : List Tree) : Term := get (resA Γ)
    let names'A (Γ : List Tree) : Term :=
      pc P "Prelude.append" [namesA Γ, pc P "Prelude.single" [nmA Γ]]
    let terms'A (Γ : List Tree) : Term :=
      pc P "Prelude.append" [termsA Γ, pc P "Prelude.single" [tA Γ]]
    let restA (Γ : List Tree) : Passes := { sA Γ with ws := some (wsA Γ) }
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let kA (Γ : List Tree) : Term := defForm P (nA Γ) (erA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    -- the hypotheses' indices
    let (hX, hC, hO, hR, hK, hNums, hKws, hLen, hRecs, hP, hOcc, hIns, hUsed) :=
      (0, 1, 2, 3, 4, 7, 9, 10, 11, 12, 13, 14, 15)
    let (hUser, hSorts, hAl, hAlKw, hAlTys, hMs, hMk, hStatic, hSound, hName) :=
      (16, 17, 18, 19, 20, 21, 22, 23, 24, 25)
    -- the last stage: the hypotheses at the states the steps leave
    let apply (iAtom iSyn iO iRes iUnres iNotIdx iTyped iNth : ℕ) : Deducer :=
      let sound : Deducer := at' "the soundness" <|
        impEs L hSound
          [stage "writtenInv: typed" (K.byHyp iSyn),
            stage "writtenInv: resolved" (K.byHyp iRes),
            stage "writtenInv: kernel typed" (K.byHyp iTyped)] <|
        at' "the definition sound" <| last fun iConv ↦
        applyThm K "globExtend"
          (fun Γ ↦ [get (synA Γ), tA Γ, nmA Γ, namesA Γ, EA Γ, (sA Γ).rel P])
          [stage "writtenInv: related before" dHyp,
            stage "writtenInv: no index" (hypOr iNotIdx),
            stage "writtenInv: the term's index" (normHyps K [hLen, iNth] K.byNorm),
            stage "writtenInv: the term's value" (K.byHyp iConv)] <|
        at' "the relation extended" <| last fun iGlob' ↦
        -- the name's atom is itself as an atom, and occurs in the program's forms, the
        -- definition's kernel form one of them
        applyThm K "atomNode" (fun Γ ↦ [nA Γ])
          [stage "writtenInv: the name an atom" (hypOr iAtom)] <|
        last fun iAtomEq ↦ at' "the occurrences" <| normHyps K [hMk] <| K.conjE <|
        last fun iMkRest ↦ normHyps K [iAtomEq, hOcc] <|
        K.conjE <| fun Γ₉ Φ₉ ψ₉ ↦
        let (iOccHead, iOccRest) := (Φ₉.length - 2, Φ₉.length - 1)
        (at' "the name's occurrence" <| fun Γ Φ ψ ↦ dAllE L K.G K.E iOccHead (nA Γ) (
          K.impE (applyThm K "occursDefName" (fun Γ ↦ [erA Γ, nA Γ])
            [stage "writtenInv: the name's atom" (hypOr iAtom)] (last K.byHyp)) <|
        last fun iOccN ↦
        -- the name is no recognizer's of a datatype of the environment: one the forms refer
        -- to is among the names, of which the name is none
        let notRec : Deducer := dAllI L <| dImpI L <| dImpI L <| fun Γ₈ Φ₈ ψ₈ ↦
          let (hHas, hEq, n₈) := (Φ₈.length - 2, Φ₈.length - 1, Γ₈.length)
          -- the recognizer's name rewritten to the definition's by the equation alone
          let named := evalRw K.G K.E [.hyp hEq] .full
          (fun Γ Φ ψ ↦ dAllE L K.G K.E hIns (v (Γ.length - n₈)) (
            K.impE (stage "writtenInv: a datatype" (hypOr hHas)) <|
            K.impE (stage "writtenInv: the recognizer referred to"
              (dRwBy named (K.byHyp iOccN))) <|
            last fun iIdx ↦ dRwHyp named iIdx <| last fun iIdx' ↦ dImpE L iNotIdx
              (stage "writtenInv: the recognizer indexed" (K.byHyp iIdx'))
              (dFalse L dHyp)) Γ Φ ψ) Γ₈ Φ₈ ψ₈
        -- the hypotheses at the states the steps leave
        (conjIs L
            [stage "writtenInv: the rest expands" (K.byHyp hX),
              stage "writtenInv: the rest checks" (K.byHyp hC),
              stage "writtenInv: the rest's recognizers" (hypOr iO),
              stage "writtenInv: the rest reads" (K.byHyp hR),
              stage "writtenInv: the kernel checks" (K.byHyp hK),
              stage "writtenInv: no rejection" (dImpI L (lastFalse K)),
              stage "writtenInv: related after" (K.byHyp iGlob'),
              stage "writtenInv: the numerals after" (
                dRwBy (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) <|
                dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) hNums <|
                last K.byHyp),
              stage "writtenInv: the names after" (applyThm K "namesExtend"
                (fun Γ ↦ [nmA Γ, namesA Γ]) [dHyp, hypOr iUnres] (last K.byHyp)),
              stage "writtenInv: the keywords after" (hypOr hKws),
              stage "writtenInv: the lengths" (
                K.cutThm "lenSnoc" (fun Γ ↦ [namesA Γ]) <| K.allEΓ nmA <|
                K.cutThm "lenSnoc" (fun Γ ↦ [termsA Γ]) <| K.allEΓ tA <| fun Γ Φ ψ ↦
                normHyps K [hLen, Φ.length - 3, Φ.length - 1] K.byNorm Γ Φ ψ),
              stage "writtenInv: the recognizers after" (applyThm K "recsExtend"
                (fun Γ ↦ [nmA Γ, namesA Γ, ErA Γ, ErA Γ, (sA Γ).rel P])
                [stage "writtenInv: the recognizers" (hypOr hRecs),
                  stage "writtenInv: the datatypes" K.byNorm,
                  stage "writtenInv: no recognizer's name" notRec] (last K.byHyp)),
              stage "writtenInv: the bodies after" (K.byHyp hP),
              stage "writtenInv: the occurrences after" (hypOr iOccRest),
              stage "writtenInv: the recognizers referred to" (applyThm K "insExtend"
                (fun Γ ↦ [nmA Γ, namesA Γ, ErA Γ, ErA Γ, fsA Γ])
                [stage "writtenInv: referred to before" (hypOr hIns),
                  stage "writtenInv: the datatypes" K.byNorm] (last K.byHyp)),
              stage "writtenInv: the names' occurrences" (
                K.cutThm "allSnoc" (fun Γ ↦ [namesA Γ]) <|
                K.allEΓ (fun Γ ↦ usedPred P (fsA Γ)) <| K.allEΓ nmA <|
                K.impE (stage "writtenInv: the names used" (hypOr hUsed)) <|
                K.impE (stage "writtenInv: the name used" (K.byHyp iOccN)) <|
                last K.byHyp),
              stage "writtenInv: the names' origin" (
                K.cutThm "allSnoc" (fun Γ ↦ [namesA Γ]) <|
                K.allEΓ (fun _ ↦ userPred P) <| K.allEΓ nmA <|
                K.impE (stage "writtenInv: the names before" (hypOr hUser)) <|
                K.impE (stage "writtenInv: the name's origin" (K.byHyp hName)) <|
                last K.byHyp),
              stage "writtenInv: no sort" (hypOr hSorts),
              stage "writtenInv: the aliases" (hypOr hAl),
              stage "writtenInv: the aliases of types read first" (hypOr hAlKw),
              stage "writtenInv: the aliases abbreviated" (hypOr hAlTys),
              stage "writtenInv: the markers" (normHyps K [hMs] K.byNorm),
              stage "writtenInv: the markers that remain" (hypOr iMkRest),
              stage "writtenInv: the markers and the numerals" (hypOr hStatic),
              stage "writtenInv: the conclusion" (dImpI L (last K.byHyp))])) Γ Φ ψ) Γ₉ Φ₉ ψ₉
      sound
    -- the terms the reader ends with: the terms, the term read, and further ones
    let finals (iAtom iSyn iO iRes iUnres iNotIdx : ℕ) : Deducer := at' "the final terms" <|
      K.cutThm "readExt" (fun Γ ↦ [rsA Γ]) <| K.allEΓ (fun Γ ↦ progState (tysA Γ) (numsA Γ)
        (names'A Γ) (terms'A Γ)) <| K.exE <| fun Γ₇ Φ₇ ψ₇ ↦
      let n₇ := Γ₇.length
      let extA (Γ : List Tree) : Term := v (Γ.length - n₇)
      let iExt := Φ₇.length - 1
      (at' "the further terms" <|
        K.cutThm "appendSnoc" (fun Γ ↦ [termsA Γ, tA Γ, extA Γ]) <| last fun iSnoc ↦
        normHyps K [iExt, iSnoc] <| at' "the terms rewritten" <|
        applyThm K "kcTyped" (fun Γ ↦ [extA Γ, tA Γ, termsA Γ])
          [stage "writtenInv: the kernel's check" (K.byHyp hK)] <| last fun iTyped ↦
        K.cutThm "nthLen" (fun Γ ↦ [termsA Γ]) <| K.allEΓ tA <| K.allEΓ extA <|
        last fun iNth ↦ apply iAtom iSyn iO iRes iUnres iNotIdx iTyped iNth) Γ₇ Φ₇ ψ₇
    -- the reader's step
    let reader (iSyn : ℕ) : Deducer := at' "the reader" <|
      applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
        [stage "writtenInv: the recognizers' insertion" (K.byHyp hO)] <| last fun iO ↦
      applyThm K "readPrefix" (fun Γ ↦ [rsA Γ, pc P "Reader.progStep" [stA Γ, kA Γ]])
        [stage "writtenInv: the reader's run" (K.byHyp hR)] <| at' "the reader's step" <|
      applyThm K "readDef" (fun Γ ↦ [erA Γ, nA Γ, termsA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "writtenInv: the reader's step" dHyp] <| at' "the reader's parts" <|
      K.conjE <| K.conjE <| K.conjE <| fun Γ₅ Φ₅ ψ₅ ↦
        let (iAtom, iFresh, iRes, iRead) :=
          (Φ₅.length - 6, Φ₅.length - 4, Φ₅.length - 2, Φ₅.length - 1)
        normHyps K [iRead] (
          decideIn K (fun Γ ↦ pc P "Reader.isAtom" [nA Γ]) (K.hypFalse iAtom) <|
          at' "the name fresh" <|
          applyThm K "freshParts" (fun Γ ↦ [nmA Γ, namesA Γ, numsA Γ, tysA Γ])
            [stage "writtenInv: fresh" (hypOr iFresh)] <| K.conjE <| K.conjE <| fun Γ Φ ψ ↦
          finals iAtom iSyn iO iRes (Φ.length - 4) (Φ.length - 2) Γ Φ ψ) Γ₅ Φ₅ ψ₅
    -- the typing's step
    let typing : Deducer := at' "the typing" <|
      applyThm K "checkPrefix" (fun Γ ↦ [(restA Γ).others P X₀,
          checkStepAt P (EA Γ) (rA Γ) (fA Γ)])
        [stage "writtenInv: the typing's run" (K.byHyp hC)] <| at' "the typing's step" <|
      applyThm K "checkDef" (fun Γ ↦ [bA Γ, nA Γ, rA Γ, EA Γ])
        [stage "writtenInv: no rejection before" dHyp,
          stage "writtenInv: the typing's step" dHyp] <|
      K.conjE <| fun Γ Φ ψ ↦
        let (iSyn, iCheck) := (Φ.length - 2, Φ.length - 1)
        normHyps K [iCheck] (reader iSyn) Γ Φ ψ
    let some d := typing a.ctx a.hyps a.concl
      | dbgTrace "writtenInv: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at the forms that remain after a form at which the expansion writes a
definition, a step of the soundness at all states ({name}`passesφ`): given it at the forms
after, the expansion's step at the form from the declarations writes the definition of a name
as a body, sound at the states ({name}`soundAtT`), the test of the definitions' bodies steps to
the state of the declarations and the abbreviations, and the hypotheses at the states give the
conclusion. The definition is before the forms of the rest ({lit}`typedFormsCons`), a pending
form before none, which leaves states of which the hypotheses hold again ({name}`writtenInv`),
at which the hypothesis on the forms after gives the conclusion. In the context of the body,
the name, the form, the forms after and the states. -/
def stepDefined (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDefined", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"stepDefined @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDefined: no partition" fun _ ↦ none
    let s := passesAt 4 (consT treeTy (v 2) (v 3))
    let hyps := [Internal.instTerm [] [v 3] (passesφ P S T X₀ (formsOk P S)),
        Term.eq (xpStepT P (xpState (v 12) nil) (v 2))
          (xpState (v 12) (consT treeTy (defForm P (v 1) (v 0)) nil)),
        Term.eq (plainStepT P (plainState (v 12) (v 8)) (v 2)) (plainState (v 12) (v 8))] ++
      s.hyps P S T X₀ ++ [soundAtT P S T s (v 0), userNameT P (pc P "Reader.nameOf" [v 1])] ++
      formsOk P S (v 3)
    let Γ₀ := [treeTy, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (bA, nA, esA, EA, dvA) := (at_ 0, at_ 1, at_ 3, at_ 11, at_ 12)
    let states (Γ : List Tree) : List Term :=
      (List.range (passesCtx T).length).map fun j ↦ at_ (4 + j) Γ
    let fA (Γ : List Tree) : Term := defForm P (nA Γ) (bA Γ)
    -- the states after the form
    let s'A (Γ : List Tree) : Passes :=
      { (passesAt (4 + (Γ.length - Γ₀.length)) (esA Γ)).written P (nA Γ) (bA Γ) nil with
        ws := none }
    let nInv := (s.hyps P S T X₀).length
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let (hStep, hPlain, hX, hSound, hName, hMore) := (1, 2, 3, 3 + nInv, 4 + nInv, 5 + nInv)
    let some d := (at' "the expansion" <| normHyps K [hStep, hPlain] <|
        at' "the typed forms" <|
        applyThm K "typedFormsCons" (fun Γ ↦ [fA Γ, dvA Γ, esA Γ]) [] <| K.conjE <|
        fun Γ₃ Φ₃ ψ₃ ↦
          let (iFlag, iImp) := (Φ₃.length - 2, Φ₃.length - 1)
          normHyps K [iFlag] (
            dImpE L iImp (stage "stepDefined: the rest's expansion" (K.byHyp hX)) <|
            last fun iTF ↦ normHyps K [iTF] <| at' "the definition written" <|
            applyThm K "writtenInv" (fun Γ ↦ [bA Γ, nA Γ, nil, esA Γ] ++ states Γ ++ [EA Γ])
              ((List.range nInv).map (fun k ↦
                  stage s!"stepDefined: the hypothesis {k} at the states" (hypOrK K (3 + k))) ++
                [stage "stepDefined: the body sound" (K.byHyp hSound),
                  stage "stepDefined: the name's origin" (hypOrK K hName)]) <|
            at' "the forms after" <| conjEs K (nInv + 1) fun inv Γ Φ ψ ↦
            dAllE L K.G K.E 0 ((s'A Γ).dv) (
              K.allEΓ (fun Γ ↦ (s'A Γ).env) <| K.allEΓ (fun Γ ↦ (s'A Γ).rej) <|
              K.allEΓ (fun Γ ↦ (s'A Γ).tys) <| K.allEΓ (fun Γ ↦ (s'A Γ).nums) <|
              K.allEΓ (fun Γ ↦ (s'A Γ).names) <| K.allEΓ (fun Γ ↦ (s'A Γ).terms) <|
              K.allEΓ (fun Γ ↦ (s'A Γ).ms) <| K.allEΓ (fun Γ ↦ (s'A Γ).fs) <|
              last fun iIH ↦ impEs L iIH
                ((List.range nInv).map (fun k ↦
                    stage s!"stepDefined: the hypothesis {k} after the form" <|
                      if k = 11 then unfoldBothK K (T.q + 6 + 2 * nFolds) (inv k)
                      else hypOrK K (inv k)) ++
                  [stage "stepDefined: the rest's kinds" (hypOrK K hMore)]) <|
              last fun iAfter ↦ dImpE L (inv nInv)
                (stage "stepDefined: the conclusion after the form" (K.byHyp iAfter))
                (stage "stepDefined: the conclusion" (last K.byHyp))) Γ Φ ψ) Γ₃ Φ₃ ψ₃)
        a.ctx a.hyps a.concl
      | dbgTrace "stepDefined: not proved" fun _ ↦ none
    pure (a, d))

/-- The step at a form at which the expansion writes a definition ({name}`stepDefined`), at a
body, a name, a form, the forms after and the states: the hypothesis on the forms after the
first hypothesis, the hypotheses at the states those from the index {lit}`hInv`, of the number
{lit}`nInv`, and the rest's kinds that of index {lit}`hMore`; the expansion's step's equation,
the test's step's, the body's soundness at the states and the name's origin by the deducers
given. The conclusion is the goal. -/
def applyDefined (K : Kit) (σ : List Tree → List Term) (hInv hMore nInv : ℕ)
    (stepEq plainEq sound user : Deducer) : Deducer :=
  applyThm K "stepDefined" σ
    ([stage "stepDefined: the hypothesis on the forms after" (hypOrK K 0),
        stage "stepDefined: the expansion's step" stepEq,
        stage "stepDefined: the test's step" plainEq] ++
      (List.range nInv).map (fun k ↦
        stage s!"stepDefined: the invariant's hypothesis {k}" (hypOrK K (hInv + k))) ++
      [stage "stepDefined: the body sound" sound,
        stage "stepDefined: the name's origin" user,
        stage "stepDefined: the kinds of the forms after" (hypOrK K hMore)])
    (stage "stepDefined: the goal" (lastOr K))

/-- The step at a form at which the expansion writes a definition ({name}`applyDefined`), the
body a source form and the test's step that of the state by the test of the definitions' bodies
({lit}`plainDefined`): at a form whose head no keyword of an instance or of a datatype names,
the hypotheses of indices 1 to 3, where the test's run is the hypothesis of index {lit}`hP` and
the name's origin that of index {lit}`hUser`, before the hypotheses at the states. The body is
sound at the states {lit}`s` by its soundness at expanded forms, which {lit}`expanded` gives
({name}`soundExpanded`). -/
def applyPlain (K : Kit) (P : Prog) (b n e es nums dv : List Tree → Term)
    (states : List Tree → List Term) (s : List Tree → Passes) (hUser hP hMore nInv : ℕ)
    (stepEq : Deducer) (expanded : (ℕ → Deducer) → Deducer) : Deducer :=
  applyThm K "plainDefined" (fun Γ ↦ [b Γ, n Γ, e Γ, es Γ, nums Γ, dv Γ])
    ([1, 2, 3].map (fun i ↦ stage s!"plainDefined: the head's test {i}" (hypOrK K i)) ++
      [stage "plainDefined: the expansion's step" stepEq,
        stage "plainDefined: the test's run" (hypOrK K hP)]) <|
  K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
    let (iSrc, iEq) := (Φ₁.length - 2, Φ₁.length - 1)
    applyDefined K (fun Γ ↦ [b Γ, n Γ, e Γ, es Γ] ++ states Γ) (hUser + 1) hMore nInv stepEq
      (hypOrK K iEq) (soundExpanded K P s (hUser + 1) iSrc expanded) (hypOrK K hUser)
      Γ₁ Φ₁ ψ₁

/-- The soundness at the forms that remain after a definition's form, a step of the soundness at
all states ({name}`passesφ`): given it at the forms after, the form the list of a head that names
a definition, a name and a body, the hypotheses at the states give the conclusion. The
expansion's step ({lit}`xpDef`) writes the definition of the name as the body's expansion, sound
at expanded forms ({name}`expandedOf`), so that the step at a definition written gives the
conclusion ({name}`applyPlain`). In the context of the body, the name, the head, the forms after
and the states. -/
def stepDef (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDef", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let nil := nilT treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDef: no partition" fun _ ↦ none
    let e := listNode [v 2, v 1, v 0]
    let s := passesAt 4 (consT treeTy e (v 3))
    let hyps := [Internal.instTerm [] [v 3] (passesφ P S T X₀ (formsOk P S))] ++ defHead P (v 2) ++
      [userNameT P (pc P "Reader.nameOf" [v 1])] ++ s.hyps P S T X₀ ++ formsOk P S (v 3)
    let nInv := (s.hyps P S T X₀).length
    let Γ₀ := [treeTy, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (FA, nA, hA, esA, numsA, dvA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 8, at_ 12)
    let states (Γ : List Tree) : List Term :=
      (List.range (passesCtx T).length).map fun j ↦ at_ (4 + j) Γ
    let exA (Γ : List Tree) : Term := pc P "Datatype.expandExpr" [dvA Γ, FA Γ]
    let bA (Γ : List Tree) : Term := pc P "Prelude.get" [exA Γ]
    let eA (Γ : List Tree) : Term := listNode [hA Γ, nA Γ, FA Γ]
    let xpA (Γ : List Tree) : Term := pc P "Datatype.xpStep" [xpState (dvA Γ) nil, eA Γ]
    let sA (Γ : List Tree) : Passes :=
      passesAt (4 + (Γ.length - Γ₀.length)) (consT treeTy (eA Γ) (esA Γ))
    let (hX, hP, hMore) := (6, 18, 6 + nInv)
    -- the expansion's step
    let expansion : Deducer := stage "stepDef: the expansion" <|
      applyThm K "xpPrefix" (fun Γ ↦ [esA Γ, xpA Γ])
        [stage "stepDef: the expansion's run" (K.byHyp hX)] <|
      applyThm K "xpDef" (fun Γ ↦ [FA Γ, nA Γ, hA Γ, nil, dvA Γ])
        [stage "stepDef: no datatype's keyword" dHyp, stage "stepDef: no tree datatype's" dHyp,
          stage "stepDef: the definitions' keyword" dHyp,
          stage "stepDef: the expansion's step" dHyp] <|
      K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iEx, iStep) := (Φ₂.length - 2, Φ₂.length - 1)
        applyPlain K P bA nA eA esA numsA dvA states sA 5 hP hMore nInv
          (normHyps K [iStep] K.byNorm)
          (expandedOf K FA dvA (K.byHyp iEx)) Γ₂ Φ₂ ψ₂
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
        (stage "stepDef: a template's instance" (refuteNot K 1)) a.ctx a.hyps a.concl
      | dbgTrace "stepDef: not proved" fun _ ↦ none
    pure (a, d))

/-- The form of a binding of a name at a type to a term in a body, as the typing and the reader
read it. -/
def letForm (P : Prog) (x A t b : Term) : Term :=
  listNode [kwAtom P "Reader.kwLet", x, A, t, b]

/-- The erasure's variable is sound at expanded forms: the soundness at its expansion
({name}`expandedOf`), which is the variable, the expansion's step at the atom unfolded. -/
def expandedR (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("expandedR", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, (vocab3 ++ ["charsMap", "handlerAtom3"]).filter
      fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let aR := pc P "Datatype.aR" []
    let a : Internal.Thm := ⟨0, [], [], Internal.instTerm [] [aR] (expandedφ P S T)⟩
    let step : List Internal.NormRule := [.delta (T.argIdx 0)]
    let unfolding (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ step) .full) k Γ Φ ψ
    let some d := (expandedOf K (fun _ ↦ aR) (fun _ ↦ nilT treeTy)
        (stage "expandedR: the expansion" (unfolding (K.solve 2))) fun i ↦
          stage "expandedR: the variable" fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ i ++ step) .full) i (unfolding dHyp) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "expandedR: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at expanded forms of the parts the expansion writes of a
function's definition: the erasure's variable and a binding. -/
def programLetDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [expandedR P S T, letCaseAt P S T true "letExpanded"]

/-- The soundness at the forms that remain after a function's form, a step of the soundness at
all states ({name}`passesφ`): given it at the forms after, the form the list of a head that names
a function, a name, binders, a result type and a body, the hypotheses at the states give the
conclusion. The expansion's step ({lit}`xpDefn`) writes the definition of the name as the
abstractions over the binders around the binding of the erasure's variable at the result type to
the body's expansion, in the variable: sound at expanded forms, the body's expansion
({name}`expandedOf`), the variable ({name}`expandedR`), the binding ({lit}`letExpanded`) and the
abstractions ({lit}`nest`), so that the step at a definition written gives the conclusion
({name}`applyPlain`). In the context of the body, the result type,
the binders, the name, the head, the forms after and the states. -/
def stepDefn (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDefn", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let nil := nilT treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDefn: no partition" fun _ ↦ none
    let e := listNode [v 4, v 3, v 2, v 1, v 0]
    let s := passesAt 6 (consT treeTy e (v 5))
    let hyps := [Internal.instTerm [] [v 5] (passesφ P S T X₀ (formsOk P S))] ++
      defnHead P (v 4) ++ [userNameT P (pc P "Reader.nameOf" [v 3])] ++ s.hyps P S T X₀ ++
      formsOk P S (v 5)
    let nInv := (s.hyps P S T X₀).length
    let Γ₀ := [treeTy, treeTy, treeTy, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (XA, RA, bsA, nA, hA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let (numsA, dvA) := (at_ 10, at_ 14)
    let states (Γ : List Tree) : List Term :=
      (List.range (passesCtx T).length).map fun j ↦ at_ (6 + j) Γ
    let aR := pc P "Datatype.aR" []
    let exA (Γ : List Tree) : Term := pc P "Datatype.expandExpr" [dvA Γ, XA Γ]
    let bA (Γ : List Tree) : Term := pc P "Prelude.get" [exA Γ]
    let letA (Γ : List Tree) : Term := letForm P aR (RA Γ) (bA Γ) aR
    let bindersA (Γ : List Tree) : Term := bindersT P (bsA Γ)
    -- the body written: the abstractions over the binders around the binding
    let BA (Γ : List Tree) : Term := nestT P (bindersA Γ) (letA Γ)
    let eA (Γ : List Tree) : Term := listNode [hA Γ, nA Γ, bsA Γ, RA Γ, XA Γ]
    let xpA (Γ : List Tree) : Term := pc P "Datatype.xpStep" [xpState (dvA Γ) nil, eA Γ]
    let sA (Γ : List Tree) : Passes :=
      passesAt (6 + (Γ.length - Γ₀.length)) (consT treeTy (eA Γ) (esA Γ))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let (hX, hP, hMore) := (6, 18, 6 + nInv)
    -- the body written sound at expanded forms
    let sound (iEx : ℕ) (k : ℕ → Deducer) : Deducer :=
      expandedOf K XA dvA (K.byHyp iEx) fun iB ↦
      K.cutThm "expandedR" (fun _ ↦ []) <| last fun iR ↦
      applyThm K "letExpanded" (fun Γ ↦ [aR, bA Γ, RA Γ, aR])
        [stage "stepDefn: the body's expansion sound" (hypOr iB),
          stage "stepDefn: the variable sound" (hypOr iR)] <|
      last fun iLet ↦ K.cutThm "nest" (fun Γ ↦ [bindersA Γ, letA Γ]) <|
      K.impE (stage "stepDefn: the binding sound" (hypOr iLet)) <| last k
    -- the expansion's step
    let expansion : Deducer := stage "stepDefn: the expansion" <|
      applyThm K "xpPrefix" (fun Γ ↦ [esA Γ, xpA Γ])
        [stage "stepDefn: the expansion's run" (K.byHyp hX)] <|
      applyThm K "xpDefn" (fun Γ ↦ [XA Γ, RA Γ, bsA Γ, nA Γ, hA Γ, nil, dvA Γ])
        [stage "stepDefn: no datatype's keyword" dHyp, stage "stepDefn: no tree datatype's" dHyp,
          stage "stepDefn: the functions' keyword" dHyp,
          stage "stepDefn: the expansion's step" dHyp] <|
      K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iEx, iStep) := (Φ₂.length - 2, Φ₂.length - 1)
        applyPlain K P BA nA eA esA numsA dvA states sA 5 hP hMore nInv
          (normHyps K [iStep] K.byNorm)
          (sound iEx) Γ₂ Φ₂ ψ₂
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
        (stage "stepDefn: a template's instance" (refuteNot K 1)) a.ctx a.hyps a.concl
      | dbgTrace "stepDefn: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at the forms that remain after a type abbreviation's form, a step of the
soundness at all states ({name}`passesφ`): the expansion's step ({lit}`xpDeftype`) declares the
abbreviation and writes the form, the typing's ({lit}`checkDeftype`) reads the body as a type
and declares the abbreviation, and the reader's ({lit}`readDeftype`) reads it as a type and
abbreviates it; the invariant, which reads no abbreviation of a type, holds of the states they
leave. In the context of the body, the name, the head, the forms after and the states. -/
def stepDeftype (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDeftype", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"stepDeftype @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDeftype: no partition" fun _ ↦ none
    let e := listNode [v 2, v 1, v 0]
    let s := passesAt 4 (consT treeTy e (v 3))
    let hyps := [Internal.instTerm [] [v 3] (passesφ P S T X₀ (formsOk P S))] ++
      deftypeHead P (v 2) ++ s.hyps P S T X₀ ++ formsOk P S (v 3)
    let Γ₀ := [treeTy, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (XA, nA, hA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3)
    let (fsA, msA, termsA, namesA, numsA, tysA) := (at_ 4, at_ 5, at_ 6, at_ 7, at_ 8, at_ 9)
    let (rA, EA, dvA) := (at_ 10, at_ 11, at_ 12)
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let eA (Γ : List Tree) : Term := listNode [hA Γ, nA Γ, XA Γ]
    let xpA (Γ : List Tree) : Term := pc P "Datatype.xpStep" [xpState (dvA Γ) nil, eA Γ]
    let sA (Γ : List Tree) : Passes :=
      passesAt (4 + (Γ.length - Γ₀.length)) (consT treeTy (eA Γ) (esA Γ))
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [nA Γ]
    let dv'A (Γ : List Tree) : Term := pc P "Datatype/Decls.append" [dvA Γ,
      pc P "Datatype/Decls.single" [pc P "Datatype.aliasD" [pc P "Datatype.atomName" [nA Γ],
        pc P "Datatype.expandAliases" [dvA Γ, XA Γ]]]]
    let E'A (Γ : List Tree) : Term := pc P "Typing.withAl" [EA Γ, consT treeTy
      (pc P "Typing.abbr" [pc P "Typing.atomName" [nA Γ],
        get (pc P "Typing.readTy" [EA Γ, XA Γ])]) (pc P "Typing.envAl" [EA Γ])]
    let tys'A (Γ : List Tree) : Term := consT treeTy
      (abbrevT P (nmA Γ) (get (pc P "Reader.readType" [tysA Γ, XA Γ]))) (tysA Γ)
    let s'A (Γ : List Tree) : Passes := ⟨esA Γ, dv'A Γ, E'A Γ, pc P "Typing/OName.nothing" [],
      tys'A Γ, numsA Γ, namesA Γ, termsA Γ, msA Γ, fsA Γ, none, none⟩
    let restA (Γ : List Tree) : Passes := { s'A Γ with env := EA Γ, rej := rA Γ }
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ
    let unfoldBoth := unfoldBothK K
    let (hNoDef, hKw, hX, hC, hO, hR, hK, hRej, hGlob, hNums, hNames, hKws, hLen, hRecs, hP,
        hOcc, hIns, hUsed) :=
      (4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21)
    let (hUser, hSorts, hAl, hAlKw, hAlTys, hMs, hMk, hStatic, hMore) :=
      (22, 23, 24, 25, 26, 27, 28, 29, 30)
    -- the head's tests decided, as the test of the definitions' bodies reads them
    let heads : Deducer → Deducer := decideEach K Γ₀.length
      [(headNamed P (v 2) "Datatype.kwData", none, some (refuteNot K 2)),
        (headNamed P (v 2) "Datatype.kwTreeData", none, some (refuteNot K 3)),
        (headNamed P (v 2) "Reader.kwDef", none, some (refuteNot K 4)),
        (headNamed P (v 2) "Reader.kwDeftype", some (K.hypFalse 5), none)]
    -- the hypothesis on the forms after, at the states the steps leave
    let apply (iReadTy iAtom iFresh iO : ℕ) : Deducer := at' "the forms after" <|
      normHyps K [hOcc] <| K.conjE <| last fun iOccRest ↦
      normHyps K [hMk] <| K.conjE <| last fun iMkRest ↦
      -- the name fresh: not reserved, abbreviating no type, so without an alias
      applyThm K "freshParts" (fun Γ ↦ [nmA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "stepDeftype: fresh" (hypOr iFresh)] <| K.conjE <| K.conjE <| K.conjE <|
      fun Γ₅ Φ₅ ψ₅ ↦
      let (iUnres, iNotTys) := (Φ₅.length - 6, Φ₅.length - 2)
      -- the name an atom's, where the expansion's and the typing's names of it are the reader's:
      -- decided within a step, the equations before it having the names as written
      let atom (k : Deducer) : Deducer :=
        decideIn K (fun Γ ↦ pc P "Reader.isAtom" [nA Γ]) (K.hypFalse iAtom) k
      let noAlias : Deducer := dImpI L fun Γ Φ ψ ↦
        let iAlias := Φ.length - 1
        dAllE L K.G K.E hAlTys (nmA Γ) (K.impE (K.byHyp iAlias) <| last fun iTy ↦
          dImpE L iNotTys (K.byHyp iTy) (dFalse L dHyp)) Γ Φ ψ
      (dConjE L hStatic <| fun Γ₆ Φ₆ ψ₆ ↦
      let iMarkers := Φ₆.length - 2
      (at' "the aliases" <|
      applyThm K "aliasExtend" (fun Γ ↦ [XA Γ, nmA Γ, msA Γ, EA Γ, dvA Γ])
        [stage "stepDeftype: the aliases before" (hypOr hAl),
          stage "stepDeftype: the aliases of types read first" (hypOr hAlKw),
          stage "stepDeftype: the markers' names" (hypOr iMarkers),
          stage "stepDeftype: no sort" (hypOr hSorts),
          stage "stepDeftype: the body's type" (K.byHyp iReadTy),
          stage "stepDeftype: the name without an alias" noAlias,
          stage "stepDeftype: the name not reserved" (hypOr iUnres)] <|
      K.conjE <| fun Γ₇ Φ₇ ψ₇ ↦
      let (iAl', iAlKw') := (Φ₇.length - 2, Φ₇.length - 1)
      (applyThm K "aliasTysExtend" (fun Γ ↦ [get (pc P "Reader.readType" [tysA Γ, XA Γ]),
          pc P "Datatype.expandAliases" [dvA Γ, XA Γ], nmA Γ, tysA Γ, dvA Γ])
        [stage "stepDeftype: the aliases abbreviated before" (hypOr hAlTys)] <|
      last fun iAlTys' ↦ fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 ((s'A Γ).dv) (
        K.allEΓ (fun Γ ↦ (s'A Γ).env) <| K.allEΓ (fun Γ ↦ (s'A Γ).rej) <|
        K.allEΓ (fun Γ ↦ (s'A Γ).tys) <| K.allEΓ (fun Γ ↦ (s'A Γ).nums) <|
        K.allEΓ (fun Γ ↦ (s'A Γ).names) <| K.allEΓ (fun Γ ↦ (s'A Γ).terms) <|
        K.allEΓ (fun Γ ↦ (s'A Γ).ms) <| K.allEΓ (fun Γ ↦ (s'A Γ).fs) <|
        last fun iIH ↦ impEs L iIH
          [stage "stepDeftype: the rest expands" (K.byHyp hX),
            stage "stepDeftype: the rest checks" (K.byHyp hC),
            stage "stepDeftype: the rest's recognizers" (hypOr iO),
            stage "stepDeftype: the rest reads" (K.byHyp hR),
            stage "stepDeftype: the kernel checks" (K.byHyp hK),
            stage "stepDeftype: no rejection" (dImpI L (lastFalse K)),
            stage "stepDeftype: related after" (unfoldBoth (T.q + 2) hGlob),
            stage "stepDeftype: the numerals after" (unfoldBoth (T.q + 3 + 2 * nFolds) hNums),
            stage "stepDeftype: the names" (hypOr hNames),
            stage "stepDeftype: the keywords" (hypOr hKws),
            stage "stepDeftype: the lengths" (hypOr hLen),
            stage "stepDeftype: the recognizers" (unfoldBoth (T.q + 6 + 2 * nFolds) hRecs),
            stage "stepDeftype: the bodies after" (K.byHyp hP),
            stage "stepDeftype: the occurrences after" (hypOr iOccRest),
            stage "stepDeftype: the recognizers referred to" (hypOr hIns),
            stage "stepDeftype: the names' occurrences" (hypOr hUsed),
            stage "stepDeftype: the names' origin" (hypOr hUser),
            stage "stepDeftype: no sort after" (hypOr hSorts),
            stage "stepDeftype: the aliases after" (atom (K.byHyp iAl')),
            stage "stepDeftype: the aliases of types read first, after" (atom (K.byHyp iAlKw')),
            stage "stepDeftype: the aliases abbreviated" (atom (K.byHyp iAlTys')),
            stage "stepDeftype: the markers" (normHyps K [hMs] K.byNorm),
            stage "stepDeftype: the markers that remain" (hypOr iMkRest),
            stage "stepDeftype: the markers and the numerals" (hypOr hStatic),
            stage "stepDeftype: the rest's kinds" (hypOr hMore)] <|
        stage "stepDeftype: the conclusion" (last K.byHyp)) Γ Φ ψ) Γ₇ Φ₇ ψ₇) Γ₆ Φ₆ ψ₆) Γ₅ Φ₅ ψ₅
    -- the reader's step
    let reader (iReadTy : ℕ) : Deducer := at' "the reader" <|
      applyThm K "eraseOther" (fun Γ ↦ [XA Γ, nA Γ, hA Γ])
        [stage "stepDeftype: no definition" dHyp] <| last fun iErase ↦ normHyps K [iErase] <|
      applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
        [stage "stepDeftype: the recognizers' insertion" (K.byHyp hO)] <| last fun iO ↦
      applyThm K "readPrefix" (fun Γ ↦ [rsA Γ, pc P "Reader.progStep" [stA Γ, eA Γ]])
        [stage "stepDeftype: the reader's run" (K.byHyp hR)] <| at' "the reader's step" <|
      applyThm K "readDeftype" (fun Γ ↦ [XA Γ, nA Γ, hA Γ, termsA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "stepDeftype: the reader's test of a definition" (K.byHyp hNoDef),
          stage "stepDeftype: the reader's keyword" (K.byHyp hKw),
          stage "stepDeftype: the reader's step" dHyp] <|
      K.conjE <| K.conjE <| K.conjE <| fun Γ Φ ψ ↦
        let (iAtom, iFresh, iRead) := (Φ.length - 6, Φ.length - 4, Φ.length - 1)
        normHyps K [iRead] (apply iReadTy iAtom iFresh iO) Γ Φ ψ
    -- the typing's step
    let typing : Deducer := at' "the typing" <|
      applyThm K "checkPrefix" (fun Γ ↦ [(restA Γ).others P X₀,
          checkStepAt P (EA Γ) (rA Γ) (eA Γ)])
        [stage "stepDeftype: the typing's run" (K.byHyp hC)] <| at' "the typing's step" <|
      applyThm K "checkDeftype" (fun Γ ↦ [XA Γ, nA Γ, hA Γ, rA Γ, EA Γ])
        [stage "stepDeftype: the typing's test of a definition" (K.byHyp hNoDef),
          stage "stepDeftype: the typing's keyword" (K.byHyp hKw),
          stage "stepDeftype: no rejection before" (hypOr hRej),
          stage "stepDeftype: the typing's step" dHyp] <|
      K.conjE <| fun Γ Φ ψ ↦
        let (iReadTy, iCheck) := (Φ.length - 2, Φ.length - 1)
        normHyps K [iCheck] (reader iReadTy) Γ Φ ψ
    -- the expansion's step
    let expansion : Deducer := at' "the expansion" <|
      applyThm K "xpPrefix" (fun Γ ↦ [esA Γ, xpA Γ])
        [stage "stepDeftype: the expansion's run" (K.byHyp hX)] <|
      at' "the expansion's step" <|
      applyThm K "xpDeftype" (fun Γ ↦ [XA Γ, nA Γ, hA Γ, nil, dvA Γ])
        [stage "stepDeftype: no datatype's keyword" dHyp,
          stage "stepDeftype: no tree datatype's" dHyp,
          stage "stepDeftype: no definition's" dHyp,
          stage "stepDeftype: the abbreviations' keyword" dHyp] <|
      last fun iStep ↦ normHyps K [iStep] <| at' "the typed forms" <|
      applyThm K "typedFormsCons" (fun Γ ↦ [eA Γ, dv'A Γ, esA Γ]) [] <| K.conjE <|
      fun Γ₃ Φ₃ ψ₃ ↦
        let (iFlag, iImp) := (Φ₃.length - 2, Φ₃.length - 1)
        normHyps K [iFlag] (
          dImpE L iImp (stage "stepDeftype: the rest's expansion" (K.byHyp hX)) <|
          last fun iTF ↦ normHyps K [iTF] typing) Γ₃ Φ₃ ψ₃
    let _ := sA
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric")
        (heads expansion)
        (stage "stepDeftype: a template's instance" (refuteNot K 1)) a.ctx a.hyps a.concl
      | dbgTrace "stepDeftype: not proved" fun _ ↦ none
    pure (a, d))

/-- The equations of the numeral abbreviations' lookup and of the typing's test of a name among
names, kept folded, at the empty list and at a construction. -/
def numsFoldEqs (P : Prog) : List Step :=
  let Γ := [list treeTy, treeTy, treeTy]
  listFoldEqs P "lookupAbbrev" "Reader.lookupAbbrev" Γ treeTy (fun xs ↦ [v 2, xs]) ++
    listFoldEqs P "hasName" "Typing.hasName" Γ treeTy (fun xs ↦ [v 2, xs])

/-- The names of {name}`numsFoldEqs`' equations. -/
def numsEqNames : List String :=
  ["lookupAbbrevNil", "lookupAbbrevCons", "hasNameNil", "hasNameCons"]

/-- The typing's test of a name among names. -/
def hasT (P : Prog) (x ns : Term) : Term := pc P "Typing.hasName" [x, ns]

/-- The typing's names with a name after them. -/
def namesSnoc (P : Prog) (ns nm : Term) : Term :=
  pc P "Typing/Names.append" [ns, pc P "Typing/Names.single" [nm]]

/-- A name among names is among them with a name after them: by induction on the names. In the
context of the names, under the name and the name after them. -/
def hasSnocOld (P : Prog) (S : Defs) : Step :=
  ("hasSnocOld", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let all (b : Term) : Term := Internal.Logic.all o treeTy (Term.lam treeTy b)
    -- under the quantifiers: the name after them v0, the name v1, the names v2
    let φ := all (all (Internal.Logic.imp o (truth o (hasT P (v 1) (v 2)))
      (truth o (hasT P (v 1) (namesSnoc P (v 2) (v 0))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ Φ ψ ↦
      k (Φ.length - 1) Γ Φ ψ
    -- a construction: the head v(0), the tail v(1), the name v(2), the name after v(3)
    let step : Deducer := intro fun g ↦
      let (b, tl, x, nm) := (at_ 0, at_ 1, at_ 2, at_ 3)
      decideIn K (fun Γ ↦ apps equalT [b Γ, x Γ])
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (x Γ) (K.allEΓ nm (K.impE (K.byHyp g) fun Γ Φ ψ ↦
          let h := Φ.length - 1
          decideIn K (fun Γ ↦ hasT P (x Γ) (namesSnoc P (tl Γ) (nm Γ)))
            (K.hypFalse h) (K.solve 3) Γ Φ ψ)) Γ Φ ψ)
        (K.solve 3)
    listInduction "hasSnocOld" φ (intro fun g ↦ K.hypFalse g) step)

/-- A name is among names with it after them: by induction on the names. In the context of the
names, under the name. -/
def hasSnocNew (P : Prog) (S : Defs) : Step :=
  ("hasSnocNew", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    -- under the quantifier: the name v0, the names v1
    let φ := Internal.Logic.all P.o treeTy (Term.lam treeTy
      (truth P.o (hasT P (v 0) (namesSnoc P (v 1) (v 0)))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let base : Deducer := dAllI L <| K.cutThm "equalRefl" (fun Γ ↦ [at_ 0 Γ]) <|
      decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 0 Γ]) (anyFalse K) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the name v(2)
    let step : Deducer := dAllI L <|
      decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 2 Γ])
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (at_ 2 Γ) (fun Γ Φ ψ ↦
          let h := Φ.length - 1
          decideIn K (fun Γ ↦ hasT P (at_ 2 Γ) (namesSnoc P (at_ 1 Γ) (at_ 2 Γ)))
            (K.hypFalse h) (K.solve 3) Γ Φ ψ) Γ Φ ψ)
        (K.solve 3)
    listInduction "hasSnocNew" φ base step)

/-- A name among names with a name after them, and not among them, is the name after them: by
induction on the names. In the context of the names, under the name and the name after them. -/
def hasSnocCases (P : Prog) (S : Defs) : Step :=
  ("hasSnocCases", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let all (b : Term) : Term := Internal.Logic.all o treeTy (Term.lam treeTy b)
    -- under the quantifiers: the name after them v0, the name v1, the names v2
    let φ := all (all (Internal.Logic.imp o (truth o (hasT P (v 1) (namesSnoc P (v 2) (v 0))))
      (Internal.Logic.imp o (notTest o (hasT P (v 1) (v 2)))
        (truth o (apps equalT [v 0, v 1])))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    let base : Deducer := intro fun h₁ _ ↦
      decideIn K (fun Γ ↦ apps equalT [at_ 1 Γ, at_ 0 Γ]) (K.hypFalse h₁) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the name v(2), the name after v(3)
    let step : Deducer := intro fun h₁ h₂ ↦
      let (b, tl, x, nm) := (at_ 0, at_ 1, at_ 2, at_ 3)
      decideIn K (fun Γ ↦ apps equalT [b Γ, x Γ])
        (decideIn K (fun Γ ↦ hasT P (x Γ) (namesSnoc P (tl Γ) (nm Γ)))
          (stage "hasSnocCases: not among them" (K.hypFalse h₁))
          (decideIn K (fun Γ ↦ hasT P (x Γ) (tl Γ))
            (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (x Γ) (K.allEΓ nm
              (K.impE (K.solve 3) (K.impE (dImpI L (lastFalse K)) fun Γ Φ ψ ↦
                K.byHyp (Φ.length - 1) Γ Φ ψ))) Γ Φ ψ)
            (stage "hasSnocCases: among the rest" (refuteNot K h₂))))
        (stage "hasSnocCases: the head" (refuteNot K h₂))
    listInduction "hasSnocCases" φ base step)

/-- An atom is the node of the atoms' label over its children: the tree a node
({lit}`treeNode`), its label the atoms' by the soundness of the labels' equality
({lit}`eqBSound`). In the context of the tree. -/
def atomNode (P : Prog) (S : Defs) : Step :=
  ("atomNode", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy], [truth P.o (pc P "Reader.isAtom" [v 0])],
      Term.eq (nodeT (Term.pair (numeral 1) (call D.children [] [v 0]))) (v 0)⟩
    let some d := K.treeNode (v 0) (K.cutThm "eqBSound" (fun _ ↦ [numeral 1]) <|
        K.allEΓ (fun _ ↦ v 1) <| K.impE (stage "atomNode: the label" (K.byHyp 0)) <|
        byLast K) a.ctx a.hyps a.concl
      | dbgTrace "atomNode: not proved" fun _ ↦ none
    pure (a, d))

/-- The numeral abbreviations' coherence with the typing environment's numeral names, extended
by an abbreviation: coherent before, the value an atom of a numeral's characters, the
abbreviations with the name's of the value before them cohere with the environment with the name
after its numeral names. A name is the name, abbreviating the value, the atom of its characters
({name}`atomNode`), and among the names ({name}`hasSnocNew`); or another, abbreviated and among
the names as before ({name}`hasSnocOld`, {name}`hasSnocCases`). In the context of the value, the
name, the abbreviations and the environment. -/
def numsExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("numsExtend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let Γ₀ := [treeTy, treeTy, list treeTy, T.envTy]
    let (val, nm, nums, Ev) := (v 0, v 1, v 2, v 3)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let chars (t : Term) : Term := call D.children [] [t]
    let a : Internal.Thm := ⟨0, Γ₀, [T.numsT Ev nums, truth P.o (pc P "Reader.isAtom" [val]),
        truth P.o (isSome (pc P "Reader.numeral" [chars val]))],
      T.numsT (pc P "Typing.withNums" [Ev, namesSnoc P (pc P "Typing.envNums" [Ev]) nm])
        (consT treeTy (abbrevT P nm val) nums)⟩
    let unfold : List Internal.NormRule := [.delta (T.q + 3 + 2 * nFolds)]
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (EA, nmA, valA, xA) := (at_ 0, at_ 2, at_ 3, at_ 4)
    let nsA (Γ : List Tree) : Term := pc P "Typing.envNums" [EA Γ]
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"numsExtend: {m}" k
    -- the coherence before, unfolded, of index 3, at the name: its two implications
    let before (k : ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E 3 (xA Γ) (K.conjE fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    -- the name the abbreviation's
    let same : Deducer :=
      applyThm K "atomNode" (fun Γ ↦ [valA Γ]) [at' "an atom" dHyp] <| last fun iAtom ↦
      normHyps K [iAtom] <| K.cutThm "hasSnocNew" (fun Γ ↦ [nsA Γ]) <| K.allEΓ nmA <|
      last fun iNew ↦ dConjI L
        (dImpI L fun Γ Φ ψ ↦ dExI L K.G K.E (chars (valA Γ)) (dConjI L
          (at' "the new abbreviation" K.byNorm) (at' "the numeral" (K.byHyp 2))) Γ Φ ψ)
        (dImpI L <| K.cutThm "equalSound" (fun Γ ↦ [xA Γ]) <| K.allEΓ nmA <|
          K.impE (K.solve 3) <| at' "the new name" (K.byHyp iNew))
    -- another name
    let other : Deducer := dConjI L
      (dImpI L <| last fun hA ↦ decideIn K (fun Γ ↦ hasT P (xA Γ) (nsA Γ))
        -- not among the names before: the abbreviation's name, which it is not
        (K.cutThm "hasSnocCases" (fun Γ ↦ [nsA Γ]) <| K.allEΓ xA <| K.allEΓ nmA <|
          K.impE (at' "among the names after" (K.byHyp hA)) <|
          K.impE (dImpI L (lastFalse K)) <| last fun iEq ↦
          applyThm K "equalSymm" (fun Γ ↦ [xA Γ, nmA Γ]) [] <|
          K.impE (at' "equal" (K.byHyp iEq)) <| at' "unequal" (lastFalse K))
        -- among them: abbreviated before
        (before fun iA _ ↦ dImpE L iA (K.solve 3) <| K.exE <| K.conjE <| fun Γ Φ ψ ↦
          let (iAbb, iNum) := (Φ.length - 2, Φ.length - 1)
          normHyps K [iAbb] (dExI L K.G K.E (v 0) (dConjI L
            (at' "the old abbreviation" K.byNorm) (at' "the old numeral" (K.byHyp iNum))))
            Γ Φ ψ))
      (dImpI L <| last fun hB ↦ before fun _ iB ↦
        dImpE L iB (at' "abbreviated before" (K.byHyp hB)) <| last fun iHas ↦
        K.cutThm "hasSnocOld" (fun Γ ↦ [nsA Γ]) <| K.allEΓ xA <| K.allEΓ nmA <|
        K.impE (at' "among the names before" (K.byHyp iHas)) <|
        at' "among the names" (last K.byHyp))
    let some d := (dRwBy (evalRw K.G K.E unfold .head) <|
        dRwHyp (evalRw K.G K.E unfold .head) 0 <| dAllI L <|
        decideIn K (fun Γ ↦ apps equalT [xA Γ, nmA Γ]) other same) a.ctx a.hyps a.concl
      | dbgTrace "numsExtend: not proved" fun _ ↦ none
    pure (a, d))

/-- That a name is one of the implementation's, as the erasure's bound names are. -/
def implT (P : Prog) (x : Term) : Term := pc P "implName" [x]

/-- That a name's characters are a numeral's. -/
def numeralNameT (P : Prog) (x : Term) : Term :=
  pc P "Prelude.isSome" [pc P "Reader.numeral" [call D.children [] [x]]]

/-- No numeral abbreviation a keyword, extended by an abbreviation: none before, the name not
reserved, not the implementation's and no numeral, none of the abbreviations with the name's
before them is. A name abbreviated is the name, or abbreviated before. In the context of the
value, the name and the abbreviations. -/
def kwsExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("kwsExtend", fun ix E ↦ do
    let K : Kit := ⟨freshProg P, S, E, ix, numsEqNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let Γ₀ := [treeTy, treeTy, list treeTy]
    let (val, nm, nums) := (v 0, v 1, v 2)
    let reserved (x : Term) : Term :=
      pc P "Prelude.isSome" [pc P "Reader.indexOf" [x, pc P "Reader.reservedNames" []]]
    let a : Internal.Thm := ⟨0, Γ₀, [T.kwsT nums, unreservedT P nm, notTest P.o (implT P nm),
        notTest P.o (numeralNameT P nm)], T.kwsT (consT treeTy (abbrevT P nm val) nums)⟩
    let unfold : List Internal.NormRule := [.delta (T.q + 5 + 2 * nFolds)]
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (nmA, xA) := (at_ 1, at_ 3)
    let some d := (dRwBy (evalRw K.G K.E unfold .head) <|
        dRwHyp (evalRw K.G K.E unfold .head) 0 <| dAllI L <| dImpI L <| dImpI L <|
        fun Γ₁ Φ₁ ψ₁ ↦
          let (hL, hP) := (Φ₁.length - 2, Φ₁.length - 1)
          decideIn K (fun Γ ↦ apps equalT [xA Γ, nmA Γ])
            -- another name: abbreviated before
            (fun Γ Φ ψ ↦ dAllE L K.G K.E 4 (xA Γ)
              (K.impE (stage "kwsExtend: abbreviated before" (K.byHyp hL))
                (K.impE (stage "kwsExtend: a keyword before" (K.byHyp hP))
                  (stage "kwsExtend: falsity" dHyp))) Γ Φ ψ)
            -- the name: no keyword
            (K.cutThm "equalSound" (fun Γ ↦ [xA Γ]) <| K.allEΓ nmA <| K.impE (K.solve 3) <|
              fun Γ Φ ψ ↦ decideEach K Γ.length
                [(reserved (nmA Γ), none, some (refuteNot K 1)),
                  (implT P (nmA Γ), none, some (refuteNot K 2)),
                  (numeralNameT P (nmA Γ), none, some (refuteNot K 3))]
                (stage "kwsExtend: no keyword" (K.hypFalse hP)) Γ Φ ψ) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "kwsExtend: not proved" fun _ ↦ none
    let _ := val
    let _ := nums
    pure (a, d))

/-- The development of the lists of the numeral abbreviations and names. -/
def programNumsDev (P : Prog) (S : Defs) : List Step :=
  numsFoldEqs P ++ [hasSnocOld P S, hasSnocNew P S, hasSnocCases P S, atomNode P S]

/-- The development of the invariants a numeral abbreviation's reading preserves. -/
def programNumsInvDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [numsExtend P S T, kwsExtend P S T]

/-- The value a numeral abbreviation's body abbreviates, where it does, is an atom of a
numeral's characters: the reader's tests of the body, its abbreviations expanded, decided. In
the context of the body and the numeral abbreviations. -/
def numOfParts (P : Prog) (S : Defs) : Step :=
  ("numOfParts", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let num := pc P "Reader.numOf" [v 1, v 0]
    let x := pc P "Reader.expandNums" [v 1, v 0]
    let val := pc P "Prelude.get" [num]
    let numeral (t : Term) : Term := isSome (pc P "Reader.numeral" [call D.children [] [t]])
    let a : Internal.Thm := ⟨0, [treeTy, list treeTy], [truth P.o (isSome num)],
      Internal.Logic.conj P.o (truth P.o (pc P "Reader.isAtom" [val])) (truth P.o (numeral val))⟩
    let some d := decideEach K 2 [(pc P "Reader.isAtom" [x], some (K.hypFalse 0), none),
        (numeral x, some (K.hypFalse 0), none)] (K.solve 3) a.ctx a.hyps a.concl
      | dbgTrace "numOfParts: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at the forms that remain after a numeral abbreviation's form, a step of the
soundness at all states ({name}`passesφ`): the expansion's step ({lit}`xpDefnum`) writes the
form, the typing's ({lit}`checkDefnum`) finds the name no numeral and has it after the numeral
names, and the reader's ({lit}`readDefnum`) abbreviates the body's numeral by the name, fresh;
the numeral abbreviations cohere with the names still ({name}`numsExtend`), and none is a
keyword ({name}`kwsExtend`), the name not one of the implementation's. In the context of the
body, the name, the head, the forms after and the states. -/
def stepDefnum (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDefnum", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"stepDefnum @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDefnum: no partition" fun _ ↦ none
    let e := listNode [v 2, v 1, v 0]
    let s := passesAt 4 (consT treeTy e (v 3))
    let hyps := [Internal.instTerm [] [v 3] (passesφ P S T X₀ (formsOk P S))] ++
      defnumHead P (v 2) ++ [userNameT P (pc P "Reader.nameOf" [v 1])] ++ s.hyps P S T X₀ ++
      formsOk P S (v 3)
    let Γ₀ := [treeTy, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (XA, nA, hA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3)
    let (fsA, msA, termsA, namesA, numsA, tysA) := (at_ 4, at_ 5, at_ 6, at_ 7, at_ 8, at_ 9)
    let (rA, EA, dvA) := (at_ 10, at_ 11, at_ 12)
    let eA (Γ : List Tree) : Term := listNode [hA Γ, nA Γ, XA Γ]
    let xpA (Γ : List Tree) : Term := pc P "Datatype.xpStep" [xpState (dvA Γ) nil, eA Γ]
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [nA Γ]
    let valA (Γ : List Tree) : Term := pc P "Prelude.get" [pc P "Reader.numOf" [numsA Γ, XA Γ]]
    let E'A (Γ : List Tree) : Term := pc P "Typing.withNums" [EA Γ,
      namesSnoc P (pc P "Typing.envNums" [EA Γ]) (pc P "Typing.atomName" [nA Γ])]
    let nums'A (Γ : List Tree) : Term := consT treeTy (abbrevT P (nmA Γ) (valA Γ)) (numsA Γ)
    let s'A (Γ : List Tree) : Passes := ⟨esA Γ, dvA Γ, E'A Γ, pc P "Typing/OName.nothing" [],
      tysA Γ, nums'A Γ, namesA Γ, termsA Γ, msA Γ, fsA Γ, none, none⟩
    let restA (Γ : List Tree) : Passes := { s'A Γ with env := EA Γ, rej := rA Γ }
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ
    let unfoldBoth := unfoldBothK K
    let (hNoDef, hNoType, hKw, hUser, hX, hC, hO, hR, hK, hRej, hGlob, hNames, hLen, hRecs,
        hP, hOcc, hIns, hUsed) :=
      (4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 19, 20, 21, 22, 23)
    let (hOrigin, hSorts, hAl, hAlKw, hAlTys, hMs, hMk, hStatic, hMore) :=
      (24, 25, 26, 27, 28, 29, 30, 31, 32)
    -- the head's tests decided, as the test of the definitions' bodies reads them
    let heads : Deducer → Deducer := decideEach K Γ₀.length
      [(headNamed P (v 2) "Datatype.kwData", none, some (refuteNot K 2)),
        (headNamed P (v 2) "Datatype.kwTreeData", none, some (refuteNot K 3)),
        (headNamed P (v 2) "Reader.kwDef", none, some (refuteNot K 4)),
        (headNamed P (v 2) "Reader.kwDeftype", none, some (refuteNot K 5)),
        (headNamed P (v 2) "Reader.kwDefnum", some (K.hypFalse 6), none)]
    -- the hypothesis on the forms after, at the states the steps leave
    let apply (iNotNum iO iUnres iAtom iNum : ℕ) : Deducer := at' "the forms after" <|
      normHyps K [hOcc] <| K.conjE <| last fun iOccRest ↦
      normHyps K [hMk] <| K.conjE <| last fun iMkRest ↦ fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 ((s'A Γ).dv) (
        K.allEΓ (fun Γ ↦ (s'A Γ).env) <| K.allEΓ (fun Γ ↦ (s'A Γ).rej) <|
        K.allEΓ (fun Γ ↦ (s'A Γ).tys) <| K.allEΓ (fun Γ ↦ (s'A Γ).nums) <|
        K.allEΓ (fun Γ ↦ (s'A Γ).names) <| K.allEΓ (fun Γ ↦ (s'A Γ).terms) <|
        K.allEΓ (fun Γ ↦ (s'A Γ).ms) <| K.allEΓ (fun Γ ↦ (s'A Γ).fs) <|
        last fun iIH ↦ impEs L iIH
          [stage "stepDefnum: the rest expands" (K.byHyp hX),
            stage "stepDefnum: the rest checks" (K.byHyp hC),
            stage "stepDefnum: the rest's recognizers" (hypOr iO),
            stage "stepDefnum: the rest reads" (K.byHyp hR),
            stage "stepDefnum: the kernel checks" (K.byHyp hK),
            stage "stepDefnum: no rejection" (dImpI L (lastFalse K)),
            stage "stepDefnum: related after" (unfoldBoth (T.q + 2) hGlob),
            stage "stepDefnum: the numerals after" (applyThm K "numsExtend"
              (fun Γ ↦ [valA Γ, nmA Γ, numsA Γ, EA Γ])
              [dHyp, stage "stepDefnum: an atom" (K.byHyp iAtom),
                stage "stepDefnum: a numeral" (K.byHyp iNum)] (last K.byHyp)),
            stage "stepDefnum: the names" (hypOr hNames),
            stage "stepDefnum: the keywords after" (applyThm K "kwsExtend"
              (fun Γ ↦ [valA Γ, nmA Γ, numsA Γ])
              [dHyp, stage "stepDefnum: not reserved" (hypOr iUnres),
                stage "stepDefnum: a user's name" (hypOr hUser),
                stage "stepDefnum: no numeral" (dImpI L fun Γ Φ ψ ↦
                  normHyps K [iNotNum] (K.hypFalse (Φ.length - 1)) Γ Φ ψ)] (last K.byHyp)),
            stage "stepDefnum: the lengths" (hypOr hLen),
            stage "stepDefnum: the recognizers" (unfoldBoth (T.q + 6 + 2 * nFolds) hRecs),
            stage "stepDefnum: the bodies after" (K.byHyp hP),
            stage "stepDefnum: the occurrences after" (hypOr iOccRest),
            stage "stepDefnum: the recognizers referred to" (hypOr hIns),
            stage "stepDefnum: the names' occurrences" (hypOr hUsed),
            stage "stepDefnum: the names' origin" (hypOr hOrigin),
            stage "stepDefnum: no sort" (hypOr hSorts),
            stage "stepDefnum: the aliases" (hypOr hAl),
            stage "stepDefnum: the aliases of types read first" (hypOr hAlKw),
            stage "stepDefnum: the aliases abbreviated" (hypOr hAlTys),
            stage "stepDefnum: the markers" (normHyps K [hMs] K.byNorm),
            stage "stepDefnum: the markers that remain" (hypOr iMkRest),
            stage "stepDefnum: the markers and the numerals" (hypOr hStatic),
            stage "stepDefnum: the rest's kinds" (hypOr hMore)] <|
        stage "stepDefnum: the conclusion" (last K.byHyp)) Γ Φ ψ
    -- the reader's step
    let reader (iNotNum : ℕ) : Deducer := at' "the reader" <|
      applyThm K "eraseOther" (fun Γ ↦ [XA Γ, nA Γ, hA Γ])
        [stage "stepDefnum: no definition" dHyp] <| last fun iErase ↦ normHyps K [iErase] <|
      applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
        [stage "stepDefnum: the recognizers' insertion" (K.byHyp hO)] <| last fun iO ↦
      applyThm K "readPrefix" (fun Γ ↦ [rsA Γ, pc P "Reader.progStep" [stA Γ, eA Γ]])
        [stage "stepDefnum: the reader's run" (K.byHyp hR)] <| at' "the reader's step" <|
      applyThm K "readDefnum" (fun Γ ↦ [XA Γ, nA Γ, hA Γ, termsA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "stepDefnum: the reader's test of a definition" (K.byHyp hNoDef),
          stage "stepDefnum: the reader's test of a type" (K.byHyp hNoType),
          stage "stepDefnum: the reader's keyword" (K.byHyp hKw),
          stage "stepDefnum: the reader's step" dHyp] <|
      K.conjE <| K.conjE <| K.conjE <| fun Γ₅ Φ₅ ψ₅ ↦
        let (iAtomN, iFresh, iSome, iRead) :=
          (Φ₅.length - 6, Φ₅.length - 4, Φ₅.length - 2, Φ₅.length - 1)
        normHyps K [iRead] (
          decideIn K (fun Γ ↦ pc P "Reader.isAtom" [nA Γ]) (K.hypFalse iAtomN) <|
          at' "the name fresh" <|
          applyThm K "freshParts" (fun Γ ↦ [nmA Γ, namesA Γ, numsA Γ, tysA Γ])
            [stage "stepDefnum: fresh" (hypOr iFresh)] <| K.conjE <| last fun iParts ↦
          applyThm K "numOfParts" (fun Γ ↦ [XA Γ, numsA Γ])
            [stage "stepDefnum: abbreviates" (hypOr iSome)] <| K.conjE <| fun Γ Φ ψ ↦
          apply iNotNum iO (iParts - 1) (Φ.length - 2) (Φ.length - 1) Γ Φ ψ) Γ₅ Φ₅ ψ₅
    -- the typing's step
    let typing : Deducer := at' "the typing" <|
      applyThm K "checkPrefix" (fun Γ ↦ [(restA Γ).others P X₀,
          checkStepAt P (EA Γ) (rA Γ) (eA Γ)])
        [stage "stepDefnum: the typing's run" (K.byHyp hC)] <| at' "the typing's step" <|
      applyThm K "checkDefnum" (fun Γ ↦ [XA Γ, nA Γ, hA Γ, rA Γ, EA Γ])
        [stage "stepDefnum: the typing's test of a definition" (K.byHyp hNoDef),
          stage "stepDefnum: the typing's test of a type" (K.byHyp hNoType),
          stage "stepDefnum: the typing's keyword" (K.byHyp hKw),
          stage "stepDefnum: no rejection before" (hypOr hRej),
          stage "stepDefnum: the typing's step" dHyp] <|
      K.conjE <| fun Γ Φ ψ ↦
        let (iNotNum, iCheck) := (Φ.length - 2, Φ.length - 1)
        normHyps K [iCheck] (reader iNotNum) Γ Φ ψ
    -- the expansion's step
    let expansion : Deducer := at' "the expansion" <|
      applyThm K "xpPrefix" (fun Γ ↦ [esA Γ, xpA Γ])
        [stage "stepDefnum: the expansion's run" (K.byHyp hX)] <|
      at' "the expansion's step" <|
      applyThm K "xpDefnum" (fun Γ ↦ [XA Γ, nA Γ, hA Γ, nil, dvA Γ])
        ((List.replicate 5 dHyp).map (stage "stepDefnum: the head")) <|
      last fun iStep ↦ normHyps K [iStep] <| at' "the typed forms" <|
      applyThm K "typedFormsCons" (fun Γ ↦ [eA Γ, dvA Γ, esA Γ]) [] <| K.conjE <|
      fun Γ₃ Φ₃ ψ₃ ↦
        let (iFlag, iImp) := (Φ₃.length - 2, Φ₃.length - 1)
        normHyps K [iFlag] (
          dImpE L iImp (stage "stepDefnum: the rest's expansion" (K.byHyp hX)) <|
          last fun iTF ↦ normHyps K [iTF] typing) Γ₃ Φ₃ ψ₃
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric")
        (heads expansion)
        (stage "stepDefnum: a template's instance" (refuteNot K 1)) a.ctx a.hyps a.concl
      | dbgTrace "stepDefnum: not proved" fun _ ↦ none
    pure (a, d))

/-- The typing's node of a template's instance over its forms. -/
def genericNode (gs : Term) : Term := nodeT (Term.pair (numeral 15) gs)

/-- The expansion's step at a template's instance, from a state that has not failed, where the
state it leaves has not: the state left has the declarations and the typing's node of an
instance over some forms. The instance's step unfolded, the run of its forms failed or not: the
forms are those the state left has written. In the context of the form and the declarations. -/
def xpGeneric (P : Prog) (S : Defs) : Step :=
  ("xpGeneric", fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++ ["Datatype.xpStep"] }, S, E, ix, []⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let step := xpStepT P (xpState (v 1) nil) (v 0)
    let a : Internal.Thm := ⟨0, [treeTy, Ls], [genericT P (v 0), truth P.o (Term.fst step)],
      Internal.Logic.ex P.o Ls (Term.lam Ls (Term.eq (sh 1 step)
        (xpState (v 2) (consT treeTy (genericNode (v 0)) nil))))⟩
    -- the forms written, read off the state the step leaves
    let written (Γ : List Tree) : Term := call D.children []
      [pc P "Datatype.nthTx" [Term.snd (Term.snd (sh (Γ.length - 2) step)), leafT bnilT]]
    let close : Deducer := fun Γ Φ ψ ↦
      (K.hypFalse 1 Γ Φ ψ).orElse fun _ ↦
        dExI L K.G K.E (written Γ) (stage "xpGeneric: the state left" K.byNorm) Γ Φ ψ
    let some d := (dConjE L 0 <| decideEach K 2
        ((genericTest P (v 0)).zipIdx.map fun (t, i) ↦ (t, some (K.hypFalse (2 + i)), none))
        (splitCond K 2 step 1 close)) a.ctx a.hyps a.concl
      | dbgTrace "xpGeneric: not proved" fun _ ↦ none
    pure (a, d))

/-- The typing's run from a state without a rejection over a template's instance before forms is
its run over the forms from the state of the environment and the rejection of the instance's
forms' run: the rejection's test decided. In the context of the forms, the instance's forms, the
rejection and the environment. -/
def checkGeneric (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkGeneric", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, Ls, treeTy, T.envTy]
    let (fs, g, r, Ev) := (v 0, v 1, v 2, v 3)
    let s := Term.pair Ev r
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let a : Internal.Thm := ⟨0, Γ, [notTest P.o (isSome r)],
      Term.eq (pc P "Typing.checkAll" [s, consT treeTy (genericNode g) fs])
        (pc P "Typing.checkAll" [Term.pair Ev (Term.snd (pc P "Typing.checkRun" [s, g])), fs])⟩
    let some d := decideEach K Γ.length [(isSome r, none, some (refuteNot K 0))]
        (linkK K "checkGeneric: checked" (K.solve 4)) a.ctx a.hyps a.concl
      | dbgTrace "checkGeneric: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at the forms that remain after a template's instance, a step of the soundness
at all states ({name}`passesφ`): the expansion's step ({name}`xpGeneric`) keeps the declarations
and writes the typing's node of the instance; the typing's run ({name}`checkGeneric`) keeps the
environment, with the rejection of the instance's forms' run, which is none
({lit}`checkPrefix`); and the kernel's forms drop the node, so that the reader's state is that
before. The hypothesis on the forms after, at those states, gives the conclusion. In the context
of the form, the forms after and the states. -/
def stepGeneric (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepGeneric", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"stepGeneric @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "stepGeneric: no partition" fun _ ↦ none
    let s := passesAt 2 (consT treeTy (v 0) (v 1))
    let hyps := [Internal.instTerm [] [v 1] (passesφ P S T X₀ (formsOk P S)), genericT P (v 0)] ++
      s.hyps P S T X₀ ++ formsOk P S (v 1)
    let Γ₀ := [treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (eA, esA, fsA, msA, termsA, namesA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let (numsA, tysA, rA, EA, dvA) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
    let stepA (Γ : List Tree) : Term := xpStepT P (xpState (dvA Γ) nil) (eA Γ)
    let restA (Γ : List Tree) : Passes := passesAt (2 + (Γ.length - Γ₀.length)) (esA Γ)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let nInv := (s.hyps P S T X₀).length
    let (hGen, hX, hC, hO, hR, hK, hRej, hMore) := (1, 2, 3, 4, 5, 6, 7, 2 + nInv)
    -- the instance's tests decided, as the test of the definitions' bodies reads them
    let heads : Deducer → Deducer := fun k ↦ dConjE L hGen fun Γ Φ ψ ↦
      decideEach K Γ₀.length ((genericTest P (v 0)).zipIdx.map fun (t, i) ↦
        (t, some (K.hypFalse (Φ.length - 2 + i)), none)) k Γ Φ ψ
    let some d := (heads <| at' "the expansion" <|
        applyThm K "xpPrefix" (fun Γ ↦ [esA Γ, stepA Γ])
          [stage "stepGeneric: the expansion's run" (K.byHyp hX)] <|
        applyThm K "xpGeneric" (fun Γ ↦ [eA Γ, dvA Γ])
          [stage "stepGeneric: an instance" (hypOr hGen),
            stage "stepGeneric: the expansion's step" (lastOr K)] <|
        K.exE <| fun Γ₁ Φ₁ ψ₁ ↦
        -- the instance's forms, the variable after the theorem's
        let n₁ := Γ₁.length
        let gA (Γ : List Tree) : Term := v (Γ.length - n₁)
        let fA (Γ : List Tree) : Term := genericNode (gA Γ)
        let r'A (Γ : List Tree) : Term :=
          Term.snd (pc P "Typing.checkRun" [Term.pair (EA Γ) (rA Γ), gA Γ])
        let iStep := Φ₁.length - 1
        (normHyps K [iStep] <| at' "the typed forms" <|
          applyThm K "typedFormsCons" (fun Γ ↦ [fA Γ, dvA Γ, esA Γ]) [] <| K.conjE <|
          fun Γ₃ Φ₃ ψ₃ ↦
            let (iFlag, iImp) := (Φ₃.length - 2, Φ₃.length - 1)
            normHyps K [iFlag] (
              dImpE L iImp (stage "stepGeneric: the rest's expansion" (K.byHyp hX)) <|
              last fun iTF ↦ normHyps K [iTF] <| at' "the typing" <|
              applyThm K "checkGeneric"
                (fun Γ ↦ [(restA Γ).others P X₀, gA Γ, rA Γ, EA Γ])
                [stage "stepGeneric: no rejection before" (hypOr hRej)] <|
              last fun iChk ↦ normHyps K [iChk] <|
              applyThm K "checkPrefix"
                (fun Γ ↦ [(restA Γ).others P X₀, Term.pair (EA Γ) (r'A Γ)])
                [stage "stepGeneric: the typing's run" (K.byHyp hC)] <|
              last fun iRej' ↦ at' "the forms after" <| fun Γ Φ ψ ↦
              dAllE L K.G K.E 0 (dvA Γ) (
                K.allEΓ EA <| K.allEΓ r'A <| K.allEΓ tysA <| K.allEΓ numsA <|
                K.allEΓ namesA <| K.allEΓ termsA <| K.allEΓ msA <| K.allEΓ fsA <|
                last fun iIH ↦ impEs L iIH
                  ([stage "stepGeneric: the rest expands" (K.byHyp hX),
                    stage "stepGeneric: the rest checks" (K.byHyp hC),
                    stage "stepGeneric: the rest's recognizers" (K.byHyp hO),
                    stage "stepGeneric: the rest reads" (K.byHyp hR),
                    stage "stepGeneric: the kernel checks" (K.byHyp hK),
                    stage "stepGeneric: no rejection" (K.byHyp iRej')] ++
                  (List.range (nInv - 6)).map (fun k ↦
                    stage s!"stepGeneric: the invariant {k}" (hypOr (hRej + 1 + k))) ++
                  [stage "stepGeneric: the rest's kinds" (hypOr hMore)]) <|
                stage "stepGeneric: the conclusion" (last K.byHyp)) Γ Φ ψ) Γ₃ Φ₃ ψ₃) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "stepGeneric: not proved" fun _ ↦ none
    pure (a, d))

/-- A form at which the expansion's step does not fail, and of which the soundness's assumptions
hold ({name}`preOk`), is of a kind the soundness reads ({name}`formOk`): the form a node, a list
by its label, else the step fails; its elements split by cases; the head's tests decided in the
order the step reads them: a template's instance; a datatype's declaration, the list of the
head, the datatype's atom and the elements after them, of which the soundness's assumptions
are those of the declaration, its reading failing where it has no atom; the tree datatypes'
keyword, refuted; a function, of five elements; a definition, a type abbreviation or a numeral
abbreviation, of three; any other head or number of elements fails the step, a list of more
elements having a length that is none of those ({lit}`neq5`). In the context of the form and the
declarations. -/
def formKind (P : Prog) (S : Defs) : Step :=
  ("formKind", fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++
      ["Datatype.dataDecl", "Datatype.marker", "Datatype.genericStep"] }, S, E, ix,
      ["neq4", "neq5"]⟩
    let L := K.L
    let Ls := list treeTy
    let hyps := [truth P.o (Term.fst (xpStepT P (xpState (v 1) (nilT treeTy)) (v 0)))] ++
      preOk P S (v 0)
    let a : Internal.Thm := ⟨0, [treeTy, Ls], hyps, formOk P S (v 0)⟩
    -- the disjunct of an index, of the kinds in the order of the disjunction
    let inj (i : ℕ) (k : Deducer) : Deducer :=
      (List.range i).foldr (fun _ k ↦ dDisjI L true k) (if i < 5 then dDisjI L false k else k)
    let conjs (ds : List Deducer) : Deducer := match ds.reverse with
      | [] => K.solve 1
      | d :: rest => rest.foldl (fun acc p ↦ dConjI L p acc) d
    let no : Deducer := dImpI L (lastFalse K)
    let yes : Deducer := K.solve 3
    -- a kind's disjunct at the elements: the form's equation and the head's facts
    let kind (i : ℕ) (xs : List (List Tree → Term)) (facts : List Deducer) : Deducer :=
      stage s!"formKind: the kind {i}" <| inj i <|
        xs.foldr (fun w k Γ Φ ψ ↦ dExI L K.G K.E (w Γ) k Γ Φ ψ)
          (conjs ([stage "formKind: the form's equation" K.byNorm] ++ facts))
    let userAt (h : ℕ) : Deducer := dImpE L h (K.solve 3) (lastOr K)
    let user : Deducer := userAt 3
    -- the head's tests in the step's order, at a list of m elements at the positions given
    -- the rules with a datatype's declaration's reading unfolded
    let Kd : Kit := { K with
      P := { K.P with folded := K.P.folded.filter (· != "Datatype.dataDecl") } }
    let chain (m : ℕ) (ps : List ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let xs := ps.map fun p Γ ↦ atPos p Γ
      let h := xs.headD fun _ ↦ Term.star
      let t (kw : String) (Γ : List Tree) : Term := headNamed P (h Γ) kw
      let fail := stage s!"formKind: the step at {m} elements" (K.hypFalse 0)
      let k₆ := decideIn K (t "Reader.kwDefnum") fail
        (if m = 3 then kind 2 xs [no, no, no, no, no, yes, user] else fail)
      let k₅ := decideIn K (t "Reader.kwDeftype") k₆
        (if m = 3 then kind 1 xs [no, no, no, no, yes] else k₆)
      let k₄ := decideIn K (t "Reader.kwDef") k₅
        (if m = 3 then kind 0 xs [no, no, no, yes, userAt 4] else k₅)
      let k₃ := decideIn K (t "Datatype.kwDefn") k₄
        (if m = 5 then kind 3 xs [no, no, no, yes, userAt 5] else k₄)
      let k₂ := decideIn K (t "Datatype.kwTreeData") k₃ (refuteNot K 2)
      -- a datatype's declaration: the head, the datatype's atom, and the elements after them,
      -- with the tail where the elements are split no further
      let cs (Γ : List Tree) : Term := (xs.drop 2).foldr (fun w acc ↦ consT treeTy (w Γ) acc)
        (if m = 6 then atPos (Γ₀.length - 1) Γ else nilT treeTy)
      let data : Deducer :=
        if m < 2 then stage "formKind: a declaration without an atom" (Kd.hypFalse 0)
        else dImpE L 1 (K.solve 3) <| K.conjE <| fun Γ Φ ψ ↦
          let n := Φ.length
          kind 5 (xs.take 2 ++ [cs])
            [no, yes, stage "formKind: the constructors' names" (K.byHyp (n - 2)),
              stage "formKind: the recognizer's name" (K.byHyp (n - 1))] Γ Φ ψ
      let k₁ := decideIn K (t "Datatype.kwData") k₂ data
      (if m = 0 then fail else
      decideIn K (t "Datatype.kwGeneric") k₁
        (stage "formKind: an instance" (inj 4 (conjs [yes, yes])))) Γ₀ Φ₀ ψ₀
    -- the elements split by cases, the tail the innermost variable: to six elements and a tail
    let split : ℕ → List ℕ → Deducer := Nat.rec (motive := fun _ ↦ List ℕ → Deducer)
      (fun ps ↦ chain 6 ps)
      (fun _ rec ps Γ Φ ψ ↦ K.listCase treeTy (v 0) (chain ps.length ps)
        (fun Γ' Φ' ψ' ↦ rec (ps ++ [Γ'.length - 2]) Γ' Φ' ψ') Γ Φ ψ)
    let some d := (K.treeNode (v 0) fun Γ₁ Φ₁ ψ₁ ↦
        let pcs := Γ₁.length - 1
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 2 then fun Γ Φ ψ ↦
            K.listCase treeTy (atPos pcs Γ) (chain 0 [])
              (fun Γ' Φ' ψ' ↦ split 5 [Γ'.length - 2] Γ' Φ' ψ') Γ Φ ψ
          else stage "formKind: no list" (K.hypFalse 0)) 3 [] (v 1) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "formKind: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at all states of forms of which its assumptions hold ({name}`passesφ`,
{name}`formsOk`): by induction on the forms. None: the passes' runs leave the states, at which
the conclusion is the invariant's relation of the definitions, and the recognizers' agreement
the invariant's. A construction: the head's kind
and its parts, from the expansion's step at it, which does not fail ({lit}`xpPrefix`,
{name}`formKind`), and the hypothesis on the forms; the step at a form of that kind
({name}`stepDef`, {name}`stepDeftype`, {name}`stepDefnum`, {name}`stepDefn`,
{name}`stepGeneric`, {lit}`stepData`). In the context of the forms. -/
def passesForms (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("passesForms", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "passesForms: no partition" fun _ ↦ none
    let φ := passesφ P S T X₀ (formsOk P S)
    let nVars := (passesCtx T).length
    let nHyps := ((passesAt 0 (v 9)).hyps P S T X₀).length + 1
    let intro (k : Deducer) : Deducer := repeatK nVars (dAllI L) (repeatK nHyps (dImpI L) k)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ
    -- no forms: the states' variables, from the outermost the declarations first
    let base : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let h (k : ℕ) : ℕ := Φ₁.length - nHyps + k
      dConjI L (stage "passesForms: none, the markers" K.byNorm) (dConjI L
        (stage "passesForms: none, related" (K.byHyp (h 6)))
        (stage "passesForms: none, the recognizers" (K.byHyp (h 11)))) Γ₁ Φ₁ ψ₁
    -- a construction: the head and the tail outermost, then the states' variables
    let step : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let h (k : ℕ) : ℕ := Φ₁.length - nHyps + k
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (esA, hA, nA, xA) := (at_ 1, at_ 11, at_ 12, at_ 13)
      let states (Γ : List Tree) : List Term := (List.range nVars).map fun j ↦ at_ (10 - j) Γ
      let σ (Γ : List Tree) : List Term := [xA Γ, nA Γ, hA Γ, esA Γ] ++ states Γ
      -- a function's parts: the body, the result type, the binders, the name and the head
      let σ₅ (Γ : List Tree) : List Term :=
        [at_ 15 Γ, at_ 14 Γ, at_ 13 Γ, at_ 12 Γ, at_ 11 Γ, esA Γ] ++ states Γ
      let invariant : List Deducer := (List.range (nHyps - 1)).map fun k ↦
        stage s!"passesForms: the hypothesis {k}" (hypOr (h k))
      (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ (h (nHyps - 1))) .full) (h (nHyps - 1))
        (stage "passesForms: the forms" <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iPre, iRest) := (Φ₂.length - 2, Φ₂.length - 1)
        -- the form's parts: its equation and the facts of its kind, of m conjuncts in all
        let parts (m : ℕ) (k : ℕ → Deducer) (vars : ℕ := 3) : Deducer := repeatK vars K.exE <|
          repeatK (m - 1) K.conjE fun Γ Φ ψ ↦ k Φ.length Γ Φ ψ
        let facts (n m : ℕ) : List Deducer :=
          ((List.range (m - 2)).map (fun i ↦ n - 2 * (m - 2 - i)) ++ [n - 1]).map fun i ↦
            stage s!"passesForms: the fact {i}" (K.byHyp i)
        let ih : Deducer := stage "passesForms: the hypothesis" (hypOr 0)
        let rest : Deducer := stage "passesForms: the rest's kinds" (K.byHyp iRest)
        let done : Deducer := stage "passesForms: the conclusion" (last K.byHyp)
        (dConjE L iPre <| K.conjE <| K.conjE <| K.conjE <| fun Γ₃ Φ₃ ψ₃ ↦
        let (iData, iTree, iNum) := (Φ₃.length - 8, Φ₃.length - 6, Φ₃.length - 4)
        let (iDef, iDefn) := (Φ₃.length - 2, Φ₃.length - 1)
        (applyThm K "xpPrefix" (fun Γ ↦ [esA Γ,
            xpStepT P (xpState (at_ 2 Γ) (nilT treeTy)) (at_ 0 Γ)])
          [stage "passesForms: the expansion's run" (K.byHyp (h 0))] <|
        applyThm K "formKind" (fun Γ ↦ [at_ 0 Γ, at_ 2 Γ])
          [stage "passesForms: the expansion's step" (lastOr K),
            stage "passesForms: a datatype's declaration's parts" (hypOr iData),
            stage "passesForms: no tree datatype" (hypOr iTree),
            stage "passesForms: the abbreviation's name" (hypOr iNum),
            stage "passesForms: the definition's name" (hypOr iDef),
            stage "passesForms: the function's name" (hypOr iDefn)] <|
        fun Γ₄ Φ₄ ψ₄ ↦ dDisjE L (Φ₄.length - 1)
          (stage "passesForms: a definition" <| parts 6 fun n ↦ applyThm K "stepDef" σ
            ([ih] ++ facts n 6 ++ invariant ++ [rest]) done)
          (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
            (stage "passesForms: a type abbreviation" <| parts 6 fun n ↦
              applyThm K "stepDeftype" σ ([ih] ++ facts n 6 ++ invariant ++ [rest]) done)
            (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
              (stage "passesForms: a numeral abbreviation" <| parts 8 fun n ↦
                applyThm K "stepDefnum" σ ([ih] ++ facts n 8 ++ invariant ++ [rest]) done)
              (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
                (stage "passesForms: a function" <| parts 6 (vars := 5) fun n ↦
                  applyThm K "stepDefn" σ₅ ([ih] ++ facts n 6 ++ invariant ++ [rest]) done)
                (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
                  (stage "passesForms: a template's instance" <|
                    applyThm K "stepGeneric" (fun Γ ↦ [at_ 0 Γ, esA Γ] ++ states Γ)
                      ([ih, stage "passesForms: an instance" (lastOr K)] ++ invariant ++
                        [rest]) done)
                  (stage "passesForms: a datatype's declaration" <| parts 5 fun n ↦
                    applyThm K "stepData" σ ([ih] ++ facts n 5 ++ invariant ++ [rest]) done)
                  Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)
            Γ Φ ψ) Γ₄ Φ₄ ψ₄) Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    listInduction "passesForms" φ base step)

/-- A defined predicate that quantifies over a tree, proved at arguments at which the
quantification's body is refuted or proved by {lit}`k` once unfolded: the statement in a
context, with hypotheses, the first normalized. -/
def unfolded (P : Prog) (S : Defs) (name : String) (idx : ℕ) (more : List String)
    (extra : List Internal.NormRule) (a : Internal.Thm) (k : Kit → Deducer) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, more⟩
    let some d := (dRwBy (evalRw K.G K.E [.delta idx] .head) <|
        (if a.hyps.isEmpty then id else normHyps K [0]) <| dAllI K.L <|
        fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (K.rules Φ ++ extra) .full) (k K) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The definitions' relation holds of no names and an environment without definitions: no name
has a type. In the context of the environment and the relation's context. -/
def globEmpty (P : Prog) (S : Defs) (T : Defs3) : Step :=
  unfolded P S "globEmpty" (T.q + 2) lookupEqNames []
    ⟨0, [T.envTy, Defs3.ctxTy], [Term.eq (pc P "Typing.envDefs" [v 0]) (nilT treeTy)],
      T.globT (v 1) (v 0) (nilT treeTy)⟩
    fun K ↦ dImpI K.L (lastFalse K)

/-- The numeral abbreviations' coherence holds of none and an environment without numeral
names. In the context of the environment. -/
def numsEmpty (P : Prog) (S : Defs) (T : Defs3) : Step :=
  unfolded P S "numsEmpty" (T.q + 3 + 2 * nFolds) []
    [.delta (P.idx "Typing.hasName"), .delta (P.idx "Reader.lookupAbbrev")]
    ⟨0, [T.envTy], [Term.eq (pc P "Typing.envNums" [v 0]) (nilT treeTy)],
      T.numsT (v 0) (nilT treeTy)⟩
    fun K ↦ dConjI K.L (dImpI K.L (lastFalse K)) (dImpI K.L (lastFalse K))

/-- No names are names of definitions. -/
def namesEmpty (P : Prog) (S : Defs) (T : Defs3) : Step :=
  unfolded P S "namesEmpty" (T.q + 4 + 2 * nFolds) lookupEqNames []
    ⟨0, [], [], T.namesT (nilT treeTy)⟩ fun K ↦ dImpI K.L (lastFalse K)

/-- No numeral abbreviations abbreviate a keyword. -/
def kwsEmpty (P : Prog) (S : Defs) (T : Defs3) : Step :=
  unfolded P S "kwsEmpty" (T.q + 5 + 2 * nFolds) [] [.delta (P.idx "Reader.lookupAbbrev")]
    ⟨0, [], [], T.kwsT (nilT treeTy)⟩ fun K ↦ dImpI K.L (lastFalse K)

/-- The hypotheses and the conclusion of the soundness of a program at its forms, as the
compiler's passes run on them: the forms expand to typed forms, whose typing with their markers
first rejects none, the recognizers their erasures refer to can be written, the reader reads the
forms they give, and the kernel types the terms; the definitions with the typing environment's
markers are then related to the environment's definitions by the reader's names, and its
recognizers decide membership. -/
def programParts (P : Prog) (T : Defs3) (es : Term) : Option (List Term × Term) := do
  let o := P.o
  let childT ← primT Kernel.Prim.child
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let kids (t : Term) : Term := call D.children [] [t]
  let ch (t : Term) (i : ℕ) : Term := apps childT [t, leafT (numeral i)]
  let x := pc P "Datatype.expandTyped" [es]
  let ts := Term.snd x
  let nothing := pc P "Typing/OName.nothing" []
  let run := pc P "Typing.checkAll" [Term.pair (pc P "Typing.env0" []) nothing,
    pc P "Datatype.markersFirst" [ts]]
  let Ev := Term.fst run
  let r := pc P "Recognize.insertRecognizers" [pc P "Datatype.kernelForms" [ts]]
  let b := pc P "Reader.readProgram" [kids (get r)]
  let terms := kids (ch (get b) 0)
  let names := kids (ch (get b) 1)
  let R := Term.pair terms (pc P "Typing.envMs" [Ev])
  pure ([truth o (Term.fst x), Term.eq (Term.snd run) nothing, isSomeT r, isSomeT b,
      isSomeT (pc P "Check.checkProgram" [terms])],
    Internal.Logic.conj o (T.globT R Ev names) (T.recsT R Ev names))

/-- The states the passes begin in, at a program's forms: no declarations, the environment of
the program's markers, no rejection, no abbreviations, names or terms, and the markers and the
kernel forms of the program. -/
def initialPasses (P : Prog) (X₀ es : Term) : Passes :=
  let nil := nilT treeTy
  let ts := typedForms P es nil
  let fs := pc P "Datatype.kernelForms" [ts]
  ⟨es, nil, pc P "Typing.withMs" [pc P "Typing.env0" [],
      txsApp P nil (Term.fst (Term.subst X₀ fun _ ↦ ts))], pc P "Typing/OName.nothing" [],
    nil, nil, nil, nil, pc P "Recognize.markers" [fs], fs, none, none⟩

/-- That each definition's body the expansion writes for a program's forms is a source form at
the numeral abbreviations before it: the run of the test of the definitions' bodies over the
forms, from no declarations and no abbreviations, ends without a failure. -/
def plainTop (P : Prog) (es : Term) : Term :=
  truth P.o (Term.fst (plainRun P es (plainState (nilT treeTy) (nilT treeTy))))

/-- The soundness of a program ({name}`programParts`) whose definitions' bodies are source forms
({name}`plainTop`) from the soundness at the states the passes begin in
({name}`initialPasses`), a hypothesis. The typing's run over the forms with
their markers first is its run over the others from the environment of the markers
({lit}`checkAllAppend`, {lit}`markersRun`); the recognizers' insertion and the reader's
program, where present, are the insertion's test and the reader's run; and the invariant holds
of the states before any form. In the context of the forms. -/
def programTop (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("programTop", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "programTop: no partition" fun _ ↦ none
    let (hs, concl) ← programParts P T (v 0)
    let s := initialPasses P X₀ (v 0)
    let passes := (s.hyps P S T X₀).foldr (Internal.Logic.imp P.o) (s.concl P T X₀)
    let assumed := [S.allL (markerPred P s.ms) (pc P "Datatype.kernelForms" [s.typed P]),
      staticT P s.ms]
    let a : Internal.Thm := ⟨0, [Ls], hs ++ [plainTop P (v 0)] ++ assumed ++ [passes], concl⟩
    let s₀ (Γ : List Tree) : Passes := initialPasses P X₀ (v (Γ.length - 1))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let nothing := pc P "Typing/OName.nothing" []
    let env0 := pc P "Typing.env0" []
    let tsA (Γ : List Tree) : Term := (s₀ Γ).typed P
    let partA (Γ : List Tree) : Term := Term.subst X₀ fun _ ↦ tsA Γ
    let (hX, hC, hO, hR, hK, hPlain, hMk, hStatic, hPasses) := (0, 1, 2, 3, 4, 5, 6, 7, 8)
    let KL : Kit := { K with more := K.more ++ lookupEqNames }
    let noName : Deducer := dAllI L <| dImpI L <| fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++
        [.delta (P.idx "Typing.hasName")]) .full) (Φ.length - 1) (dFalse L dHyp) Γ Φ ψ
    let some d := (
        -- the typing's run: over the markers, then over the others
        K.cutThm "checkAllAppend" (fun Γ ↦ [Term.fst (partA Γ)]) <|
        K.allEΓ (fun Γ ↦ Term.snd (partA Γ)) <| K.allEΓ (fun _ ↦ Term.pair env0 nothing) <|
        last fun iApp ↦ K.cutThm "markersRun" (fun Γ ↦ [tsA Γ]) <| K.allEΓ (fun _ ↦ env0) <|
        K.allEΓ (fun _ ↦ nil) <| last fun iMs ↦ normHyps K [iApp, iMs] <|
        -- the recognizers' insertion's test and the reader's run's flag decided
        decideIn K (fun Γ ↦ Term.fst ((s₀ Γ).inserted P))
          (stage "programTop: the recognizers" (K.hypFalse hO)) <|
        decideIn K (fun Γ ↦ Term.fst ((s₀ Γ).read P))
          (stage "programTop: the reader" (K.hypFalse hR)) <|
        stage "programTop: the passes" <| fun Γ Φ ψ ↦
        let s := s₀ Γ
        (impEs L hPasses
            [stage "programTop: expands" (K.byHyp hX),
              stage "programTop: checks" (dImpI L fun Γ Φ ψ ↦
                normHyps K [hC] (K.hypFalse (Φ.length - 1)) Γ Φ ψ),
              stage "programTop: inserts" (K.solve 3),
              stage "programTop: reads" (K.solve 3),
              stage "programTop: kernel checks" (K.byHyp hK),
              stage "programTop: no rejection" (dImpI L (lastFalse K)),
              stage "programTop: related" (applyThm K "globEmpty"
                (fun _ ↦ [s.env, s.rel P]) [K.byNorm] (last K.byHyp)),
              stage "programTop: the numerals" (applyThm K "numsEmpty"
                (fun _ ↦ [s.env]) [K.byNorm] (last K.byHyp)),
              stage "programTop: the names" (K.cutThm "namesEmpty" (fun _ ↦ []) dHyp),
              stage "programTop: the keywords" (K.cutThm "kwsEmpty" (fun _ ↦ []) dHyp),
              stage "programTop: the lengths" K.byNorm,
              stage "programTop: the recognizers" (applyThm K "recsEmpty"
                (fun _ ↦ [s.env, s.rel P]) [] (last K.byHyp)),
              stage "programTop: the definitions' bodies" (hypOrK K hPlain),
              stage "programTop: the occurrences" (K.cutThm "occSelf" (fun _ ↦ [s.fs]) <|
                K.allEΓ (fun _ ↦ nil) <| last K.byHyp),
              stage "programTop: the recognizers referred to" noName,
              stage "programTop: the names' occurrences" (K.solve 3),
              stage "programTop: the names' origin" (K.solve 3),
              stage "programTop: no sort" noName,
              stage "programTop: the aliases" (dAllI L <| dConjI L
                (dImpI L <| dImpI L <| lastFalse KL) (dImpI L (lastFalse K))),
              stage "programTop: the aliases of types read first" (dConjI L
                (dImpI L (lastFalse K)) (dImpI L (lastFalse K))),
              stage "programTop: the aliases abbreviated" (dAllI L <| dImpI L (lastFalse K)),
              stage "programTop: the markers" (
                K.cutThm "markersKernel" (fun _ ↦ [s.typed P]) <| normLastK K <| K.byNorm),
              stage "programTop: the markers that remain" (hypOrK K hMk),
              stage "programTop: the markers and the numerals" (hypOrK K hStatic)] <|
          -- the final environment's markers the first's, then the conclusion
          K.conjE <| fun Γ Φ ψ ↦
          let (iMs', iC) := (Φ.length - 2, Φ.length - 1)
          normHyps K [iMs'] (stage "programTop: the conclusion" (K.byHyp iC)) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "programTop: not proved" fun _ ↦ none
    pure (a, d))

/-- The statement of the soundness of a program: the soundness's parts ({name}`programParts`)
under the hypotheses that the program's definitions' bodies are source forms ({name}`plainTop`),
that its markers and numerals are as the soundness assumes ({name}`markerPred`,
{name}`staticT`), and that the soundness's assumptions hold of its forms ({name}`formsOk`). In
the context of the forms. -/
def programFormsThm (P : Prog) (S : Defs) (T : Defs3) : Option Internal.Thm := do
  let (hs, concl) ← programParts P T (v 0)
  let fs := pc P "Datatype.kernelForms" [typedForms P (v 0) (nilT treeTy)]
  let ms := pc P "Recognize.markers" [fs]
  pure ⟨0, [list treeTy], hs ++ [plainTop P (v 0), S.allL (markerPred P ms) fs, staticT P ms] ++
    formsOk P S (v 0), concl⟩

/-- The soundness of a program ({name}`programFormsThm`): the soundness at all states
({name}`passesForms`) at the states the passes begin in, of which the program's soundness
follows ({name}`programTop`). -/
def programForms (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("programForms", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "programForms: no partition" fun _ ↦ none
    let (hs, _) ← programParts P T (v 0)
    let s := initialPasses P X₀ (v 0)
    let a ← programFormsThm P S T
    let n := (s.hyps P S T X₀).length
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    -- the soundness at the first states, from that at all states and the forms' kinds
    let passes : Deducer := K.cutThm "passesForms" (fun _ ↦ [v 0]) <|
      K.allEΓ (fun _ ↦ s.dv) <| K.allEΓ (fun _ ↦ s.env) <| K.allEΓ (fun _ ↦ s.rej) <|
      K.allEΓ (fun _ ↦ s.tys) <| K.allEΓ (fun _ ↦ s.nums) <| K.allEΓ (fun _ ↦ s.names) <|
      K.allEΓ (fun _ ↦ s.terms) <| K.allEΓ (fun _ ↦ s.ms) <| K.allEΓ (fun _ ↦ s.fs) <|
      last fun iP ↦ repeatK n (dImpI L) <|
        impEs L iP ((List.replicate (n + 1) dHyp).map (stage "programForms: a hypothesis")) dHyp
    let some d := applyThm K "programTop" (fun _ ↦ [v 0])
        ((List.replicate (hs.length + 3) dHyp).map (stage "programForms: the program") ++
          [stage "programForms: the passes" passes]) dHyp a.ctx a.hyps a.concl
      | dbgTrace "programForms: not proved" fun _ ↦ none
    pure (a, d))

/-- The statement of the soundness of a program as one formula without hypotheses
({name}`programFormsThm`): the hypotheses of the soundness imply its conclusion, in the context
of the forms. -/
def programClosedThm (P : Prog) (S : Defs) (T : Defs3) : Option Internal.Thm := do
  let a ← programFormsThm P S T
  pure ⟨0, a.ctx, [], a.hyps.foldr (Internal.Logic.imp P.o) a.concl⟩

/-- The soundness of a program as one formula without hypotheses ({name}`programClosedThm`):
the hypotheses introduced, the soundness of a program ({name}`programForms`) at the forms. -/
def programClosed (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("programClosed", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let a ← programFormsThm P S T
    let c ← programClosedThm P S T
    let n := a.hyps.length
    let some d := (repeatK n (dImpI L) <|
        applyThm K "programForms" (fun _ ↦ [v 0])
          ((List.replicate n dHyp).map (stage "programClosed: a hypothesis")) dHyp)
        c.ctx c.hyps c.concl
      | dbgTrace "programClosed: not proved" fun _ ↦ none
    pure (c, d))

/-- The development of the soundness of a program from that at the states its passes begin
in. -/
def programTopDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [globEmpty P S T, numsEmpty P S T, namesEmpty P S T, kwsEmpty P S T, programTop P S T]

/-- The development of the facts of the empty context. -/
def programEmptyDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [envNil P S T, cxNil P S T]

/-- The definition the expansion's reading of a constructor writes, where the constructor has no
variable field: the definition of the constructor's atom as the abstractions over its fields'
binders around the coercion to the datatype of the node of the constructor's position over the
fields' values, the term of the constructors' soundness
({name}`GebTests.Prototypes.FreeTopos.Datatypes.ctorPlain`). In the context of the fields'
types, the constructor's atom, its position and the datatype's name. -/
def ctorDeclPlain (P : Prog) (S : Defs) : Step :=
  ("ctorDeclPlain", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, treeTy, treeTy, treeTy]
    let (fs, nm, j, d) := (v 0, v 1, v 2, v 3)
    let ltT ← primT Kernel.Prim.lt
    let subT ← primT Kernel.Prim.sub
    let c := nodeT (Term.pair (numeral 2) (consT treeTy nm fs))
    let nr := pc P "Datatype/Txs.length" [fs]
    let more := apps ltT [leafT (numeral 1), nr]
    let amp := pc P "Datatype.namedTx"
      [pc P "Datatype.nthTx" [fs, apps subT [nr, leafT (numeral 2)]], pc P "Datatype.kwAmp" []]
    let z := pc P "Datatype.sx2" [pc P "Datatype.aNil" [], pc P "Datatype.aT" []]
    let cs := call D.children [] [d]
    let decl := pc P "Datatype.ctorDecl" [d, j, c]
    let a : Internal.Thm := ⟨0, Γ, [notTest P.o (pc P "Prelude.and" [more, amp])],
      Term.eq (Term.snd (Term.snd decl))
        (defForm P nm (nestT P (binderFold P nr fs) (ctorBody P cs j nr z fs)))⟩
    let written : Deducer := fun Γ' Φ ψ ↦ (K.byNorm Γ' Φ ψ).orElse fun _ ↦
      let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules Φ) .full Γ' Φ t).map Prod.fst
      let d := (Internal.eqParts ψ).bind fun (l, r) ↦
        (nf l).bind fun x ↦ (nf r).bind fun y ↦ firstDiff x y
      dbgTrace s!"ctorDeclPlain: {d.map fun (x, y) ↦ s!"{showT x}\n  vs {showT y}"}" fun _ ↦ none
    let at_ (t : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) t
    let some d := decideIn K (at_ more) written
        (decideIn K (at_ amp) written (refuteNot K 0)) a.ctx a.hyps a.concl
      | dbgTrace "ctorDeclPlain: not proved" fun _ ↦ none
    pure (a, d))

/-- A form sound at every context and environment, as the constructors' definitions are
({name}`GebTests.Prototypes.FreeTopos.Datatypes.formAllT`), is sound at states of the relation's
context, the typing environment and the reader's abbreviations and names given
({name}`soundAtT`): at the empty context and environment ({lit}`envNil`), the form typed and
resolved, it denotes a value related at its type, to which the resolved term converges. In the
context of the form, the kernel's types of the globals, the numeral abbreviations, the names,
the type abbreviations, the typing environment and the relation's context. -/
def soundOfFormAll (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("soundOfFormAll", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let Γ := [treeTy, Ls, Ls, Ls, Ls, T.envTy, Defs3.ctxTy]
    let (x, G, nums, names, tys, Ev, R) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let syn := pc P "Typing.synIn" [Ev, nil, x]
    let res := pc P "Reader.resolve" [tys, names,
      pc P "Reader.expandNums" [nums, pc P "Datatype.eraseExpr" [x]], nil]
    let kernel := pc P "Check.typeIn" [G, nil, get res]
    let a : Internal.Thm := ⟨0, Γ, [formAllT P S T R nums names tys Ev x],
      [isSomeT syn, isSomeT res, isSomeT kernel].foldr (Internal.Logic.imp o)
        (S.conv (Term.lam nat (S.evN (Term.fst (sh 1 R)) (v 0) (sh 1 nil) (sh 1 (get res))))
          (T.relT R (get syn)))⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ' Φ ψ ↦ k (Φ.length - 1) Γ' Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"soundOfFormAll: {m}" k
    let some d := (dImpI L <| dImpI L <| dImpI L <| fun Γ₀ Φ₀ ψ₀ ↦
        let (iSyn, iRes) := (Φ₀.length - 3, Φ₀.length - 2)
        dAllE L K.G K.E 0 nil (K.allEΓ (fun _ ↦ nil) <|
          K.impE (at' "the empty environment"
            (K.cutThm "envNil" (fun Γ' ↦ [atPos 0 Γ']) (last K.byHyp))) <|
          K.impE (at' "no name in the context" (dImpI L (lastFalse K))) <|
          K.impE (at' "no name in the scope" (dImpI L (lastFalse K))) <|
          K.impE (at' "typed" (K.byHyp iSyn)) <| K.impE (at' "resolved" (K.byHyp iRes)) <|
          K.exE <| K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
            let (iDen, iRel) := (Φ₁.length - 2, Φ₁.length - 1)
            denE K iDen (fun _ n w st Γ' Φ ψ ↦
              dConv L K.G K.E S (atPos n Γ') (atPos w Γ')
                (at' "stable" (instNK K st (fun _ ↦ v 0) K.byNorm))
                (at' "related" (K.byHyp iRel)) Γ' Φ ψ) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀)
        a.ctx a.hyps a.concl
      | dbgTrace "soundOfFormAll: not proved" fun _ ↦ none
    pure (a, d))

/-- An atom that occurs in a form occurs in a list with the form after forms and before others:
by induction on the forms before it. In the context of those forms, under the others, the form
and the atom. -/
def occInAppend (P : Prog) (S : Defs) : Step :=
  ("occInAppend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let all (A : Tree) (b : Term) : Term := Internal.Logic.all o A (Term.lam A b)
    -- under the quantifiers: the atom v0, the form v1, the forms after v2, the forms before v3
    let φ := all Ls (all treeTy (all treeTy (Internal.Logic.imp o (truth o (occT P (v 0) (v 1)))
      (truth o (occInT P (v 0) (txsApp P (v 3) (consT treeTy (v 1) (v 2))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dAllI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let base : Deducer := intro fun h ↦
      decideIn K (fun Γ ↦ occT P (at_ 2 Γ) (at_ 1 Γ)) (K.hypFalse h) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the forms after v(2), the form v(3), the
    -- atom v(4)
    let step : Deducer := intro fun h ↦
      decideIn K (fun Γ ↦ occT P (at_ 4 Γ) (at_ 0 Γ))
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) <| K.allEΓ (at_ 4) <|
          K.impE (K.byHyp h) <| fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
        (K.solve 3)
    listInduction "occInAppend" φ base step)

/-- Each atom that occurs in a form of a list after forms occurs in the list of those forms and
the list: by induction on the list, the head's atoms by {name}`occInAppend`, the rest's by the
induction hypothesis at the forms with the head after them ({lit}`appendSnoc`). In the context
of the list, under the forms before. -/
def occSelf (P : Prog) (S : Defs) : Step :=
  ("occSelf", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifier: the forms before v0, the list v1
    let φ := Internal.Logic.all o Ls (Term.lam Ls
      (S.allL (occPred P (txsApp P (v 0) (v 1))) (v 1)))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    -- a construction: the head v(0), the tail v(1), the forms before v(2)
    let (g, xs, pre) := (at_ 0, at_ 1, at_ 2)
    let step : Deducer := dAllI L <| K.norm <| dConjI L
      (stage "occSelf: the head" <| dAllI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let h := Φ₁.length - 1
        (K.cutThm "occInAppend" (fun Γ ↦ [pre Γ]) <| K.allEΓ xs <| K.allEΓ g <|
          K.allEΓ (at_ 3) <| K.impE (K.byHyp h) <| lastOr K) Γ₁ Φ₁ ψ₁)
      (stage "occSelf: the rest" <| fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (txsApp P (pre Γ) (consT treeTy (g Γ) (nilT treeTy)))
          (fun Γ₁ Φ₁ ψ₁ ↦
            let i := Φ₁.length - 1
            (K.cutThm "appendSnoc" (fun Γ ↦ [pre Γ, g Γ, xs Γ]) <| K.byHyp i) Γ₁ Φ₁ ψ₁) Γ Φ ψ)
    listInduction "occSelf" φ (dAllI L (K.solve 2)) step)

/-- A predicate that holds of each element of a list and of an element holds of each element of
the list with the element after them: by induction on the list. In the context of the list,
under the predicate and the element. -/
def allSnoc (P : Prog) (S : Defs) : Step :=
  ("allSnoc", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let PrTy := exp treeTy omega
    let snoc (xs x : Term) : Term := pc P "Prelude.append" [xs, pc P "Prelude.single" [x]]
    -- under the quantifiers: the element v0, the predicate v1, the list v2
    let φ := Internal.Logic.all o PrTy (Term.lam PrTy (Internal.Logic.all o treeTy
      (Term.lam treeTy (Internal.Logic.imp o (S.allL (v 1) (v 2))
        (Internal.Logic.imp o (Term.app (v 1) (v 0)) (S.allL (v 1) (snoc (v 2) (v 0))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    let base : Deducer := intro fun _ h₂ ↦
      K.norm (dConjI L (stage "allSnoc: the element" (K.byHyp h₂)) (K.solve 2))
    -- a construction: the head v(0), the tail v(1), the predicate v(2), the element v(3)
    let step : Deducer := intro fun h₁ h₂ ↦ normHyps K [h₁] <| K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
      let (iHead, iTail) := (Φ₁.length - 2, Φ₁.length - 1)
      K.norm (dConjI L (stage "allSnoc: the head" (K.byHyp iHead))
        (stage "allSnoc: the rest" <| fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) <|
          K.impE (K.byHyp iTail) <| K.impE (K.byHyp h₂) <| lastOr K) Γ Φ ψ)) Γ₁ Φ₁ ψ₁
    listInduction "allSnoc" φ base step)

/-- The rebuilding of a tree by a function's fold, whose value at a node pairs the node rebuilt
with the function's value: the first component is the tree
({name}`GebTests.Prototypes.FreeTopos.Normalization.rebuildLemmas`). The function is applied to
the variables of the context {lit}`Γt`, the tree the innermost; the lemmas' names begin with
{lit}`tag`. The lemmas' sides are in the normal form of a kit's rules: the vocabulary's with the
lemmas of addition and of a list's head and tail, as the fold's unfolding at a node has them. -/
def foldRebuild (P : Prog) (tag fn : String) (Γt : List Tree) : List Step :=
  let args := (List.range Γt.length).reverse.map v
  match firstFoldApp (weakNF P (baseNorm P) 0 Γt (pc P fn args)) with
  | some (C, s, Fp) => match Internal.expParts C with
    | some (FX, _) => rebuildLemmas P tag FX
        (fun x F ↦ Term.fst (Term.app (Term.roseRec C s x) F)) Γt.tail
        (Term.app (Term.roseRec C s (v 0)) Fp) Fp none
        fun ix ↦ addLemmaRules ix ++ [.thm (ix "walkHead") [], .thm (ix "walkTail") []]
    | none => []
  | none => []

/-- The children rebuilt by such a fold ({name}`foldRebuild`) are the children: the first
components of the map of the folds applied, by induction on the children with the rebuilding of
each. Its left side is in the normal form of a kit's rules, in which it occurs where the fold
is unfolded at a node. In the context of the children and the function's other arguments. -/
def foldKids (P : Prog) (S : Defs) (tag fn : String) (Γt : List Tree) : Step :=
  (s!"{tag}Kids", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, [s!"{tag}Fst"]⟩
    let rs := K.rules []
    let Γ := list treeTy :: Γt.tail
    let args := (List.range Γt.length).reverse.map v
    let (C, s, Fp) ← firstFoldApp (weakNF P (baseNorm P) 0 Γt (pc P fn args))
    let θ ← defnObjs D.mapApp s
    let lhs := Term.listRec (nilT treeTy) (consT treeTy (Term.fst (v 1)) (v 0))
      (call D.mapApp θ [Term.listRec (nilT C) (consT C (Term.roseRec C s (v 1)) (v 0)) (v 0),
        Fp])
    let some l := nfE P.G E rs Γ lhs | dbgTrace s!"{tag}Kids: left" fun _ ↦ none
    let some d := Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l (v 0)
      | dbgTrace s!"{tag}Kids: {(firstDiff l (v 0)).map fun (x, y) ↦
          s!"{showT x}\n  vs {showT y}"}" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l (v 0)⟩, d))

/-- The rebuilding of a tree by the fold of the recognizers' test of an atom's occurrence
({name}`foldRebuild`). -/
def occursRebuild (P : Prog) : List Step :=
  foldRebuild P "oc" "Recognize.occurs" [treeTy, treeTy]

/-- The children rebuilt by the fold of the recognizers' test of an atom's occurrence are the
children ({name}`foldKids`). In the context of the children and the atom. -/
def occursKids (P : Prog) (S : Defs) : Step :=
  foldKids P S "oc" "Recognize.occurs" [treeTy, treeTy]

/-- The names of the rules of the rebuilding by the recognizers' test of an atom's occurrence:
of a tree ({name}`occursRebuild`) and of a node's children ({name}`occursKids`). -/
def occursRebuildNames : List String := ["ocFst", "ocKids"]

/-- A definition's name's atom occurs in the definition's form: the atom a node of the atoms'
label, equal to itself ({lit}`equalRefl`): the form's and the keyword's equalities with it
decided, it occurs either way. In the context of the body and the atom. -/
def occursDefName (P : Prog) (S : Defs) : Step :=
  ("occursDefName", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, occursRebuildNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let a : Internal.Thm := ⟨0, [treeTy, treeTy], [truth P.o (pc P "Reader.isAtom" [v 1])],
      truth P.o (occT P (v 1) (defForm P (v 1) (v 0)))⟩
    let nA (Γ : List Tree) : Term := v (Γ.length - 1)
    let atom : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      (K.cutThm "equalRefl" (fun Γ ↦ [nA Γ]) <| fun Γ₂ Φ₂ ψ₂ ↦
        let iRefl := Φ₂.length - 1
        decideKnown K (fun Γ ↦ apps equalT [nA Γ, nA Γ])
          (stage "occursDefName: the atom itself" (K.hypFalse iRefl)) (
          -- the form the atom or not, and the keyword the atom or not: the atom occurs
          decideKnown K (fun Γ ↦ apps equalT [defForm P (nA Γ) (v (Γ.length - 2)), nA Γ])
            (decideKnown K (fun Γ ↦ occT P (nA Γ) (pc P "Datatype.aDef" []))
              (stage "occursDefName: the keyword not the atom" (K.solve 3))
              (stage "occursDefName: the keyword the atom" (K.solve 3)))
            (stage "occursDefName: the form the atom" (K.solve 3))) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let some d := (K.treeNode (v 1) fun Γ₁ Φ₁ ψ₁ ↦
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          if bs.map Oitavem.rank == some 1 then atom
          else stage "occursDefName: no atom" (K.hypFalse 0)) 3 [] (v 1) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "occursDefName: not proved" fun _ ↦ none
    pure (a, d))

/-- The recognizers' agreement holds of an environment of the same datatypes and of the names
with a name after them, where the name is no recognizer's of a datatype of the environment: a
recognizer's name with an index among the names with the name after them has it among the names
({lit}`idxSnocCases`), where its index is the same ({lit}`indexAppendOld`). In the context of
the name, the names, the two environments and the relation's context. -/
def recsExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("recsExtend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Γ₀ := [treeTy, list treeTy, T.envTy, T.envTy, Defs3.ctxTy]
    let (n, names, E', Ev, R) := (v 0, v 1, v 2, v 3, v 4)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    let recName (d : Term) : Term := pc P "Typing.recognizerName" [d]
    let noms (e : Term) : Term := pc P "Typing.envNoms" [e]
    let one (x : Term) : Term := pc P "Prelude.single" [x]
    let notRec := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (pc P "Typing.hasName" [v 0, noms (sh 1 Ev)]))
      (Internal.Logic.imp o (Term.eq (recName (v 0)) (sh 1 n)) (Internal.Logic.ff o))))
    let a : Internal.Thm := ⟨0, Γ₀,
      [T.recsT R Ev names, Term.eq (noms E') (noms Ev), notRec],
      T.recsT R E' (pc P "Prelude.append" [names, one n])⟩
    let unfold : List Internal.NormRule := [.delta (T.q + 6 + 2 * nFolds)]
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (namesA, nA, dA) := (at_ 3, at_ 4, at_ 5)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"recsExtend: {m}" k
    let some d := (dRwBy (evalRw K.G K.E unfold .head) <|
        dRwHyp (evalRw K.G K.E unfold .head) 0 <| dAllI L <| dImpI L <| dImpI L <|
        fun Γ₁ Φ₁ ψ₁ ↦
          let (hHas, hIdx) := (Φ₁.length - 2, Φ₁.length - 1)
          -- the datatype is one of the environment before
          let hasOld : Deducer := at' "a datatype before" (normHyps K [1] (K.byHyp hHas))
          let rec_ (Γ : List Tree) : Term := recName (dA Γ)
          decideIn K (fun Γ ↦ isSome (idx (rec_ Γ) (namesA Γ)))
            -- no index among the names: the name after them, which is no recognizer's
            (K.cutThm "idxSnocCases" (fun Γ ↦ [namesA Γ]) <| K.allEΓ rec_ <| K.allEΓ nA <|
              K.impE (at' "an index" (K.byHyp hIdx)) <| K.impE (dImpI L (lastFalse K)) <|
              last fun iEqT ↦ K.cutThm "equalSound" (fun Γ ↦ [rec_ Γ]) <| K.allEΓ nA <|
              K.impE (at' "the names equal" (hypOrK K iEqT)) <| last fun iEq ↦
              fun Γ Φ ψ ↦ dAllE L K.G K.E 2 (dA Γ) (K.impE hasOld <|
                K.impE (at' "the name a recognizer's" (hypOrK K iEq)) <|
                dFalse L dHyp) Γ Φ ψ)
            -- an index among the names: the same among the names with the name after them
            (fun Γ Φ ψ ↦ dAllE L K.G K.E 3 (dA Γ) (K.impE hasOld <|
              K.impE (at' "indexed" (K.solve 3)) <| K.exE <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
                let (iIdx, iRec) := (Φ₂.length - 2, Φ₂.length - 1)
                (K.cutThm "indexAppendOld" (fun Γ ↦ [namesA Γ]) <| K.allEΓ rec_ <|
                  K.allEΓ (fun Γ ↦ one (nA Γ)) <| K.impE (at' "indexed before" (K.solve 3)) <|
                  last fun iApp ↦ normHyps K [iIdx, iApp] <|
                  dExI L K.G K.E (v 0) (dConjI L (at' "the index" K.byNorm)
                    (at' "the recognizer" (K.byHyp iRec)))) Γ₂ Φ₂ ψ₂) Γ Φ ψ) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "recsExtend: not proved" fun _ ↦ none
    let _ := (R, E')
    pure (a, d))

/-- The recognizers the forms refer to are among the names with a name after them, at an
environment of the same datatypes: a recognizer's index among the names is its index among
those ({lit}`indexAppendOld`). In the context of the name, the names, the two environments and
the forms. -/
def insExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("insExtend", fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++ ["Recognize.occurs"] }, S, E, ix,
      lookupEqNames⟩
    let L := K.L
    let Γ₀ := [treeTy, list treeTy, T.envTy, T.envTy, list treeTy]
    let (n, names, E', Ev, fs) := (v 0, v 1, v 2, v 3, v 4)
    let noms (e : Term) : Term := pc P "Typing.envNoms" [e]
    let recName (d : Term) : Term := pc P "Typing.recognizerName" [d]
    let one (x : Term) : Term := pc P "Prelude.single" [x]
    let a : Internal.Thm := ⟨0, Γ₀, [insT P Ev names fs, Term.eq (noms E') (noms Ev)],
      insT P E' (pc P "Prelude.append" [names, one n]) fs⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (namesA, nA, dA) := (at_ 3, at_ 4, at_ 5)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let some d := (dAllI L <| dImpI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let (hHas, hOcc) := (Φ₁.length - 2, Φ₁.length - 1)
        dAllE L K.G K.E 0 (dA Γ₁) (
          K.impE (stage "insExtend: a datatype before" (normHyps K [1] (K.byHyp hHas))) <|
          K.impE (stage "insExtend: referred to" (hypOrK K hOcc)) <| last fun iIdx ↦
          K.cutThm "indexAppendOld" (fun Γ ↦ [namesA Γ]) <|
          K.allEΓ (fun Γ ↦ recName (dA Γ)) <| K.allEΓ (fun Γ ↦ one (nA Γ)) <|
          K.impE (stage "insExtend: indexed" (hypOrK K iIdx)) <| last fun iEq ↦
          normHyps K [iEq] (stage "insExtend: the index" (K.byHyp iIdx))) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "insExtend: not proved" fun _ ↦ none
    let _ := (E', fs)
    pure (a, d))

/-- The recognizers' agreement holds of no names: no recognizer's name has an index. In the
context of the typing environment and the relation's context. -/
def recsEmpty (P : Prog) (S : Defs) (T : Defs3) : Step :=
  unfolded P S "recsEmpty" (T.q + 6 + 2 * nFolds) lookupEqNames []
    ⟨0, [T.envTy, Defs3.ctxTy], [], T.recsT (v 1) (v 0) (nilT treeTy)⟩ fun K ↦
      dImpI K.L (dImpI K.L (lastFalse K))

/-- The program with the expansion's lookup of an alias kept folded, as the statements about
the aliases name it. -/
def aliasProg (P : Prog) : Prog := { P with folded := P.folded ++ ["Datatype.findAlias"] }

/-- The typing's form of an atom is the atom ({lit}`rawAtom`), its sides in the normal form of
the rules of a kit without the datatype language's vocabulary, in which the form's fold stays
folded. In the context of the characters and the typing environment. -/
def rawAtomEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("rawAtomEq", fun ix E ↦ do
    let K₀ : Kit := ⟨P, S, E, ix, []⟩
    let K : Kit := ⟨P, S, E, ix,
      (vocab3 ++ ["rawAtom"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let Γ := [list treeTy, T.envTy]
    let atom := nodeT (Term.pair (numeral 1) (v 0))
    let l ← nfE K₀.G K₀.E (K₀.rules []) Γ (rawT T (v 1) atom)
    let r ← nfE K₀.G K₀.E (K₀.rules []) Γ atom
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := K.byNorm a.ctx a.hyps a.concl | dbgTrace "rawAtomEq: not proved" fun _ ↦ none
    pure (a, d))

/-- A type form whose expansion of aliases is a marker's datatype's atom reads, where the typing
reads it, as that datatype: the aliases coherent with the environment's abbreviations
({name}`aliasT`, {name}`aliasKwT`), the markers' names atoms naming no type the typing reads
before them ({name}`markerNamesT`), and the environment without sorts ({name}`noSortsT`). The
form a node: at an atom, the typing's tests decided in the order it reads them: the trees' type
and the unit type have no alias and are no marker's name; an abbreviation is that of an alias,
the datatype where the alias is a marker's; a datatype's name without an abbreviation has no
alias and is the marker's; and no sort is read. At any other form the expansion is no atom. The
typing reads the form itself, as it reads a type abbreviation's body, or, where {lit}`raw`
holds, the form as its fold rebuilds it, as it reads an annotation within an expression. In the
context of the form, the markers, the typing environment and the declarations. -/
def cohAtWith (P : Prog) (S : Defs) (T : Defs3) (name : String) (raw : Bool) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨aliasProg P, S, E, ix,
      lookupEqNames ++ ["hasNameNil", "rawAtomEq", "rtFst", "rtKids", "eaFst", "eaKids"]⟩
    let L := K.L
    let o := P.o
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let Γ₀ := [treeTy, list treeTy, T.envTy, list treeTy]
    let (F, ms, Ev, dv) := (v 0, v 1, v 2, v 3)
    let read (Ev F : Term) : Term := pc P "Typing.readTy" [Ev, if raw then rawT T Ev F else F]
    let expand (dv F : Term) : Term := pc P "Datatype.expandAliases" [dv, F]
    let marked (ms x : Term) : Term :=
      isSome (pc P "Reader.indexOf" [x, pc P "Typing.markerNames" [ms]])
    let a : Internal.Thm := ⟨0, Γ₀,
      [aliasT P dv Ev ms, aliasKwT P dv, markerNamesT P ms, noSortsT P Ev,
        truth o (isSome (read Ev F)), truth o (marked ms (expand dv F))],
      Term.eq (get (read Ev F)) (pc P "Typing.tyData" [atomNameT (expand dv F)])⟩
    let (hAl, hKw, hMs, hSorts, hRead, hMark) := (0, 1, 2, 3, 4, 5)
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (dvA, EA, FA) := (at_ 0, at_ 1, at_ 3)
    let nmA (Γ : List Tree) : Term := atomNameT (FA Γ)
    let XA (Γ : List Tree) : Term := expand (dvA Γ) (FA Γ)
    let faA (Γ : List Tree) : Term := pc P "Datatype.findAlias" [nmA Γ, dvA Γ]
    let laA (Γ : List Tree) : Term :=
      pc P "Typing.lookupName" [nmA Γ, pc P "Typing.envAl" [EA Γ]]
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"{name}: {m}" k
    -- the markers' names' properties at the expansion: an atom, then the two types' names
    let atMarker (k : ℕ → ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E hMs (XA Γ) (K.impE (at' "a marker's name" (K.byHyp hMark)) <|
        K.conjE <| K.conjE fun Γ Φ ψ ↦ k (Φ.length - 4) (Φ.length - 2) (Φ.length - 1) Γ Φ ψ)
        Γ Φ ψ
    let refuted (h : ℕ) : Deducer := dImpE L h (K.solve 3) (dFalse L dHyp)
    -- a type the typing reads before the abbreviations: no alias, and no marker's name
    let keyword (kw : String) (hNoAlias : ℕ) (named : ℕ → ℕ → ℕ) : Deducer :=
      K.cutThm "equalSound" (fun Γ ↦ [nmA Γ]) <| K.allEΓ (fun _ ↦ pc P kw []) <|
      K.impE (at' s!"{kw}: the name" (K.solve 3)) <| normLastK K <|
      decideOpt K faA
        (at' s!"{kw}: no alias" (atMarker fun _ iT iU ↦ refuted (named iT iU)))
        (at' s!"{kw}: an alias" (refuted hNoAlias))
    let atom (iNoT iNoU : ℕ) : Deducer :=
      decideIn K (fun Γ ↦ pc P "Reader.named" [FA Γ, pc P "Reader.kwT" []])
        (decideIn K (fun Γ ↦ pc P "Reader.named" [FA Γ, pc P "Reader.kwUnit" []])
          -- the coherence at the name: the absence's part and the presence's
          (fun Γ Φ ψ ↦ dAllE L K.G K.E hAl (nmA Γ) (K.conjE fun Γ₁ Φ₁ ψ₁ ↦
            let (iA, iB) := (Φ₁.length - 2, Φ₁.length - 1)
            let present (k : ℕ → ℕ → Deducer) : Deducer :=
              dImpE L iB (K.solve 3) <| K.conjE fun Γ Φ ψ ↦
                k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
            (decideOpt K laA
              (decideIn K (fun Γ ↦ pc P "Typing.hasName" [nmA Γ, pc P "Typing.envNoms" [EA Γ]])
                (decideIn K (fun Γ ↦ pc P "Typing.hasName"
                    [nmA Γ, pc P "Typing.envSorts" [EA Γ]])
                  (at' "no type" (K.hypFalse hRead))
                  (at' "a sort" fun Γ Φ ψ ↦
                    dAllE L K.G K.E hSorts (nmA Γ) (last refuted) Γ Φ ψ))
                (decideOpt K faA
                  (at' "a datatype's name" (K.solve 3))
                  (at' "an alias without an abbreviation" <| present fun iLa _ ↦
                    K.hypFalse iLa)))
              (decideOpt K faA
                (at' "an abbreviation without an alias" <|
                  dImpE L iA (dImpI L (lastFalse K)) <| last refuted)
                (at' "an abbreviation of an alias" <| present fun _ iTy ↦
                  dImpE L iTy (at' "the alias a marker's" (K.byHyp hMark)) <|
                  normLastK K <| at' "the abbreviation's type" K.byNorm))) Γ₁ Φ₁ ψ₁) Γ Φ ψ)
          (keyword "Reader.kwUnit" iNoU fun _ iU ↦ iU))
        (keyword "Reader.kwT" iNoT fun iT _ ↦ iT)
    let other : Deducer := at' "no atom" <| atMarker fun iAtom _ _ ↦ K.hypFalse iAtom
    let some d := (dConjE L hKw <| fun Γ₀' Φ₀ ψ₀ ↦
        let (iNoT, iNoU) := (Φ₀.length - 2, Φ₀.length - 1)
        (K.treeNode (v 0) fun Γ₁ Φ₁ ψ₁ ↦
          dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
            if bs.map Oitavem.rank == some 1 then atom iNoT iNoU else other) 2 [] (v 1)
            Γ₁ Φ₁ ψ₁) Γ₀' Φ₀ ψ₀) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    let _ := (F, ms, Ev, dv)
    pure (a, d))

/-- {name}`cohAtWith` at an annotation within an expression, as the typing rebuilds it. -/
def cohAt (P : Prog) (S : Defs) (T : Defs3) : Step := cohAtWith P S T "cohAt" true

/-- {name}`cohAtWith` at a form the typing reads itself. -/
def cohRead (P : Prog) (S : Defs) (T : Defs3) : Step := cohAtWith P S T "cohRead" false

/-- The expansion's alias of a name among declarations with an alias after them: the alias
among the declarations where there is one, else that of the alias after them. By induction on
the declarations; at a construction the head a node, an alias of the name or not. In the
context of the declarations, under the alias's form, its name and the name. -/
def findAliasSnoc (P : Prog) (S : Defs) : Step :=
  ("findAliasSnoc", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let childT ← primT Kernel.Prim.child
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
    let one (m a : Term) : Term := pc P "Datatype/Decls.single" [pc P "Datatype.aliasD" [m, a]]
    let snoc (dv m a : Term) : Term := pc P "Datatype/Decls.append" [dv, one m a]
    -- under the quantifiers: the name v0, the alias's name v1, its form v2, the declarations v3
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o treeTy
      (Term.lam treeTy (Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.conj o
        (Internal.Logic.imp o (truth o (isSome (fa (v 0) (v 3))))
          (Term.eq (fa (v 0) (snoc (v 3) (v 1) (v 2))) (fa (v 0) (v 3))))
        (Internal.Logic.imp o (notTest o (isSome (fa (v 0) (v 3))))
          (Term.eq (fa (v 0) (snoc (v 3) (v 1) (v 2)))
            (fa (v 0) (one (v 1) (v 2)))))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let refuted : Deducer := fun Γ Φ ψ ↦ dImpE L (Φ.length - 1) (K.solve 3) (dFalse L dHyp) Γ Φ ψ
    let base : Deducer := dAllI L <| dAllI L <| dAllI L <|
      dConjI L (dImpI L (lastFalse K)) (dImpI L K.byNorm)
    -- a construction: the head v(0), the tail v(1), then the form, the alias's name, the name
    let step : Deducer := dAllI L <| dAllI L <| dAllI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let (hd, aA, mA, nA) := (at_ 0, at_ 2, at_ 3, at_ 4)
      dAllE L K.G K.E 0 (aA Γ₁) (K.allEΓ mA <| K.allEΓ nA <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (i₁, i₂) := (Φ₂.length - 2, Φ₂.length - 1)
        let rest : Deducer := dConjI L (stage "findAliasSnoc: an alias among the rest" (K.byHyp i₁))
          (stage "findAliasSnoc: no alias among the rest" (K.byHyp i₂))
        (K.treeNode (hd Γ₂) fun Γ₃ Φ₃ ψ₃ ↦
          dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
            if bs.map Oitavem.rank == some 2 then
              decideIn K (fun Γ ↦ pc P "Datatype.sameName"
                  [apps childT [hd Γ, leafT bnilT], nA Γ]) rest
                (dConjI L (stage "findAliasSnoc: the head the alias" (dImpI L K.byNorm))
                  (stage "findAliasSnoc: the head no alias" (dImpI L refuted)))
            else rest) 2 [] (v 1) Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    listInduction "findAliasSnoc" φ base step)

/-- The aliases are type abbreviations of the reader's ({name}`aliasTysT`) after a type
abbreviation is declared: the declarations with the alias after them, and the reader's
abbreviations with the name's before them. A name is the alias's, abbreviated, or another,
with an alias among the declarations as before ({name}`findAliasSnoc`). In the context of the
abbreviation's type, the alias's form, the name, the abbreviations and the declarations. -/
def aliasTysExtend (P : Prog) (S : Defs) : Step :=
  ("aliasTysExtend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, numsEqNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let Γ₀ := [treeTy, treeTy, treeTy, list treeTy, list treeTy]
    let (ty, a, nm, tys, dv) := (v 0, v 1, v 2, v 3, v 4)
    let one (m a : Term) : Term := pc P "Datatype/Decls.single" [pc P "Datatype.aliasD" [m, a]]
    let dv' := pc P "Datatype/Decls.append" [dv, one nm a]
    let thm : Internal.Thm := ⟨0, Γ₀, [aliasTysT P dv tys],
      aliasTysT P dv' (consT treeTy (abbrevT P nm ty) tys)⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (dvA, nmA, aA, nA) := (at_ 0, at_ 2, at_ 3, at_ 5)
    let faA (Γ : List Tree) : Term := pc P "Datatype.findAlias" [nA Γ, dvA Γ]
    let some d := (dAllI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
        let hAl := Φ₁.length - 1
        (K.cutThm "findAliasSnoc" (fun Γ ↦ [dvA Γ]) <| K.allEΓ aA <| K.allEΓ nmA <|
          K.allEΓ nA <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
          let i₂ := Φ₂.length - 1
          decideIn K (fun Γ ↦ apps equalT [nA Γ, nmA Γ])
            (decideOpt K faA
              (stage "aliasTysExtend: no alias before" <|
                dImpE L i₂ (dImpI L (lastFalse K)) <| normLastK K <|
                decideIn K (fun Γ ↦ apps equalT [nmA Γ, nA Γ])
                  (stage "aliasTysExtend: no alias" (K.hypFalse hAl))
                  (stage "aliasTysExtend: the alias's name" <|
                    K.cutThm "equalSymm" (fun Γ ↦ [nA Γ, nmA Γ]) <| K.impE (K.solve 3) <|
                    lastFalse K))
              (stage "aliasTysExtend: an alias before" fun Γ Φ ψ ↦
                dAllE L K.G K.E 0 (nA Γ) (K.impE (K.solve 3) <| fun Γ Φ ψ ↦
                  K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ))
            (stage "aliasTysExtend: the name abbreviated" (K.solve 3)) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
        thm.ctx thm.hyps thm.concl
      | dbgTrace "aliasTysExtend: not proved" fun _ ↦ none
    let _ := (ty, tys)
    pure (thm, d))

/-- A keyword is reserved: closed, by normalization of the presence of its index among the
reserved names, unfolded along them without the rest's index duplicated
({name}`isSomeIndexOfCons`, {name}`truthOfEq`). -/
def kwReserved (P : Prog) (S : Defs) (name kw : String) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, ["isSomeIndexOfCons", "indexOfNil"]⟩
    let t := pc P "Prelude.isSome"
      [pc P "Reader.indexOf" [pc P kw [], pc P "Reader.reservedNames" []]]
    let φ := truth P.o t
    let some d := (applyThm K "truthOfEq" (fun _ ↦ [t]) [fun Γ Φ ψ ↦
        dEq (fun Γ _ t u ↦ byMode .full K.G K.E 0 (K.rules []) Γ [] t u) Γ Φ ψ] dHyp) [] [] φ
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- The aliases stay coherent with the typing environment's abbreviations ({name}`aliasT`,
{name}`aliasKwT`) after a type abbreviation is declared, where the typing reads its body, the
name has no alias and is not reserved: the declarations with the alias of the name as the
body's expansion after them ({name}`findAliasSnoc`), and the environment with the abbreviation
of the name as the body's type before its abbreviations. At the name, the alias is the body's
expansion and the abbreviation the body's type, the datatype where the expansion is a marker's
({name}`cohRead`); at another name both are as before. No type the typing reads before the
abbreviations is the name, which is not reserved ({name}`kwReserved`). In the context of the
body, the name, the markers, the typing environment and the declarations. -/
def aliasExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("aliasExtend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let fa (n dv : Term) : Term := pc P "Datatype.findAlias" [n, dv]
    let Γ₀ := [treeTy, treeTy, list treeTy, T.envTy, list treeTy]
    let (X, nm, ms, Ev, dv) := (v 0, v 1, v 2, v 3, v 4)
    let expand (dv X : Term) : Term := pc P "Datatype.expandAliases" [dv, X]
    let read (Ev X : Term) : Term := pc P "Typing.readTy" [Ev, X]
    let dv' := pc P "Datatype/Decls.append" [dv,
      pc P "Datatype/Decls.single" [pc P "Datatype.aliasD" [nm, expand dv X]]]
    let Ev' := pc P "Typing.withAl" [Ev, consT treeTy
      (pc P "Typing.abbr" [nm, get (read Ev X)]) (pc P "Typing.envAl" [Ev])]
    let a : Internal.Thm := ⟨0, Γ₀,
      [aliasT P dv Ev ms, aliasKwT P dv, markerNamesT P ms, noSortsT P Ev,
        truth o (isSome (read Ev X)), notTest o (isSome (fa nm dv)),
        notTest o (isSome (pc P "Reader.indexOf" [nm, pc P "Reader.reservedNames" []]))],
      Internal.Logic.conj o (aliasT P dv' Ev' ms) (aliasKwT P dv')⟩
    let (hKw, hFresh, hRes) := (1, 5, 6)
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (dvA, EA, msA, nmA, XA, nA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let aA (Γ : List Tree) : Term := expand (dvA Γ) (XA Γ)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let at' (m : String) (k : Deducer) : Deducer := stage s!"aliasExtend: {m}" k
    let refuted (h : ℕ) : Deducer := dImpE L h (K.solve 3) (dFalse L dHyp)
    -- the alias of a name among the declarations after: where there is one before, where none
    let snocAt (n : List Tree → Term) (k : ℕ → ℕ → Deducer) : Deducer :=
      K.cutThm "findAliasSnoc" (fun Γ ↦ [dvA Γ]) <| K.allEΓ aA <| K.allEΓ nmA <| K.allEΓ n <|
      K.conjE fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    -- the coherence at every name
    let coherent : Deducer := dAllI L <| fun Γ₁ Φ₁ ψ₁ ↦
      dAllE L K.G K.E 0 (nA Γ₁) (K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iA, iB) := (Φ₂.length - 2, Φ₂.length - 1)
        (snocAt nA fun i₁ i₂ ↦
          decideIn K (fun Γ ↦ apps equalT [nmA Γ, nA Γ])
            -- another name: the alias and the abbreviation as before
            ((decideOpt K (fun Γ ↦ fa (nA Γ) (dvA Γ))
              (at' "another name without an alias" <|
                dImpE L i₂ (dImpI L (lastFalse K)) <| normLastK K <|
                dConjI L (at' "no abbreviation" (K.byHyp iA)) (dImpI L (lastFalse K)))
              (at' "another name with an alias" <|
                dImpE L i₁ (K.solve 3) <| normLastK K <|
                dConjI L (at' "an alias, the absence" (K.byHyp iA))
                  (at' "an alias, the presence" (K.byHyp iB)))))
            -- the name: the alias the body's expansion, the abbreviation the body's type
            (at' "the name" <|
              -- the name has no alias before: equal to the alias's name, which has none; the
              -- equation is kept to this step, the names' equality being decided as written
              dImpE L i₂ (at' "the name fresh" <| dImpI L fun Γ Φ ψ ↦
                let iSome := Φ.length - 1
                (K.cutThm "equalSound" (fun Γ ↦ [nmA Γ]) <| K.allEΓ nA <|
                  K.impE (K.solve 3) <| normLastK K <|
                  dImpE L hFresh (K.byHyp iSome) (dFalse L dHyp)) Γ Φ ψ) <|
              normLastK K <|
              dConjI L (dImpI L (last refuted)) <| dImpI L <|
              dConjI L (at' "the name abbreviated" (K.solve 3)) <| dImpI L <|
              last fun iMark ↦
              applyThm K "cohRead" (fun Γ ↦ [XA Γ, msA Γ, EA Γ, dvA Γ])
                [dHyp, dHyp, dHyp, dHyp, dHyp,
                  at' "the expansion a marker's" (K.byHyp iMark)] <|
              normLastK K <| at' "the abbreviation's type" K.byNorm)) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    -- no alias of a type the typing reads before the abbreviations
    let noAlias (kw reserved : String) (iOld : ℕ) : Deducer :=
      let kwA (_ : List Tree) : Term := pc P kw []
      at' s!"{kw}" <| snocAt kwA fun _ i₂ ↦
        decideIn K (fun Γ ↦ apps equalT [nmA Γ, kwA Γ])
          (dImpE L i₂ (K.byHyp iOld) <| normLastK K <| dImpI L (lastFalse K))
          -- the name the keyword: reserved, its index present, rewritten by the equation alone
          (at' s!"{kw}: the name reserved" <|
            K.cutThm "equalSound" (fun Γ ↦ [nmA Γ]) <| K.allEΓ kwA <| K.impE (K.solve 3) <|
            last fun iEq ↦ dImpE L hRes
              (dRwBy (evalRw K.G K.E [.hyp iEq] .full) (K.cutThm reserved (fun _ ↦ []) dHyp))
              (dFalse L dHyp))
    let some d := (dConjI L coherent <| dConjE L hKw <| fun Γ Φ ψ ↦
        dConjI L (noAlias "Reader.kwT" "kwTReserved" (Φ.length - 2))
          (noAlias "Reader.kwUnit" "kwUnitReserved" (Φ.length - 1)) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "aliasExtend: not proved" fun _ ↦ none
    pure (a, d))

/-- The markers the recognizers read off a program's kernel forms are the markers the typing
checks first, those of the typed forms. By induction on the typed forms; at a construction the
head a node, its label split: a template's instance is dropped, a marker is kept as it is, and
any other form's erasure is no marker, a list's erasure a list whichever way its test goes. In
the context of the typed forms. -/
def markersKernel (P : Prog) (S : Defs) : Step :=
  ("markersKernel", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let Ls := list treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "markersKernel: no partition" fun _ ↦ none
    let ms (ts : Term) : Term := pc P "Recognize.markers" [pc P "Datatype.kernelForms" [ts]]
    let φ := Term.eq (ms (v 0)) (Term.fst X₀)
    -- a construction: the tail v0, the head v1; the head's label and children before them
    let step : Deducer := normHyps K [0] <| fun Γ₀ Φ₀ ψ₀ ↦
      (K.treeNode (v 1) fun Γ₁ Φ₁ ψ₁ ↦
        -- the head's erasure, whose test, where the head is a list, is split
        let t := pc P "Datatype.eraseForm" [v 3]
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun _ ↦
          splitCond K Γ₁.length t 4 (stage "markersKernel: a form" K.byNorm)) 4 [] (v 1)
          Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀
    listInduction "markersKernel" φ (stage "markersKernel: no forms" K.byNorm) step)

/-- The development of the recognizers' agreement along the names. -/
def programRecsDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [recsEmpty P S T, recsExtend P S T, insExtend P S T]

/-- The development of the atoms' occurrences in the program's forms. -/
def programOccursDev (P : Prog) (S : Defs) : List Step :=
  [occInAppend P S, occSelf P S, allSnoc P S] ++ occursRebuild P ++
    [occursKids P S, occursDefName P S]

end GebTests.Prototypes.FreeTopos.Datatypes

end
