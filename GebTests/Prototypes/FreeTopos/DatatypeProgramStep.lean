/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeProgramRuns
public import GebTests.Prototypes.FreeTopos.DatatypeClosed
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgramRuns -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeClosed -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of a whole program, by induction on its forms

The soundness of a program of the datatype language, generalized over the states of the
compiler's passes: from the declarations the expansion has, the typing's environment, and the
reader's abbreviations, names and terms, where the passes over the forms that remain end without
a failure, the definitions the reader ends with are related to the typing environment the typing
ends with. It is proved by induction on the forms, each of a kind: a definition, a type or a
numeral abbreviation, a function, or a template's instance. The step at a kind shows that the
states the passes' steps leave at a form of it satisfy the invariant; a definition and a
function share the step at a form at which the expansion writes a definition, whose body is a
source form sound at expanded forms. At the states the passes begin in, the soundness at all
states is that of the program. A form that declares a datatype is of no kind, and a body's
expansion is assumed a source form.

## Main definitions

* {lit}`Passes` — the states of the passes and the forms that remain.
* {lit}`Passes.hyps`, {lit}`Passes.concl` — the hypotheses and the conclusion at the states.
* {lit}`formOk` — the kinds of forms.
* {lit}`programSoundGroups` — the developments, each with its certificate's name.

## Main statements

* {lit}`stepDefined` — the step at a form at which the expansion writes a definition.
* {lit}`passesForms` — the soundness at all states, by induction on the forms.
* {lit}`programForms` — the soundness of a program whose forms are of the kinds.

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

namespace Passes

variable (P : Prog) (S : Defs) (T : Defs3) (X₀ : Term) (s : Passes)

/-- The typed forms the expansion writes for the forms that remain. -/
def typed : Term := typedForms P s.es s.dv

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
as terms, and no datatype declared. -/
def hyps : List Term :=
  let o := P.o
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
    Term.eq (pc P "Typing.envNoms" [s.env]) (nilT treeTy)]

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
  ⟨es, v (k + 8), v (k + 7), v (k + 6), v (k + 5), v (k + 4), v (k + 3), v (k + 2), v (k + 1), v k⟩

/-- The soundness at the forms that remain, the variable of index 0, at all states: the
quantification over the states' variables of the implication of the conclusion by the hypotheses
and the further hypotheses {lit}`more` of the forms. -/
def passesφ (P : Prog) (T : Defs3) (X₀ : Term) (more : Term → List Term) : Term :=
  let s := passesAt 0 (v 9)
  (passesCtx T).foldl (fun b A ↦ Internal.Logic.all P.o A (Term.lam A b))
    ((s.hyps P T X₀ ++ more (v 9)).foldr (Internal.Logic.imp P.o) (s.concl P T X₀))

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

/-- The recognizers' agreement holds of a typing environment that declares no datatype. In the
context of the names, the environment and the relation's context. -/
def recsNoData (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("recsNoData", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [list treeTy, T.envTy, Defs3.ctxTy],
      [Term.eq (pc P "Typing.envNoms" [v 1]) (nilT treeTy)], T.recsT (v 2) (v 1) (v 0)⟩
    let hasName : List Internal.NormRule := [.delta (P.idx "Typing.hasName")]
    let some d := (dRwBy (evalRw K.G K.E [.delta (T.q + 6 + 2 * nFolds)] .head) <|
        normHyps K [0] <| dAllI K.L <| dImpI K.L fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1) ++ hasName) .full) (Φ.length - 1)
            (linkK K "recsNoData: a datatype" (dFalse K.L dHyp)) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "recsNoData: not proved" fun _ ↦ none
    pure (a, d))

/-- That a definition's body, where it expands under declarations, expands to a source form at
any numeral abbreviations: under the declarations and the abbreviations. -/
def expandsSrc (P : Prog) (body : Term) : Term :=
  let o := P.o
  let Ls := list treeTy
  let ex := pc P "Datatype.expandExpr" [v 1, sh 2 body]
  Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
    (Internal.Logic.imp o (truth o (pc P "Prelude.isSome" [ex]))
      (truth o (pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 1, v 0]),
        pc P "Prelude.get" [ex]]))))))

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

/-- That a name is not one of the implementation's. -/
def userNameT (P : Prog) (x : Term) : Term := notTest P.o (pc P "implName" [x])

/-- The hypotheses of a head that names a function: no template's instance, no declaration of a
datatype, the functions' keyword. -/
def defnHead (P : Prog) (h : Term) : List Term :=
  ["Datatype.kwGeneric", "Datatype.kwData", "Datatype.kwTreeData"].map
    (fun kw ↦ notTest P.o (headNamed P h kw)) ++ [truth P.o (headNamed P h "Datatype.kwDefn")]

/-- That a form is a source form at any numeral abbreviations: under the abbreviations. -/
def srcAllT (P : Prog) (t : Term) : Term :=
  Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy) (srcAt P (v 0) (sh 1 t)))

/-- The binders the expansion reads of a function's list of binders. -/
def bindersT (P : Prog) (bs : Term) : Term := pc P "Datatype.bindersTx" [bs]

/-- That each binder the expansion reads of a list of binders is a source form at any numeral
abbreviations: under the abbreviations. -/
def srcBindersT (P : Prog) (S : Defs) (bs : Term) : Term :=
  Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy)
    (S.allL (Term.lam treeTy (srcAt P (v 1) (v 0))) (bindersT P (sh 1 bs))))

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

/-- That a form is of a kind the soundness of a whole program reads: a definition, whose body
expands to a source form, a type abbreviation, a numeral abbreviation whose name is not one of
the implementation's, a function, the list of a head, a name, binders, a result type and a
body, whose body expands to a source form and whose binders and result type are source forms, or
a template's instance. -/
def formOk (P : Prog) (S : Defs) (e : Term) : Term :=
  Internal.Logic.disj P.o (kindT P e (defHead P (v 2) ++ [expandsSrc P (v 0)]))
    (Internal.Logic.disj P.o (kindT P e (deftypeHead P (v 2)))
      (Internal.Logic.disj P.o
        (kindT P e (defnumHead P (v 2) ++ [userNameT P (pc P "Reader.nameOf" [v 1])]))
        (Internal.Logic.disj P.o
          (kindT P e (defnHead P (v 4) ++
            [expandsSrc P (v 0), srcBindersT P S (v 2), srcAllT P (v 1)]) 5)
          (genericT P e))))

/-- The hypothesis of forms each of a kind the soundness reads ({name}`formOk`). -/
def formsOk (P : Prog) (S : Defs) (es : Term) : List Term :=
  [S.allL (Term.lam treeTy (formOk P S (v 0))) es]

/-- The program with the passes' steps kept folded, and with them the erasure of a form and the
recognizers' insertion at a form, whose values at a definition's form are equations
({lit}`eraseDefForm`, {lit}`recAtThree`). -/
def passProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Typing.checkStep", "Datatype.xpStep", "Datatype.genericStep",
      "Reader.progStep", "Datatype.eraseForm", "Recognize.recognizersAt"] }

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

/-- The soundness at the forms that remain after a form at which the expansion writes a
definition, a step of the soundness at all states ({name}`passesφ`): given it at the forms
after, the expansion's step at the form from the declarations writes the definition of a name
as a body, a source form at the numeral abbreviations and sound at expanded forms, and the
hypotheses at the states give the conclusion. The definition is before the forms of the rest
({lit}`typedFormsCons`); the typing's step ({lit}`checkDef`) declares the name at the body's
type; the reader's ({lit}`readDef`) has the name after the names and the resolved term after the
terms. The terms the reader ends with have the term at the index of the names' length
({lit}`readExt`, {lit}`nthLen`), with a kernel type ({lit}`kcTyped`), so that the term converges
to a value related at its type, by the body's soundness, and the invariant holds of the states
the steps leave ({lit}`globExtend`, {lit}`namesExtend`), at which the hypothesis on the forms
after gives the conclusion. In the context of the body, the name, the form, the forms after and
the states. -/
def stepDefined (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDefined", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let at' (m : String) (k : Deducer) : Deducer := stage s!"stepDefined @ {m}" k
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDefined: no partition" fun _ ↦ none
    let s := passesAt 4 (consT treeTy (v 2) (v 3))
    let hyps := [Internal.instTerm [] [v 3] (passesφ P T X₀ (formsOk P S)),
        Term.eq (xpStepT P (xpState (v 12) nil) (v 2))
          (xpState (v 12) (consT treeTy (defForm P (v 1) (v 0)) nil))] ++
      s.hyps P T X₀ ++ [srcAt P (v 8) (v 0), Internal.instTerm [] [v 0] (expandedφ P S T)] ++
      formsOk P S (v 3)
    let Γ₀ := [treeTy, treeTy, treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    -- the variables, from any context that extends the theorem's
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (bA, nA, eA, esA) := (at_ 0, at_ 1, at_ 2, at_ 3)
    let (fsA, msA, termsA, namesA, numsA, tysA) := (at_ 4, at_ 5, at_ 6, at_ 7, at_ 8, at_ 9)
    let (rA, EA, dvA) := (at_ 10, at_ 11, at_ 12)
    let get (t : Term) : Term := pc P "Prelude.get" [t]
    let fA (Γ : List Tree) : Term := defForm P (nA Γ) (bA Γ)
    -- the states before the form, and the parts of the states after it
    let sA (Γ : List Tree) : Passes :=
      passesAt (4 + (Γ.length - Γ₀.length)) (consT treeTy (eA Γ) (esA Γ))
    let synA (Γ : List Tree) : Term := pc P "Typing.synIn" [EA Γ, nil, bA Γ]
    let nmA (Γ : List Tree) : Term := pc P "Reader.nameOf" [nA Γ]
    let erA (Γ : List Tree) : Term := pc P "Datatype.eraseExpr" [bA Γ]
    let resA (Γ : List Tree) : Term := pc P "Reader.resolve" [tysA Γ, namesA Γ,
      pc P "Reader.expandNums" [numsA Γ, erA Γ], nil]
    let tA (Γ : List Tree) : Term := get (resA Γ)
    let E'A (Γ : List Tree) : Term := pc P "Typing.withDefs" [EA Γ,
      declareT P (pc P "Typing.envDefs" [EA Γ]) (nmA Γ) (get (synA Γ))]
    let names'A (Γ : List Tree) : Term :=
      pc P "Prelude.append" [namesA Γ, pc P "Prelude.single" [nmA Γ]]
    let terms'A (Γ : List Tree) : Term :=
      pc P "Prelude.append" [termsA Γ, pc P "Prelude.single" [tA Γ]]
    let s'A (Γ : List Tree) : Passes := ⟨esA Γ, dvA Γ, E'A Γ, pc P "Typing/OName.nothing" [],
      tysA Γ, numsA Γ, names'A Γ, terms'A Γ, msA Γ, fsA Γ⟩
    let restA (Γ : List Tree) : Passes := { sA Γ with es := esA Γ }
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let kA (Γ : List Tree) : Term := defForm P (nA Γ) (erA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    -- the hypotheses' indices
    let (hStep, hX, hC, hO, hR, hK, hGlob, hNums, hNames, hKws, hLen, hNoms, hSrc, hExp,
        hMore) := (1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 16)
    -- the last stage: the hypothesis on the forms after, at the states the steps leave
    let apply (iSyn iO iRes iUnres iNotIdx iTyped iNth : ℕ) : Deducer :=
      let sound : Deducer := at' "the soundness" <| fun Γ₈ Φ₈ ψ₈ ↦
        dAllE L K.G K.E hExp (Term.snd (kcRun P (termsA Γ₈) kcInit)) (
        K.allEΓ (fun _ ↦ nil) <|
        K.allEΓ dvA <| K.allEΓ EA <| K.allEΓ (fun _ ↦ nil) <| K.allEΓ tysA <| K.allEΓ numsA <|
        K.allEΓ namesA <| K.allEΓ (fun _ ↦ nil) <| K.allEΓ (fun Γ ↦ (sA Γ).rel P) <|
        last fun iS ↦ impEs L iS
          [stage "stepDefined: the definitions related" (hypOr hGlob),
            stage "stepDefined: the empty environment"
              (K.cutThm "envNil" (fun Γ ↦ [(sA Γ).rel P]) (last K.byHyp)),
            stage "stepDefined: the numerals" (hypOr hNums),
            stage "stepDefined: the names" (hypOr hNames),
            stage "stepDefined: a source form" (K.byHyp hSrc),
            stage "stepDefined: expanded" (K.solve 3),
            stage "stepDefined: typed" (K.byHyp iSyn),
            stage "stepDefined: resolved" (K.byHyp iRes),
            stage "stepDefined: kernel typed" (K.byHyp iTyped),
            stage "stepDefined: the keywords" (hypOr hKws),
            stage "stepDefined: the markers" K.byNorm,
            stage "stepDefined: the recognizers" (applyThm K "recsNoData"
              (fun Γ ↦ [namesA Γ, EA Γ, (sA Γ).rel P]) [dHyp] (last K.byHyp)),
            stage "stepDefined: the empty context"
              (K.cutThm "cxNil" (fun Γ ↦ [EA Γ]) (last K.byHyp))] <|
        at' "the definition sound" <| last fun iConv ↦
        applyThm K "globExtend"
          (fun Γ ↦ [get (synA Γ), tA Γ, nmA Γ, namesA Γ, EA Γ, (sA Γ).rel P])
          [stage "stepDefined: related before" dHyp,
            stage "stepDefined: no index" (hypOr iNotIdx),
            stage "stepDefined: the term's index" (normHyps K [hLen, iNth] K.byNorm),
            stage "stepDefined: the term's value" (K.byHyp iConv)] <|
        at' "the relation extended" <| last fun iGlob' ↦
        -- the hypothesis on the forms after, at the states the steps leave
        let s' := s'A
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 ((s' Γ).dv) (
          K.allEΓ (fun Γ ↦ (s' Γ).env) <| K.allEΓ (fun Γ ↦ (s' Γ).rej) <|
          K.allEΓ (fun Γ ↦ (s' Γ).tys) <| K.allEΓ (fun Γ ↦ (s' Γ).nums) <|
          K.allEΓ (fun Γ ↦ (s' Γ).names) <| K.allEΓ (fun Γ ↦ (s' Γ).terms) <|
          K.allEΓ (fun Γ ↦ (s' Γ).ms) <| K.allEΓ (fun Γ ↦ (s' Γ).fs) <|
          last fun iIH ↦ impEs L iIH
            [stage "stepDefined: the rest expands" (K.byHyp hX),
              stage "stepDefined: the rest checks" (K.byHyp hC),
              stage "stepDefined: the rest's recognizers" (hypOr iO),
              stage "stepDefined: the rest reads" (K.byHyp hR),
              stage "stepDefined: the kernel checks" (K.byHyp hK),
              stage "stepDefined: no rejection" (dImpI L (lastFalse K)),
              stage "stepDefined: related after" (K.byHyp iGlob'),
              stage "stepDefined: the numerals after" (
                dRwBy (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) <|
                dRwHyp (evalRw K.G K.E [.delta (T.q + 3 + 2 * nFolds)] .head) hNums <|
                last K.byHyp),
              stage "stepDefined: the names after" (applyThm K "namesExtend"
                (fun Γ ↦ [nmA Γ, namesA Γ]) [dHyp, hypOr iUnres] (last K.byHyp)),
              stage "stepDefined: the keywords after" (hypOr hKws),
              stage "stepDefined: the lengths" (
                K.cutThm "lenSnoc" (fun Γ ↦ [namesA Γ]) <| K.allEΓ nmA <|
                K.cutThm "lenSnoc" (fun Γ ↦ [termsA Γ]) <| K.allEΓ tA <| fun Γ Φ ψ ↦
                normHyps K [hLen, Φ.length - 3, Φ.length - 1] K.byNorm Γ Φ ψ),
              stage "stepDefined: no datatype" (normHyps K [hNoms] K.byNorm),
              stage "stepDefined: the rest's kinds" (hypOr hMore)] <|
          stage "stepDefined: the conclusion" (last K.byHyp)) Γ Φ ψ)) Γ₈ Φ₈ ψ₈
      sound
    -- the terms the reader ends with: the terms, the term read, and further ones
    let finals (iSyn iO iRes iUnres iNotIdx : ℕ) : Deducer := at' "the final terms" <|
      K.cutThm "readExt" (fun Γ ↦ [rsA Γ]) <| K.allEΓ (fun Γ ↦ progState (tysA Γ) (numsA Γ)
        (names'A Γ) (terms'A Γ)) <| K.exE <| fun Γ₇ Φ₇ ψ₇ ↦
      let n₇ := Γ₇.length
      let extA (Γ : List Tree) : Term := v (Γ.length - n₇)
      let iExt := Φ₇.length - 1
      (at' "the further terms" <|
        K.cutThm "appendSnoc" (fun Γ ↦ [termsA Γ, tA Γ, extA Γ]) <| last fun iSnoc ↦
        normHyps K [iExt, iSnoc] <| at' "the terms rewritten" <|
        applyThm K "kcTyped" (fun Γ ↦ [extA Γ, tA Γ, termsA Γ])
          [stage "stepDefined: the kernel's check" (K.byHyp hK)] <| last fun iTyped ↦
        K.cutThm "nthLen" (fun Γ ↦ [termsA Γ]) <| K.allEΓ tA <| K.allEΓ extA <|
        last fun iNth ↦ apply iSyn iO iRes iUnres iNotIdx iTyped iNth) Γ₇ Φ₇ ψ₇
    -- the reader's step
    let reader (iSyn : ℕ) : Deducer := at' "the reader" <|
      applyThm K "someTruth" (fun Γ ↦ [Term.fst ((restA Γ).inserted P)])
        [stage "stepDefined: the recognizers' insertion" (K.byHyp hO)] <| last fun iO ↦
      applyThm K "readPrefix" (fun Γ ↦ [rsA Γ, pc P "Reader.progStep" [stA Γ, kA Γ]])
        [stage "stepDefined: the reader's run" (K.byHyp hR)] <| at' "the reader's step" <|
      applyThm K "readDef" (fun Γ ↦ [erA Γ, nA Γ, termsA Γ, namesA Γ, numsA Γ, tysA Γ])
        [stage "stepDefined: the reader's step" dHyp] <| at' "the reader's parts" <|
      K.conjE <| K.conjE <| K.conjE <| fun Γ₅ Φ₅ ψ₅ ↦
        let (iAtom, iFresh, iRes, iRead) :=
          (Φ₅.length - 6, Φ₅.length - 4, Φ₅.length - 2, Φ₅.length - 1)
        normHyps K [iRead] (
          decideIn K (fun Γ ↦ pc P "Reader.isAtom" [nA Γ]) (K.hypFalse iAtom) <|
          at' "the name fresh" <|
          applyThm K "freshParts" (fun Γ ↦ [nmA Γ, namesA Γ, numsA Γ, tysA Γ])
            [stage "stepDefined: fresh" (hypOr iFresh)] <| K.conjE <| K.conjE <| fun Γ Φ ψ ↦
          finals iSyn iO iRes (Φ.length - 4) (Φ.length - 2) Γ Φ ψ) Γ₅ Φ₅ ψ₅
    -- the typing's step
    let typing : Deducer := at' "the typing" <|
      applyThm K "checkPrefix" (fun Γ ↦ [(restA Γ).others P X₀,
          checkStepAt P (EA Γ) (rA Γ) (fA Γ)])
        [stage "stepDefined: the typing's run" (K.byHyp hC)] <| at' "the typing's step" <|
      applyThm K "checkDef" (fun Γ ↦ [bA Γ, nA Γ, rA Γ, EA Γ])
        [stage "stepDefined: no rejection before" dHyp,
          stage "stepDefined: the typing's step" dHyp] <|
      K.conjE <| fun Γ Φ ψ ↦
        let (iSyn, iCheck) := (Φ.length - 2, Φ.length - 1)
        normHyps K [iCheck] (reader iSyn) Γ Φ ψ
    -- the expansion's step, the equation given
    let expansion : Deducer := at' "the expansion" <| normHyps K [hStep] <|
      at' "the typed forms" <|
      applyThm K "typedFormsCons" (fun Γ ↦ [fA Γ, dvA Γ, esA Γ]) [] <| K.conjE <|
      fun Γ₃ Φ₃ ψ₃ ↦
        let (iFlag, iImp) := (Φ₃.length - 2, Φ₃.length - 1)
        normHyps K [iFlag] (
          dImpE L iImp (stage "stepDefined: the rest's expansion" (K.byHyp hX)) <|
          last fun iTF ↦ normHyps K [iTF] typing) Γ₃ Φ₃ ψ₃
    let some d := expansion a.ctx a.hyps a.concl
      | dbgTrace "stepDefined: not proved" fun _ ↦ none
    pure (a, d))

/-- The step at a form at which the expansion writes a definition ({name}`stepDefined`), at a
body, a name, a form, the forms after and the states: the hypothesis on the forms after the
first hypothesis, the invariant's hypotheses those from the index {lit}`hInv` and the rest's
kinds that of index {lit}`hMore`; the expansion's step's equation, the body's being a source form
and its soundness at expanded forms by the deducers given. The conclusion is the goal. -/
def applyDefined (K : Kit) (σ : List Tree → List Term) (hInv hMore : ℕ)
    (stepEq src sound : Deducer) : Deducer :=
  applyThm K "stepDefined" σ
    ([stage "stepDefined: the hypothesis on the forms after" (hypOrK K 0),
        stage "stepDefined: the expansion's step" stepEq] ++
      (List.range 12).map (fun k ↦
        stage s!"stepDefined: the invariant's hypothesis {k}" (hypOrK K (hInv + k))) ++
      [stage "stepDefined: the body a source form" src,
        stage "stepDefined: the body sound" sound,
        stage "stepDefined: the kinds of the forms after" (hypOrK K hMore)])
    (stage "stepDefined: the goal" (lastOr K))

/-- The soundness at the forms that remain after a definition's form, a step of the soundness at
all states ({name}`passesφ`): given it at the forms after, the form the list of a head that names
a definition, a name and a body whose expansion is a source form, the hypotheses at the states
give the conclusion. The expansion's step ({lit}`xpDef`) writes the definition of the name as
the body's expansion, sound at expanded forms ({name}`expandedOf`), so that the step at a
definition written gives the conclusion ({name}`stepDefined`). In the context of the body, the
name, the head, the forms after and the states. -/
def stepDef (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDef", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDef: no partition" fun _ ↦ none
    let e := listNode [v 2, v 1, v 0]
    let s := passesAt 4 (consT treeTy e (v 3))
    let hyps := [Internal.instTerm [] [v 3] (passesφ P T X₀ (formsOk P S))] ++ defHead P (v 2) ++
      s.hyps P T X₀ ++ [expandsSrc P (v 0)] ++ formsOk P S (v 3)
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
    let (hX, hSrc, hMore) := (5, 17, 18)
    -- the body's expansion a source form, by the hypothesis on the body
    let src (iEx : ℕ) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E hSrc (dvA Γ) (K.allEΓ numsA (K.impE (K.byHyp iEx) (lastOr K))) Γ Φ ψ
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
        applyDefined K (fun Γ ↦ [bA Γ, nA Γ, eA Γ, esA Γ] ++ states Γ) 5 hMore
          (normHyps K [iStep] K.byNorm) (src iEx)
          (expandedOf K FA dvA (K.byHyp iEx) (hypOrK K)) Γ₂ Φ₂ ψ₂
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
        (stage "stepDef: a template's instance" (refuteNot K 1)) a.ctx a.hyps a.concl
      | dbgTrace "stepDef: not proved" fun _ ↦ none
    pure (a, d))

/-- The form of a binding of a name at a type to a term in a body, as the typing and the reader
read it. -/
def letForm (P : Prog) (x A t b : Term) : Term :=
  listNode [kwAtom P "Reader.kwLet", x, A, t, b]

/-- The test of source forms at a closed term or at a term whose parts' tests are decided, by
normalization: by the rules, then with the test's step, the expansion of numeral abbreviations'
step and the test of an atom's characters unfolded, which decide the tests at the keywords'
atoms and at the empty list. -/
def srcTrue (K : Kit) (T : Defs3) : Deducer :=
  K.norm fun Γ Φ ψ ↦
    dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta (T.argIdx 5), .delta (T.argIdx 3),
      .delta (K.P.idx "charsFixed")]) .full) (K.solve 2) Γ Φ ψ

/-- The kit of the proofs about the test of source forms: the vocabulary's rules and the test at
a list split at its head ({lit}`srcCons`). -/
def srcKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  datumKit P S ix E ((vocab3 ++ ["charsMap", "handlerAtom3", "srcCons"]).filter
    fun nm ↦ 0 < ix nm ∧ ix nm < E.size)

/-- The test of source forms at a term, as a test, under the abbreviations of the position
given. -/
def srcTest (P : Prog) (nums x : Term) : Term :=
  pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 nums, v 0]), x]

/-- A binding of the erasure's variable at a type to a term, in the variable, is a source form
where the type and the term are: their tests decided, the atoms' by normalization. In the
context of the term, the type and the abbreviations. -/
def srcLet (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("srcLet", fun ix E ↦ do
    let K := srcKit P S ix E
    let aR := pc P "Datatype.aR" []
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy],
      [srcAt P (v 2) (v 1), srcAt P (v 2) (v 0)], srcAt P (v 2) (letForm P aR (v 1) (v 0) aR)⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - 3))
    let some d := (decideIn K (fun Γ ↦ srcTest P (at_ 2 Γ) (at_ 1 Γ))
          (stage "srcLet: the type" (K.hypFalse 0)) <|
        decideIn K (fun Γ ↦ srcTest P (at_ 2 Γ) (at_ 0 Γ))
          (stage "srcLet: the term" (K.hypFalse 1)) <|
        stage "srcLet: the binding" (srcTrue K T)) a.ctx a.hyps a.concl
      | dbgTrace "srcLet: not proved" fun _ ↦ none
    pure (a, d))

/-- The abstractions over each binder of a list in turn around a body are a source form where
each binder and the body are: by induction on the list. None: the body. A binder before a
list: the binder's test and that of the abstractions over the list, the induction hypothesis,
decided. In the context of the binders, under the body and the abbreviations. -/
def srcNest (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("srcNest", fun ix E ↦ do
    let K := srcKit P S ix E
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the abbreviations v0, the body v1, the binders v2
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o Ls (Term.lam Ls
      (Internal.Logic.imp o (S.allL (Term.lam treeTy (srcAt P (v 1) (v 0))) (v 2))
        (Internal.Logic.imp o (srcAt P (v 0) (v 1)) (srcAt P (v 0) (nestT P (v 2) (v 1))))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let intro (k : ℕ → ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    let base : Deducer := intro fun _ h₂ ↦ stage "srcNest: no binders" (K.byHyp h₂)
    -- a construction: the head v(0), the tail v(1), the body v(2), the abbreviations v(3)
    let step : Deducer := intro fun h₁ h₂ ↦
      let (x, xs, body, nums) := (at_ 0, at_ 1, at_ 2, at_ 3)
      normHyps K [h₁] <| K.conjE <| fun Γ₁ Φ₁ ψ₁ ↦
        let (iHead, iTail) := (Φ₁.length - 2, Φ₁.length - 1)
        dAllE L K.G K.E 0 (body Γ₁) (K.allEΓ nums <|
          K.impE (stage "srcNest: the rest's binders" (K.byHyp iTail)) <|
          K.impE (stage "srcNest: the body" (K.byHyp h₂)) <| last fun iRest ↦
          decideIn K (fun Γ ↦ srcTest P (nums Γ) (x Γ))
            (stage "srcNest: the binder" (K.hypFalse iHead)) <|
          decideIn K (fun Γ ↦ srcTest P (nums Γ) (nestT P (xs Γ) (body Γ)))
            (stage "srcNest: the rest" (K.hypFalse iRest)) <|
          stage "srcNest: the abstraction" (srcTrue K T)) Γ₁ Φ₁ ψ₁
    listInduction "srcNest" φ base step)

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

/-- The development of the source forms and the soundness of the parts the expansion writes of a
function's definition. -/
def programSrcDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [srcCons P S T, srcLet P S T, srcNest P S T, expandedR P S T,
    letCaseAt P S T true "letExpanded"]

/-- The soundness at the forms that remain after a function's form, a step of the soundness at
all states ({name}`passesφ`): given it at the forms after, the form the list of a head that names
a function, a name, binders, a result type and a body, where the body's expansion, the binders
and the result type are source forms, the hypotheses at the states give the conclusion. The
expansion's step ({lit}`xpDefn`) writes the definition of the name as the abstractions over the
binders around the binding of the erasure's variable at the result type to the body's expansion,
in the variable: a source form ({name}`srcLet`, {name}`srcNest`), sound at expanded forms, the
body's expansion ({name}`expandedOf`), the variable ({name}`expandedR`), the binding
({lit}`letExpanded`) and the abstractions ({lit}`nest`), so that the step at a definition
written gives the conclusion ({name}`stepDefined`). In the context of the body, the result type,
the binders, the name, the head, the forms after and the states. -/
def stepDefn (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepDefn", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, []⟩
    let L := K.L
    let Ls := list treeTy
    let nil := nilT treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "stepDefn: no partition" fun _ ↦ none
    let e := listNode [v 4, v 3, v 2, v 1, v 0]
    let s := passesAt 6 (consT treeTy e (v 5))
    let hyps := [Internal.instTerm [] [v 5] (passesφ P T X₀ (formsOk P S))] ++
      defnHead P (v 4) ++ s.hyps P T X₀ ++
      [expandsSrc P (v 0), srcBindersT P S (v 2), srcAllT P (v 1)] ++ formsOk P S (v 5)
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
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let (hX, hSrcX, hSrcBs, hSrcR, hMore) := (5, 17, 18, 19, 20)
    -- the body written a source form: the body's expansion, the result type and the binders
    let src (iEx : ℕ) : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      dAllE L K.G K.E hSrcX (dvA Γ₁) (K.allEΓ numsA <| K.impE (K.byHyp iEx) <| last fun iB ↦
        fun Γ₂ Φ₂ ψ₂ ↦ dAllE L K.G K.E hSrcR (numsA Γ₂) (last fun iR ↦
          applyThm K "srcLet" (fun Γ ↦ [bA Γ, RA Γ, numsA Γ])
            [stage "stepDefn: the result type a source form" (hypOr iR),
              stage "stepDefn: the body's expansion a source form" (hypOr iB)] <|
          last fun iL ↦ fun Γ₃ Φ₃ ψ₃ ↦ dAllE L K.G K.E hSrcBs (numsA Γ₃) (last fun iBs ↦
            K.cutThm "srcNest" (fun Γ ↦ [bindersA Γ]) <| K.allEΓ letA <| K.allEΓ numsA <|
            K.impE (stage "stepDefn: the binders source forms" (hypOr iBs)) <|
            K.impE (stage "stepDefn: the binding a source form" (hypOr iL)) <|
            stage "stepDefn: the abstractions a source form" (lastOr K)) Γ₃ Φ₃ ψ₃)
          Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    -- the body written sound at expanded forms
    let sound (iEx : ℕ) : Deducer :=
      expandedOf K XA dvA (K.byHyp iEx) fun iB ↦
      K.cutThm "expandedR" (fun _ ↦ []) <| last fun iR ↦
      applyThm K "letExpanded" (fun Γ ↦ [aR, bA Γ, RA Γ, aR])
        [stage "stepDefn: the body's expansion sound" (hypOr iB),
          stage "stepDefn: the variable sound" (hypOr iR)] <|
      last fun iLet ↦ K.cutThm "nest" (fun Γ ↦ [bindersA Γ, letA Γ]) <|
      K.impE (stage "stepDefn: the binding sound" (hypOr iLet)) <|
      stage "stepDefn: the abstractions sound" (lastOr K)
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
        applyDefined K (fun Γ ↦ [BA Γ, nA Γ, eA Γ, esA Γ] ++ states Γ) 5 hMore
          (normHyps K [iStep] K.byNorm) (src iEx) (sound iEx) Γ₂ Φ₂ ψ₂
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
        (stage "stepDefn: a template's instance" (refuteNot K 1)) a.ctx a.hyps a.concl
      | dbgTrace "stepDefn: not proved" fun _ ↦ none
    pure (a, d))

/-- A number of deducer transformers applied in turn. -/
def repeatK (n : ℕ) (f : Deducer → Deducer) (k : Deducer) : Deducer :=
  Nat.rec (motive := fun _ ↦ Deducer) k (fun _ r ↦ f r) n

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
    let hyps := [Internal.instTerm [] [v 3] (passesφ P T X₀ (formsOk P S))] ++
      deftypeHead P (v 2) ++ s.hyps P T X₀ ++ formsOk P S (v 3)
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
      tys'A Γ, numsA Γ, namesA Γ, termsA Γ, msA Γ, fsA Γ⟩
    let restA (Γ : List Tree) : Passes := { s'A Γ with env := EA Γ, rej := rA Γ }
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ
    let unfoldBoth (idx h : ℕ) : Deducer := dRwBy (evalRw K.G K.E [.delta idx] .head) <|
      dRwHyp (evalRw K.G K.E [.delta idx] .head) h <| last K.byHyp
    let (hNoDef, hKw, hX, hC, hO, hR, hK, hRej, hGlob, hNums, hNames, hKws, hLen, hNoms,
        hMore) := (4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18)
    -- the hypothesis on the forms after, at the states the steps leave
    let apply (iO : ℕ) : Deducer := at' "the forms after" <| fun Γ Φ ψ ↦
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
            stage "stepDeftype: no datatype" (normHyps K [hNoms] K.byNorm),
            stage "stepDeftype: the rest's kinds" (hypOr hMore)] <|
        stage "stepDeftype: the conclusion" (last K.byHyp)) Γ Φ ψ
    -- the reader's step
    let reader : Deducer := at' "the reader" <|
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
      K.conjE <| K.conjE <| K.conjE <| last fun iRead ↦ normHyps K [iRead] (apply iO)
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
      K.conjE <| last fun iCheck ↦ normHyps K [iCheck] reader
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
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
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
    let hyps := [Internal.instTerm [] [v 3] (passesφ P T X₀ (formsOk P S))] ++
      defnumHead P (v 2) ++ [userNameT P (pc P "Reader.nameOf" [v 1])] ++ s.hyps P T X₀ ++
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
      tysA Γ, nums'A Γ, namesA Γ, termsA Γ, msA Γ, fsA Γ⟩
    let restA (Γ : List Tree) : Passes := { s'A Γ with env := EA Γ, rej := rA Γ }
    let stA (Γ : List Tree) : Term := progState (tysA Γ) (numsA Γ) (namesA Γ) (termsA Γ)
    let rsA (Γ : List Tree) : Term := flatT P (Term.snd ((restA Γ).inserted P))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ
    let unfoldBoth (idx h : ℕ) : Deducer := dRwBy (evalRw K.G K.E [.delta idx] .head) <|
      dRwHyp (evalRw K.G K.E [.delta idx] .head) h <| last K.byHyp
    let (hNoDef, hNoType, hKw, hUser, hX, hC, hO, hR, hK, hRej, hGlob, hNames, hLen, hNoms,
        hMore) := (4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 18, 19, 20)
    -- the hypothesis on the forms after, at the states the steps leave
    let apply (iNotNum iO iUnres iAtom iNum : ℕ) : Deducer := at' "the forms after" <|
      fun Γ Φ ψ ↦ dAllE L K.G K.E 0 ((s'A Γ).dv) (
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
            stage "stepDefnum: no datatype" (normHyps K [hNoms] K.byNorm),
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
    let some d := decideIn K (fun Γ ↦ headNamed P (hA Γ) "Datatype.kwGeneric") expansion
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
    let hyps := [Internal.instTerm [] [v 1] (passesφ P T X₀ (formsOk P S)), genericT P (v 0)] ++
      s.hyps P T X₀ ++ formsOk P S (v 1)
    let Γ₀ := [treeTy, Ls] ++ passesCtx T
    let a : Internal.Thm := ⟨0, Γ₀, hyps, s.concl P T X₀⟩
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (j + (Γ.length - Γ₀.length))
    let (eA, esA, fsA, msA, termsA, namesA) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4, at_ 5)
    let (numsA, tysA, rA, EA, dvA) := (at_ 6, at_ 7, at_ 8, at_ 9, at_ 10)
    let stepA (Γ : List Tree) : Term := xpStepT P (xpState (dvA Γ) nil) (eA Γ)
    let restA (Γ : List Tree) : Passes := passesAt (2 + (Γ.length - Γ₀.length)) (esA Γ)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr := hypOrK K
    let (hGen, hX, hC, hO, hR, hK, hRej, hMore) := (1, 2, 3, 4, 5, 6, 7, 14)
    let some d := (at' "the expansion" <|
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
                  (List.range 6).map (fun k ↦
                    stage s!"stepGeneric: the invariant {k}" (hypOr (hRej + 1 + k))) ++
                  [stage "stepGeneric: the rest's kinds" (hypOr hMore)]) <|
                stage "stepGeneric: the conclusion" (last K.byHyp)) Γ Φ ψ) Γ₃ Φ₃ ψ₃) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "stepGeneric: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness at all states of forms each of a kind the soundness reads ({name}`passesφ`,
{name}`formsOk`): by induction on the forms. None: the passes' runs leave the states, at which
the conclusion is the invariant's relation of the definitions, and the recognizers' agreement
that of an environment without datatypes ({lit}`recsNoData`). A construction: the head's kind
and its parts from the hypothesis on the forms, the step at a form of that kind
({name}`stepDef`, {name}`stepDeftype`, {name}`stepDefnum`, {name}`stepDefn`,
{name}`stepGeneric`). In the context of the forms. -/
def passesForms (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("passesForms", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "passesForms: no partition" fun _ ↦ none
    let φ := passesφ P T X₀ (formsOk P S)
    let nVars := (passesCtx T).length
    let nHyps := ((passesAt 0 (v 9)).hyps P T X₀).length + 1
    let intro (k : Deducer) : Deducer := repeatK nVars (dAllI L) (repeatK nHyps (dImpI L) k)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let hypOr (h : ℕ) : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp h Γ Φ ψ
    -- no forms: the states' variables, from the outermost the declarations first
    let base : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let h (k : ℕ) : ℕ := Φ₁.length - nHyps + k
      let s (Γ : List Tree) : Passes := passesAt (Γ.length - nVars) (nilT treeTy)
      dConjI L (stage "passesForms: none, the markers" K.byNorm) (dConjI L
        (stage "passesForms: none, related" (K.byHyp (h 6)))
        (applyThm K "recsNoData" (fun Γ ↦ [(s Γ).finalNames P,
            Term.fst ((s Γ).checked P X₀), (s Γ).rel P])
          [stage "passesForms: none, no datatype" (normHyps K [h 11] K.byNorm)]
          (stage "passesForms: none, the recognizers" dHyp))) Γ₁ Φ₁ ψ₁
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
      let invariant : List Deducer := (List.range 12).map fun k ↦
        stage s!"passesForms: the hypothesis {k}" (hypOr (h k))
      (fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ (h 12)) .full) (h 12)
        (stage "passesForms: the forms" <| K.conjE <| fun Γ₂ Φ₂ ψ₂ ↦
        let (iForm, iRest) := (Φ₂.length - 2, Φ₂.length - 1)
        -- the form's parts: its equation and the facts of its kind, of m conjuncts in all
        let parts (m : ℕ) (k : ℕ → Deducer) (vars : ℕ := 3) : Deducer := repeatK vars K.exE <|
          repeatK (m - 1) K.conjE fun Γ Φ ψ ↦ k Φ.length Γ Φ ψ
        let facts (n m : ℕ) : List Deducer :=
          ((List.range (m - 2)).map (fun i ↦ n - 2 * (m - 2 - i)) ++ [n - 1]).map fun i ↦
            stage s!"passesForms: the fact {i}" (K.byHyp i)
        let ih : Deducer := stage "passesForms: the hypothesis" (hypOr 0)
        let rest : Deducer := stage "passesForms: the rest's kinds" (K.byHyp iRest)
        let done : Deducer := stage "passesForms: the conclusion" (last K.byHyp)
        dDisjE L iForm
          (stage "passesForms: a definition" <| parts 6 fun n ↦ applyThm K "stepDef" σ
            ([ih] ++ (facts n 6).take 4 ++ invariant ++ (facts n 6).drop 4 ++ [rest]) done)
          (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
            (stage "passesForms: a type abbreviation" <| parts 6 fun n ↦
              applyThm K "stepDeftype" σ ([ih] ++ facts n 6 ++ invariant ++ [rest]) done)
            (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
              (stage "passesForms: a numeral abbreviation" <| parts 8 fun n ↦
                applyThm K "stepDefnum" σ ([ih] ++ facts n 8 ++ invariant ++ [rest]) done)
              (fun Γ Φ ψ ↦ dDisjE L (Φ.length - 1)
                (stage "passesForms: a function" <| parts 8 (vars := 5) fun n ↦
                  applyThm K "stepDefn" σ₅ ([ih] ++ (facts n 8).take 4 ++ invariant ++
                    (facts n 8).drop 4 ++ [rest]) done)
                (stage "passesForms: a template's instance" <|
                  applyThm K "stepGeneric" (fun Γ ↦ [at_ 0 Γ, esA Γ] ++ states Γ)
                    ([ih, stage "passesForms: an instance" (lastOr K)] ++ invariant ++ [rest])
                    done) Γ Φ ψ) Γ Φ ψ)
            Γ Φ ψ) Γ₂ Φ₂ ψ₂) Γ Φ ψ) Γ₁ Φ₁ ψ₁
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
    nil, nil, nil, nil, pc P "Recognize.markers" [fs], fs⟩

/-- The soundness of a program ({name}`programParts`) from the soundness at the states the
passes begin in ({name}`initialPasses`), a hypothesis. The typing's run over the forms with
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
    let passes := (s.hyps P T X₀).foldr (Internal.Logic.imp P.o) (s.concl P T X₀)
    let a : Internal.Thm := ⟨0, [Ls], hs ++ [passes], concl⟩
    let s₀ (Γ : List Tree) : Passes := initialPasses P X₀ (v (Γ.length - 1))
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let nothing := pc P "Typing/OName.nothing" []
    let env0 := pc P "Typing.env0" []
    let tsA (Γ : List Tree) : Term := (s₀ Γ).typed P
    let partA (Γ : List Tree) : Term := Term.subst X₀ fun _ ↦ tsA Γ
    let (hX, hC, hO, hR, hK, hPasses) := (0, 1, 2, 3, 4, 5)
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
              stage "programTop: no datatype" K.byNorm] <|
          -- the final environment's markers the first's, then the conclusion
          K.conjE <| fun Γ Φ ψ ↦
          let (iMs', iC) := (Φ.length - 2, Φ.length - 1)
          normHyps K [iMs'] (stage "programTop: the conclusion" (K.byHyp iC)) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "programTop: not proved" fun _ ↦ none
    pure (a, d))

/-- The soundness of a program whose forms are of the kinds read ({name}`programParts`,
{name}`formsOk`): the soundness at all states ({name}`passesForms`) at the states the passes
begin in, of which the program's soundness follows ({name}`programTop`). In the context of the
forms. -/
def programForms (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("programForms", fun ix E ↦ do
    let K : Kit := ⟨passProg P, S, E, ix, ["eraseDefForm", "recAtThree"]⟩
    let L := K.L
    let Ls := list treeTy
    let some X₀ := partitionT K [Ls] | dbgTrace "programForms: no partition" fun _ ↦ none
    let (hs, concl) ← programParts P T (v 0)
    let a : Internal.Thm := ⟨0, [Ls], hs ++ formsOk P S (v 0), concl⟩
    let s := initialPasses P X₀ (v 0)
    let n := (s.hyps P T X₀).length
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    -- the soundness at the first states, from that at all states and the forms' kinds
    let passes : Deducer := K.cutThm "passesForms" (fun _ ↦ [v 0]) <|
      K.allEΓ (fun _ ↦ s.dv) <| K.allEΓ (fun _ ↦ s.env) <| K.allEΓ (fun _ ↦ s.rej) <|
      K.allEΓ (fun _ ↦ s.tys) <| K.allEΓ (fun _ ↦ s.nums) <| K.allEΓ (fun _ ↦ s.names) <|
      K.allEΓ (fun _ ↦ s.terms) <| K.allEΓ (fun _ ↦ s.ms) <| K.allEΓ (fun _ ↦ s.fs) <|
      last fun iP ↦ repeatK n (dImpI L) <|
        impEs L iP ((List.replicate (n + 1) dHyp).map (stage "programForms: a hypothesis")) dHyp
    let some d := applyThm K "programTop" (fun _ ↦ [v 0])
        ((List.replicate hs.length dHyp).map (stage "programForms: the program") ++
          [stage "programForms: the passes" passes]) dHyp a.ctx a.hyps a.concl
      | dbgTrace "programForms: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness of a program from that at the states its passes begin
in. -/
def programTopDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [globEmpty P S T, numsEmpty P S T, namesEmpty P S T, kwsEmpty P S T, programTop P S T]

/-- The development of the facts of the empty context and of programs without datatypes. -/
def programEmptyDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [envNil P S T, cxNil P S T, recsNoData P S T]

/-- The developments of the soundness of a whole program, each with its certificate's name, in
the order in which each continues from those before it: the runs' ({name}`stepGroups`), the
steps at each kind of form, the induction on the forms and the program's soundness. -/
def programSoundGroups (P : Prog) (S : Defs) (T : Defs3) : List (String × List Step) :=
  stepGroups P S T ++
    [("datatype-program-empty", programEmptyDev P S T),
      ("datatype-program-forms", [eraseDefForm P S, recAtThree P S, eraseOther P S]),
      ("datatype-program-top", programTopDev P S T),
      ("datatype-program-nums", programNumsDev P S),
      ("datatype-program-nums-inv", programNumsInvDev P S T),
      ("datatype-program-src", programSrcDev P S T),
      ("datatype-program-defined", [stepDefined P S T]),
      ("datatype-program-def", [stepDef P S T]),
      ("datatype-program-deftype", [stepDeftype P S T]),
      ("datatype-program-defnum", [numOfParts P S, stepDefnum P S T]),
      ("datatype-program-defn", [stepDefn P S T]),
      ("datatype-program-generic", [xpGeneric P S, checkGeneric P S T, stepGeneric P S T]),
      ("datatype-program-defs", [passesForms P S T]),
      ("datatype-program-sound", [programForms P S T])]

/-- The names of the certificates the developments of the soundness of a whole program continue
from, in order: the base's, the typing's runs', the soundness at every tree's, and those of
atoms, lists, abstractions over one binder, the stage functions at applications and abstractions
over lists of binders. -/
def programSoundBefore : List String :=
  ["datatype-base", "datatype-program", "datatype-closed", "datatype-atom", "datatype-list",
    "datatype-app", "datatype-stages", "datatype-lam"]

/-- The names of the lemmas of the certificates of {name}`programSoundBefore`, in order. -/
def programSoundNames (P : Prog) (S : Defs) (T : Defs3) : Option (List String) := do
  let dev ← baseDev3 P S T
  pure ((dev ++ programDev P S T ++ closedDev P S T ++ atomDev3 P S T ++ listDev3 P S T ++
    appDev3 P S T ++ stagesDev3 P S T ++ lamDev3 P S T).map (·.1))

/-- The developments of the soundness of a whole program ({name}`programSoundGroups`), each
stored as its certificate, after the theorems of the certificates of
{name}`programSoundBefore` and of the developments before it. -/
def programSoundCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := programSoundNames P S T | throw "the base is not stated"
  let thmsOf (c : Stored.Cert) : Except String (List Internal.Thm) :=
    match Stored.declsOfNats c.table with
    | some ds => pure (ds.filterMap fun
      | .language a _ => some a
      | _ => none)
    | none => throw s!"{c.name} does not read back"
  let (_, _, certs) ← (programSoundGroups P S T).foldlM
    (fun (names, before, certs) (cert, steps) ↦ do
      let cs ← certifyAfter P names cert steps before
      let thms ← cs.mapM thmsOf
      pure (names ++ steps.map (·.1), before ++ thms.flatten, certs ++ cs))
    (names, before, ([] : List Stored.Cert))
  pure certs

end GebTests.Prototypes.FreeTopos.Datatypes

end
