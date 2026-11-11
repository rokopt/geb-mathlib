/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeProgram
public meta import GebTests.Prototypes.FreeTopos.DatatypeProgram -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The runs of a program's forms through the datatype language's compiler

The passes of the datatype language's compiler over a program's forms as runs: the state a
pass's step leaves after each form in order, for the expansion, the typing, the reader and the
kernel's check. A run whose state has failed stays failed, so that a run that ends in a state
that has not failed passed through none that had. The steps at the forms of definitions, of type
and numeral abbreviations and of functions are proved, with the forms the expansion writes, in
the order of the forms, the terms the reader ends with, which extend those it has, the kernel's
types of those terms, and the invariants the reading of a definition preserves: the names are
those of definitions, and the definitions are related to the typing environment's. A run of its
own tests the definitions' bodies: at each form, where the expansion's step writes a definition,
whether its body is a source form at the numeral abbreviations the reader has by then.

## Main definitions

* {lit}`runT` — a run of a step function over a list from a state.
* {lit}`readRun`, {lit}`xpRun`, {lit}`kcRun` — the reader's, the expansion's and the kernel
  check's runs.
* {lit}`typedForms` — the typed forms the expansion writes.
* {lit}`plainRun` — the run of the test of the definitions' bodies.
* {lit}`stepGroups` — the developments, each with its certificate's name.

## Tags

internal language, datatypes, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- A run: the state a step function leaves after the elements of a list in order, from a state, by
the prelude's right fold of the elements' continuations, as the compiler's passes over a program's
forms are written. The step is a function of the state and the element. -/
def runT (A St : Tree) (step : Term → Term → Term) (xs s : Term) : Term :=
  let C := exp St St
  Term.app (foldrT A C (Term.lam A (Term.lam C (Term.lam St
    (Term.app (v 1) (step (v 0) (v 2)))))) (Term.lam St (v 0)) xs) s

/-- The type of the reader's state as it reads a program's forms: whether every form has read, the
type abbreviations, the numeral abbreviations, the names of the definitions, and their terms. -/
def progTy : Tree :=
  let Ls := list treeTy
  prod treeTy (prod Ls (prod Ls (prod Ls Ls)))

/-- The reader's state of its parts, none having failed to read. -/
def progState (tys nums names terms : Term) : Term :=
  Term.pair (leafT (numeral 1)) (Term.pair tys (Term.pair nums (Term.pair names terms)))

/-- The reader's run over a list of forms from a state. -/
def readRun (P : Prog) (xs s : Term) : Term :=
  runT treeTy progTy (fun s e ↦ pc P "Reader.progStep" [s, e]) xs s

/-- The program with the reader's step kept folded, for the proofs about the reader's runs. -/
def readProg (P : Prog) : Prog := { P with folded := P.folded ++ ["Reader.progStep"] }

/-- An equation by normalization with further rules after those of the hypotheses given, the
first hypothesis among them where {lit}`first` holds. -/
def byNormWith (K : Kit) (extra : List Internal.NormRule) (first : Bool := false) : Deducer :=
  dEq fun Γ Φ t u ↦
    let rs := (if first then [Internal.NormRule.hyp 0] else []) ++ K.rules Φ ++ extra
    byMode .full K.G K.E 0 rs Γ (rwHyps rs Φ) t u

/-- The reader's step from a state that has failed is the failed state of its parts: the step
unfolded, the state's test false. In the context of the form and the state. -/
def progStepFailed (P : Prog) (S : Defs) : Step :=
  ("progStepFailed", fun ix E ↦ do
    let K : Kit := ⟨readProg P, S, E, ix, []⟩
    let Γ := [treeTy, progTy]
    let a : Internal.Thm := ⟨0, Γ, [Term.eq (call D.lab [] [Term.fst (v 1)]) (nilT bitTy)],
      Term.eq (pc P "Reader.progStep" [v 1, v 0]) (Term.pair (leafT bnilT) (Term.snd (v 1)))⟩
    let some d := byNormWith K [.delta (P.idx "Reader.progStep")] true a.ctx a.hyps a.concl
      | dbgTrace "progStepFailed: not proved" fun _ ↦ none
    pure (a, d))

/-- The reader's run from a state that has failed ends in a state that has failed: by induction on
the forms, at a construction the induction hypothesis at the state the step leaves, which has
failed ({name}`progStepFailed`). In the context of the forms, under the state. -/
def readFailed (P : Prog) (S : Defs) : Step :=
  ("readFailed", fun ix E ↦ do
    let K : Kit := ⟨readProg P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let failedT (s : Term) : Term := Term.eq (call D.lab [] [Term.fst s]) (nilT bitTy)
    -- under the quantifier: the state v0, the forms v1
    let φ := Internal.Logic.all o progTy (Term.lam progTy (Internal.Logic.imp o (failedT (v 0))
      (failedT (readRun P (v 1) (v 0)))))
    let some d₀ := dAllI L (dImpI L fun Γ Φ ψ ↦
          normHyps K [Φ.length - 1] K.byNorm Γ Φ ψ) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "readFailed: empty" fun _ ↦ none
    -- a construction, under the quantifier the state v0, the tail v1 and the head v2: the
    -- induction hypothesis at the state the step leaves, its premise by the step's equation
    let cons : Deducer := dAllI L <| dImpI L <|
      dAllE L K.G K.E 0 (pc P "Reader.progStep" [v 0, v 2]) fun Γ Φ ψ ↦
        let last : Deducer := fun Γ Φ ψ ↦ normHyps K [Φ.length - 1] (K.solve 2) Γ Φ ψ
        dImpE L (Φ.length - 1)
          (applyThm K "progStepFailed" (fun _ ↦ [v 2, v 0]) [dHyp] last) last Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "readFailed: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The form of a definition: the list of the definition keyword's atom, a name and a term. -/
def defForm (P : Prog) (n c : Term) : Term := listNode [pc P "Datatype.aDef" [], n, c]

/-- The reader's step at a definition's form, from a state that has not failed, where the state it
leaves has not: the name is an atom's, fresh in the state, the term's numeral abbreviations
expanded resolves, and the state left has the name after the names and the resolved term after the
terms. Each of the step's tests decided, a false one refuting the hypothesis. In the context of
the term, the name and the state's parts. -/
def readDef (P : Prog) (S : Defs) : Step :=
  ("readDef", fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++ ["Reader.isFresh"] }, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [treeTy, treeTy, Ls, Ls, Ls, Ls]
    let (c, n, terms, names, nums, tys) := (v 0, v 1, v 2, v 3, v 4, v 5)
    let s := progState tys nums names terms
    let step := pc P "Reader.progStep" [s, defForm P n c]
    let nm := pc P "Reader.nameOf" [n]
    let res := pc P "Reader.resolve" [tys, names, pc P "Reader.expandNums" [nums, c], nilT treeTy]
    let tests : List Term := [pc P "Reader.isAtom" [n],
      pc P "Reader.isFresh" [tys, nums, names, nm], pc P "Prelude.isSome" [res]]
    let after := progState tys nums (pc P "Prelude.append" [names, pc P "Prelude.single" [nm]])
      (pc P "Prelude.append" [terms, pc P "Prelude.single" [pc P "Prelude.get" [res]]])
    let parts := tests.map (truth P.o) ++ [Term.eq step after]
    let a : Internal.Thm := ⟨0, Γ, [truth P.o (Term.fst step)],
      parts.dropLast.foldr (Internal.Logic.conj P.o) (parts.getLastD Term.star)⟩
    let refute (msg : String) : Deducer := linkK K s!"readDef: {msg}" (K.hypFalse 0)
    let some d := (tests.zipIdx.foldr
        (fun (t, i) k ↦ decideIn K (fun Γ' ↦ sh (Γ'.length - Γ.length) t) (refute s!"test {i}") k)
        (linkK K "readDef: read" (K.solve 6))) a.ctx a.hyps a.concl
      | dbgTrace "readDef: not proved" fun _ ↦ none
    pure (a, d))

/-- Tests decided in turn, each as expected and its other case refuted by a hypothesis: the tests
in a context of {lit}`n₀` variables, each with whether it is expected to hold and the index of the
hypothesis its other case contradicts, the test's truth where it is expected to hold and the
truth's negation where it is not. -/
def decideAll (K : Kit) (n₀ : ℕ) (tests : List (Term × Bool × ℕ)) (k : Deducer) : Deducer :=
  tests.zipIdx.foldr (fun ((t, expect, h), i) k ↦
    let test (Γ : List Tree) : Term := sh (Γ.length - n₀) t
    let msg := s!"decideAll: test {i}"
    if expect then decideIn K test (linkK K msg (K.hypFalse h)) k
    else decideIn K test k (linkK K msg (dImpE K.L h (K.solve 3) (dFalse K.L dHyp)))) k

/-- The reader's step at the form of a type or numeral abbreviation, the list of a head, a name
and a body, from a state that has not failed, where the state it leaves has not: the head named
by the keyword {lit}`kw` and by none of the keywords {lit}`before`, which the step tests first, the
name is an atom's, fresh in the state, the body reads by {lit}`read`, and the state left is
{lit}`after` of the name and the reading. In the context of the body, the name, the head and the
state's parts. -/
def readAbbrev (P : Prog) (S : Defs) (name kw : String) (before : List String)
    (read : Term → Term → Term → Term)
    (after : Term → Term → Term → Term → Term → Term → Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++ ["Reader.isFresh"] }, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [treeTy, treeTy, treeTy, Ls, Ls, Ls, Ls]
    let (x, n, h, terms, names, nums, tys) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let s := progState tys nums names terms
    let step := pc P "Reader.progStep" [s, listNode [h, n, x]]
    let nm := pc P "Reader.nameOf" [n]
    let r := read tys nums x
    let named (k : String) : Term := pc P "Reader.named" [h, pc P k []]
    let hyps := before.map (fun k ↦ notTest P.o (named k)) ++
      [truth P.o (named kw), truth P.o (Term.fst step)]
    let ok := hyps.length - 1
    let tests : List Term := [pc P "Reader.isAtom" [n],
      pc P "Reader.isFresh" [tys, nums, names, nm], pc P "Prelude.isSome" [r]]
    let parts := tests.map (truth P.o) ++
      [Term.eq step (after tys nums names terms nm (pc P "Prelude.get" [r]))]
    let a : Internal.Thm := ⟨0, Γ, hyps,
      parts.dropLast.foldr (Internal.Logic.conj P.o) (parts.getLastD Term.star)⟩
    let decided := before.zipIdx.map (fun (k, i) ↦ (named k, false, i)) ++
      [(named kw, true, before.length)] ++ tests.map fun t ↦ (t, true, ok)
    let some d := decideAll K Γ.length decided (linkK K s!"{name}: read" (K.solve 6))
        a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The entry of an abbreviation: the node of label 0 over a name and its meaning. -/
def abbrevT (P : Prog) (nm x : Term) : Term := pc P "Reader.node2" [leafT bnilT, nm, x]

/-- The reader's step at a type abbreviation's form ({name}`readAbbrev`): the body reads as a type,
and the state left has the abbreviation before the type abbreviations. -/
def readDeftype (P : Prog) (S : Defs) : Step :=
  readAbbrev P S "readDeftype" "Reader.kwDeftype" ["Reader.kwDef"]
    (fun tys _ x ↦ pc P "Reader.readType" [tys, x])
    (fun tys nums names terms nm r ↦
      progState (consT treeTy (abbrevT P nm r) tys) nums names terms)

/-- The reader's step at a numeral abbreviation's form ({name}`readAbbrev`): the body is a numeral
or abbreviates one, and the state left has the abbreviation before the numeral abbreviations. -/
def readDefnum (P : Prog) (S : Defs) : Step :=
  readAbbrev P S "readDefnum" "Reader.kwDefnum" ["Reader.kwDef", "Reader.kwDeftype"]
    (fun _ nums x ↦ pc P "Reader.numOf" [nums, x])
    (fun tys nums names terms nm r ↦
      progState tys (consT treeTy (abbrevT P nm r) nums) names terms)

/-- No tree is named by both of two keywords: were it, it is an atom, whose name is the first
keyword's by the soundness of the equality of trees ({lit}`equalSound`), which is not the second's.
In the context of the tree. -/
def namedApart (P : Prog) (S : Defs) (kwA kwB : String) : Step :=
  (s!"namedApart/{kwA}/{kwB}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let named (kw : String) : Term := truth P.o (pc P "Reader.named" [v 0, pc P kw []])
    let a : Internal.Thm := ⟨0, [treeTy], [named kwA, named kwB], Internal.Logic.ff P.o⟩
    let nameAt (Γ : List Tree) : Term := pc P "Reader.nameOf" [v (Γ.length - 1)]
    let apart : Deducer := K.cutThm "equalSound" (fun Γ ↦ [nameAt Γ]) <|
      K.allEΓ (fun _ ↦ pc P kwA []) <|
      K.impE (linkK K "namedApart: the first" (K.solve 3)) fun Γ Φ ψ ↦
        normHyps K [Φ.length - 1] (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ 1 ++ [.delta D.equal]) .full) 1
            (dFalse K.L dHyp) Γ Φ ψ) Γ Φ ψ
    let some d := (decideIn K (fun Γ ↦ pc P "Reader.isAtom" [v (Γ.length - 1)]) (K.hypFalse 0) <|
        decideBits K (fun Γ ↦ call D.equal [] [nameAt Γ, pc P kwA []])
          (linkK K "namedApart: unequal" (K.hypFalse 0))
          (linkK K "namedApart: named" apart)) a.ctx a.hyps a.concl
      | dbgTrace s!"namedApart/{kwA}/{kwB}: not proved" fun _ ↦ none
    pure (a, d))

/-- Tests decided in turn in a context of {lit}`n₀` variables: each with the deducer that refutes
its not holding and the one that refutes its holding, where there is one; a case not refuted
continues. -/
def decideEach (K : Kit) (n₀ : ℕ) (tests : List (Term × Option Deducer × Option Deducer))
    (k : Deducer) : Deducer :=
  tests.zipIdx.foldr (fun ((t, kF, kT), i) k ↦
    decideIn K (fun Γ ↦ sh (Γ.length - n₀) t)
      ((kF.map (linkK K s!"decideEach: test {i} not holding")).getD k)
      ((kT.map (linkK K s!"decideEach: test {i} holding")).getD k)) k

/-- A goal refuted by the negation of a truth, the hypothesis of index {lit}`h`, the truth by
normalization. -/
def refuteNot (K : Kit) (h : ℕ) : Deducer := dImpE K.L h (K.solve 3) (dFalse K.L dHyp)

/-- That a test does not hold, as the equation of its label with the empty bitstring. -/
def falseT (t : Term) : Term := Term.eq (call D.lab [] [t]) (nilT bitTy)

/-- The typing's state of an environment and a rejection, and the typing's step from it. -/
def checkStepAt (P : Prog) (E r f : Term) : Term :=
  pc P "Typing.checkStep" [Term.pair E r, f]

/-- The typing's state of an environment without a rejection. -/
def checkOk (P : Prog) (E : Term) : Term := Term.pair E (pc P "Typing/OName.nothing" [])

/-- The typing's run from a state with a rejection leaves the state, at any rejection: by
induction on the forms; at a construction the rejection's test decided and the head a template's
instance or not, the step returning the state, the induction hypothesis at it. In the context of
the forms, under the state. -/
def checkAllStuck (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkAllStuck", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let CS := prod T.envTy treeTy
    let rejected (s : Term) : Term := truth o (pc P "Prelude.isSome" [Term.snd s])
    -- under the quantifier: the state v0, the forms v1
    let φ := Internal.Logic.all o CS (Term.lam CS (Internal.Logic.imp o (rejected (v 0))
      (Term.eq (pc P "Typing.checkAll" [v 0, v 1]) (v 0))))
    let some d₀ := dAllI L (dImpI L K.byNorm) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "checkAllStuck: empty" fun _ ↦ none
    -- a construction, under the quantifier the state v0, the tail v1 and the head v2: the
    -- induction hypothesis at the state, its premise the hypothesis; the tests decided
    let cons : Deducer := dAllI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let hR := Φ₁.length - 1
      (dAllE L K.G K.E 0 (v 0) <| K.impE dHyp <| fun Γ Φ ψ ↦
        normHyps K [Φ.length - 1] (decideEach K Γ.length
          [(pc P "Prelude.isSome" [Term.snd (v 0)], some (K.hypFalse hR), none),
            (eqL (apps labelK [v 2]) (leafT (numeral 15)), none, none)]
          (linkK K "checkAllStuck: stuck" (K.solve 3))) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "checkAllStuck: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The typing's step at a definition's form, from a state without a rejection, where the state it
leaves has none: the term has a type in the empty context, and the state left declares the name
at that type after the definitions. In the context of the term, the name, the rejection and the
environment. -/
def checkDef (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkDef", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Γ := [treeTy, treeTy, treeTy, T.envTy]
    let (x, n, r, Ev) := (v 0, v 1, v 2, v 3)
    let step := checkStepAt P Ev r (defForm P n x)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let syn := pc P "Typing.synIn" [Ev, nilT treeTy, x]
    let after := checkOk P (pc P "Typing.withDefs" [Ev, pc P "Typing/Abbrs.append"
      [pc P "Typing.envDefs" [Ev], pc P "Typing/Abbrs.single"
        [pc P "Typing.abbr" [pc P "Typing.atomName" [n], pc P "Prelude.get" [syn]]]]])
    let a : Internal.Thm := ⟨0, Γ, [notTest P.o (isSome r), notTest P.o (isSome (Term.snd step))],
      Internal.Logic.conj P.o (truth P.o (isSome syn)) (Term.eq step after)⟩
    let some d := decideEach K Γ.length
        [(isSome r, none, some (refuteNot K 0)), (isSome syn, some (refuteNot K 1), none)]
        (linkK K "checkDef: checked" (K.solve 4)) a.ctx a.hyps a.concl
      | dbgTrace "checkDef: not proved" fun _ ↦ none
    pure (a, d))

/-- The typing's step at the form of a type or numeral abbreviation, the list of a head, a name
and a body, from a state without a rejection, where the state it leaves has none: the head named
by the keyword {lit}`kw` and by none of {lit}`before`, the test {lit}`test` of the name and the
body holds, or does not where {lit}`holds` is false, and the state left is {lit}`after`. In the
context of the body, the name, the head, the rejection and the environment. -/
def checkAbbrev (P : Prog) (S : Defs) (T : Defs3) (name kw : String) (before : List String)
    (test : Term → Term → Term → Term) (holds : Bool) (after : Term → Term → Term → Term) :
    Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Γ := [treeTy, treeTy, treeTy, treeTy, T.envTy]
    let (x, n, h, r, Ev) := (v 0, v 1, v 2, v 3, v 4)
    let step := checkStepAt P Ev r (listNode [h, n, x])
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let named (k : String) : Term := pc P "Reader.named" [h, pc P k []]
    let t := test Ev n x
    let hyps := before.map (fun k ↦ notTest P.o (named k)) ++
      [truth P.o (named kw), notTest P.o (isSome r), notTest P.o (isSome (Term.snd step))]
    let (hKw, hR, hOk) := (before.length, before.length + 1, before.length + 2)
    let a : Internal.Thm := ⟨0, Γ, hyps, Internal.Logic.conj P.o
      (if holds then truth P.o t else falseT t) (Term.eq step (checkOk P (after Ev n x)))⟩
    -- the head named by the postulates' keyword is not named by the abbreviation's
    let apart : Deducer := fun Γ' Φ ψ ↦
      applyThm K s!"namedApart/Typing.kwPostulate/{kw}" (fun _ ↦ [sh (Γ'.length - Γ.length) h])
        [K.solve 3, dHyp] (dFalse K.L dHyp) Γ' Φ ψ
    let decided : List (Term × Option Deducer × Option Deducer) :=
      [(isSome r, none, some (refuteNot K hR)), (named "Typing.kwSort", none, none)] ++
      before.zipIdx.map (fun (k, i) ↦ (named k, none, some (refuteNot K i))) ++
      [(named "Typing.kwPostulate", none, some apart), (named kw, some (K.hypFalse hKw), none),
        (t, if holds then some (refuteNot K hOk) else none,
          if holds then none else some (refuteNot K hOk))]
    let some d := decideEach K Γ.length decided (linkK K s!"{name}: checked" (K.solve 4))
        a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The typing's step at a type abbreviation's form ({name}`checkAbbrev`): the body reads as a
type, and the state left has the name's abbreviation of it before the abbreviations. -/
def checkDeftype (P : Prog) (S : Defs) (T : Defs3) : Step :=
  let readTy (Ev x : Term) : Term := pc P "Typing.readTy" [Ev, x]
  checkAbbrev P S T "checkDeftype" "Reader.kwDeftype" ["Reader.kwDef"]
    (fun Ev _ x ↦ pc P "Prelude.isSome" [readTy Ev x]) true
    (fun Ev n x ↦ pc P "Typing.withAl" [Ev, consT treeTy
      (pc P "Typing.abbr" [pc P "Typing.atomName" [n], pc P "Prelude.get" [readTy Ev x]])
      (pc P "Typing.envAl" [Ev])])

/-- The typing's step at a numeral abbreviation's form ({name}`checkAbbrev`): the name is no
numeral, and the state left has the name after the numeral names. -/
def checkDefnum (P : Prog) (S : Defs) (T : Defs3) : Step :=
  let nm (n : Term) : Term := pc P "Typing.atomName" [n]
  checkAbbrev P S T "checkDefnum" "Reader.kwDefnum" ["Reader.kwDef", "Reader.kwDeftype"]
    (fun _ n _ ↦ pc P "Prelude.isSome" [pc P "Reader.numeral" [call D.children [] [nm n]]]) false
    (fun Ev n _ ↦ pc P "Typing.withNums" [Ev, pc P "Typing/Names.append"
      [pc P "Typing.envNums" [Ev], pc P "Typing/Names.single" [nm n]]])

/-- The development of the typing's steps at a program's forms. -/
def programCheckDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [checkAllStuck P S T, checkDef P S T, checkDeftype P S T, checkDefnum P S T]

/-- The type of the expansion's state as it expands a program's forms: whether every form has
expanded, the declarations, and the forms written, the most recent first. -/
def xpTy : Tree := prod treeTy (prod (list treeTy) (list treeTy))

/-- The expansion's state of its declarations and the forms written, none having failed. -/
def xpState (dv out : Term) : Term := Term.pair (leafT (numeral 1)) (Term.pair dv out)

/-- The expansion's step at a form from a state: a template's instance's, or a form's. -/
def xpStepT (P : Prog) (s e : Term) : Term :=
  condT xpTy (call D.lab [] [pc P "Prelude.and" [pc P "Datatype.isListTx" [e],
      pc P "Datatype.namedTx" [pc P "Datatype.nthTx" [pc P "Datatype.elems" [e], leafT bnilT],
        pc P "Datatype.kwGeneric" []]]])
    (pc P "Datatype.genericStep" [s, e]) (pc P "Datatype.xpStep" [s, e])

/-- The expansion's run over a list of forms from a state. -/
def xpRun (P : Prog) (xs s : Term) : Term := runT treeTy xpTy (xpStepT P) xs s

/-- The program with the expansion's steps kept folded, for the proofs about its runs. -/
def xpProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Datatype.xpStep", "Datatype.genericStep"] }

/-- The program with the declarations of datatypes kept folded, for the proofs that unfold the
expansion's step at a form that declares none. -/
def xpStepProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Datatype.dataDecl", "Datatype.marker"] }

/-- The expansion's step at a list of a head, a name and a body, from a state that has not failed,
where the head is named by the keyword {lit}`kw` and by none of the keywords {lit}`before`, which
the step tests first, and by the keyword of functions or not: the test {lit}`test` of the
declarations and the body holds where the state the step leaves has not failed, and that state is
{lit}`after` of the declarations, the forms written, the head, the name and the body. In the
context of the body, the name, the head, the forms written and the declarations. -/
def xpThree (P : Prog) (S : Defs) (name kw : String) (before : List String)
    (test : Option (Term → Term → Term)) (after : Term → Term → Term → Term → Term → Term) :
    Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨xpStepProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [treeTy, treeTy, treeTy, Ls, Ls]
    let (x, n, h, out, dv) := (v 0, v 1, v 2, v 3, v 4)
    let step := pc P "Datatype.xpStep" [xpState dv out, listNode [h, n, x]]
    let named (k : String) : Term := pc P "Datatype.namedTx" [h, pc P k []]
    let hyps := before.map (fun k ↦ notTest P.o (named k)) ++ [truth P.o (named kw)] ++
      (test.map fun _ ↦ truth P.o (Term.fst step)).toList
    let hOk := before.length + 1
    let eqn := Term.eq step (after dv out h n x)
    let a : Internal.Thm := ⟨0, Γ, hyps, match test with
      | some t => Internal.Logic.conj P.o (truth P.o (t dv x)) eqn
      | none => eqn⟩
    let decided : List (Term × Option Deducer × Option Deducer) :=
      before.zipIdx.map (fun (k, i) ↦ (named k, none, some (refuteNot K i))) ++
      [(named "Datatype.kwDefn", none, none), (named kw, some (K.hypFalse before.length), none)] ++
      (test.map fun t ↦ (t dv x, some (K.hypFalse hOk), none)).toList
    let some d := decideEach K Γ.length decided (linkK K s!"{name}: expanded" (K.solve 4))
        a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The keywords the expansion's step tests before the definitions' keyword. -/
def xpData : List String := ["Datatype.kwData", "Datatype.kwTreeData"]

/-- The expansion's step at a definition's form ({name}`xpThree`): the body expands under the
declarations, and the state left has the definition of the name as the body's expansion before
the forms written. -/
def xpDef (P : Prog) (S : Defs) : Step :=
  let ex (dv x : Term) : Term := pc P "Datatype.expandExpr" [dv, x]
  xpThree P S "xpDef" "Reader.kwDef" xpData (some fun dv x ↦ pc P "Prelude.isSome" [ex dv x])
    (fun dv out _ n x ↦
      xpState dv (consT treeTy (defForm P n (pc P "Prelude.get" [ex dv x])) out))

/-- The expansion's step at a type abbreviation's form ({name}`xpThree`): the state left has the
name's abbreviation of the body, its abbreviations expanded, after the declarations, and the form
before the forms written. -/
def xpDeftype (P : Prog) (S : Defs) : Step :=
  xpThree P S "xpDeftype" "Reader.kwDeftype" (xpData ++ ["Reader.kwDef"]) none
    (fun dv out h n x ↦ xpState (pc P "Datatype/Decls.append" [dv, pc P "Datatype/Decls.single"
        [pc P "Datatype.aliasD" [pc P "Datatype.atomName" [n],
          pc P "Datatype.expandAliases" [dv, x]]]])
      (consT treeTy (listNode [h, n, x]) out))

/-- The expansion's step at a numeral abbreviation's form ({name}`xpThree`): the state left has
the form before the forms written. -/
def xpDefnum (P : Prog) (S : Defs) : Step :=
  xpThree P S "xpDefnum" "Reader.kwDefnum" (xpData ++ ["Reader.kwDef", "Reader.kwDeftype"]) none
    (fun dv out h n x ↦ xpState dv (consT treeTy (listNode [h, n, x]) out))

/-- The form of a function's definition as the expansion writes it: the definition of the name as
the abstractions over the binders around the body, bound at the result type. -/
def defnBody (P : Prog) (bs R b : Term) : Term :=
  let aR := pc P "Datatype.aR" []
  pc P "Datatype.curry" [pc P "Datatype.bindersTx" [bs], pc P "Datatype.sLet" [aR, R, b, aR]]

/-- The expansion's step at a function's form, the list of a head named by the keyword of
functions and by no keyword of datatypes, a name, binders, a result type and a body, from a state
that has not failed, where the state it leaves has not: the body expands under the declarations,
and the state left has the definition of the name, the abstractions over the binders around the
body's expansion, before the forms written. In the context of the body, the result type, the
binders, the name, the head, the forms written and the declarations. -/
def xpDefn (P : Prog) (S : Defs) : Step :=
  ("xpDefn", fun ix E ↦ do
    let K : Kit := ⟨xpStepProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [treeTy, treeTy, treeTy, treeTy, treeTy, Ls, Ls]
    let (x, R, bs, n, h, out, dv) := (v 0, v 1, v 2, v 3, v 4, v 5, v 6)
    let step := pc P "Datatype.xpStep" [xpState dv out, listNode [h, n, bs, R, x]]
    let named (k : String) : Term := pc P "Datatype.namedTx" [h, pc P k []]
    let ex := pc P "Datatype.expandExpr" [dv, x]
    let hyps := xpData.map (fun k ↦ notTest P.o (named k)) ++
      [truth P.o (named "Datatype.kwDefn"), truth P.o (Term.fst step)]
    let a : Internal.Thm := ⟨0, Γ, hyps, Internal.Logic.conj P.o
      (truth P.o (pc P "Prelude.isSome" [ex]))
      (Term.eq step (xpState dv (consT treeTy
        (defForm P n (defnBody P bs R (pc P "Prelude.get" [ex]))) out)))⟩
    let decided : List (Term × Option Deducer × Option Deducer) :=
      xpData.zipIdx.map (fun (k, i) ↦ (named k, none, some (refuteNot K i))) ++
      [(named "Datatype.kwDefn", some (K.hypFalse 2), none),
        (pc P "Prelude.isSome" [ex], some (K.hypFalse 3), none)]
    let some d := decideEach K Γ.length decided (linkK K "xpDefn: expanded" (K.solve 4))
        a.ctx a.hyps a.concl
      | dbgTrace "xpDefn: not proved" fun _ ↦ none
    pure (a, d))

/-- That a state's flag does not hold, as the equation of its label with the empty bitstring. -/
def failedT (s : Term) : Term := Term.eq (call D.lab [] [Term.fst s]) (nilT bitTy)

/-- The expansion's step from a state that has failed leaves a state that has failed: the form a
template's instance or not, the step unfolded. In the context of the form and the state. -/
def xpStepFailed (P : Prog) (S : Defs) : Step :=
  ("xpStepFailed", fun ix E ↦ do
    let K : Kit := ⟨xpStepProg P, S, E, ix, []⟩
    let Γ := [treeTy, xpTy]
    let a : Internal.Thm := ⟨0, Γ, [failedT (v 1)], failedT (xpStepT P (v 1) (v 0))⟩
    let test := pc P "Prelude.and" [pc P "Datatype.isListTx" [v 0],
      pc P "Datatype.namedTx" [pc P "Datatype.nthTx" [pc P "Datatype.elems" [v 0], leafT bnilT],
        pc P "Datatype.kwGeneric" []]]
    let some d := normHyps K [0] (decideEach K Γ.length [(test, none, none)]
        (linkK K "xpStepFailed: failed" (byNormWith K [] true))) a.ctx a.hyps a.concl
      | dbgTrace "xpStepFailed: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion's run from a state that has failed ends in a state that has failed: by induction
on the forms, at a construction the induction hypothesis at the state the step leaves, which has
failed ({name}`xpStepFailed`). In the context of the forms, under the state. -/
def xpFailed (P : Prog) (S : Defs) : Step :=
  ("xpFailed", fun ix E ↦ do
    let K : Kit := ⟨xpProg P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifier: the state v0, the forms v1
    let φ := Internal.Logic.all o xpTy (Term.lam xpTy (Internal.Logic.imp o (failedT (v 0))
      (failedT (xpRun P (v 1) (v 0)))))
    let last : Deducer := fun Γ Φ ψ ↦ normHyps K [Φ.length - 1] (K.solve 2) Γ Φ ψ
    let some d₀ := dAllI L (dImpI L last) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "xpFailed: empty" fun _ ↦ none
    let cons : Deducer := dAllI L <| dImpI L <|
      dAllE L K.G K.E 0 (xpStepT P (v 0) (v 2)) fun Γ Φ ψ ↦
        dImpE L (Φ.length - 1)
          (applyThm K "xpStepFailed" (fun _ ↦ [v 2, v 0]) [dHyp] last) last Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "xpFailed: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The development of the expansion's steps at a program's forms. -/
def programExpandDev (P : Prog) (S : Defs) : List Step :=
  [xpDef P S, xpDeftype P S, xpDefnum P S, xpDefn P S, xpStepFailed P S, xpFailed P S]

/-- The bitstring a conditional's normal form tests, where a term is one. -/
def headBits (X : Term) : Option Term :=
  match X.label, X.children with
  | .app, [f, _] => match f.label, f.children with
    | .app, [lr, _] => match lr.label, lr.children with
      | .listRec, [z, _, bits] => match z.label, z.children with
        | .lam _, [zb] => match zb.label with
          | .lam _ => some bits
          | _ => none
        | _, _ => none
      | _, _ => none
    | _, _ => none
  | _, _ => none

/-- A goal proved by {lit}`close` once a term's normal form is no conditional: while it is one,
to a depth, the bitstring it tests split into its cases. The term in a context of {lit}`n₀`
variables. -/
def splitCond (K : Kit) (n₀ : ℕ) (t : Term) (depth : ℕ) (close : Deducer) : Deducer :=
  Nat.rec (motive := fun _ ↦ Deducer) close (fun _ rec Γ Φ ψ ↦
    match evalRw K.G K.E (K.rules Φ) .full Γ Φ (sh (Γ.length - n₀) t) with
    | some (X, _) => match headBits X with
      | some bits => K.listCase bitTy bits rec rec Γ Φ ψ
      | none => close Γ Φ ψ
    | none => dbgTrace "splitCond: no normal form" fun _ ↦ none) depth

/-- The last hypothesis normalized, then the goal by normalization, truth and conjunctions. -/
def byLast (K : Kit) : Deducer := fun Γ Φ ψ ↦ normHyps K [Φ.length - 1] (K.solve 3) Γ Φ ψ

/-- A test that is some value holds: its label decided. In the context of the tree. -/
def someTruth (P : Prog) (S : Defs) : Step :=
  ("someTruth", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy], [truth P.o (pc P "Prelude.isSome" [v 0])],
      truth P.o (v 0)⟩
    let some d := decideIn K (fun Γ ↦ v (Γ.length - 1)) (K.hypFalse 0) (K.solve 2)
        a.ctx a.hyps a.concl
      | dbgTrace "someTruth: not proved" fun _ ↦ none
    pure (a, d))

/-- The concatenation of lists of forms is associative: by induction on the first. In the context
of the first, under the second and the third. -/
def appendAssoc (P : Prog) (S : Defs) : Step :=
  ("appendAssoc", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the third v0, the second v1, the first v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
      (Term.eq (txsApp P (txsApp P (v 2) (v 1)) (v 0)) (txsApp P (v 2) (txsApp P (v 1) (v 0)))))))
    let some d₀ := dAllI L (dAllI L K.byNorm) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "appendAssoc: empty" fun _ ↦ none
    let cons : Deducer := dAllI L <| dAllI L <| dAllE L K.G K.E 0 (v 1) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (v 0) (normLastK K K.byNorm) Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "appendAssoc: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A typing's run that ends without a rejection began without one: were there one, the run would
leave its state ({name}`checkAllStuck`). In the context of the forms and the state. -/
def checkPrefix (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("checkPrefix", fun ix E ↦ do
    let K : Kit := ⟨runProg P, S, E, ix, []⟩
    let rejected (s : Term) : Term := pc P "Prelude.isSome" [Term.snd s]
    let a : Internal.Thm := ⟨0, [list treeTy, prod T.envTy treeTy],
      [notTest P.o (rejected (pc P "Typing.checkAll" [v 1, v 0]))], notTest P.o (rejected (v 1))⟩
    let some d := (dImpI K.L <| K.cutThm "checkAllStuck" (fun _ ↦ [v 0]) <|
        K.allEΓ (fun _ ↦ v 1) <| K.impE dHyp fun Γ Φ ψ ↦
        normHyps K [Φ.length - 1] (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0
            (dImpE K.L 0 (K.byHyp 1) (dFalse K.L dHyp)) Γ Φ ψ) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "checkPrefix: not proved" fun _ ↦ none
    pure (a, d))

/-- A run that ends in a state that has not failed began in one, by the lemma {lit}`failed` that a
run from a state that has failed ends in one: the state's flag decided. In the context of the
forms and the state. -/
def runPrefix (P : Prog) (S : Defs) (K₀ : Prog) (name failed : String) (St : Tree)
    (run : Term → Term → Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨K₀, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [list treeTy, St], [truth P.o (Term.fst (run (v 0) (v 1)))],
      truth P.o (Term.fst (v 1))⟩
    let lAt (Γ : List Tree) : Term := v (Γ.length - 2)
    let sAt (Γ : List Tree) : Term := v (Γ.length - 1)
    let some d := decideIn K (fun Γ ↦ Term.fst (sAt Γ))
        (K.cutThm failed (fun Γ ↦ [lAt Γ]) <| K.allEΓ sAt <|
          K.impE (linkK K s!"{name}: failed" (K.solve 3)) fun Γ Φ ψ ↦
            normHyps K [Φ.length - 1] (linkK K s!"{name}: the run" (K.hypFalse 0)) Γ Φ ψ)
        (K.solve 2) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The reversal of a list of forms onto forms: the run of the construction of each element
before the forms reversed so far. -/
def revRun (xs acc : Term) : Term :=
  runT treeTy (list treeTy) (fun acc x ↦ consT treeTy x acc) xs acc

/-- The reversal of a concatenation onto forms is that of the second list onto the first's: by
induction on the first. In the context of the first, under the second and the forms. -/
def revRunAppend (P : Prog) (S : Defs) : Step :=
  ("revRunAppend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the forms v0, the second v1, the first v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
      (Term.eq (revRun (txsApp P (v 2) (v 1)) (v 0)) (revRun (v 1) (revRun (v 2) (v 0)))))))
    let some d₀ := dAllI L (dAllI L K.byNorm) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "revRunAppend: empty" fun _ ↦ none
    -- a construction: the induction hypothesis at the second and at the forms after the head
    let cons : Deducer := dAllI L <| dAllI L <| dAllE L K.G K.E 0 (v 1) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (consT treeTy (v 3) (v 0)) (normLastK K K.byNorm) Γ Φ ψ
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "revRunAppend: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The reversal of a list of forms. -/
def reverseT (P : Prog) (xs : Term) : Term := pc P "Datatype/Txs.reverse" [xs]

/-- The reversal of a list with a form after it is the form before the list's reversal
({name}`revRunAppend`). In the context of the list and the form. -/
def reverseSnoc (P : Prog) (S : Defs) : Step :=
  ("reverseSnoc", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let one (x : Term) : Term := consT treeTy x (nilT treeTy)
    let a : Internal.Thm := ⟨0, [Ls, treeTy], [],
      Term.eq (reverseT P (txsApp P (v 0) (one (v 1)))) (consT treeTy (v 1) (reverseT P (v 0)))⟩
    let some d := (K.cutThm "revRunAppend" (fun _ ↦ [v 0]) <| K.allEΓ (fun _ ↦ one (v 1)) <|
        K.allEΓ (fun _ ↦ nilT treeTy) (byLast K)) a.ctx a.hyps a.concl
      | dbgTrace "reverseSnoc: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion's step from a state with forms written, against that from the state with none:
where the latter has not failed, it is the state of some declarations and forms, and the former
that of those declarations and of those forms before the forms written; where it has failed, the
former is the latter. The tests of the step, a template's instance's or a form's, decided until
the latter is no conditional. In the context of the form, the forms written and the
declarations. -/
def xpStepOut (P : Prog) (S : Defs) : Step :=
  ("xpStepOut", fun ix E ↦ do
    let K : Kit := ⟨xpStepProg P, S, E, ix, ["appendNil"]⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let Γ := [treeTy, Ls, Ls]
    let (e, out, dv) := (v 0, v 1, v 2)
    let s₀ := xpStepT P (xpState dv (nilT treeTy)) e
    let s₁ := xpStepT P (xpState dv out) e
    let ex (b : Term) : Term := Internal.Logic.ex o Ls (Term.lam Ls b)
    let a : Internal.Thm := ⟨0, Γ, [], Internal.Logic.conj o
      (Internal.Logic.imp o (truth o (Term.fst s₀)) (ex (ex (Internal.Logic.conj o
        (Term.eq (sh 2 s₀) (xpState (v 1) (v 0)))
        (Term.eq (sh 2 s₁) (xpState (v 1) (txsApp P (v 0) (sh 2 out))))))))
      (Internal.Logic.imp o (notTest o (Term.fst s₀)) (Term.eq s₁ s₀))⟩
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    let parts : Deducer := fun Γ' Φ ψ ↦
      let t := sh (Γ'.length - Γ.length) s₀
      dExI L K.G K.E (Term.fst (Term.snd t)) (dExI L K.G K.E (Term.snd (Term.snd t))
        (K.solve 4)) Γ' Φ ψ
    let close : Deducer := dConjI L
      (dImpI L fun Γ Φ ψ ↦ (parts Γ Φ ψ).orElse fun _ ↦ last K.hypFalse Γ Φ ψ)
      (dImpI L fun Γ Φ ψ ↦ (K.byNorm Γ Φ ψ).orElse fun _ ↦ last (refuteNot K) Γ Φ ψ)
    let some d := splitCond K Γ.length s₀ 16 (linkK K "xpStepOut: a case" close)
        a.ctx a.hyps a.concl
      | dbgTrace "xpStepOut: not proved" fun _ ↦ none
    pure (a, d))

/-- The expansion's run from a state with forms written, against that from the state with none:
the two end in states that have both failed or neither, and where they have not, the forms the
former has written are those the latter has, before the forms written at the start. By induction
on the forms; at a construction the step's two cases ({name}`xpStepOut`): not failed, the
induction hypothesis at the step's declarations, from its forms before the forms written and
from its forms alone, the concatenations reassociated ({name}`appendAssoc`); failed, the two runs
the same, which fail ({name}`xpFailed`). In the context of the forms, under the declarations and
the forms written. -/
def xpRunOut (P : Prog) (S : Defs) : Step :=
  ("xpRunOut", fun ix E ↦ do
    let K : Kit := ⟨xpProg P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let flag (t : Term) : Term := call D.lab [] [Term.fst t]
    let outs (t : Term) : Term := Term.snd (Term.snd t)
    let nil := nilT treeTy
    -- under the quantifiers: the forms written v0, the declarations v1, the forms v2
    let r₁ := xpRun P (v 2) (xpState (v 1) (v 0))
    let r₀ := xpRun P (v 2) (xpState (v 1) nil)
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o Ls (Term.lam Ls
      (Internal.Logic.conj o (Term.eq (flag r₁) (flag r₀)) (Internal.Logic.imp o
        (truth o (Term.fst r₀)) (Term.eq (outs r₁) (txsApp P (outs r₀) (v 0))))))))
    let some d₀ := dAllI L (dAllI L (dConjI L K.byNorm (dImpI L K.byNorm))) [] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "xpRunOut: empty" fun _ ↦ none
    let cons : Deducer := dAllI L <| dAllI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let n₁ := Γ₁.length
      let at_ (k : ℕ) (Γ : List Tree) : Term := v (k + (Γ.length - n₁))
      let (outA, dvA, esA, eA) := (at_ 0, at_ 1, at_ 2, at_ 3)
      let s₀ (Γ : List Tree) : Term := xpStepT P (xpState (dvA Γ) nil) (eA Γ)
      -- the step failed: the two steps the same, and the run from it fails
      let bad (iBad : ℕ) : Deducer :=
        dImpE L iBad (dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) fun Γ Φ ψ ↦
          normHyps K [Φ.length - 1] (dConjI L (linkK K "xpRunOut: failed flags" K.byNorm)
            (dImpI L fun Γ' Φ' ψ' ↦
              let iP := Φ'.length - 1
              (K.cutThm "xpFailed" (fun Γ ↦ [esA Γ]) <| K.allEΓ s₀ <|
                K.impE (linkK K "xpRunOut: failed step" (K.solve 3)) fun Γ Φ ψ ↦
                normHyps K [Φ.length - 1] (linkK K "xpRunOut: failed run" (K.hypFalse iP))
                  Γ Φ ψ) Γ' Φ' ψ')) Γ Φ ψ
      -- the step not failed: its state's parts, the induction hypothesis twice
      let good (iOk : ℕ) : Deducer :=
        dImpE L iOk (linkK K "xpRunOut: the step" (K.solve 3)) <| K.exE <| K.exE <| K.conjE <|
        fun Γ₃ Φ₃ ψ₃ ↦
          let n₃ := Γ₃.length
          let dW (Γ : List Tree) : Term := v (1 + (Γ.length - n₃))
          let oW (Γ : List Tree) : Term := v (Γ.length - n₃)
          let ih (out : List Tree → Term) (k : ℕ → ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
            dAllE L K.G K.E 0 (dW Γ) (fun Γ Φ ψ ↦
              dAllE L K.G K.E (Φ.length - 1) (out Γ) (K.conjE fun Γ Φ ψ ↦
                k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
          normHyps K [Φ₃.length - 2, Φ₃.length - 1]
            (ih (fun Γ ↦ txsApp P (oW Γ) (outA Γ)) fun f1 i1 ↦ ih oW fun f2 i2 ↦
              normHyps K [f1, f2] (dConjI L (linkK K "xpRunOut: flags" K.byNorm)
                (dImpI L fun Γ Φ ψ ↦
                  let iP := Φ.length - 1
                  (dImpE L i1 (linkK K "xpRunOut: first premise" (K.byHyp iP)) <|
                    dImpE L i2 (linkK K "xpRunOut: second premise" (K.byHyp iP)) <|
                    fun Γ Φ ψ ↦
                      let (o1, o2) := (Φ.length - 2, Φ.length - 1)
                      (K.cutThm "appendAssoc" (fun Γ ↦
                          [outs (xpRun P (esA Γ) (xpState (dW Γ) nil))]) <|
                        K.allEΓ oW <| K.allEΓ outA <| fun Γ Φ ψ ↦
                        normHyps K [o1, o2, Φ.length - 1]
                          (linkK K "xpRunOut: the forms" K.byNorm) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ)))
            Γ₃ Φ₃ ψ₃
      (applyThm K "xpStepOut" (fun Γ ↦ [eA Γ, outA Γ, dvA Γ]) [] <| K.conjE <|
        fun Γ₂ Φ₂ ψ₂ ↦
          decideIn K (fun Γ ↦ Term.fst (s₀ Γ)) (bad (Φ₂.length - 1)) (good (Φ₂.length - 2))
            Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let some d₁ := cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "xpRunOut: construction" fun _ ↦ none
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The typed forms the expansion writes for forms from declarations: its run from the state of
the declarations with no forms written, the forms it has written reversed. -/
def typedForms (P : Prog) (es dv : Term) : Term :=
  reverseT P (Term.snd (Term.snd (xpRun P es (xpState dv (nilT treeTy)))))

/-- The expansion's run from a state with one form written, against that from the state with
none ({name}`xpRunOut`): both fail or neither, and where they do not the former's forms reversed
are the form before the latter's ({name}`reverseSnoc`). In the context of the form, the
declarations and the forms. -/
def typedFormsCons (P : Prog) (S : Defs) : Step :=
  ("typedFormsCons", fun ix E ↦ do
    let K : Kit := ⟨xpProg P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let nil := nilT treeTy
    let (f, dv, es) := (v 0, v 1, v 2)
    let one := consT treeTy f nil
    let r₁ := xpRun P es (xpState dv one)
    let r₀ := xpRun P es (xpState dv nil)
    let outs (t : Term) : Term := Term.snd (Term.snd t)
    let a : Internal.Thm := ⟨0, [treeTy, Ls, Ls], [], Internal.Logic.conj o
      (Term.eq (call D.lab [] [Term.fst r₁]) (call D.lab [] [Term.fst r₀]))
      (Internal.Logic.imp o (truth o (Term.fst r₀))
        (Term.eq (reverseT P (outs r₁)) (consT treeTy f (typedForms P es dv))))⟩
    let some d := (K.cutThm "xpRunOut" (fun _ ↦ [es]) <| K.allEΓ (fun _ ↦ dv) <|
        K.allEΓ (fun _ ↦ one) <| K.conjE fun Γ Φ ψ ↦
        let (fl, im) := (Φ.length - 2, Φ.length - 1)
        dConjI L (linkK K "typedFormsCons: flags" (normHyps K [fl] (K.solve 2)))
          (dImpI L <| dImpE L im dHyp <|
            K.cutThm "reverseSnoc" (fun _ ↦ [outs r₀, f]) fun Γ Φ ψ ↦
            normHyps K [Φ.length - 2, Φ.length - 1]
              (linkK K "typedFormsCons: reversed" K.byNorm) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "typedFormsCons: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the runs' beginnings and of the expansion's forms written. -/
def programPrefixDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [someTruth P S, appendAssoc P S, checkPrefix P S T,
    runPrefix P S (readProg P) "readPrefix" "readFailed" progTy (readRun P),
    runPrefix P S (xpProg P) "xpPrefix" "xpFailed" xpTy (xpRun P),
    revRunAppend P S, reverseSnoc P S]

/-- An induction on a list of trees, the variable of index 0 of the statement {lit}`φ` in a
context of that list alone: the empty list by {lit}`base`, a construction by {lit}`step` under
the induction hypothesis, the first hypothesis. -/
def listInduction (name : String) (φ : Term) (base step : Deducer) :
    Option (Internal.Thm × Internal.Deriv) := do
  let Ls := list treeTy
  let some d₀ := base [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    | dbgTrace s!"{name}: empty" fun _ ↦ none
  let some d₁ := step [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    | dbgTrace s!"{name}: construction" fun _ ↦ none
  pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁])

/-- The last hypothesis refuted: normalized to falsity. -/
def lastFalse (K : Kit) : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ

/-- A name absent from a list of names has, in the list with it after them, the index of the
list's length: by induction on the list; at a construction the head is not the name, nor has the
name an index in the rest, either refuting the absence. In the context of the list, under the
name. -/
def idxNew (P : Prog) (S : Defs) : Step :=
  ("idxNew", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    -- under the quantifier: the name v0, the list v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (notTest o (isSome (idx (v 0) (v 1))))
      (Term.eq (idx (v 0) (pc P "Prelude.append" [v 1, pc P "Prelude.single" [v 0]]))
        (pc P "Prelude.some" [pc P "Prelude.length" [v 1]]))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let base : Deducer := dAllI L <| dImpI L <| K.cutThm "equalRefl" (fun Γ ↦ [at_ 0 Γ]) <|
      decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 0 Γ]) (anyFalse K) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the name v(2), from the outermost
    let step : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 1
      let (b, tl, nm) := (at_ 0, at_ 1, at_ 2)
      let refute : Deducer := dImpE L g (K.solve 3) (lastFalse K)
      decideIn K (fun Γ ↦ apps equalT [nm Γ, b Γ])
        (decideIn K (fun Γ ↦ isSome (idx (nm Γ) (tl Γ)))
          (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (nm Γ)
            (K.impE (dImpI L (lastFalse K)) (byLast K)) Γ Φ ψ)
          (linkK K "idxNew: indexed in the rest" refute))
        (linkK K "idxNew: the head" refute) Γ₁ Φ₁ ψ₁
    listInduction "idxNew" φ base step)

/-- The element at the index of a list's length, in the list before an element and further ones,
is that element: by induction on the list, the lookup at a successor the rest's. In the context
of the list, under the element and the further ones. -/
def nthLen (P : Prog) (S : Defs) : Step :=
  ("nthLen", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the further elements v0, the element v1, the list v2
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o Ls (Term.lam Ls
      (Term.eq (pc P "Prelude.nth" [pc P "Prelude.append" [v 2, consT treeTy (v 1) (v 0)],
          pc P "Prelude.length" [v 2]])
        (pc P "Prelude.some" [v 1])))))
    let step : Deducer := dAllI L <| dAllI L <| dAllE L K.G K.E 0 (v 1) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (v 0) (normLastK K K.byNorm) Γ Φ ψ
    listInduction "nthLen" φ (dAllI L (dAllI L K.byNorm)) step)

/-- The length of a list with an element after it is that of the list with the element before
it: by induction on the list. In the context of the list, under the element. -/
def lenSnoc (P : Prog) (S : Defs) : Step :=
  ("lenSnoc", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let len (xs : Term) : Term := pc P "Prelude.length" [xs]
    -- under the quantifier: the element v0, the list v1
    let φ := Internal.Logic.all P.o treeTy (Term.lam treeTy
      (Term.eq (len (pc P "Prelude.append" [v 1, pc P "Prelude.single" [v 0]]))
        (len (consT treeTy (v 0) (v 1)))))
    let step : Deducer := dAllI L <| dAllE L K.G K.E 0 (v 0) (normLastK K K.byNorm)
    listInduction "lenSnoc" φ (dAllI L K.byNorm) step)

/-- A name with an index in a list of names has the same index in the list before further names:
by induction on the list; at a construction the head the name, or the name indexed in the rest.
In the context of the list, under the name and the further names. -/
def indexAppendOld (P : Prog) (S : Defs) : Step :=
  ("indexAppendOld", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let equalT ← primT Kernel.Prim.equal
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    -- under the quantifiers: the further names v0, the name v1, the list v2
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o Ls (Term.lam Ls
      (Internal.Logic.imp o (truth o (isSome (idx (v 1) (v 2))))
        (Term.eq (idx (v 1) (pc P "Prelude.append" [v 2, v 0])) (idx (v 1) (v 2)))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    -- a construction: the head v(0), the tail v(1), the name v(2), the further names v(3)
    let step : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 1
      let (b, tl, nm, ys) := (at_ 0, at_ 1, at_ 2, at_ 3)
      decideIn K (fun Γ ↦ apps equalT [nm Γ, b Γ])
        (decideIn K (fun Γ ↦ isSome (idx (nm Γ) (tl Γ)))
          (linkK K "indexAppendOld: not indexed" (K.hypFalse g))
          (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (nm Γ) (K.allEΓ ys
            (K.impE (K.solve 3) (byLast K))) Γ Φ ψ))
        (K.solve 3) Γ₁ Φ₁ ψ₁
    listInduction "indexAppendOld" φ (dAllI L (dAllI L (dImpI L (lastFalse K)))) step)

/-- The typing's lookup of a name among the definitions' types. -/
def lookupT (P : Prog) (x ds : Term) : Term := pc P "Typing.lookupName" [x, ds]

/-- The definitions' types with a name's type after them. -/
def declareT (P : Prog) (ds x A : Term) : Term :=
  pc P "Typing/Abbrs.append" [ds, pc P "Typing/Abbrs.single" [pc P "Typing.abbr" [x, A]]]

/-- A name with no type among definitions' types has, among them with its type after them, that
type: by induction on the types; at a construction the head is not the name's, which would give
it a type. In the context of the types, under the name and the type. -/
def lookupAppendNew (P : Prog) (S : Defs) : Step :=
  ("lookupAppendNew", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let childT ← primT Kernel.Prim.child
    let equalT ← primT Kernel.Prim.equal
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    -- under the quantifiers: the type v0, the name v1, the types v2
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o treeTy
      (Term.lam treeTy (Internal.Logic.imp o (notTest o (isSome (lookupT P (v 1) (v 2))))
        (Term.eq (lookupT P (v 1) (declareT P (v 2) (v 1) (v 0)))
          (pc P "Typing/OTy.just" [v 0]))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let base : Deducer := dAllI L <| dAllI L <| dImpI L <|
      K.cutThm "equalRefl" (fun Γ ↦ [at_ 0 Γ]) <|
      decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 0 Γ]) (anyFalse K) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the name v(2), the type v(3)
    let step : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 1
      let (d, x, A) := (at_ 0, at_ 2, at_ 3)
      decideIn K (fun Γ ↦ apps equalT [apps childT [d Γ, leafT bnilT], x Γ])
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (x Γ) (K.allEΓ A
          (K.impE (linkK K "lookupAppendNew: the rest" (K.byHyp g)) (byLast K))) Γ Φ ψ)
        (linkK K "lookupAppendNew: the head" (dImpE L g (K.solve 3) (lastFalse K))) Γ₁ Φ₁ ψ₁
    listInduction "lookupAppendNew" φ base step)

/-- A name's type among definitions' types with another name's type after them is its type among
them: by induction on the types. In the context of the types, under the name, the other name and
its type. -/
def lookupAppendOld (P : Prog) (S : Defs) : Step :=
  ("lookupAppendOld", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let all (b : Term) : Term := Internal.Logic.all o treeTy (Term.lam treeTy b)
    -- under the quantifiers: the type v0, the other name v1, the name v2, the types v3
    let φ := all (all (all (Internal.Logic.imp o (notTest o (apps equalT [v 1, v 2]))
      (Term.eq (lookupT P (v 2) (declareT P (v 3) (v 1) (v 0))) (lookupT P (v 2) (v 3))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : Deducer) : Deducer := dAllI L <| dAllI L <| dAllI L <| dImpI L k
    let base : Deducer := intro fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 1
      decideIn K (fun Γ ↦ apps equalT [at_ 1 Γ, at_ 0 Γ]) (K.solve 3)
        (dImpE L g (K.solve 3) (lastFalse K)) Γ₁ Φ₁ ψ₁
    -- a construction: the head v(0), the tail v(1), the name v(2), the other v(3), the type v(4)
    let step : Deducer := intro fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (at_ 2 Γ) (K.allEΓ (at_ 3) (K.allEΓ (at_ 4)
        (K.impE dHyp (byLast K)))) Γ Φ ψ
    listInduction "lookupAppendOld" φ base step)

/-- The terms of a reader's state. -/
def termsOf (s : Term) : Term := Term.snd (Term.snd (Term.snd (Term.snd s)))

/-- The second list of a concatenation's normal form. -/
def appendTail (X : Term) : Option Term :=
  match X.label, X.children with
  | .app, [_, fz] => match fz.label, fz.children with
    | .pair, [_, ys] => some ys
    | _, _ => none
  | _, _ => none

/-- The terms of the state the reader's step leaves are the state's before further ones: the
step's tests decided until it is no conditional, the further terms read from the normal form.
In the context of the form and the state. -/
def progStepExt (P : Prog) (S : Defs) : Step :=
  ("progStepExt", fun ix E ↦ do
    let K : Kit := ⟨{ P with folded := P.folded ++ ["Reader.isFresh"] }, S, E, ix, ["appendNil"]⟩
    let L := K.L
    let Ls := list treeTy
    let Γ := [treeTy, progTy]
    let step := pc P "Reader.progStep" [v 1, v 0]
    let a : Internal.Thm := ⟨0, Γ, [], Internal.Logic.ex P.o Ls (Term.lam Ls
      (Term.eq (termsOf (sh 1 step)) (pc P "Prelude.append" [termsOf (v 2), v 0])))⟩
    let close : Deducer := fun Γ' Φ ψ ↦
      let t := sh (Γ'.length - Γ.length) step
      let w := ((evalRw K.G K.E (K.rules Φ) .full Γ' Φ (termsOf t)).bind fun r ↦
        appendTail r.1).getD (nilT treeTy)
      (dExI L K.G K.E (nilT treeTy) K.byNorm Γ' Φ ψ).orElse fun _ ↦
        dExI L K.G K.E w K.byNorm Γ' Φ ψ
    let some d := splitCond K Γ.length step 16 (linkK K "progStepExt: a case" close)
        a.ctx a.hyps a.concl
      | dbgTrace "progStepExt: not proved" fun _ ↦ none
    pure (a, d))

/-- The terms of the state the reader's run ends in are the state's before further ones: by
induction on the forms, the step's ({name}`progStepExt`) before the rest's, reassociated
({name}`appendAssoc`). In the context of the forms, under the state. -/
def readExt (P : Prog) (S : Defs) : Step :=
  ("readExt", fun ix E ↦ do
    let K : Kit := ⟨readProg P, S, E, ix, ["appendNil"]⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let app (xs ys : Term) : Term := pc P "Prelude.append" [xs, ys]
    -- under the quantifier: the state v0, the forms v1; under the further terms, each shifted
    let φ := Internal.Logic.all o progTy (Term.lam progTy (Internal.Logic.ex o Ls (Term.lam Ls
      (Term.eq (termsOf (readRun P (v 2) (v 1))) (app (termsOf (v 1)) (v 0))))))
    let base : Deducer := dAllI L (dExI L K.G K.E (nilT treeTy) K.byNorm)
    -- a construction, under the quantifier the state v0, the tail v1 and the head v2
    let step : Deducer := dAllI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let n₁ := Γ₁.length
      let at_ (k : ℕ) (Γ : List Tree) : Term := v (k + (Γ.length - n₁))
      let (sA, xA) := (at_ 0, at_ 2)
      let stepA (Γ : List Tree) : Term := pc P "Reader.progStep" [sA Γ, xA Γ]
      (dAllE L K.G K.E 0 (stepA Γ₁) <| K.exE <|
        K.cutThm "progStepExt" (fun Γ ↦ [xA Γ, sA Γ]) <| K.exE <| fun Γ Φ ψ ↦
        -- the rest's further terms v1, the step's v0
        let (iRest, iStep) := (Φ.length - 3, Φ.length - 1)
        (K.cutThm "appendAssoc" (fun Γ ↦ [termsOf (sA Γ)]) <| K.allEΓ (fun _ ↦ v 0) <|
          K.allEΓ (fun _ ↦ v 1) <| fun Γ Φ ψ ↦
          normHyps K [iStep, iRest, Φ.length - 1]
            (dExI L K.G K.E (app (v 0) (v 1)) (linkK K "readExt: the terms" K.byNorm)) Γ Φ ψ)
          Γ Φ ψ) Γ₁ Φ₁ ψ₁
    listInduction "readExt" φ base step)

/-- The type of the kernel check's state: whether every term has a type, and the types. -/
def chkTy : Tree := prod treeTy (list treeTy)

/-- The kernel check's step at a term from a state: the term's type given the types, after them,
or a failure; a state that has failed left as it is. -/
def kcStepT (P : Prog) (s t : Term) : Term :=
  let ty := pc P "Check.typeOf" [Term.snd s, t]
  condT chkTy (call D.lab [] [Term.fst s])
    (condT chkTy (call D.lab [] [pc P "Prelude.isSome" [ty]])
      (Term.pair (leafT (numeral 1)) (pc P "Prelude.append"
        [Term.snd s, pc P "Prelude.single" [pc P "Prelude.get" [ty]]]))
      (Term.pair (leafT bnilT) (Term.snd s))) s

/-- The kernel check's run over a list of terms from a state. -/
def kcRun (P : Prog) (xs s : Term) : Term := runT treeTy chkTy (kcStepT P) xs s

/-- The kernel check's state before any term. -/
def kcInit : Term := Term.pair (leafT (numeral 1)) (nilT treeTy)

/-- The kernel check's run from a state that has failed ends in a state that has failed: by
induction on the terms, the step from a state that has failed the state. In the context of the
terms, under the state. -/
def kcFailed (P : Prog) (S : Defs) : Step :=
  ("kcFailed", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let φ := Internal.Logic.all P.o chkTy (Term.lam chkTy (Internal.Logic.imp P.o
      (failedT (v 0)) (failedT (kcRun P (v 1) (v 0)))))
    let step : Deducer := dAllI L <| dImpI L <|
      dAllE L K.G K.E 0 (kcStepT P (v 0) (v 2)) fun Γ Φ ψ ↦
        normHyps K [Φ.length - 2] (dImpE L (Φ.length - 1) (K.solve 2) (byLast K)) Γ Φ ψ
    listInduction "kcFailed" φ (dAllI L (dImpI L (byLast K))) step)

/-- The kernel check's run over a concatenation is its run over the second list from the state
its run over the first leaves: by induction on the first. In the context of the first, under the
second and the state. -/
def kcAppend (P : Prog) (S : Defs) : Step :=
  ("kcAppend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the state v0, the second v1, the first v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o chkTy (Term.lam chkTy
      (Term.eq (kcRun P (pc P "Prelude.append" [v 2, v 1]) (v 0))
        (kcRun P (v 1) (kcRun P (v 2) (v 0)))))))
    let step : Deducer := dAllI L <| dAllI L <| dAllE L K.G K.E 0 (v 1) fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (kcStepT P (v 0) (v 3)) (normLastK K K.byNorm) Γ Φ ψ
    listInduction "kcAppend" φ (dAllI L (dAllI L K.byNorm)) step)

/-- Where the kernel checks a list of terms, a term among them has a type given the types of the
terms before it: the check's run over them is its run over the term and those after it from the
state its run over those before it leaves ({name}`kcAppend`), which has not failed
({lit}`kcPrefix`), so that the step at the term has not, its tests decided. In the context of
the terms after it, the term and the terms before it. -/
def kcTyped (P : Prog) (S : Defs) : Step :=
  ("kcTyped", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [Ls, treeTy, Ls]
    let (ext, t, pre) := (v 0, v 1, v 2)
    let isSome (x : Term) : Term := pc P "Prelude.isSome" [x]
    let all := pc P "Prelude.append" [pre, consT treeTy t ext]
    let s := kcRun P pre kcInit
    let typed := isSome (pc P "Check.typeIn" [Term.snd s, nilT treeTy, t])
    let a : Internal.Thm := ⟨0, Γ, [truth P.o (isSome (pc P "Check.checkProgram" [all]))],
      truth P.o typed⟩
    let up (x : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) x
    let some d := (K.cutThm "kcAppend" (fun Γ' ↦ [up pre Γ']) <|
        K.allEΓ (up (consT treeTy t ext)) <| K.allEΓ (fun _ ↦ kcInit) <| fun Γ₁ Φ₁ ψ₁ ↦
        normHyps K [Φ₁.length - 1] (
          decideIn K (up (Term.fst (kcRun P all kcInit)))
            (linkK K "kcTyped: the check" (K.hypFalse 0)) <|
          applyThm K "kcPrefix" (fun Γ' ↦ [up ext Γ', up (kcStepT P s t) Γ'])
            [linkK K "kcTyped: the rest" (K.solve 3)] <| fun Γ₂ Φ₂ ψ₂ ↦
          let h := Φ₂.length - 1
          decideEach K Γ.length
            [(Term.fst s, some (K.hypFalse h), none), (typed, some (K.hypFalse h), none)]
            (linkK K "kcTyped: typed" (K.solve 3)) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "kcTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the kernel check's runs. -/
def programKernelDev (P : Prog) (S : Defs) : List Step :=
  [kcFailed P S, kcAppend P S, runPrefix P S P "kcPrefix" "kcFailed" chkTy (kcRun P),
    kcTyped P S]

/-- A name with an index in a list of names with a name after them, and none in the list, is the
name after them: by induction on the list; at a construction the head not the name, the name's
index in the rest's lists decided. In the context of the list, under the name and the name after
them. -/
def idxSnocCases (P : Prog) (S : Defs) : Step :=
  ("idxSnocCases", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    let snoc (xs x : Term) : Term := pc P "Prelude.append" [xs, pc P "Prelude.single" [x]]
    let all (b : Term) : Term := Internal.Logic.all o treeTy (Term.lam treeTy b)
    -- under the quantifiers: the name after them v0, the name v1, the list v2
    let φ := all (all (Internal.Logic.imp o (truth o (isSome (idx (v 1) (snoc (v 2) (v 0)))))
      (Internal.Logic.imp o (notTest o (isSome (idx (v 1) (v 2))))
        (truth o (apps equalT [v 1, v 0])))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let intro (k : ℕ → ℕ → Deducer) : Deducer := dAllI L <| dAllI L <| dImpI L <| dImpI L
      fun Γ Φ ψ ↦ k (Φ.length - 2) (Φ.length - 1) Γ Φ ψ
    -- the empty list: the name v(0), the name after v(1)
    let base : Deducer := intro fun h₁ _ ↦
      decideIn K (fun Γ ↦ apps equalT [at_ 0 Γ, at_ 1 Γ]) (K.hypFalse h₁) (K.solve 3)
    -- a construction: the head v(0), the tail v(1), the name v(2), the name after v(3)
    let step : Deducer := intro fun h₁ h₂ ↦
      let (b, tl, x, nm) := (at_ 0, at_ 1, at_ 2, at_ 3)
      decideIn K (fun Γ ↦ apps equalT [x Γ, b Γ])
        (decideIn K (fun Γ ↦ isSome (idx (x Γ) (snoc (tl Γ) (nm Γ))))
          (linkK K "idxSnocCases: no index" (K.hypFalse h₁))
          (decideIn K (fun Γ ↦ isSome (idx (x Γ) (tl Γ)))
            (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (x Γ) (K.allEΓ nm
              (K.impE (linkK K "idxSnocCases: the rest's index" (K.solve 3))
                (K.impE (dImpI L (lastFalse K)) (linkK K "idxSnocCases: the rest" fun Γ Φ ψ ↦
                  K.byHyp (Φ.length - 1) Γ Φ ψ)))) Γ Φ ψ)
            (linkK K "idxSnocCases: indexed in the rest" (refuteNot K h₂))))
        (linkK K "idxSnocCases: the head" (refuteNot K h₂))
    listInduction "idxSnocCases" φ base step)

/-- The program with the reader's names of the primitives kept folded. -/
def primProg (P : Prog) : Prog := { P with folded := P.folded ++ ["Reader.primNames"] }

/-- That a name is a primitive's or the unit value's, as the reader's names of definitions
exclude. -/
def primTest (P : Prog) (x : Term) : Term :=
  pc P "Prelude.or" [pc P "Prelude.isSome" [pc P "Reader.indexOf" [x, pc P "Reader.primNames" []]],
    apps ((primT Kernel.Prim.equal).getD Term.star) [x, pc P "Reader.kwUnitValue" []]]

/-- That a name is not reserved. -/
def unreservedT (P : Prog) (x : Term) : Term :=
  notTest P.o (pc P "Prelude.isSome" [pc P "Reader.indexOf" [x, pc P "Reader.reservedNames" []]])

/-- A name with an index in a list of names has one in the list after further names: by
induction on the further names; at a construction the head the name, or the name indexed in the
rest. In the context of the further names, under the name and the list. -/
def idxAppendRight (P : Prog) (S : Defs) : Step :=
  ("idxAppendRight", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let equalT ← primT Kernel.Prim.equal
    let found (x xs : Term) : Term := pc P "Prelude.isSome" [pc P "Reader.indexOf" [x, xs]]
    -- under the quantifiers: the list v0, the name v1, the further names v2
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.all o Ls (Term.lam Ls
      (Internal.Logic.imp o (truth o (found (v 1) (v 0)))
        (truth o (found (v 1) (pc P "Prelude.append" [v 2, v 0])))))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    -- a construction: the head v(0), the tail v(1), the name v(2), the list v(3)
    let step : Deducer := dAllI L <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 1
      let (b, tl, x, ys) := (at_ 0, at_ 1, at_ 2, at_ 3)
      decideIn K (fun Γ ↦ apps equalT [x Γ, b Γ])
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (x Γ) (K.allEΓ ys (K.impE (K.byHyp g) fun Γ Φ ψ ↦
          let h := Φ.length - 1
          decideIn K (fun Γ ↦ found (x Γ) (pc P "Prelude.append" [tl Γ, ys Γ]))
            (K.hypFalse h) (K.solve 3) Γ Φ ψ)) Γ Φ ψ)
        (K.solve 3) Γ₁ Φ₁ ψ₁
    listInduction "idxAppendRight" φ (dAllI L (dAllI L (dImpI L (last K.byHyp)))) step)

/-- Whether a name is one of a list's, by the right fold of the disjunction of its equalities
with them: a test without the two uses of the rest's result that the index's has, whose normal
form at a list of constants is linear in the list. -/
def anyEq (P : Prog) (x xs : Term) : Term :=
  let equalT := (primT Kernel.Prim.equal).getD Term.star
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy
    (pc P "Prelude.or" [apps equalT [sh 2 x, v 1], v 0]))) (leafT bnilT) xs

/-- A name that is one of a list's has an index in it: by induction on the list; at a
construction the head the name, or the name one of the rest's. In the context of the list, under
the name. -/
def idxAny (P : Prog) (S : Defs) : Step :=
  ("idxAny", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let o := P.o
    let equalT ← primT Kernel.Prim.equal
    let found (x xs : Term) : Term := pc P "Prelude.isSome" [pc P "Reader.indexOf" [x, xs]]
    -- under the quantifier: the name v0, the list v1
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (anyEq P (v 0) (v 1))) (truth o (found (v 0) (v 1)))))
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    -- a construction: the head v(0), the tail v(1), the name v(2)
    let step : Deducer := dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let g := Φ₁.length - 1
      let (b, tl, x) := (at_ 0, at_ 1, at_ 2)
      decideIn K (fun Γ ↦ apps equalT [x Γ, b Γ])
        (fun Γ Φ ψ ↦ dAllE L K.G K.E 0 (x Γ)
          (K.impE (linkK K "idxAny: the rest" (K.byHyp g)) fun Γ Φ ψ ↦
            let h := Φ.length - 1
            decideIn K (fun Γ ↦ found (x Γ) (tl Γ)) (K.hypFalse h) (K.solve 3) Γ Φ ψ) Γ Φ ψ)
        (K.solve 3) Γ₁ Φ₁ ψ₁
    listInduction "idxAny" φ (dAllI L (dImpI L (lastFalse K))) step)

/-- The two lists of a concatenation as a definition's body applies it. -/
def appendParts (t : Term) : Option (Term × Term) :=
  match t.label, t.children with
  | .app, [f, ys] => match f.label, f.children with
    | .app, [_, xs] => some (xs, ys)
    | _, _ => none
  | _, _ => none

/-- A name that is not reserved is neither a primitive's nor the unit value's: the unit value's
is one of the reserved names, so indexed among them ({name}`idxAny`); a primitive's is, the
reserved names ending with the primitives' ({name}`idxAppendRight`). In the context of the
name. -/
def reservedParts (P : Prog) (S : Defs) : Step :=
  ("reservedParts", fun ix E ↦ do
    let K : Kit := ⟨primProg P, S, E, ix, []⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let some (.language dR) := P.G.defs[P.idx "Reader.reservedNames"]? | none
    let some (lits, prims) := appendParts dR.body
      | dbgTrace s!"reservedParts: the reserved names {showT dR.body}" fun _ ↦ none
    let a : Internal.Thm := ⟨0, [treeTy], [unreservedT P (v 0)], notTest P.o (primTest P (v 0))⟩
    let xA (Γ : List Tree) : Term := v (Γ.length - 1)
    let kw := pc P "Reader.kwUnitValue" []
    let found (x xs : Term) : Term := pc P "Prelude.isSome" [pc P "Reader.indexOf" [x, xs]]
    let last (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦ k (Φ.length - 1) Γ Φ ψ
    -- the name, known, one of the reserved names: its equalities with them computed
    let closed : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta D.equal]) .full) (K.solve 2) Γ Φ ψ
    let reserved := pc P "Reader.reservedNames" []
    let some d := (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        let hA := Φ₁.length - 1
        decideIn K (fun Γ ↦ apps equalT [xA Γ, kw])
          (K.cutThm "idxAppendRight" (fun _ ↦ [lits]) <| K.allEΓ xA <| K.allEΓ (fun _ ↦ prims) <|
            K.impE (decideIn K (fun Γ ↦ found (xA Γ) prims)
              (linkK K "reservedParts: neither" (K.hypFalse hA)) (K.solve 3)) <|
            dImpE L 0 (linkK K "reservedParts: a primitive's" (last K.byHyp)) (dFalse L dHyp))
          (K.cutThm "equalSound" (fun Γ ↦ [xA Γ]) <| K.allEΓ (fun _ ↦ kw) <|
            K.impE (K.solve 3) <| fun Γ Φ ψ ↦ normHyps K [Φ.length - 1]
              (K.cutThm "idxAny" (fun _ ↦ [reserved]) <| K.allEΓ xA <|
                K.impE (linkK K "reservedParts: the unit value's" closed) <|
                dImpE L 0 dHyp (dFalse L dHyp)) Γ Φ ψ) Γ₁ Φ₁ ψ₁) a.ctx a.hyps a.concl
      | dbgTrace "reservedParts: not proved" fun _ ↦ none
    pure (a, d))

/-- The program with the reader's reserved names and names of the primitives kept folded. -/
def freshProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Reader.primNames", "Reader.reservedNames"] }

/-- A name fresh in a reader's state is not reserved, has no index among the names, and
abbreviates no type and no numeral: each of the freshness' tests decided. In the context of the
name, the names, the numeral abbreviations and the type abbreviations. -/
def freshParts (P : Prog) (S : Defs) : Step :=
  ("freshParts", fun ix E ↦ do
    let K : Kit := ⟨freshProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let Γ := [treeTy, Ls, Ls, Ls]
    let (nm, names, nums, tys) := (v 0, v 1, v 2, v 3)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let tests : List Term := [isSome (pc P "Reader.indexOf" [nm, pc P "Reader.reservedNames" []]),
      isSome (pc P "Reader.indexOf" [nm, names]), isSome (pc P "Reader.lookupAbbrev" [nm, tys]),
      isSome (pc P "Reader.lookupAbbrev" [nm, nums])]
    let parts := tests.map (notTest P.o)
    let a : Internal.Thm := ⟨0, Γ, [truth P.o (pc P "Reader.isFresh" [tys, nums, names, nm])],
      parts.dropLast.foldr (Internal.Logic.conj P.o) (parts.getLastD Term.star)⟩
    let neg : Deducer := dImpI K.L (lastFalse K)
    let some d := decideEach K Γ.length (tests.map fun t ↦ (t, none, some (K.hypFalse 0)))
        (linkK K "freshParts: fresh" (dConjI K.L neg (dConjI K.L neg (dConjI K.L neg neg))))
        a.ctx a.hyps a.concl
      | dbgTrace "freshParts: not proved" fun _ ↦ none
    pure (a, d))

/-- The reader's names with a name that is not reserved after them are names of definitions
still: a name with an index among them has one among the names, which are, or is the name after
them ({name}`idxSnocCases`), which is neither a primitive's nor the unit value's
({name}`reservedParts`). In the context of the name and the names. -/
def namesExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("namesExtend", fun ix E ↦ do
    let K : Kit := ⟨freshProg P, S, E, ix, []⟩
    let L := K.L
    let Γ := [treeTy, list treeTy]
    let (nm, names) := (v 0, v 1)
    let snoc := pc P "Prelude.append" [names, pc P "Prelude.single" [nm]]
    let a : Internal.Thm := ⟨0, Γ, [T.namesT names, unreservedT P nm], T.namesT snoc⟩
    let kNames := T.q + 4 + 2 * nFolds
    let unfold : List Internal.NormRule := [.delta kNames]
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (namesA, nmA, xA) := (at_ 0, at_ 1, at_ 2)
    let isSome (t : Term) : Term := pc P "Prelude.isSome" [t]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    let some d := (dRwBy (evalRw K.G K.E unfold .head) <|
        -- the hypothesis on the names unfolded, added after the hypotheses, of index 2
        dRwHyp (evalRw K.G K.E unfold .head) 0 <| dAllI L <| dImpI L <| dImpI L <|
        fun Γ₁ Φ₁ ψ₁ ↦
          let (hI, hP) := (Φ₁.length - 2, Φ₁.length - 1)
          decideIn K (fun Γ ↦ isSome (idx (xA Γ) (namesA Γ)))
            -- not among the names: the name after them
            (K.cutThm "idxSnocCases" (fun Γ ↦ [namesA Γ]) <| K.allEΓ xA <| K.allEΓ nmA <|
              K.impE (linkK K "namesExtend: indexed" (K.byHyp hI)) <|
              K.impE (dImpI L (linkK K "namesExtend: not among them" (lastFalse K))) <|
              linkK K "namesExtend: the name after them" <|
              K.cutThm "equalSound" (fun Γ ↦ [xA Γ]) <| K.allEΓ nmA <|
              K.impE (linkK K "namesExtend: equal" (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 3) Γ Φ ψ)) <|
              fun Γ Φ ψ ↦ normHyps K [Φ.length - 1]
                (applyThm K "reservedParts" (fun Γ ↦ [nmA Γ])
                    [linkK K "namesExtend: not reserved" dHyp] <|
                  linkK K "namesExtend: reserved parts" fun Γ Φ ψ ↦
                  dImpE L (Φ.length - 1) (linkK K "namesExtend: a primitive's" (K.byHyp hP))
                    (linkK K "namesExtend: falsity" dHyp) Γ Φ ψ) Γ Φ ψ)
            -- among the names: the hypothesis on them
            (linkK K "namesExtend: among the names" fun Γ Φ ψ ↦ dAllE L K.G K.E 2 (xA Γ)
              (K.impE (linkK K "namesExtend: its index" (K.solve 3))
                (K.impE (linkK K "namesExtend: old" (K.byHyp hP))
                (linkK K "namesExtend: false" dHyp))) Γ Φ ψ) Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "namesExtend: not proved" fun _ ↦ none
    pure (a, d))

/-- The definitions' relation to the typing environment's, extended by a definition: the
definitions related to the environment's by the names, a name with no index among the names, the
term at the index of the names' length converging to a value related at a type, the definitions
are related to the environment's with the name at that type after them, by the names with the
name after them. A name with a type there is the name, at the new index and type
({lit}`idxNew`, {lit}`lookupAppendNew`), having had none, or another, typed and indexed as
before ({lit}`lookupAppendOld`, {lit}`indexAppendOld`). In the context of the type, the term,
the name, the names, the environment and the relation's context. -/
def globExtend (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("globExtend", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames⟩
    let L := K.L
    let equalT ← primT Kernel.Prim.equal
    let Γ := [treeTy, treeTy, treeTy, list treeTy, T.envTy, Defs3.ctxTy]
    let (A, t, nm, names, Ev, R) := (v 0, v 1, v 2, v 3, v 4, v 5)
    let isSome (x : Term) : Term := pc P "Prelude.isSome" [x]
    let idx (x xs : Term) : Term := pc P "Reader.indexOf" [x, xs]
    let single (x : Term) : Term := pc P "Prelude.single" [x]
    let len (xs : Term) : Term := pc P "Prelude.length" [xs]
    let defs (e : Term) : Term := pc P "Typing.envDefs" [e]
    let a : Internal.Thm := ⟨0, Γ, [T.globT R Ev names, notTest P.o (isSome (idx nm names)),
        Term.eq (pc P "Prelude.nth" [Term.fst R, len names]) (pc P "Prelude.some" [t]),
        S.conv (Term.lam nat (S.evN (Term.fst (sh 1 R)) (v 0) (nilT treeTy) (sh 1 t)))
          (T.relT R A)],
      T.globT R (pc P "Typing.withDefs" [Ev, declareT P (defs Ev) nm A])
        (pc P "Prelude.append" [names, single nm])⟩
    let unfold : List Internal.NormRule := [.delta (T.q + 2)]
    -- an equation that is a hypothesis: found among them, or by normalization with it
    let eqHyp (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      (dHyp Γ Φ ψ).orElse fun _ ↦ normHyps K [h] K.byNorm Γ Φ ψ
    let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
    let (EA, namesA, nmA, tA, AA, xA) := (at_ 1, at_ 2, at_ 3, at_ 4, at_ 5, at_ 6)
    let dsA (Γ : List Tree) : Term := defs (EA Γ)
    let some d := (dRwBy (evalRw K.G K.E unfold .head) <|
        -- the relation unfolded, added after the hypotheses, of index 4
        dRwHyp (evalRw K.G K.E unfold .head) 0 <| dAllI L <| dImpI L <| fun Γ₁ Φ₁ ψ₁ ↦
      let hT := Φ₁.length - 1
      -- another name: its type and its index as before
      let other : Deducer :=
        K.cutThm "lookupAppendOld" (fun Γ ↦ [dsA Γ]) <| K.allEΓ xA <| K.allEΓ nmA <|
        K.allEΓ AA <| K.impE (dImpI L (lastFalse K)) <| fun Γ Φ ψ ↦
        let iOld := Φ.length - 1
        normHyps K [iOld] (dAllE L K.G K.E 4 (xA Γ) <|
          K.impE (linkK K "globExtend: typed before" (K.byHyp hT)) <| K.exE <| K.conjE <|
          fun Γ Φ ψ ↦
            let eqIdx := Φ.length - 2
            (K.exE <| K.conjE <| fun Γ Φ ψ ↦
              let (eqNth, convH) := (Φ.length - 2, Φ.length - 1)
              dExI L K.G K.E (at_ 7 Γ) (dConjI L
                (K.cutThm "indexAppendOld" (fun Γ ↦ [namesA Γ]) <| K.allEΓ xA <|
                  K.allEΓ (fun Γ ↦ single (nmA Γ)) <|
                  K.impE (linkK K "globExtend: indexed before"
                    (normHyps K [eqIdx] (K.solve 3))) <| fun Γ Φ ψ ↦
                  normHyps K [eqIdx, Φ.length - 1]
                    (linkK K "globExtend: the old index" K.byNorm) Γ Φ ψ)
                (dExI L K.G K.E (at_ 8 Γ) (dConjI L
                  (linkK K "globExtend: the old term" (eqHyp eqNth))
                  (linkK K "globExtend: the old value" (K.byHyp convH))))) Γ Φ ψ) Γ Φ ψ)
          Γ Φ ψ
      -- the name has no type before: it would have an index
      let noType : Deducer := dImpI L fun Γ Φ ψ ↦
        let hA := Φ.length - 1
        (dAllE L K.G K.E 4 (nmA Γ) <| K.impE (linkK K "globExtend: typed" (K.byHyp hA)) <|
          K.exE <| K.conjE <| fun Γ Φ ψ ↦
          normHyps K [Φ.length - 2] (linkK K "globExtend: indexed" (refuteNot K 1)) Γ Φ ψ)
          Γ Φ ψ
      -- the name: the new index and the new type
      let same : Deducer :=
        K.cutThm "equalSound" (fun Γ ↦ [nmA Γ]) <| K.allEΓ xA <| K.impE (K.solve 3) <|
        fun Γ Φ ψ ↦ normHyps K [Φ.length - 1] (
          K.cutThm "lookupAppendNew" (fun Γ ↦ [dsA Γ]) <| K.allEΓ nmA <| K.allEΓ AA <|
          K.impE (linkK K "globExtend: no type before" noType) <| fun Γ Φ ψ ↦
          normHyps K [Φ.length - 1] (dExI L K.G K.E (len (namesA Γ)) (dConjI L
            (K.cutThm "idxNew" (fun Γ ↦ [namesA Γ]) <| K.allEΓ nmA <| K.impE dHyp <|
              linkK K "globExtend: the new index" (byLast K))
            (dExI L K.G K.E (tA Γ) (dConjI L
              (linkK K "globExtend: the new term" (eqHyp 2))
              (linkK K "globExtend: the new value" (K.byHyp 3)))))) Γ Φ ψ) Γ Φ ψ
      decideIn K (fun Γ ↦ apps equalT [nmA Γ, xA Γ]) other same Γ₁ Φ₁ ψ₁)
        a.ctx a.hyps a.concl
      | dbgTrace "globExtend: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the invariants a definition's reading preserves. -/
def programInvDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [idxSnocCases P S, idxAppendRight P S, idxAny P S, reservedParts P S, freshParts P S,
    namesExtend P S T, globExtend P S T]

/-- The development of the lists of names and of terms. -/
def programListsDev (P : Prog) (S : Defs) : List Step :=
  [idxNew P S, nthLen P S, lenSnoc P S, indexAppendOld P S]

/-- The development of the typing's lookups and of the reader's terms. -/
def programLookupDev (P : Prog) (S : Defs) : List Step :=
  [lookupAppendNew P S, lookupAppendOld P S, progStepExt P S, readExt P S]

/-- The development of the reader's runs. -/
def programReadDev (P : Prog) (S : Defs) : List Step :=
  [progStepFailed P S, readFailed P S, readDef P S, readDeftype P S, readDefnum P S,
    namedApart P S "Typing.kwPostulate" "Reader.kwDeftype",
    namedApart P S "Typing.kwPostulate" "Reader.kwDefnum"]

/-- The type of the state of the test of the definitions' bodies: whether each body the
expansion has written is a source form, the expansion's declarations and the reader's numeral
abbreviations. -/
def plainTy : Tree := prod treeTy (prod (list treeTy) (list treeTy))

/-- The state of the test of the definitions' bodies at declarations and numeral abbreviations,
no body having failed it. -/
def plainState (dv nums : Term) : Term := Term.pair (leafT (numeral 1)) (Term.pair dv nums)

/-- The test of source forms at a term, at the expansion of numeral abbreviations. -/
def srcTestT (P : Prog) (nums x : Term) : Term :=
  pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [sh 1 nums, v 0]), x]

/-- The step at a form of the test of the definitions' bodies, from a state: the expansion's
step at the form from the declarations leaves declarations and writes forms. At a template's
instance or a datatype's declaration the state has those declarations. Else, where the form
written is a definition's, the state has them where the definition's body is a source form at
the numeral abbreviations, and has failed where it is not; where it is a numeral abbreviation's,
the state has the abbreviation of its name before the others, as the reader does. A state that
has failed is left as it is. -/
def plainStepT (P : Prog) (s e : Term) : Term :=
  let (dv, nums) := (Term.fst (Term.snd s), Term.snd (Term.snd s))
  let x := xpStepT P (xpState dv (nilT treeTy)) e
  let dv' := Term.fst (Term.snd x)
  let nth (xs : Term) (i : ℕ) : Term :=
    pc P "Datatype.nthTx" [xs, if i = 0 then leafT bnilT else leafT (numeral i)]
  let named (h : Term) (kw : String) : Term := pc P "Datatype.namedTx" [h, pc P kw []]
  let he := nth (pc P "Datatype.elems" [e]) 0
  let fs := pc P "Datatype.elems" [nth (Term.snd (Term.snd x)) 0]
  let (hf, n, b) := (nth fs 0, nth fs 1, nth fs 2)
  let test (t a b : Term) : Term := condT plainTy (call D.lab [] [t]) a b
  let keep := plainState dv' nums
  let nums' := consT treeTy (abbrevT P (pc P "Reader.nameOf" [n])
    (pc P "Prelude.get" [pc P "Reader.numOf" [nums, b]])) nums
  test (Term.fst s)
    (test (pc P "Prelude.and" [pc P "Datatype.isListTx" [e], named he "Datatype.kwGeneric"]) keep
      (test (pc P "Prelude.or" [named he "Datatype.kwData", named he "Datatype.kwTreeData"]) keep
        (test (named hf "Reader.kwDef")
          (test (srcTestT P nums b) keep (Term.pair (leafT bnilT) (Term.pair dv' nums)))
          (test (named hf "Reader.kwDeftype") keep
            (test (named hf "Reader.kwDefnum") (plainState dv' nums') keep)))))
    s

/-- The run over a list of forms, from a state, of the test of the definitions' bodies. -/
def plainRun (P : Prog) (xs s : Term) : Term := runT treeTy plainTy (plainStepT P) xs s

/-- The step of the test of the definitions' bodies from a state that has failed leaves it. In
the context of the form and the state. -/
def plainStepFailed (P : Prog) (S : Defs) : Step :=
  ("plainStepFailed", fun ix E ↦ do
    let K : Kit := ⟨xpProg P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy, plainTy], [failedT (v 1)],
      failedT (plainStepT P (v 1) (v 0))⟩
    let some d := normHyps K [0] (linkK K "plainStepFailed: failed" (byNormWith K [] true))
        a.ctx a.hyps a.concl
      | dbgTrace "plainStepFailed: not proved" fun _ ↦ none
    pure (a, d))

/-- A run from a state that has failed ends in a state that has failed, by the lemma
{lit}`step` that the run's step from a state that has failed leaves one: by induction on the
list, at a construction the induction hypothesis at the state the step leaves. In the context of
the list, under the state. -/
def runFailed (P : Prog) (S : Defs) (K₀ : Prog) (name step : String) (St : Tree)
    (stepT run : Term → Term → Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨K₀, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    -- under the quantifier: the state v0, the list v1
    let φ := Internal.Logic.all o St (Term.lam St (Internal.Logic.imp o (failedT (v 0))
      (failedT (run (v 1) (v 0)))))
    let last : Deducer := fun Γ Φ ψ ↦ normHyps K [Φ.length - 1] (K.solve 2) Γ Φ ψ
    let cons : Deducer := dAllI L <| dImpI L <|
      dAllE L K.G K.E 0 (stepT (v 0) (v 2)) fun Γ Φ ψ ↦
        dImpE L (Φ.length - 1) (applyThm K step (fun _ ↦ [v 2, v 0]) [dHyp] last) last Γ Φ ψ
    listInduction name φ (dAllI L (dImpI L last)) cons)

/-- The body of a definition the expansion's step writes at a form that is no template's
instance and declares no datatype is a source form at the numeral abbreviations, where the run
of the test of the definitions' bodies over the form and those after it ends without a failure
({lit}`plainPrefix`); and the test's step leaves the declarations and the abbreviations. In the
context of the body, the name, the form, the forms after, the abbreviations and the
declarations. -/
def plainDefined (P : Prog) (S : Defs) : Step :=
  ("plainDefined", fun ix E ↦ do
    let K : Kit := ⟨xpProg P, S, E, ix, []⟩
    let Ls := list treeTy
    let nil := nilT treeTy
    let Γ := [treeTy, treeTy, treeTy, Ls, Ls, Ls]
    let (b, n, e, es, nums, dv) := (v 0, v 1, v 2, v 3, v 4, v 5)
    let he := pc P "Datatype.nthTx" [pc P "Datatype.elems" [e], leafT bnilT]
    let named (kw : String) : Term := pc P "Datatype.namedTx" [he, pc P kw []]
    let s := plainState dv nums
    let hyps := ["Datatype.kwGeneric", "Datatype.kwData", "Datatype.kwTreeData"].map
        (fun kw ↦ notTest P.o (named kw)) ++
      [Term.eq (xpStepT P (xpState dv nil) e) (xpState dv (consT treeTy (defForm P n b) nil)),
        truth P.o (Term.fst (plainRun P (consT treeTy e es) s))]
    let a : Internal.Thm := ⟨0, Γ, hyps, Internal.Logic.conj P.o
      (truth P.o (srcTestT P nums b)) (Term.eq (plainStepT P s e) s)⟩
    let at_ (t : Term) (Γ' : List Tree) : Term := sh (Γ'.length - Γ.length) t
    let decided : List (Term × Option Deducer × Option Deducer) :=
      [(pc P "Datatype.isListTx" [e], none, none),
        (named "Datatype.kwGeneric", none, some (refuteNot K 0)),
        (named "Datatype.kwData", none, some (refuteNot K 1)),
        (named "Datatype.kwTreeData", none, some (refuteNot K 2))]
    let some d := (decideEach K Γ.length decided <| normHyps K [3] <|
        applyThm K "plainPrefix" (fun Γ' ↦ [at_ es Γ', at_ (plainStepT P s e) Γ'])
          [linkK K "plainDefined: the run" (K.byHyp 4)] <| fun Γ₁ Φ₁ ψ₁ ↦
        let iOk := Φ₁.length - 1
        decideIn K (fun Γ' ↦ at_ (srcTestT P nums b) Γ')
          (linkK K "plainDefined: the body" (K.hypFalse iOk))
          (linkK K "plainDefined: the step" (K.solve 3)) Γ₁ Φ₁ ψ₁) a.ctx a.hyps a.concl
      | dbgTrace "plainDefined: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the test of the definitions' bodies. -/
def programPlainDev (P : Prog) (S : Defs) : List Step :=
  [plainStepFailed P S,
    runFailed P S (xpProg P) "plainFailed" "plainStepFailed" plainTy (plainStepT P) (plainRun P),
    runPrefix P S (xpProg P) "plainPrefix" "plainFailed" plainTy (plainRun P),
    plainDefined P S]

/-- The developments of the runs of a program's forms, each with its certificate's name, in the
order in which each continues from those before it. -/
def stepGroups (P : Prog) (S : Defs) (T : Defs3) : List (String × List Step) :=
  [("datatype-program-read", programReadDev P S ++ programCheckDev P S T),
    ("datatype-program-expand", programExpandDev P S),
    ("datatype-program-prefix", programPrefixDev P S T),
    ("datatype-program-out-step", [xpStepOut P S]),
    ("datatype-program-out", [xpRunOut P S, typedFormsCons P S]),
    ("datatype-program-lists", programListsDev P S),
    ("datatype-program-lookup", programLookupDev P S),
    ("datatype-program-kernel", programKernelDev P S),
    ("datatype-program-inv", programInvDev P S T),
    ("datatype-program-plain", programPlainDev P S)]

end GebTests.Prototypes.FreeTopos.Datatypes

end
