/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeList
public meta import GebTests.Prototypes.FreeTopos.DatatypeList -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at applications

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at a list whose head no keyword names: the
application of the head to the further elements, from the soundness at the head and at each
further element. The typing types the application by a right fold over the reversal of the
arguments' types, and the reader resolves it by a right fold over the reversal of their resolved
terms, each a left fold, which a construction unrolls ({lit}`applyTyCons`, {lit}`appsCons`). The
stage functions at a list whose head is a variable that no keyword names, as each stage reads it,
reach their applications' cases by deciding first each test their weak head normal forms are
blocked on ({lit}`lazyNf`): full normalization normalizes the cases of a test it cannot decide
before the test selects one. The soundness at expanded forms follows by induction on the further
elements, the type and the resolved term so far generalized, each step by the application's
compatibility with the relation; that at source forms, from it and the soundness at the
expansions of the head and of each further element.

## Main definitions

* {lit}`revFoldAll` — a right fold over a reversal onto a list, by induction on the list
  reversed.
* {lit}`lazyNf` — a term's normal form, the tests its reduction is blocked on decided first.
* {lit}`appEq` — the stage functions' equations at a list of a head and further elements.
* {lit}`spineK` — the soundness at the application of a head to further elements at expanded
  forms, by induction on the further elements, given the head's relation.
* {lit}`appCore` — the soundness at such a list at expanded forms.
* {lit}`srcSound` — the soundness at a list at source forms from that at expanded forms.
* {lit}`appSrc` — the soundness at such a list at source forms.
* {lit}`stagesCertificates`, {lit}`applyCertificates` — the developments, stored as the
  certificates {lit}`datatype-stages` and {lit}`datatype-apply`.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The prelude's reversal of the list {lit}`xs` onto the list {lit}`acc`: the right fold the
reversal applies to the empty list, applied to {lit}`acc` instead. -/
def revOnto (xs acc : Term) : Term :=
  let Ts := list treeTy
  Term.app (foldrT treeTy (exp Ts Ts)
    (Term.lam treeTy (Term.lam (exp Ts Ts) (Term.lam Ts (Term.app (v 1)
      (consT treeTy (v 2) (v 0))))))
    (Term.lam Ts (v 0)) xs) acc

/-- The right fold of a function over the reversal of a list onto another, from any value: its
right fold over the reversal onto the empty list, from the fold over the other list, by induction
on the list reversed, the hypothesis of induction at two lists and two values. -/
def revFoldAll (P : Prog) (S : Defs) : Step :=
  ("revFoldAll", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Ts := list treeTy
    let gTy := exp treeTy (exp treeTy treeTy)
    let fold (g z xs : Term) : Term := foldrT treeTy treeTy g z xs
    -- in the context of the list onto which it is reversed, the value, the list reversed and the
    -- function
    let body := Term.eq (fold (v 3) (v 1) (revOnto (v 2) (v 0)))
      (fold (v 3) (fold (v 3) (v 1) (v 0)) (revOnto (v 2) (nilT treeTy)))
    let φ := Internal.Logic.all P.o treeTy (Term.lam treeTy
      (Internal.Logic.all P.o Ts (Term.lam Ts body)))
    let some d₀ := dAllI K.L (dAllI K.L K.byNorm) [gTy] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "revFoldAll: nil" fun _ ↦ none
    -- the hypothesis of induction at the value and the head before the list, and at the fold
    -- over the list and the head alone
    let some d₁ := dAllI K.L (dAllI K.L fun Γ Φ ψ ↦
        dAllE K.L K.G K.E 0 (v 1) (K.allEΓ (fun _ ↦ consT treeTy (v 3) (v 0))
          (dAllE K.L K.G K.E 0 (fold (v 4) (v 1) (v 0))
            (K.allEΓ (fun _ ↦ consT treeTy (v 3) (nilT treeTy)) K.byNorm))) Γ Φ ψ)
        [Ts, treeTy, gTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "revFoldAll: cons" fun _ ↦ none
    pure (⟨0, [Ts, gTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A right fold over the reversal of a construction, by normal forms: the fold over the reversal
of the tail from the value at the head, in the context of the tail, the head and the value, by
{name}`revFoldAll` at the fold's function. The fold {lit}`whole` is given at a value and a list,
its value at a head {lit}`step` in the context of the head and the value, the value innermost. -/
def revFoldCons (P : Prog) (S : Defs) (name : String) (whole : Term → Term → Term)
    (step : Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Γ := [list treeTy, treeTy, treeTy]
    let rs := vRules P ix
    let some l := nfE P.G E rs Γ (whole (v 2) (consT treeTy (v 1) (v 0)))
      | dbgTrace s!"{name}: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ (whole (Term.subst step fun i ↦ v (if i = 0 then 2 else i)) (v 0))
      | dbgTrace s!"{name}: right" fun _ ↦ none
    let some d := K.cutThm "revFoldAll" (fun _ ↦ [v 0, Term.lam treeTy (Term.lam treeTy step)])
        (K.allEΓ (fun _ ↦ v 2) (K.allEΓ (fun _ ↦ consT treeTy (v 1) (nilT treeTy))
          fun Γ Φ ψ ↦
            let rs := evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full
            dRwHyp rs (Φ.length - 1) (dRwBy rs dHyp) Γ Φ ψ))
        Γ [] (Term.eq l r)
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The typing's type of an application to a construction: that of the application to the tail of
the application to the head ({name}`revFoldCons`). -/
def applyTyCons (P : Prog) (S : Defs) : Step :=
  revFoldCons P S "applyTyCons" (fun s xs ↦ pc P "Typing.applyTy" [s, xs])
    (pc P "Typing.applyTy" [v 0, consT treeTy (v 1) (nilT treeTy)])

/-- The reader's application to a construction: the application to the tail of the application to
the head ({name}`revFoldCons`). -/
def appsCons (P : Prog) (S : Defs) : Step :=
  revFoldCons P S "appsCons" (fun f xs ↦ pc P "Reader.apps" [f, xs])
    (pc P "Reader.app" [v 0, v 1])

/-- A formula by induction on the innermost variable, a list: at the empty list by {lit}`base`,
in the context without the variable, and at a construction by {lit}`step`, in the context of the
tail and the head, the formula at the tail the last hypothesis. -/
def dListIndHyp (G : Internal.Globals) (base step : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let c :: Γ' := Γ | dbgTrace "dListIndHyp: no variable" fun _ ↦ none
  let some a := Internal.listPart c | dbgTrace "dListIndHyp: not a list" fun _ ↦ none
  let some Φ' := Internal.lowerHyps G 0 Γ' Φ
    | dbgTrace s!"dListIndHyp: hypotheses {(List.range Φ.length).filter fun i ↦
        ((Φ[i]?).map fun φ ↦ Term.occurs φ 0).getD false}" fun _ ↦ none
  let some d₀ := base Γ' Φ' (Term.subst ψ (Internal.instVar (Term.arr 0 [a] Term.star)))
    | dbgTrace "dListIndHyp: the empty list" fun _ ↦ none
  let some d₁ := step (c :: a :: Γ') (Φ'.map Internal.weaken2 ++ [Internal.weakenElem ψ])
      (Internal.listConsAt 1 a ψ)
    | dbgTrace "dListIndHyp: a construction" fun _ ↦ none
  pure (nd (.listIndHyp 0 1) [d₀, d₁])

/-- A bitstring decided empty, by {lit}`kF`, or a construction, by {lit}`kT`, by case analysis of
its normal form; one already a constant decided at once. -/
def decideBits (K : Kit) (t : List Tree → Term) (kF kT : Deducer) : Deducer := fun Γ Φ ψ ↦
  match evalRw K.G K.E (K.rules Φ) .full Γ Φ (t Γ) with
  | some (X, _) => match X.label with
    | .arr 0 _ => kF Γ Φ ψ
    | .arr 1 _ => kT Γ Φ ψ
    | _ => K.listCase bitTy X kF kT Γ Φ ψ
  | none => dbgTrace s!"a bitstring without a normal form: {showT (t Γ)}" fun _ ↦ none

/-- The head and the tail of a list node's children, its normal form a node over a
construction. -/
def consParts (t : Term) : Option (Term × Term) := do
  let [p] := t.children | none
  let [_, cs] := p.children | none
  let .arr 1 _ := cs.label | none
  let [q] := cs.children | none
  let [h, tl] := q.children | none
  pure (h, tl)

/-- The datum a term's weak head normal form is blocked on: below the applications' functions and
the projections, the datum of a fold of lists or of natural numbers. -/
def blockedDatum (t : Term) : Option Term :=
  ((List.range 64).foldl (fun (r : Term × Option Term) _ ↦ match r with
    | (_, some X) => (Term.star, some X)
    | (t, none) => match t.label, t.children with
      | .app, f :: _ => (f, none)
      | .fst, [p] => (p, none)
      | .snd, [p] => (p, none)
      | .listRec, [_, _, X] => (Term.star, some X)
      | .natRec, [_, _, X] => (Term.star, some X)
      | _, _ => (Term.star, none)) (t, none)).2

/-- The normal form of a term by rules, the data its weak head normal form is blocked on decided
first, to a number of decisions: a datum whose normal form is closed has its equation with that
form cut in after the hypotheses, so that the fold selects its case before the cases are
normalized, the reduction resumed from the weak head normal form; with the derivation of the
term's equation with its normal form. -/
def lazyNf (G : Internal.Globals) (E : Array Internal.Entry) (rs : List Internal.NormRule)
    (Γ : List Tree) (fuel : ℕ) (Φ : List Term) (l : Term) : Option (Term × Internal.Deriv) :=
  -- the term reached and its reduction from the term given
  let full (Φ : List Term) (t : Term) (dt : Internal.Deriv) : Option (Term × Internal.Deriv) := do
    let (r, d, _) ← Internal.eval G E 0 (rs ++ eqHyps Φ) 4096 .full Γ Φ t
    pure (r, nd .join [nd .trans [dt, d], nd .refl])
  (Nat.rec (motive := fun _ ↦ List Term → Term → Internal.Deriv →
      Option (Term × Internal.Deriv)) full (fun _ rec Φ t dt ↦ do
    let (w, dw, _) ← Internal.eval G E 0 (rs ++ eqHyps Φ) 4096 .head Γ Φ t
    let dw := nd .trans [dt, dw]
    let some X := blockedDatum w | full Φ w dw
    let (X', dX, _) ← Internal.eval G E 0 (rs ++ eqHyps Φ) 4096 .full Γ Φ X
    if X' == X || (List.range Γ.length).any (Term.occurs X') then full Φ w dw else
    let (r, d) ← rec (Φ ++ [Term.eq X X']) w dw
    pure (r, nd (.cut (Term.eq X X')) [nd .join [dX, nd .refl], d])) fuel) Φ l (nd .refl)

/-- The soundness at expanded forms at a term, the variable of index 0 outside the quantifiers. -/
def expandedAt (P : Prog) (S : Defs) (T : Defs3) (t : Term) : Term :=
  Internal.instTerm [] [t] (expandedφ P S T)

/-- The soundness at a source form gives that at its expansion: for all declarations of the
expansion at which the form's expansion is present, the soundness at the expanded form. -/
def expSoundThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  let e := pc P "Datatype.expandExpr" [v 0, v 1]
  ⟨0, [treeTy], [Internal.instTerm [] [v 0] (datatypeφ P S T)],
    Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy) (Internal.Logic.imp P.o
      (truth P.o (pc P "Prelude.isSome" [e])) (expandedAt P S T (pc P "Prelude.get" [e]))))⟩

/-- The soundness at a source form gives that at its expansion ({name}`expSoundThm`): the
expanded form's statement introduced, the source form's instantiated at its variables, the
declarations of the expansion at those given, its antecedents the expanded form's, the expansion's
presence that given. -/
def expSound (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("expSound", fun ix E ↦ do
    let W := kwKit P S T ix E 1 [true] "" true
    let K := W.K
    let a := expSoundThm P S T
    -- the context: the form, the declarations, then the statement's variables, the outermost
    -- first; the hypotheses: the source form's soundness, the declarations' truth, the
    -- expansion's presence, the variables' truths and the statement's hypotheses
    let at_ (j : ℕ) (Γ : List Tree) : Term := if j = 3 then atPos 1 Γ else atPos (1 + j) Γ
    let inst : Deducer := fun Γ Φ ψ ↦
      dAllE K.L K.G K.E 0 (at_ 1 Γ) (((List.range (nQ - 1)).foldr
        (fun j k ↦ K.allEΓ (at_ (j + 2)) k) <|
        (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"expSound: antecedent {i}"
          (if i = 5 then K.byHyp 2 else K.byHyp (3 + nQ + i))) k)
          (linkK K "expSound: the conclusion" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ))) Γ Φ ψ
    let some d := dAllI K.L (dImpI K.L ((List.range nQ).foldr (fun _ k ↦ dAllI K.L k)
        ((List.range W.nH).foldr (fun _ k ↦ dImpI K.L k) inst))) a.ctx a.hyps a.concl
      | dbgTrace "expSound: not proved" fun _ ↦ none
    pure (a, d))

/-- The keywords whose forms the typing reads. -/
def typingKeywords : List String :=
  ["Reader.kwLam", "Reader.kwLet", "Reader.kwPair", "Reader.kwFst", "Reader.kwSnd", "Reader.kwIf",
    "Reader.kwCons", "Reader.kwNil", "Reader.kwQuote", "Typing.kwDatum", "Typing.kwRep",
    "Typing.kwDecode", "Reader.kwFold", "Reader.kwPara", "Reader.kwIter", "Reader.kwFoldr",
    "Reader.kwLcase"]

/-- The keywords whose forms the erasure rewrites. -/
def erasureKeywords : List String := ["Typing.kwRep", "Typing.kwDecode", "Typing.kwDatum"]

/-- The keywords whose forms the reader reads. -/
def readerKeywords : List String :=
  ["Reader.kwLam", "Reader.kwLet", "Reader.kwPair", "Reader.kwFst", "Reader.kwSnd", "Reader.kwIf",
    "Reader.kwQuote", "Reader.kwCons", "Reader.kwNil", "Reader.kwFold", "Reader.kwPara",
    "Reader.kwIter", "Reader.kwFoldr", "Reader.kwLcase"]

/-- That no keyword names a term, the test's label empty. -/
def unnamed (P : Prog) (h : Term) (kw : String) : Term :=
  Term.eq (call D.lab [] [pc P "Typing.namedTx" [h, pc P kw []]]) bnilT

/-- Under the quantifiers of the soundness, of a head {lit}`x`: no keyword names it as each stage
reads it at the head of a list, its form by the typing's fold, its erasure, and its erasure with
the numeral abbreviations expanded, which the reader reads. -/
def headFreeAt (P : Prog) (T : Defs3) (x : Term) : List Term :=
  typingKeywords.map (unnamed P (Term.fst (Term.app (Term.snd (T.foldAt 1 [v 6] x)) Term.star))) ++
    erasureKeywords.map (unnamed P (pc P "Datatype.eraseExpr" [x])) ++
    readerKeywords.map (unnamed P (pc P "Reader.expandNums" [v 3, pc P "Datatype.eraseExpr" [x]]))

/-- That of the head the variable of index {name}`nQ` plus one ({name}`headFreeAt`). -/
def headFree (P : Prog) (T : Defs3) : List Term := headFreeAt P T (v (nQ + 1))

/-- The context of the soundness's quantifiers, the innermost first, with the further elements and
the head of a list after them. -/
def appCtx (T : Defs3) : List Tree :=
  [Defs3.ctxTy, list treeTy, list treeTy, list treeTy, list treeTy, list treeTy, T.envTy,
    list treeTy, list treeTy, list treeTy, list treeTy, treeTy]

/-- The vocabulary's rules and the stage functions' equations at a construction, after the base,
the atom's and the list's developments. -/
def appKit (P : Prog) (S : Defs) (ix : String → ℕ) (E : Array Internal.Entry) : Kit :=
  ⟨P, S, E, ix, (vocab3 ++ ["charsMap", "handlerAtom3", "rawAtom", "rawList", "rawAtomR",
    "applyTyCons", "appsCons"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩

/-- The head named by no keyword ({name}`headFree`), each test in normal form, in the context
{name}`appCtx`. -/
def headFreeNf (P : Prog) (T : Defs3) (K : Kit) : Option (List Term) :=
  (headFree P T).mapM (nfE K.G K.E (K.rules []) (appCtx T))

/-- The list of a head and further elements, under the soundness's quantifiers. -/
def appForm : Term := nodeT (Term.pair (numeral 2) (consT treeTy (v (nQ + 1)) (v nQ)))

/-- A form under the soundness's quantifiers, by default the list of a head and further elements
({name}`appForm`), and its test of source forms, its type and its optional resolution there. -/
def appTerms (P : Prog) (F : Term := appForm) : List Term :=
  let (tyT, kT) := expansionTerms P (pc P "Prelude.some" [F])
  [pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), F], tyT, kT]

/-- The stage functions' equation at a list of a head and further elements, its term the one of
{name}`appTerms` of index i: its normal form, and its normal form reached by {name}`lazyNf` with
the stage functions' steps unfolded, in the context {name}`appCtx`, the head named by no keyword
({name}`headFreeNf`); or at another form, in another context, under other hypotheses in normal
form, with further equations as rules, where they are given. -/
def appEq (P : Prog) (S : Defs) (T : Defs3) (name : String) (i : ℕ) (F : Term := appForm)
    (Γ : List Tree := appCtx T) (hyps : Option (List Term) := none) (more : List String := []) :
    Step :=
  (name, fun ix E ↦ do
    let K₀ := appKit P S ix E
    let K := { K₀ with more := K₀.more ++ more }
    let Φ ← match hyps with
      | some hs => hs.mapM (nfE K.G K.E (K.rules []) Γ)
      | none => headFreeNf P T K
    let t ← (appTerms P F)[i]?
    let unfold := ((List.range nFolds).map T.argIdx ++
      [P.idx "Typing.synList", P.idx "Reader.resolveList"]).map Internal.NormRule.delta
    -- the first hypothesis among the rules as well, which the rules of hypotheses leave out
    let rs (Φ : List Term) : List Internal.NormRule := K.rules Φ ++ [.hyp 0]
    let some l := nfE K.G K.E (rs Φ) Γ t | dbgTrace s!"{name}: left" fun _ ↦ none
    let some (r, d) := lazyNf K.G K.E (rs Φ ++ unfold) Γ 64 Φ l
      | dbgTrace s!"{name}: right" fun _ ↦ none
    pure (⟨0, Γ, Φ, Term.eq l r⟩, d))

/-- The soundness at a list of a head and further elements at expanded forms, in the context of
the further elements and the head, given that at the head and at each further element, the head
named by no keyword as each stage reads it, the tests {lit}`kws` ({name}`headFreeNf`). -/
def appCoreThm (P : Prog) (S : Defs) (T : Defs3) (kws : List Term) : Internal.Thm :=
  ⟨0, [list treeTy, treeTy],
    [Internal.instTerm [] [v 1] (expandedφ P S T),
      S.allL (Term.lam treeTy (expandedφ P S T)) (v 0)],
    expansionφ P S T (pc P "Prelude.some"
      [nodeT (Term.pair (numeral 2) (consT treeTy (v (nQ + 1)) (v nQ)))]) kws⟩

/-- The soundness at the application of a head to further elements at expanded forms, in a context
of the further elements at position 1, the statement's variables and hypotheses after them and the
head's resolved term the innermost variable, by induction on the further elements: for every type
and resolved term the soundness relates, the soundness at their application to the further
elements, the hypotheses at the list, its type and its resolved term abstracted over the head's
type {lit}`tyHead` and resolved term; at a construction, the type and the term of their application
to the element related by the application's compatibility ({name}`appCompat`), the type an arrow
of exactly two children whose domain is the element's type, as the typing's application decides,
and the rest by the hypothesis of induction. Its instance at the head's type and resolved term,
related by {lit}`goodHead`, the soundness at every further element the hypothesis of index
{lit}`iAll`. -/
def spineK (P : Prog) (S : Defs) (T : Defs3) (W : KwKit) (tyHead : List Tree → Term) (iAll : ℕ)
    (goodHead : Deducer) : Deducer := fun Γc Φc ψc ↦ do
  let K := W.K
  let L := K.L
  let o := P.o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let (tyH, kH) := expansionTerms P (pc P "Prelude.some" [v nQ])
  let srcH := pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), v nQ]
  let trace (msg : String) : Deducer := fun Γ Φ ψ ↦
    let nf (t : Term) : String := ((evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map fun r ↦
      s!"{showT r.1}").getD "none"
    dbgTrace s!"appCore {msg}: {Γ.length} vars, {Φ.length} hyps\n{
      (Φ.drop (Φ.length - 8)).map nf}\n goal {nf ψ}" fun _ ↦ none
  -- in a context, a term's convergence related at a type, as the soundness concludes
  let convAt (Γ : List Tree) (k A : Term) : Term :=
    let sh (t : Term) : Term := Term.rename t (· + 1)
    S.conv (Term.lam nat (S.evN (Term.fst (sh (W.qv 10 Γ))) (v 0) (sh (W.qv 9 Γ)) (sh k)))
      (T.relT (W.qv 10 Γ) A)
  let nfc (t : Term) : Option Term :=
    (evalRw K.G K.E (K.rules Φc) .full Γc Φc t).map Prod.fst
  let hs ← [4, 6, 7, 8].mapM fun i ↦ Φc[W.hyp i]? >>= nfc
  let goal ← nfc ψc
  let s₀ ← nfc (tyHead Γc)
  let n := Γc.length
  -- a term of the context in the context of a resolved term, a type and a list before it,
  -- the head's type, its resolved term (the innermost variable) and the further elements
  -- (the variable of position 1) abstracted to them
  let up (t : Term) : Term :=
    Term.rename (abstractTerms [Term.rename s₀ (· + 3)] 1 (Term.rename t (· + 3))) fun i ↦
      if i = 3 then 0 else if i = n + 1 then 2 else i
  let Γb := treeTy :: treeTy :: list treeTy :: Γc
  let good := Internal.Logic.imp o (isSomeT (v 1)) (Internal.Logic.imp o
    (isSomeT (pc P "Check.typeIn" [W.qv 1 Γb, W.qv 2 Γb, v 0]))
    (convAt Γb (v 0) (pc P "Prelude.get" [v 1])))
  let allE := S.allL (Term.lam treeTy (expandedφ P S T)) (v 2)
  let body := ([good, allE] ++ hs.map up).foldr (Internal.Logic.imp o) (up goal)
  let x := n - 1 + 3
  if Term.occurs body x then
    dbgTrace s!"spine: the head remains: {showT body}" fun _ ↦ none
  else
  let all (A : Tree) (b : Term) : Term := Internal.Logic.all o A (Term.lam A b)
  let ψ := all (list treeTy) (all treeTy (all treeTy body))
  -- the empty list: the type and the term themselves
  let base : Deducer := dAllI L <| dAllI L <|
    (List.range 6).foldr (fun _ k ↦ dImpI L k) fun Γ Φ ψ ↦
      let h := Φ.length
      dImpE L (h - 6) (K.byHyp (h - 3)) (fun Γ Φ ψ ↦
        dImpE L (Φ.length - 1) (K.byHyp (h - 1)) (fun Γ Φ ψ ↦
          K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
  -- a construction: the head's soundness and the rest's, the head's antecedents decided, the
  -- hypothesis of induction at the type of the head's application and its resolved term
  let step : Deducer := dAllI L <| dAllI L <| (List.range 6).foldr (fun _ k ↦ dImpI L k)
    fun Γ₀ Φ₀ ψ₀ ↦
    -- context: the term g, the type s, the tail, the head, then the spine's
    let hd (Γ : List Tree) : Term := atPos n Γ
    let sV (Γ : List Tree) : Term := atPos (n + 2) Γ
    let gV (Γ : List Tree) : Term := atPos (n + 3) Γ
    let h := Φ₀.length
    -- the hypothesis of induction, the variables' truths, then the hypotheses introduced
    let (iIH, iGood, iAll, iSrc, iTy, iRd, iK) := (h - 9, h - 6, h - 5, h - 4, h - 3, h - 2,
      h - 1)
    let tyOf (Γ : List Tree) : Term := W.inΓ hd Γ tyH
    -- the head's soundness at the statement's variables, its antecedents decided, then k
    let instHead (hIdx : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E hIdx (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
        (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
        (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"spine: the head's antecedent {i}"
          (if i ∈ antecedentHyps then K.solve 3 else K.byHyp (W.hyp i))) k) k)) Γ Φ ψ
    -- the head's term generalized, the innermost variable, after its decisions
    let induct (iHead iTail : ℕ) : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
      let kV (Γ : List Tree) : Term := atPos (Γ₁.length - 1) Γ
      let s' (Γ : List Tree) : Term := pc P "Typing.applyTy"
        [sV Γ, consT treeTy (tyOf Γ) (nilT treeTy)]
      let g' (Γ : List Tree) : Term := pc P "Reader.app" [gV Γ, kV Γ]
      -- the type an arrow over the domain dV and the codomain cV: the head's type the domain,
      -- the parts typed in the kernel, the function's and the head's convergences combined
      let arrow (iS' : ℕ) (bV dV cV : List Tree → Term) : Deducer := fun Γ₈ Φ₈ ψ₈ ↦
        let iK' := iS' + 1
        let refute (msg : String) : Deducer := linkK K s!"spine: {msg}" (K.hypFalse iS')
        let refuteK (msg : String) : Deducer := linkK K s!"spine: {msg}" (K.hypFalse iK')
        let typeIn (t : List Tree → Term) (Γ : List Tree) : Term :=
          pc P "Check.typeIn" [W.qv 1 Γ, W.qv 2 Γ, t Γ]
        let arrowT (Γ : List Tree) : Term := nodeT (Term.pair (numeral Kernel.Label.tyArrow)
          (consT treeTy (dV Γ) (consT treeTy (cV Γ) (nilT treeTy))))
        -- the parts typed in the kernel, the function's and the head's convergences
        -- combined by the application's compatibility, the arrow's relation η-expanded
        let afterDomain : Deducer :=
          decideOpt K (typeIn gV) (refuteK "the function untyped") (minimal := true) <|
          decideOpt K (typeIn kV) (refuteK "the argument untyped") (minimal := true) <|
          dImpE L iGood (K.solve 3) <| fun Γ Φ ψ ↦
          dImpE L (Φ.length - 1) (K.solve 3) (fun Γ Φ ψ ↦
            let iF := Φ.length - 1
            instHead iHead (fun Γ Φ ψ ↦
              let iX := Φ.length - 1
              let eta := Term.eq (Term.lam treeTy (Term.app (T.relT (Term.rename (W.qv 10 Γ)
                (· + 1)) (Term.rename (arrowT Γ) (· + 1))) (v 0)))
                (T.relT (W.qv 10 Γ) (arrowT Γ))
              match dEq (Internal.byFunExt P.G 0 (byMode .full P.G K.E 0 [.rule .beta])) Γ Φ
                  eta with
              | none => trace "spine: the η-expansion" Γ Φ ψ
              | some dEta =>
              dCut eta dEta (K.cutThm "appCompat" (fun Γ ↦ [W.qv 9 Γ, kV Γ, gV Γ, cV Γ, dV Γ,
                  W.qv 10 Γ]) <|
                K.impE (linkK K "spine: the function's convergence" (K.byHyp iF)) <|
                K.impE (linkK K "spine: the argument's convergence" (K.byHyp iX)) <|
                linkK K "spine: the application's convergence" fun Γ Φ ψ ↦
                  K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
        -- the domain the head's type, the test's equation renormalized by that equation
        let eqDom (k : Deducer) : Deducer := K.cutThm "equalSound" (fun Γ ↦ [dV Γ]) <|
          K.allEΓ bV <| K.impE (K.solve 3) k
        let combine : Deducer :=
          decideBits K (fun Γ ↦ call D.equal [] [dV Γ, bV Γ]) (refute "the domain")
            fun Γ Φ ψ ↦
            let iEq := Φ.length - 1
            eqDom (fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ iEq) .full) iEq afterDomain Γ Φ ψ) Γ Φ ψ
        combine Γ₈ Φ₈ ψ₈
      -- the type and the term of the head's application related
      let good : Deducer := dImpI L <| dImpI L fun Γ₂ Φ₂ ψ₂ ↦
        let iS' := Φ₂.length - 2
        let refute (msg : String) : Deducer := linkK K s!"spine: {msg}" (K.hypFalse iS')
        (decideOpt K sV (refute "no type") (minimal := true) (W.generalize (fun Γ ↦
          pc P "Prelude.get" [sV Γ]) fun Γ₃ Φ₃ ψ₃ ↦
          let y (Γ : List Tree) : Term := atPos (Γ₃.length - 1) Γ
          K.treeNode (y Γ₃) (fun Γ₄ Φ₄ ψ₄ ↦
            let X := ((evalRw K.G K.E (K.rules Φ₄) .full Γ₄ Φ₄ (call D.lab [] [y Γ₄])).map
              Prod.fst).getD Term.star
            let cs := atPos (Γ₄.length - 1)
            dBits L K.G K.E (K.ix "listCases") (K.ix "bitCases") (fun bs ↦
              if bs.map Oitavem.rank != some Kernel.Label.tyArrow then
                refute s!"the type's label {bs.map Oitavem.rank}"
              else K.norm <| decideOpt K tyOf (refute "the head untyped") (minimal := true) <|
              W.generalize (fun Γ ↦ pc P "Prelude.get" [tyOf Γ]) fun Γ₅ Φ₅ ψ₅ ↦
              let bV (Γ : List Tree) : Term := atPos (Γ₅.length - 1) Γ
              K.listCase treeTy (cs Γ₅) (refute "no domain") (fun Γ₆ Φ₆ ψ₆ ↦
                let dV := atPos (Γ₆.length - 2)
                K.listCase treeTy (v 0) (refute "no codomain") (fun Γ₇ Φ₇ ψ₇ ↦
                  let cV := atPos (Γ₇.length - 2)
                  K.listCase treeTy (v 0) (arrow iS' bV dV cV)
                    (refute "more children") Γ₇ Φ₇ ψ₇) Γ₆ Φ₆ ψ₆) Γ₅ Φ₅ ψ₅)
              3 [] X Γ₄ Φ₄ ψ₄) Γ₃ Φ₃ ψ₃)) Γ₂ Φ₂ ψ₂
      -- the hypothesis of induction's antecedents, after its instance
      let main : Deducer := K.impE (linkK K "spine: related" good) <|
        K.impE (K.byHyp iTail) <| [iSrc, iTy, iRd, iK].foldr (fun i k ↦
          K.impE (linkK K s!"spine: hypothesis {i}" (K.byHyp i)) k)
          (linkK K "spine: the goal" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
      -- the rest's resolutions present, their test's bits decided first; then the
      -- hypothesis of induction at the application's type and term
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₁ iRd) .full) iRd (fun Γ Φ ψ ↦
        K.splitHyp (Φ.length - 1) (fun Γ Φ ψ ↦
          dAllE L K.G K.E iIH (s' Γ) (K.allEΓ g' main) Γ Φ ψ) 6 Γ Φ ψ) Γ₁ Φ₁ ψ₁
    -- the head's source form and resolution decided, after its soundness and the rest's
    let split : Deducer := fun Γ Φ ψ ↦
      let iHead := Φ.length - 2
      let iTail := Φ.length - 1
      (decideIn K (fun Γ ↦ W.inΓ hd Γ srcH)
        (linkK K "spine: the head not a source form" (K.hypFalse iSrc)) <|
      (W.presentAt "spine: the head's resolution" (fun Γ ↦ W.inΓ hd Γ kH) iRd iRd
        (induct iHead iTail) (unfolding := false))) Γ Φ ψ
    dRwHyp (evalRw K.G K.E (K.rulesEx Φ₀ iAll) .full) iAll (K.conjE split) Γ₀ Φ₀ ψ₀
  -- the head's soundness, its antecedents present
  let use : Deducer := fun Γ Φ ψ ↦
    dAllE L K.G K.E (Φ.length - 1) (atPos 1 Γ) (K.allEΓ (fun _ ↦ s₀)
      (K.allEΓ (fun Γ ↦ atPos (n - 1) Γ) (K.impE (linkK K "spine: the head" goodHead)
        (K.impE (K.byHyp iAll) ([4, 6, 7, 8].foldr (fun i k ↦ K.impE (K.byHyp (W.hyp i)) k)
          (linkK K "spine: the goal" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)))))) Γ Φ ψ
  let some dψ := (dAllI L (dListIndHyp K.G base step)) Γc Φc ψ
    | dbgTrace s!"spine: the induction fails; body {showT body}" fun _ ↦ none
  dCut ψ dψ (linkK K "spine: its use" use) Γc Φc ψc

/-- The soundness at a list of a head and further elements at expanded forms
({name}`appCoreThm`): the stage functions' equations at the list cut in ({name}`appEq`); the head
a source form and its resolution present, its resolved term generalized; then, by induction on the
further elements, for every type and resolved term the soundness relates, the soundness at their
application to the further elements: at a construction, the type and the term of their
application to the head related by the application's compatibility ({name}`appCompat`), the type
an arrow of exactly two children whose domain is the head's type, as the typing's application
decides, and the rest by the hypothesis of induction; at the head's type and resolved term,
related by the soundness at the head. -/
def appCore (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("appCore", fun ix E ↦ do
    let W₀ := kwKit P S T ix E 2 [true, true] "" true
    let W := { W₀ with K := appKit P S ix E }
    let K := W.K
    let kws ← headFreeNf P T K
    let a := appCoreThm P S T kws
    let nK := kws.length
    -- the head's resolution and test of source forms, under the quantifiers
    let (_, kH) := expansionTerms P (pc P "Prelude.some" [v nQ])
    let srcH := pc P "srcForm" [Term.lam treeTy (pc P "Reader.expandNums" [v 4, v 0]), v nQ]
    -- the stage functions' equations at the context's variables, after the hypotheses
    let eqs (k : Deducer) : Deducer := ["appSrcEq", "appTyEq", "appResEq"].foldr (fun nm k ↦
      W.cutApply nm (fun Γ ↦ (List.range 12).map fun i ↦ atPos (11 - i) Γ)
        ((List.range nK).map fun _ ↦ dHyp) k) k
    let (tyH, _) := expansionTerms P (pc P "Prelude.some" [v nQ])
    let L := K.L
    -- the head's soundness, its antecedents present
    let goodHead : Deducer := dImpI L <| dImpI L fun Γ₀ Φ₀ ψ₀ ↦
      let (iTy, iK) := (Φ₀.length - 2, Φ₀.length - 1)
      dAllE L K.G K.E (W.ihIdx 0) (W.qv 1 Γ₀) (((List.range (nQ - 1)).foldr
        (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
        (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"spine: the head's antecedent {i}"
          (if i = 6 then K.byHyp iTy else if i = 8 then K.byHyp iK
            else if i ∈ antecedentHyps then K.solve 3 else K.byHyp (W.hyp i))) k)
        fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ₀ Φ₀ ψ₀
    -- the spine: the hypotheses at the list, its type and its resolved term, the head's type and
    -- resolved term generalized, by induction on the further elements
    let spine : Deducer := spineK P S T W (fun Γ ↦ W.inΓ (atPos 0) Γ tyH) 1 goodHead
    let decisions : Deducer :=
      eqs <|
      decideIn K (fun Γ ↦ W.inΓ (atPos 0) Γ srcH)
        (linkK K "the head not a source form" (W.hypFalseU (W.hyp 4))) <|
      W.present "the head's resolution" (fun Γ ↦ W.inΓ (atPos 0) Γ kH) 7 spine
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI K.L k)
        ((List.range (W.nH + nK)).foldr (fun _ k ↦ dImpI K.L k) decisions) a.ctx a.hyps a.concl
      | dbgTrace "appCore: not proved" fun _ ↦ none
    pure (a, d))

/-- Under the quantifiers of the soundness, of a list of a head, the variable of index {name}`nQ`
plus one, and further elements: the head, its form by the expansion's fold, named neither by the
keyword of case analyses nor by that of structural recursion, its expansion not named by the
keyword of abstractions, and its expansion named by no keyword as each stage reads it
({name}`headFreeAt`). -/
def srcFree (P : Prog) (T : Defs3) : List Term :=
  let h := v (nQ + 1)
  let h₀ := Term.fst (Term.app (Term.snd (T.foldAt 0 [] h)) Term.star)
  let h' := pc P "Prelude.get" [expansionOf P h]
  [unnamed P h₀ "Datatype.kwCase", unnamed P h₀ "Datatype.kwCata", unnamed P h' "Reader.kwLam"] ++
    headFreeAt P T h'

/-- The soundness at a list of a head and further elements at source forms, in the context of
the further elements and the head, given that at the head and at each further element, the head
and its expansion named by no keyword, the tests {lit}`kws` ({name}`srcFree` in normal form). -/
def appSrcThm (P : Prog) (S : Defs) (T : Defs3) (kws : List Term) : Internal.Thm :=
  ⟨0, [list treeTy, treeTy],
    [Internal.instTerm [] [v 1] (datatypeφ P S T),
      S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0)],
    expansionφ P S T (expansionOf P
      (nodeT (Term.pair (numeral 2) (consT treeTy (v (nQ + 1)) (v nQ))))) kws⟩

/-- The soundness at a list of elements at source forms from that at expanded forms, in a context
of the list's elements and the statement's variables and hypotheses after them, the source form
{lit}`F` under the statement's quantifiers: the expansions of the elements at the positions
{lit}`heads` present, generalized, in turn; the list's expansion's equation with its lazy normal
form cut in, which writes it as the list of its elements' expansions; the expansions of the further
elements, at the position {lit}`tailPos`, sound at expanded forms by induction on them, each by
{name}`expSound`, from the soundness at every further element, the hypothesis of index
{lit}`allIdx`, the further elements those after the first {lit}`skip` of the expansion; then the
theorem {lit}`core` at its instance {lit}`σ` at the heads' expansions and the further elements',
its hypotheses the premises {lit}`prems` and the further elements' soundness, instantiated at the
statement's variables, the statement's hypotheses and the {lit}`nKws` tests after them its
antecedents. The statement's {lit}`nRenorm` hypotheses after its own are renormalized after the
list's expansion is generalized. -/
def srcSound (P : Prog) (S : Defs) (T : Defs3) (W : KwKit) (F : Term) (heads : List ℕ)
    (skip tailPos allIdx : ℕ) (core : String) (σ : List ℕ → Term → List Tree → List Term)
    (prems : List Deducer) (nRenorm nKws : ℕ) : Deducer :=
  let K := W.K
  let L := K.L
  let o := P.o
  let n₀ := W.n
  let unfold := ((List.range nFolds).map T.argIdx ++
    [P.idx "Typing.synList", P.idx "Reader.resolveList"]).map Internal.NormRule.delta
  -- a term under the quantifiers in a context that extends theirs
  let atCtx (t : Term) (Γ : List Tree) : Term := Term.rename t (· + (Γ.length - (nQ + n₀)))
  let expF := expansionOf P F
  -- a term's equation with its lazy normal form, after the hypotheses
  let cutLazy (t : Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
    let (l, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ (atCtx t Γ)
    let (r, d) ← lazyNf K.G K.E (K.rules Φ ++ unfold) Γ 64 Φ l
    dCut (Term.eq l r) d k Γ Φ ψ
  -- the keyword hypotheses renormalized, after the hypotheses
  let renorm (k : Deducer) : Deducer := (List.range nRenorm).foldr (fun j k ↦
    dRwHyp (fun Γ Φ t ↦ evalRw K.G K.E (K.rulesEx Φ (W.hyp (W.nH + j))) .full Γ Φ t)
      (W.hyp (W.nH + j)) k) k
  let trace (msg : String) : Deducer := fun Γ Φ ψ ↦
    let nf (t : Term) : String := ((evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map fun r ↦
      s!"{showT r.1}").getD "none"
    dbgTrace s!"appSrc {msg}: {Γ.length} vars, {Φ.length} hyps\n{
      (Φ.drop (Φ.length - 4)).map nf}\n goal {nf ψ}" fun _ ↦ none
  -- the expanded list's tail, its further elements' expansions sound at expanded forms by
  -- induction, then the soundness at expanded forms at the expanded heads and tail
  let main (hPos : List ℕ) (pres₀ : Term) (n₁ : ℕ) : Deducer := fun Γ Φ ψ ↦ do
    -- the presence test, from the context before its decision
    let pres := Term.rename pres₀ (· + (Γ.length - n₁))
    let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules Φ) .full Γ Φ t).map Prod.fst
    let some F' := nf (pc P "Prelude.get" [atCtx expF Γ]) | trace "no expansion" Γ Φ ψ
    let tl? := (List.range (skip - 1)).foldl (fun t _ ↦ t.bind fun t ↦ (consParts t).map
      fun (_, tl) ↦ nodeT (Term.pair (numeral 2) tl)) (some F')
    let some (_, tl) := tl?.bind consParts | trace "the expansion not a construction" Γ Φ ψ
    let n := Γ.length
    let rsI := n - 1 - tailPos
    -- a term of the context in the context of a list before it, the further elements
    -- abstracted to it
    let up (t : Term) : Term := Term.rename (Term.rename t (· + 1)) fun i ↦
      if i = rsI + 1 then 0 else i
    let allD := S.allL (Term.lam treeTy (datatypeφ P S T)) (v 0)
    let allX (t : Term) : Term := S.allL (Term.lam treeTy (expandedφ P S T)) t
    let ψt := Internal.Logic.imp o allD (Internal.Logic.imp o (up pres) (allX (up tl)))
    let ψ' := Internal.Logic.all o (list treeTy) (Term.lam (list treeTy) ψt)
    let base : Deducer := dImpI L <| dImpI L <| K.solve 3
    -- a construction: the head's expansion present, sound by expSound; the rest's by the
    -- hypothesis of induction
    let step : Deducer := dImpI L <| dImpI L fun Γ₀ Φ₀ ψ₀ ↦
      let (iIH, iAll, iPres) := (Φ₀.length - 3, Φ₀.length - 2, Φ₀.length - 1)
      let hd (Γ : List Tree) : Term := atPos n Γ
      let anyHyp : Deducer := fun Γ Φ ψ ↦
        (List.range Φ.length).reverse.findSome? fun h ↦ K.byHyp h Γ Φ ψ
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₀ iAll) .full) iAll (K.conjE <|
        decideOpt K (fun Γ ↦ pc P "Datatype.expandExpr" [W.qv 3 Γ, hd Γ])
          (fun Γ Φ ψ ↦ (K.hypFalse iPres Γ Φ ψ).orElse fun _ ↦
            dbgTrace s!"appSrc: an element's expansion absent; presence {((evalRw K.G K.E
              (K.rulesEx Φ iPres) .full Γ Φ ((Φ[iPres]?).getD Term.star)).map
                fun r ↦ showT r.1)}" fun _ ↦ none)
          (minimal := true) <|
        W.generalize (fun Γ ↦ pc P "Prelude.get" [pc P "Datatype.expandExpr"
          [W.qv 3 Γ, hd Γ]]) <|
        -- the rest's expansions present, their test's bits decided
        (fun k Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ iPres) .full) iPres (fun Γ Φ ψ ↦
          (K.splitHyp (Φ.length - 1) k) Γ Φ ψ) Γ Φ ψ) <| K.norm <| dConjI L
          (linkK K "appSrc: the element's expansion" <|
            W.cutApply "expSound" (fun Γ ↦ [hd Γ]) [anyHyp] <|
            K.allEΓ (W.qv 3) <| K.impE (K.solve 3) fun Γ Φ ψ ↦
              K.byHyp (Φ.length - 1) Γ Φ ψ)
          (linkK K "appSrc: the rest" <|
            dImpE L iIH anyHyp fun Γ Φ ψ ↦
              dImpE L (Φ.length - 1) (K.byHyp iPres) (fun Γ Φ ψ ↦
                K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) Γ₀ Φ₀ ψ₀
    let core : Deducer := fun Γ Φ ψ ↦
      (W.cutApply core (fun Γ ↦ σ hPos (Term.rename tl (· + (Γ.length - n))) Γ)
        (prems ++ [linkK K "appSrc: the tail's expansions" fun Γ Φ ψ ↦
          K.byHyp (Φ.length - 1) Γ Φ ψ]) <|
      fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
        (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <| fun Γ Φ ψ ↦
        ((List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"appSrc: hypothesis {i}"
          (if i = 5 then K.solve 3 else K.byHyp (W.hyp i))) k) <|
        (List.range nKws).foldr (fun j k ↦
          K.impE (linkK K s!"appSrc: keyword {j}" (K.solve 3)) k) <|
        linkK K "appSrc: the goal" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) Γ Φ ψ)
        Γ Φ ψ
    let use : Deducer := fun Γ Φ ψ ↦
      dAllE L K.G K.E (Φ.length - 1) (atPos tailPos Γ) (K.impE (K.byHyp allIdx) <|
        K.impE (K.byHyp (W.hyp 5)) core) Γ Φ ψ
    let some dψ := (dAllI L (dListIndHyp K.G base step)) Γ Φ ψ'
      | dbgTrace s!"appSrc: the tail's induction fails; {showT ψt}" fun _ ↦ none
    dCut ψ' dψ (linkK K "appSrc: the tail's use" use) Γ Φ ψ
  -- the heads' expansions present, generalized, the first first
  let final (hPos : List ℕ) : Deducer := fun Γg Φg ψg ↦
    (renorm <| cutLazy expF <|
    -- the further elements' expansions present, their test's bits decided
    fun Γ Φ ψ ↦ match (evalRw K.G K.E (K.rules Φ) .full Γ Φ ((Φ[W.hyp 5]?).getD
        Term.star)).map Prod.fst with
      | none => trace "no presence" Γ Φ ψ
      | some pres => dRwHyp (evalRw K.G K.E (K.rulesEx Φ (W.hyp 5)) .full) (W.hyp 5)
          (fun Γ' Φ ψ ↦ (K.splitHyp (Φ.length - 1) (main hPos pres Γ.length))
            Γ' Φ ψ) Γ Φ ψ) Γg Φg ψg
  let _ := (L, o)
  (heads.foldr (fun p (rec : List ℕ → Deducer) hPos ↦
    decideOpt K (atCtx (expansionOf P (v (nQ + n₀ - 1 - p)))) (cutLazy expF <|
        linkK K "appSrc: the head's expansion absent" (K.hypFalse (W.hyp 5)))
      (W.generalize (fun Γ ↦ pc P "Prelude.get" [atCtx (expansionOf P (v (nQ + n₀ - 1 - p))) Γ]) <|
        fun Γg Φg ψg ↦ rec (hPos ++ [Γg.length - 1]) Γg Φg ψg)
      (minimal := true)) final) []

/-- The soundness at a list of a head and further elements at source forms ({name}`appSrcThm`):
by {name}`srcSound`, the head's expansion generalized, from the soundness at expanded forms
({name}`appCore`) at the expansions, the head's by {name}`expSound`. -/
def appSrc (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("appSrc", fun ix E ↦ do
    let W₀ := kwKit P S T ix E 2 [true, true]
    let W := { W₀ with K := appKit P S ix E }
    let K := W.K
    let kws ← (srcFree P T).mapM (nfE K.G K.E (K.rules []) (appCtx T))
    let a := appSrcThm P S T kws
    let nK := kws.length
    let headSound : Deducer := linkK K "appSrc: the head's expansion" <|
      W.cutApply "expSound" (fun Γ ↦ [atPos 0 Γ]) [K.byHyp 0] <|
      K.allEΓ (W.qv 3) <| K.impE (K.solve 3) fun Γ Φ ψ ↦
        K.byHyp (Φ.length - 1) Γ Φ ψ
    let body := srcSound P S T W appForm [0] 1 1 1 "appCore"
      (fun hPos tl Γ ↦ [tl, atPos (hPos.headD 0) Γ]) [headSound] nK (headFree P T).length
    let some d := (List.range nQ).foldr (fun _ k ↦ dAllI K.L k)
        ((List.range (W.nH + nK)).foldr (fun _ k ↦ dImpI K.L k) body) a.ctx a.hyps a.concl
      | dbgTrace "appSrc: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the stage functions at applications and the soundness there at expanded
forms: the unrollings of the folds over reversals, the soundness at a source form given at its
expansion, the stage functions' equations at a list of a head and further elements, and the
soundness at such a list at expanded forms. -/
def stagesDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [revFoldAll P S, applyTyCons P S, appsCons P S, expSound P S T, appEq P S T "appSrcEq" 0,
    appEq P S T "appTyEq" 1, appEq P S T "appResEq" 2, appCore P S T]

/-- The development of the soundness at applications at source forms. -/
def applyDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [appSrc P S T]

/-- The names of the base's, the atom's and the list's declarations. -/
def listNames (P : Prog) (S : Defs) (T : Defs3) : Option (List String) := do
  let dev ← baseDev3 P S T
  pure (dev.map (·.1) ++ (atomDev3 P S T).map (·.1) ++ (listDev3 P S T).map (·.1))

/-- A development after declarations of the given names, stored as the certificate of a name,
each declaration checked as it is stored and its statement reported as it is proved. -/
def certifyAfter (P : Prog) (names : List String) (cert : String) (steps : List Step)
    (before : List Internal.Thm) : Except String (List (String × List Internal.Decl)) := do
  let E : Array Internal.Entry := (before.map Internal.Entry.language).toArray
  unless names.length = E.size do
    throw s!"the certificates before {cert} are not those it continues from"
  let steps := steps.map fun (nm, f) ↦
    (nm, fun ix E ↦ (f ix E).map fun r ↦
      dbgTrace s!"{nm} proved" fun _ ↦ r)
  let (_, _, ds) ← developAfter names E steps
  checkAfter P.G E (steps.map (·.1)) ds
  pure [(cert, ds)]

/-- The development of the stage functions at applications ({name}`stagesDev3`), after the
base's, the atom's and the list's declarations, stored as the certificate
{lit}`datatype-stages`. -/
def stagesCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P names "datatype-stages" (stagesDev3 P S T) before

/-- The development of the soundness at applications at source forms ({name}`applyDev3`), after
the base's, the atom's, the list's and the stage functions', stored as the certificate
{lit}`datatype-apply`. -/
def applyCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1)) "datatype-apply" (applyDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
