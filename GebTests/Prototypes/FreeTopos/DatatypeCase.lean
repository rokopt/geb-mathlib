/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeDecode
public import GebTests.Prototypes.FreeTopos.DatatypeFolds
public meta import GebTests.Prototypes.FreeTopos.DatatypeDecode -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at case analyses

The soundness of the datatype language's stage-1 compiler at a case analysis.

## Main definitions

* {lit}`caseCertificates` — the development, stored as the certificate {lit}`datatype-case`.

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

/-- The program with the typing's tests of a datatype's constructors kept folded. -/
def caseProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ ["Typing.ctorOk"] }

/-- The disjunction, by the prelude's right fold, of a test at each element of a list of trees, the
test a term in the element v1 and the disjunction of the rest v0, the list's variables shifted by
two beneath them. -/
def anyT (P : Prog) (test xs : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy (pc P "Prelude.or" [test, v 0])))
    (leafT bnilT) xs

/-- The equality of labels, the kernel's primitive applied. -/
def eqL (a b : Term) : Term := apps ((primT Kernel.Prim.eq).getD Term.star) [a, b]

/-- A tree's child of index 0, the kernel's primitive applied. -/
def child0 (t : Term) : Term := apps ((primT Kernel.Prim.child).getD Term.star) [t, leafT bnilT]

/-- A constructor among a list of a marker's constructors whose test holds at a label has that
label ({lit}`Typing.ctorOk` tests the constructor's label first): by induction on the
constructors; at a construction, the head's label equal to the label or not. Equal, the goal's
disjunction holds at the head; unequal, the head's test fails, and the induction hypothesis
gives the rest's. In the context of the constructors, under the markers, the label and the
children's memberships. -/
def ctorsLabel (P : Prog) (S : Defs) : Step :=
  ("ctorsLabel", fun ix E ↦ do
    let P := caseProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the memberships v0, the label v1, the markers v2, the constructors
    -- v3; beneath the folds' two binders, each shifted by two
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.all o (list Ls) (Term.lam (list Ls) (Internal.Logic.imp o
        (truth o (anyT P (pc P "Typing.ctorOk" [v 4, v 1, v 3, v 2]) (v 3)))
        (truth o (anyT P (eqL (child0 (v 1)) (v 3)) (v 3)))))))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dAllI L (dAllI L (dImpI L (linkK K "ctorsLabel: empty" lastFalse)))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the memberships, the label, the markers, the rest, the head; hypotheses: the
    -- induction hypothesis, the disjunction's truth at the construction
    let cons : Deducer := dAllI L <| dAllI L <| dAllI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (hd, ms, l, rs) := (at_ 0, at_ 2, at_ 3, at_ 4)
      let found := Φ₁.length - 1
      -- the head's label the label: the goal's disjunction at the head
      let equal : Deducer := linkK K "ctorsLabel: the head" (K.solve 3)
      -- another: the head's test false, by its unfolding, an equation cut in, by which the
      -- disjunction is the rest's; the induction hypothesis at the rest
      let unfolded : List Internal.NormRule := [.delta (P.idx "Typing.ctorOk")]
      let rest : Deducer := linkK K "ctorsLabel: the rest" fun Γ Φ ψ ↦ do
        let e := Term.eq (pc P "Typing.ctorOk" [ms Γ, hd Γ, l Γ, rs Γ]) (leafT bnilT)
        let de ← linkK K "ctorsLabel: the head's test false"
          (evalTools K Φ (List.range Φ.length) unfolded).byNorm Γ Φ e
        dCut e de (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ found) .full) found (fun Γ Φ ψ ↦
            dAllE L K.G K.E 0 (ms Γ) (K.allEΓ l (K.allEΓ rs (K.impE (K.byHyp found)
              (K.auto 3)))) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
      decideIn K (fun Γ ↦ eqL (child0 (hd Γ)) (l Γ)) rest equal Γ₁ Φ₁ ψ₁
    let d₁ ← cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The elements of a list of trees whose child of index 0 has the label {lit}`l`, as the typing
selects a clause's constructors, by the prelude's right fold. -/
def filterL (l xs : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls (condT Ls
    (call D.lab [] [eqL (child0 (v 1)) (Term.rename l (· + 2))]) (consT treeTy (v 1) (v 0))
    (v 0)))) (nilT treeTy) xs

/-- Where an element of a list of trees has the label {lit}`l`, the selection of those elements
({name}`filterL`) is not of length zero: by induction on the list; at a construction, the head's
label decided. Equal, the selection is a construction, whose length is not zero; unequal, it is
the rest's, and the disjunction the rest's, by the induction hypothesis. In the context of the list,
under the label. -/
def labelFilter (P : Prog) (S : Defs) : Step :=
  ("labelFilter", fun ix E ↦ do
    let P := caseProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifier: the label v0, the list v1; beneath the folds' binders, shifted by two
    let φ := Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o
      (truth o (anyT P (eqL (child0 (v 1)) (v 2)) (v 1)))
      (Internal.Logic.imp o (truth o (eqL (pc P "Prelude.length" [filterL (v 0) (v 1)])
        (leafT bnilT))) (Internal.Logic.ff o))))
    let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let d₀ ← dAllI L (dImpI L (dImpI L (linkK K "labelFilter: empty" fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 2) Γ Φ ψ))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the label, the rest, the head; hypotheses: the induction hypothesis, the
    -- disjunction's truth and the length's being zero at the construction
    let cons : Deducer := dAllI L <| dImpI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (hd, l) := (at_ 0, at_ 2)
      let (found, isZero) := (Φ₁.length - 2, Φ₁.length - 1)
      let equal : Deducer := linkK K "labelFilter: the head" (K.hypFalse isZero)
      let rest : Deducer := linkK K "labelFilter: the rest" fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (l Γ) (K.impE (K.byHyp found) (K.impE (K.byHyp isZero) lastFalse)) Γ Φ ψ
      decideIn K (fun Γ ↦ eqL (child0 (hd Γ)) (l Γ)) rest equal Γ₁ Φ₁ ψ₁
    let d₁ ← cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The constructor a clause names, the only one of a marker's constructors with the clause's
label, passes its test at a tree of that label where some constructor does: by induction on the
constructors; at a construction, the head's label decided. Equal, the selection's first element is
the head, whose test, decided, holds or fails; failing, some constructor of the rest passes, of
that label ({name}`ctorsLabel`), so that the rest's selection, decided, is empty, against
{name}`labelFilter`, or not, against the selection's length one. Unequal, the head's test fails,
and the selection, the disjunction and the length are the rest's: the induction hypothesis. In the
context of the constructors, under the markers, the label and the children's memberships. -/
def ctorUnique (P : Prog) (S : Defs) : Step :=
  ("ctorUnique", fun ix E ↦ do
    let P := caseProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    let ok (c : Term) : Term := pc P "Typing.ctorOk" [v 2, c, v 1, v 0]
    -- under the quantifiers: the memberships v0, the label v1, the markers v2, the constructors
    -- v3; beneath the folds' two binders, each shifted by two
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.all o (list Ls) (Term.lam (list Ls) (Internal.Logic.imp o
        (truth o (anyT P (pc P "Typing.ctorOk" [v 4, v 1, v 3, v 2]) (v 3)))
        (Internal.Logic.imp o
          (truth o (eqL (pc P "Prelude.length" [filterL (v 1) (v 3)]) (leafT (numeral 1))))
          (truth o (ok (pc P "Prelude.at" [filterL (v 1) (v 3), leafT bnilT]))))))))))
    let d₀ ← dAllI L (dAllI L (dAllI L (dImpI L (dImpI L (linkK K "ctorUnique: empty"
        fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 2) Γ Φ ψ))))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let unfolded : List Internal.NormRule := [.delta (P.idx "Typing.ctorOk")]
    -- context: the memberships, the label, the markers, the rest, the head; hypotheses: the
    -- induction hypothesis, the disjunction's truth and the selection's length one
    let cons : Deducer := dAllI L <| dAllI L <| dAllI L <| dImpI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (hd, tl, ms, l, rs) := (at_ 0, at_ 1, at_ 2, at_ 3, at_ 4)
      let (found, one) := (Φ₁.length - 2, Φ₁.length - 1)
      let okAt (c : List Tree → Term) (Γ : List Tree) : Term :=
        pc P "Typing.ctorOk" [ms Γ, c Γ, l Γ, rs Γ]
      -- the head's test false, its equation cut in, and the disjunction rewritten by it
      let headFalse (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
        let e := Term.eq (okAt hd Γ) (leafT bnilT)
        let de ← linkK K "ctorUnique: the head's test false"
          (evalTools K Φ (List.range Φ.length) unfolded).byNorm Γ Φ e
        dCut e de (fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ found) .full) found k Γ Φ ψ) Γ Φ ψ
      -- equal, the head's test failing: the rest's disjunction of labels, then its selection
      -- decided
      let second : Deducer := linkK K "ctorUnique: a second constructor" <|
        (fun k Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ found) .full) found k Γ Φ ψ) <|
        K.cutThm "ctorsLabel" (fun Γ ↦ [tl Γ]) <| K.allEΓ ms <| K.allEΓ l <| K.allEΓ rs <|
        K.impE (K.byHyp found) fun Γ Φ ψ ↦
        let labels := Φ.length - 1
        K.listCase treeTy (filterL (l Γ) (tl Γ))
          (linkK K "ctorUnique: the rest's selection empty" <|
            K.cutThm "labelFilter" (fun Γ ↦ [tl Γ]) <| K.allEΓ l <|
            K.impE (K.byHyp labels) <| K.impE (K.solve 3) fun Γ Φ ψ ↦
              K.hypFalse (Φ.length - 1) Γ Φ ψ)
          (linkK K "ctorUnique: the rest's selection a construction" (K.hypFalse one)) Γ Φ ψ
      let equal : Deducer := linkK K "ctorUnique: the head" <|
        decideIn K (okAt hd) second (K.solve 3)
      let rest : Deducer := linkK K "ctorUnique: the rest" <| headFalse fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (ms Γ) (K.allEΓ l (K.allEΓ rs (K.impE (K.byHyp found)
          (K.impE (K.byHyp one) (K.auto 3))))) Γ Φ ψ
      decideIn K (fun Γ ↦ eqL (child0 (hd Γ)) (l Γ)) rest equal Γ₁ Φ₁ ψ₁
    let d₁ ← cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The conjunction, by the prelude's right fold, of a test at each element of a list of trees, the
test a term in the element v1 and the conjunction of the rest v0, the list's variables shifted by
two beneath them. -/
def allT (P : Prog) (test xs : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy (pc P "Prelude.and" [test, v 0])))
    (leafT (numeral 1)) xs

/-- Where each of a marker's constructors has the label of one of a list of labels, as the typing
requires of a case analysis's clauses without an else clause, and one of the constructors has the
label {lit}`l`, so has one of the labels: by induction on the constructors; at a construction, the
head's covering decided, false refuting the hypothesis, then the head's label. Equal, the labels'
equation ({lit}`eqBSound`) rewrites the head's covering to the goal; unequal, the induction
hypothesis at the rest. In the context of the constructors, under the labels and the label. -/
def covers (P : Prog) (S : Defs) : Step :=
  ("covers", fun ix E ↦ do
    let P := caseProg P
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let Ls := list treeTy
    -- under the quantifiers: the label v0, the labels v1, the constructors v2
    let φ := Internal.Logic.all o Ls (Term.lam Ls (Internal.Logic.all o treeTy (Term.lam treeTy
      (Internal.Logic.imp o
        (truth o (allT P (anyT P (eqL (v 1) (child0 (v 3))) (v 3)) (v 2)))
        (Internal.Logic.imp o (truth o (anyT P (eqL (child0 (v 1)) (v 2)) (v 2)))
          (truth o (anyT P (eqL (v 1) (v 2)) (v 1))))))))
    let d₀ ← dAllI L (dAllI L (dImpI L (dImpI L (linkK K "covers: empty" fun Γ Φ ψ ↦
        K.hypFalse (Φ.length - 1) Γ Φ ψ)))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the label, the labels, the rest, the head; hypotheses: the induction hypothesis,
    -- the covering and the disjunction at the construction
    let cons : Deducer := dAllI L <| dAllI L <| dImpI L <| dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (hd, labels, l) := (at_ 0, at_ 2, at_ 3)
      let (cover, found) := (Φ₁.length - 2, Φ₁.length - 1)
      let headCover (Γ : List Tree) : Term :=
        anyT P (eqL (v 1) (child0 (Term.rename (hd Γ) (· + 2)))) (labels Γ)
      -- the head's label the label: the labels' equation, the decision rewritten by it
      let equal (decided : ℕ) : Deducer := linkK K "covers: the head" fun Γ Φ ψ ↦
        let lb (t : Term) : Term := call D.lab [] [t]
        (K.cutThm "eqBSound" (fun Γ ↦ [lb (l Γ)]) <| K.allEΓ (fun Γ ↦ lb (child0 (hd Γ))) <|
          K.impE (K.solve 3) <| normLastK K fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E (K.rulesEx Φ decided) .full) decided (K.solve 3) Γ Φ ψ) Γ Φ ψ
      let rest : Deducer := linkK K "covers: the rest" fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (labels Γ) (K.allEΓ l (K.impE (K.byHyp cover)
          (K.impE (K.byHyp found) (K.auto 3)))) Γ Φ ψ
      decideIn K headCover (linkK K "covers: the head uncovered" (K.hypFalse cover))
        (fun Γ Φ ψ ↦ decideIn K (fun Γ ↦ eqL (child0 (hd Γ)) (l Γ)) rest
          (equal (Φ.length - 1)) Γ Φ ψ) Γ₁ Φ₁ ψ₁
    let d₁ ← cons [Ls, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [Ls], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The removal of the head of a list of trees, as a function. -/
def tailFn : Term := Term.lam (list treeTy) (call D.tail [treeTy] [v 0])

/-- The removal of the first n elements of a list of trees, the library's iteration of
{name}`tailFn`, as the kernel's child of index n reads a tree's children. -/
def dropT (n xs : Term) : Term := call D.iter [list treeTy] [n, tailFn, xs]

/-- The head of a list of trees, the tree 0 at the empty list. -/
def headT (xs : Term) : Term := call D.headD [treeTy] [leafT bnilT, xs]

/-- A function of trees applied to each element of a list, by the prelude's right fold. -/
def mapFnT (g xs : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls
    (consT treeTy (Term.app (Term.rename g (· + 2)) (v 1)) (v 0)))) (nilT treeTy) xs

/-- A function of trees to lists of trees applied to each element of a list of trees, by the
prelude's right fold. -/
def mapListsT (g xs : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy (list Ls) (Term.lam treeTy (Term.lam (list Ls)
    (consT Ls (Term.app (Term.rename g (· + 2)) (v 1)) (v 0)))) (nilT Ls) xs

/-- The removal of any number of elements of the empty list leaves the empty list: by induction on
the number's bits, the iteration of the rest's number applying the removal to its own result,
which the induction hypothesis rewrites, then the bit decided. Its left side is in normal form. -/
def dropNil (P : Prog) (S : Defs) : Step :=
  ("dropNil", fun ix E ↦ do
    let K : Kit := ⟨caseProg P, S, E, ix, []⟩
    -- the left side in the normal form of the rules, as a rule it rewrites there
    let l ← nfE K.G K.E (K.rules []) [bitsTy] (dropT (v 0) (nilT treeTy))
    let φ := Term.eq l (nilT treeTy)
    let byIH : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (.hyp 0 :: K.rules Φ) .full) (fun _ _ ψ ↦
        match Internal.eqParts ψ with
        | some (a, b) => if a == b then some (nd .join [nd .refl, nd .refl]) else none
        | none => none) Γ Φ ψ
    let d₀ ← K.byNorm [] [] (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
    let d₁ ← linkK K "dropNil: a bit" (fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 0) .full) 0 (K.bitCase (v 1) byIH byIH) Γ Φ ψ)
      [list bitTy, bitTy] [Internal.weakenElem φ]
      (Internal.listConsAt 1 bitTy φ)
    pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The head of a list's map, after the removal of any number of elements, is the function at the
head of the list after it, for a function taking the tree 0 to itself: by induction on the list.
The empty list's removals leave it empty ({name}`dropNil`). At a construction, the number empty,
or a successor ({lit}`bitsSucc`), by which the removal is the rest's after one fewer
({lit}`rIterSucc`): the induction hypothesis at it. In the context of the list, under the function
and the number. -/
def headDropMap (P : Prog) (S : Defs) : Step :=
  ("headDropMap", fun ix E ↦ do
    let K : Kit := ⟨caseProg P, S, E, ix, ["dropNil"]⟩
    let L := K.L
    let o := P.o
    let F := exp treeTy treeTy
    let zero := leafT bnilT
    -- under the quantifiers: the number v0, the function v1, the list v2
    let φ := Internal.Logic.all o F (Term.lam F (Internal.Logic.all o bitsTy (Term.lam bitsTy
      (Internal.Logic.imp o (Term.eq (Term.app (v 1) zero) zero)
        (Term.eq (headT (dropT (v 0) (mapFnT (v 1) (v 2))))
          (Term.app (v 1) (headT (dropT (v 0) (v 2)))))))))
    let d₀ ← dAllI L (dAllI L (dImpI L (linkK K "headDropMap: empty" (normLastK K K.byNorm))))
      [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let some (Internal.Entry.language bs) := E[ix "bitsSucc"]? | none
    let succRule := Internal.NormRule.thm (ix "rIterSucc") [list treeTy]
    -- context: the number, the function, the rest, the head; hypotheses: the induction
    -- hypothesis, the function's value at 0
    let cons : Deducer := dAllI L <| dAllI L <| dImpI L <| normLastK K fun Γ₁ Φ₁ ψ₁ ↦
      let at_ (j : ℕ) (Γ : List Tree) : Term := v (Γ.length - 1 - j)
      let (g, n) := (at_ 2, at_ 3)
      let cases := Internal.instTerm [] [n Γ₁] bs.concl
      -- the number a successor: its equation, then the induction hypothesis at the predecessor
      let succ : Deducer := K.exE fun Γ Φ ψ ↦
        let pred := atPos (Γ.length - 1)
        let eqn := Φ.length - 1
        let refl : Deducer := fun _ _ ψ ↦ match Internal.eqParts ψ with
          | some (a, b) => if a == b then some (nd .join [nd .refl, nd .refl]) else none
          | none => none
        dRwBy (evalRw K.G K.E (K.rules Φ ++ [succRule]) .full) (fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (g Γ) (K.allEΓ pred (K.impE (K.solve 3) <| normLastK K
            fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (K.rules Φ ++ [succRule]) .full) refl Γ Φ ψ))
            Γ Φ ψ) Γ (Φ.set eqn (Φ.getD eqn Term.star)) ψ
      dCut cases (nd (.apply (ix "bitsSucc") [] [n Γ₁]))
        (dDisjE L Φ₁.length (linkK K "headDropMap: the number empty" K.byNorm)
          (linkK K "headDropMap: a successor" succ)) Γ₁ Φ₁ ψ₁
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The statement of a binding's convergence: where a term converges to a value of which a
predicate {lit}`Q` holds, and a body, in the environment extended by any such value, converges to
a value of which a predicate {lit}`Pr` holds, the application of the abstraction of the body to
the term converges to such a value. In the context of the environment, the term, the body, the
annotation, the predicates and the relation's context. -/
def letConvThm (P : Prog) (S : Defs) : Internal.Thm :=
  let o := P.o
  let Pred := exp treeTy omega
  ⟨0, [list treeTy, treeTy, treeTy, treeTy, Pred, Pred, Defs3.ctxTy],
    [S.conv (Term.lam nat (S.evN (Term.fst (v 7)) (v 0) (v 1) (v 2))) (v 4),
      Internal.Logic.all o treeTy (Term.lam treeTy (Internal.Logic.imp o (Term.app (v 5) (v 0))
        (S.conv (Term.lam nat (S.evN (Term.fst (v 8)) (v 0) (consT treeTy (v 1) (v 2)) (v 4)))
          (v 6))))],
    S.conv (Term.lam nat (S.evN (Term.fst (v 7)) (v 0) (v 1) (appT (lamT (v 4) (v 3)) (v 2))))
      (v 5)⟩

/-- A binding converges ({name}`letConvThm`): the term's convergence's threshold, value and
stability; the body's at that value; both thresholds shifted to their sum, two levels above which
the application evaluates to the body's value: the abstraction to its closure at once, the term at
the application's level, and the closure's application a level below, which evaluates the body a
level below it. -/
def letConv (P : Prog) (S : Defs) : Step :=
  ("letConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let a := letConvThm P S
    let d? : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      -- the term's convergence's parts
      dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) 0 (K.exE <| K.exE <| K.conjE
        fun Γ₁ Φ₁ ψ₁ ↦
        let (ne, we) := (atPos (Γ₁.length - 2), atPos (Γ₁.length - 1))
        let (se, qe) := (Φ₁.length - 2, Φ₁.length - 1)
        -- the body's at the term's value
        dAllE L K.G K.E 1 (we Γ₁) (K.impE (K.byHyp qe) <| K.unfoldConv <| K.exE <| K.exE <|
          K.conjE fun Γ₂ Φ₂ ψ₂ ↦
          let (nb, wb) := (atPos (Γ₂.length - 2), atPos (Γ₂.length - 1))
          let (sb, pb) := (Φ₂.length - 2, Φ₂.length - 1)
          let sum (Γ : List Tree) : Term := S.add (ne Γ) (nb Γ)
          shiftK K se false nb (shiftK K sb true ne fun Γ Φ ψ ↦
            let (e₁, b₁) := (Φ.length - 2, Φ.length - 1)
            dConv L K.G K.E S (succN (succN (sum Γ))) (wb Γ)
              (linkK K "letConv stable" <|
                instNK K e₁ (fun _ ↦ succN (succN (v 0))) <| instNK K b₁ (fun _ ↦ v 0) K.byNorm)
              (linkK K "letConv satisfied" (K.byHyp pb)) Γ Φ ψ) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
      Γ₀ Φ₀ ψ₀
    let some d := d? a.ctx a.hyps a.concl | dbgTrace "letConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The instance of a theorem with hypotheses at terms of the context, each hypothesis proved by
its deducer, cut in after the hypotheses. -/
def applyThm (K : Kit) (name : String) (σ : List Tree → List Term) (prems : List Deducer)
    (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
  let some (Internal.Entry.language b) := K.E[K.ix name]? | none
  let ds ← (b.hyps.zip prems).mapM fun (h, d) ↦ d Γ Φ (Internal.instTerm [] (σ Γ) h)
  dCut (Internal.instTerm [] (σ Γ) b.concl) (nd (.apply (K.ix name) [] (σ Γ)) ds) k Γ Φ ψ

/-- The typing's functions of field types kept folded: the reading of a type, the naming of a
datatype, the markers' names, the recognizer of the typing's forms and the memberships. -/
def fieldFolded : List String :=
  ["Typing.readTy", "Typing.namesData", "Typing.markerNames", "Typing.Tx.member",
    "Typing.memberships"]

/-- A field's tree, of whose memberships the field's test ({lit}`Typing.fieldOk`) holds, has its
quotation related at the field's type ({lit}`Typing.fieldTy`), where the type is present and the
relation's markers are the typing environment's. In the context of the tree, the field's type's
form, the typing environment and the relation's context. -/
def fieldRelThm (P : Prog) (T : Defs3) : Internal.Thm :=
  let ms := pc P "Typing.envMs" [v 2]
  let ty := pc P "Typing.fieldTy" [v 2, v 1]
  ⟨0, [treeTy, treeTy, T.envTy, Defs3.ctxTy],
    [Term.eq (Term.snd (v 3)) ms, truth P.o (pc P "Prelude.isSome" [ty]),
      truth P.o (pc P "Typing.fieldOk" [ms, v 1, pc P "Typing.memberships" [ms, v 0]])],
    Term.app (T.relT (v 3) (pc P "Prelude.get" [ty])) (pc P "Eval.valQuote" [v 0])⟩

/-- A field's quotation related at its type ({name}`fieldRelThm`): the field's type unfolded; the
form's being one of the typing's forms decided, the type's reading present, generalized, and its
label decided. At the trees and at an opaque sort every quotation is related; at a datatype, its
naming and the marker's presence decided, the quotation related by {lit}`relTDatum`, the
membership the field's test; at any other label, and where a decision fails, the field's type is
absent, refuting its presence. -/
def fieldRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("fieldRel", fun ix E ↦ do
    let P := { P with folded := P.folded ++ fieldFolded }
    let K : Kit := ⟨P, S, E, ix, (vocab3 ++ ["relTTree"]).filter fun nm ↦
      0 < ix nm ∧ ix nm < E.size⟩
    let L := K.L
    let a := fieldRelThm P T
    let fieldTyD := Internal.NormRule.delta (P.idx "Typing.fieldTy")
    let (t, ft, env, R) := (atPos 3, atPos 2, atPos 1, atPos 0)
    let ms (Γ : List Tree) : Term := pc P "Typing.envMs" [env Γ]
    -- the field's type absent, against its hypothesis: the hypothesis's image by the test of
    -- presence, falsity equal to truth
    let refute (msg : String) : Deducer := linkK K s!"fieldRel: {msg}" fun Γ Φ ψ ↦
      (anyFalse K Γ Φ ψ).orElse fun _ ↦
        K.hypFalse 1 Γ Φ ψ
    -- at the trees or an opaque sort: every quotation related
    let anyQuote : Deducer := linkK K "fieldRel: a quotation" <|
      fun Γ Φ ψ ↦ dRwBy (evalRw K.G K.E (K.rules Φ ++ [.delta T.q]) .full)
        (dExI L K.G K.E (t Γ) (K.solve 3)) Γ Φ ψ
    -- at a datatype: its naming and the marker's presence decided, the relation by relTDatum
    let datatype (pA : ℕ) : Deducer := linkK K "fieldRel: a datatype" <|
      decideIn K (fun Γ ↦ pc P "Typing.namesData" [env Γ, atPos pA Γ, ft Γ])
        (refute "unnamed") <|
      decideIn K (fun Γ ↦ pc P "Prelude.isSome"
          [pc P "Reader.indexOf" [ft Γ, pc P "Typing.markerNames" [ms Γ]]])
        (refute "no marker") <|
      applyThm K "relTDatum" (fun Γ ↦ [t Γ, ft Γ, atPos pA Γ, env Γ, R Γ])
        [linkK K "fieldRel: markers" dHyp, linkK K "fieldRel: naming" (K.solve 3),
          linkK K "fieldRel: membership" (K.byHyp 2)] <|
        fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- the type read, of position pA: its node, its label decided
    let byLabel (pA : ℕ) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦ K.treeNode (atPos pA Γ₀) (fun Γ Φ ψ ↦
      dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
        match bs.map Oitavem.rank with
        | some 0 => anyQuote
        | some 6 => anyQuote
        | some 5 => datatype pA
        | _ => refute s!"the type's label {bs.map Oitavem.rank}") 3 [] (v 1) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    let body : Deducer := fun Γ Φ ψ ↦
      dRwBy (evalRw K.G K.E (K.rules Φ ++ [fieldTyD]) .full) (fun Γ Φ ψ ↦
      dRwHyp (fun Γ Φ u ↦ evalRw K.G K.E (K.rulesEx Φ 1 ++ [fieldTyD]) .full Γ Φ u) 1 (
      decideIn K (fun Γ ↦ pc P "Typing.Tx.member" [ft Γ]) (refute "no form") <|
      decideOpt K (fun Γ ↦ pc P "Typing.readTy" [env Γ, ft Γ]) (refute "no type") <|
      generalizeK K (fun Γ ↦ pc P "Prelude.get" [pc P "Typing.readTy" [env Γ, ft Γ]])
        fun Γ Φ ψ ↦ byLabel (Γ.length - 1) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
    let some d := body a.ctx a.hyps a.concl | dbgTrace "fieldRel: not proved" fun _ ↦ none
    pure (a, d))

/-- The quotations of a list of trees, by the prelude's right fold. -/
def quotesT (P : Prog) (ts : Term) : Term :=
  let Ls := list treeTy
  foldrT treeTy Ls (Term.lam treeTy (Term.lam Ls
    (consT treeTy (pc P "Eval.valQuote" [v 1]) (v 0)))) (nilT treeTy) ts

/-- The tree type, as the typing writes it. -/
def tyTreeT : Term := nodeT (Term.pair (numeral Kernel.Label.tyTree) (nilT treeTy))

/-- The quotations of a list of trees are related at the tree type: by induction on the list, each
quotation related by {lit}`relTTree`. In the context of the list, under the relation's context. -/
def quotesRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("quotesRel", fun ix E ↦ do
    let K : Kit := ⟨caseProg P, S, E, ix, ["relTTree"]⟩
    let L := K.L
    let o := P.o
    -- under the quantifier: the relation's context v0, the list v1
    let φ := Internal.Logic.all o Defs3.ctxTy (Term.lam Defs3.ctxTy
      (S.allL (T.relT (v 0) tyTreeT) (quotesT P (v 1))))
    let d₀ ← linkK K "quotesRel: empty" (dAllI L (K.solve 3)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- context: the relation's context, the rest, the head: the head's quotation's witness, the
    -- rest's by the induction hypothesis at the context
    let cons : Deducer := dAllI L fun Γ Φ ψ ↦
      dAllE L K.G K.E 0 (v 0) (normLastK K <| K.norm <| dConjI L
        (linkK K "quotesRel: the head" (dExI L K.G K.E (v 2) (K.solve 3)))
        (linkK K "quotesRel: the rest" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- A right fold's list, function and start, where a term is the prelude's right fold of a list
({name}`foldrT`): the application of a fold of the list to the pair of the function and the start.
-/
def foldrParts (t : Term) : Option (Term × Term × Term) :=
  match t.label, t.children with
  | .app, [lr, pr] => match lr.label, lr.children, pr.label, pr.children with
    | .listRec, [_, _, xs], .pair, [f, z] => some (xs, f, z)
    | _, _, _, _ => none
  | _, _ => none

/-- A right fold rebuilt at another list: the fold whose parts {name}`foldrParts` reads, its
list replaced. -/
def foldrAt (t xs : Term) : Term :=
  match t.label, t.children with
  | .app, [lr, pr] => match lr.label, lr.children with
    | .listRec, [n, c, _] => RoseTree.node .app [RoseTree.node .listRec [n, c, xs], pr]
    | _, _ => t
  | _, _ => t

/-- The first subterm of a term that is a right fold of the list {lit}`xs`, in the subterm order
of the term. -/
def findFoldr (xs t : Term) : Option Term :=
  RoseTree.para (fun (l : Internal.Label) (cs : List (Term × Option Term)) ↦
    let t' : Term := RoseTree.node l (cs.map Prod.fst)
    match foldrParts t' with
    | some (ys, _, _) => if ys == xs then some t' else cs.findSome? (·.2)
    | none => cs.findSome? (·.2)) t

/-- The context of the walk of a clause's fields: the fixed fields' variables v0, the body's
erasure v1, its typing as a function of the named context v2, the remaining children's variables
v3, the constructor v4, the typing environment v5, the kernel's globals' types v6, the type and
numeral abbreviations v7 and v8, the definitions' names v9 and the relation's context v10. -/
def walkCtx (T : Defs3) : List Tree :=
  [list treeTy, treeTy, exp (list treeTy) treeTy, list treeTy, treeTy, T.envTy, list treeTy,
    list treeTy, list treeTy, list treeTy, Defs3.ctxTy]

/-- The node of a list of trees. -/
def listNode' (xs : Term) : Term := nodeT (Term.pair (numeral 2) xs)

/-- The folds of a clause's walk in {name}`walkCtx`, read off the normal forms of the typing's walk
({lit}`Typing.caseFields`), of the constructor's test ({lit}`Typing.ctorOk`) and of the erasure's
bindings ({lit}`Datatype.bindVars`, at the case analysis's binders): each a right fold of the
fixed fields' variables, or of the field types, given to {name}`foldrAt`. -/
structure WalkParts where
  /-- The typing's walk. -/
  ty : Term
  /-- The constructor's test of the fields. -/
  ok : Term
  /-- The erasure's bindings. -/
  er : Term

/-- The parts of a clause's walk ({name}`WalkParts`), by the rules of a kit. -/
def walkParts (K : Kit) (T : Defs3) : Option WalkParts := do
  let P := K.P
  let Γ := walkCtx T
  let nf (t : Term) : Option Term := (evalRw K.G K.E (K.rules []) .full Γ [] t).map Prod.fst
  let parts := listNode' (consT treeTy (leafT bnilT) (consT treeTy (listNode' (v 0))
    (consT treeTy (listNode' (v 3)) (nilT treeTy))))
  let tyNF ← nf (pc P "Typing.caseFields" [v 5, v 4, parts, v 2, nilT treeTy])
  let ty ← findFoldr (v 0) tyNF
  let fts ← nf (call D.children [] [apps ((primT Kernel.Prim.child).getD Term.star)
    [v 4, leafT (numeral 1)]])
  let okNF ← nf (pc P "Typing.ctorOk" [pc P "Typing.envMs" [v 5], v 4, leafT bnilT,
    nilT (list treeTy)])
  let ok ← findFoldr fts okNF
  let aT := pc P "Datatype.aT" []
  let aC := pc P "Datatype.aC" []
  let sLet (x a e b : Term) : Term := pc P "Datatype.sLet" [x, a, e, b]
  let fb := Term.lam treeTy (Term.lam treeTy (sLet (v 1) aT (pc P "Datatype.sHeadOf" [aC])
    (sLet aC (pc P "Datatype.sList" [aT]) (pc P "Datatype.sTailOf" [aC]) (v 0))))
  let rb := Term.lam treeTy (Term.lam treeTy (sLet (v 1) (pc P "Datatype.sList" [aT]) aC (v 0)))
  let erNF ← nf (pc P "Datatype.bindVars" [fb, rb, parts, v 1])
  let er ← findFoldr (v 0) erNF
  pure ⟨ty, ok, er⟩

/-- A term shifted beneath k binders. -/
def sh (k : ℕ) (t : Term) : Term := Term.rename t (· + k)

/-- A tree's characters fixed by the expansion of the numeral abbreviations {lit}`nums` where it
is an atom, as a predicate of the tree; {lit}`nums` outside the predicate's binder. A source form's
atoms are fixed so; a variable the typing admits is an atom. -/
def fixedAtom (P : Prog) (nums : Term) : Term :=
  Term.lam treeTy (Internal.Logic.imp P.o (truth P.o (pc P "Datatype.isAtomTx" [v 0]))
    (truth P.o (pc P "charsFixed" [Term.lam treeTy (pc P "Reader.expandNums" [sh 2 nums, v 0]),
      call D.children [] [v 0]])))

/-- The named context's entry of the children remaining, at the list type of the trees. -/
def fieldsEntry (P : Prog) : Term :=
  pc P "Typing.abbr" [pc P "Typing.boundName" [pc P "Typing.kwFields" []],
    pc P "Typing.tyList" [pc P "Typing.tyT" []]]

/-- The kernel's type the reader reads of the list type of the trees, at the type abbreviations. -/
def listTK (P : Prog) (tys : Term) : Term :=
  pc P "Prelude.get" [pc P "Reader.readType" [tys, pc P "Datatype.sList" [pc P "Datatype.aT" []]]]

/-- The soundness of a term's erasure at a typing of it as a function of the named context, in
{name}`walkCtx` beneath k binders: for all named contexts, environments and kernel's contexts,
the environment related to the named context, the typing present at the context, the erasure's
resolution in the context's scope present, of a type in the kernel's context, and the context's
names admitted, the resolution converges to a value related at the type. -/
def bodyφ (P : Prog) (S : Defs) (T : Defs3) (k : ℕ) (b syn : Term) : Term :=
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  -- beneath the three quantifiers: the named context v2, the environment v1, the kernel's context
  -- v0; the walk's context's variables shifted by k + 3
  let q (i : ℕ) : Term := v (i + k + 3)
  let kb := pc P "Reader.resolve" [q 7, q 9, pc P "Reader.expandNums" [q 8, sh 3 b],
    scopeOf P (q 8) (v 2)]
  let ty := Term.app (sh 3 syn) (v 2)
  all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    imp (T.envT (q 10) (v 2) (v 1)) <| imp (isSomeT ty) <| imp (isSomeT kb) <|
    imp (isSomeT (pc P "Check.typeIn" [q 6, v 0, get kb])) <| imp (T.cxT (q 5) (v 2)) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (q 10))) (v 0) (v 2) (sh 1 (get kb))))
      (T.relT (q 10) (get ty))

/-- The statement of the walk of a clause's fields, at the fixed fields' variables v0 of
{name}`walkCtx`: where the relation's markers are the typing environment's, no numeral
abbreviation names a keyword, the variables' characters are fixed by the expansion of the numeral
abbreviations, as a source form's are, and the body's erasure is sound at its typing
({name}`bodyφ`), for
all field types, children remaining, and environment, named context and kernel's context beneath
the children remaining's entries, if the typing's walk is present at the field types, the
constructor's test holds of the children's memberships, the environment is related to the named
context, whose names are admitted, and the erasure's bindings resolve, of a type in the kernel's
context, the resolution converges to a value related at the walk's type. -/
def walkφ (P : Prog) (S : Defs) (T : Defs3) (w : WalkParts) : Term :=
  let o := P.o
  let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
  let imp := Internal.Logic.imp o
  let isSomeT (t : Term) : Term := truth o (pc P "Prelude.isSome" [t])
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  -- beneath the five quantifiers: the field types v4, the children v3, the environment, the named
  -- context and the kernel's context beneath the children's entries v2, v1 and v0; the walk's
  -- context's variables shifted by 5
  let q (i : ℕ) : Term := v (i + 5)
  let ms := pc P "Typing.envMs" [q 5]
  let cx := consT treeTy (fieldsEntry P) (v 1)
  let env := consT treeTy (pc P "Eval.ofList" [leafT (numeral Kernel.Label.tyTree),
    quotesT P (v 3)]) (v 2)
  let kc := consT treeTy (listTK P (q 7)) (v 0)
  let tyW := Term.app (Term.app (sh 5 w.ty) (v 4)) cx
  let mem := Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])
  let okW := Term.app (foldrAt (sh 5 w.ok) (v 4)) (mapListsT mem (v 3))
  let kw := pc P "Reader.resolve" [q 7, q 9, pc P "Reader.expandNums" [q 8, sh 5 w.er],
    scopeOf P (q 8) cx]
  -- an atom's characters fixed by the expansion of the numeral abbreviations
  let fixed : Term := fixedAtom P (v 8)
  imp (Term.eq (Term.snd (v 10)) (pc P "Typing.envMs" [v 5])) <| imp (T.kwsT (v 8)) <|
    imp (S.allL fixed (v 0)) <| imp (S.allL fixed (v 3)) <|
    imp (bodyφ P S T 0 (v 1) (v 2)) <|
    all (list treeTy) <| all (list treeTy) <| all (list treeTy) <| all (list treeTy) <|
    all (list treeTy) <|
    imp (isSomeT tyW) <| imp (truth o okW) <| imp (T.envT (q 10) cx env) <|
    imp (T.cxT (q 5) cx) <| imp (isSomeT kw) <|
    imp (isSomeT (pc P "Check.typeIn" [q 6, kc, get kw])) <|
    S.conv (Term.lam nat (S.evN (Term.fst (sh 1 (q 10))) (v 0) (sh 1 env) (sh 1 (get kw))))
      (T.relT (q 10) (get tyW))

/-- The statement of the kernel's typing of a binding at its parts: where the kernel types the
application of an abstraction over a type to a term, it types the abstraction's body in the context
extended by the type and the term in the context. In the context of the term, the body, the type,
the kernel's context and the globals' types. -/
def letTypedThm (P : Prog) : Internal.Thm :=
  let typed (ctx t : Term) : Term :=
    truth P.o (pc P "Prelude.isSome" [pc P "Check.typeIn" [v 4, ctx, t]])
  ⟨0, [treeTy, treeTy, treeTy, list treeTy, list treeTy],
    [typed (v 3) (appT (lamT (v 2) (v 1)) (v 0))],
    Internal.Logic.conj P.o (typed (consT treeTy (v 2) (v 3)) (v 1)) (typed (v 3) (v 0))⟩

/-- The kernel's typing of a binding at its parts ({name}`letTypedThm`): the type's being a type
decided, then the body's type in the context extended and the term's type, each absent refuting
the hypothesis, as the typing tests them; the conjuncts then by normalization. -/
def letTyped (P : Prog) (S : Defs) : Step :=
  ("letTyped", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a := letTypedThm P
    let (e, b, A, C, G) := (atPos 4, atPos 3, atPos 2, atPos 1, atPos 0)
    let refute (msg : String) : Deducer := linkK K s!"letTyped: {msg}" (K.hypFalse 0)
    let typeIn (ctx t : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Check.typeIn" [G Γ, ctx Γ, t Γ]
    let some d := (decideIn K (fun Γ ↦ pc P "Check.isTy" [A Γ]) (refute "not a type") <|
        decideOpt K (typeIn (fun Γ ↦ consT treeTy (A Γ) (C Γ)) b) (refute "the body untyped") <|
        decideOpt K (typeIn C e) (refute "the term untyped") <|
        linkK K "letTyped: the parts" (dConjI K.L (K.solve 3) (K.solve 3)))
        a.ctx a.hyps a.concl
      | dbgTrace "letTyped: not proved" fun _ ↦ none
    pure (a, d))

/-- The hypothesis of index {lit}`h`, an equation of bitstrings, refuted: normalized without itself,
its sides' images by the test of their truth are falsity and truth. -/
def eqClash (K : Kit) (h : ℕ) : Deducer := fun Γ Φ ψ ↦
  match (Φ[h]?).bind Internal.eqParts with
  | some _ => dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h (fun Γ Φ ψ ↦
      K.image (Φ.length - 1) (fun u ↦ K.truthB u) (K.trueOf (dFalse K.L dHyp)) Γ Φ ψ)
      Γ Φ ψ
  | none => none

/-- A hypothesis refuted: normalized to falsity, or an equation of bitstrings by {name}`eqClash`,
the latest first. -/
def anyClash (K : Kit) : Deducer := fun Γ Φ ψ ↦
  (anyFalse K Γ Φ ψ).orElse fun _ ↦
    (List.range Φ.length).reverse.findSome? fun h ↦ eqClash K h Γ Φ ψ

/-- The erasure's builders of the syntax of a case analysis's clauses, which the proofs keep
folded, each stage function at them stated by an equation ({lit}`builderEq`). -/
def builders : List String :=
  ["Datatype.sLet", "Datatype.sHeadOf", "Datatype.sTailOf"]

/-- The program for the walk of a clause's fields: the typing's functions of field types and of
the walk's steps, and the erasure's builders ({name}`builders`), kept folded. -/
def walkProg (P : Prog) : Prog :=
  { P with folded := P.folded ++ fieldFolded ++ ["Typing.fieldTy", "Typing.bindVar",
      "Typing.bindRest", "Typing.fieldOk"] ++ builders }

/-- The names of the vocabulary's rules of the walk: the datatype language's, the readings of atoms
and lists, and the reader's resolution at the erasure's bindings and at the head of the children
remaining ({lit}`bindEqs`). -/
def walkMore (ix : String → ℕ) (E : Array Internal.Entry) : List String :=
  (vocab3 ++ ["charsMap", "handlerAtom3", "rawAtom", "rawList", "rawAtomR", "letRes",
      "headRes"]).filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size

/-- The vocabulary's rules of the walk ({name}`walkMore`) without the reader's resolution at a
binding and at the head of the children remaining, which the equation at a field's binding
({lit}`stepRes`) states in their place, the resolution at a binding kept folded; and the
rebuilding of the field types and of the children's memberships by the case analysis of lists
({lit}`lcaseRebuild`). -/
def walkRules (ix : String → ℕ) (E : Array Internal.Entry) : List String :=
  (walkMore ix E).filter (· ∉ ["letRes", "headRes"]) ++
    (["lcaseRebuild", "lcaseRebuildL"].filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size)

/-- The name of an atom, as the reader looks it up among the abbreviations. -/
def atomNameT (a : Term) : Term := nodeT (Term.pair (numeral 0) (call D.children [] [a]))

/-- The atoms the erasure's bindings write, none of which a numeral abbreviation names: the
reserved keywords of bindings, types, abstractions and the case analysis of lists, the
implementation's names of the children remaining and of a list's head and tail, and the numeral
zero. -/
def walkAtoms (P : Prog) : List Term :=
  ["Reader.kwLet", "Reader.kwT", "Reader.kwList", "Reader.kwLcase", "Reader.kwNil",
    "Reader.kwLam"].map (pc P · []) ++
  ["Datatype.aC", "Datatype.aH", "Datatype.aTl", "Datatype.aZero"].map
    fun a ↦ atomNameT (pc P a [])

/-- The rules that resolve the erasure's fixed syntax: the reader's steps unfolded, and the
lookups' equations. -/
def resolveRules (P : Prog) (T : Defs3) (ix : String → ℕ) (E : Array Internal.Entry) :
    List Internal.NormRule :=
  [T.argIdx 4, P.idx "Reader.resolveList", P.idx "Reader.resolveAtom",
      P.idx "Reader.numeral"].map Internal.NormRule.delta ++
    (lookupEqNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size).map
      fun nm ↦ Internal.NormRule.thm (ix nm) []

/-- The presence of a name's index among names at a construction is the disjunction of its equality
with the head and its presence among the rest, which occurs once: in the context of the rest, the
head and the name, both sides in the normal form with the index folded. Proved by deciding the
equality and, unequal, the rest's presence, with the index's equations. -/
def isSomeIndexOfCons (P : Prog) (S : Defs) : Step :=
  ("isSomeIndexOfCons", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, lookupEqNames.filter fun nm ↦ 0 < ix nm ∧ ix nm < E.size⟩
    let equalT ← primT Kernel.Prim.equal
    let Γ := [list treeTy, treeTy, treeTy]
    let isSome (xs : Term) : Term := pc P "Prelude.isSome" [pc P "Reader.indexOf" [v 2, xs]]
    -- both sides in the normal form of the rules without the index's equations, the index
    -- folded, as the rule meets it
    let K₀ : Kit := ⟨P, S, E, ix, []⟩
    let (l, _) ← evalRw K₀.G K₀.E (K₀.rules []) .full Γ [] (isSome (consT treeTy (v 1) (v 0)))
    let (r, _) ← evalRw K₀.G K₀.E (K₀.rules []) .full Γ []
      (pc P "Prelude.or" [apps equalT [v 2, v 1], isSome (v 0)])
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let restIx (Γ : List Tree) : Term := pc P "Reader.indexOf" [atPos 0 Γ, atPos 2 Γ]
    let some d := decideIn K (fun Γ ↦ apps equalT [atPos 0 Γ, atPos 1 Γ])
        (decideOpt K restIx (linkK K "isSomeIndexOfCons: unequal, absent" K.byNorm)
          (linkK K "isSomeIndexOfCons: unequal, present" K.byNorm))
        (linkK K "isSomeIndexOfCons: equal" K.byNorm) a.ctx a.hyps a.concl
      | dbgTrace "isSomeIndexOfCons: not proved" fun _ ↦ none
    pure (a, d))

/-- A test equal to truth's value is true: in the context of the test. Proved by rewriting by the
hypothesis, then normalization. -/
def truthOfEq (P : Prog) (S : Defs) : Step :=
  ("truthOfEq", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let a : Internal.Thm := ⟨0, [treeTy], [Term.eq (v 0) (leafT (numeral 1))], truth P.o (v 0)⟩
    let some d := dRwBy (evalRw K.G K.E [.hyp 0] .full) (K.solve 3) a.ctx a.hyps a.concl
      | dbgTrace "truthOfEq: not proved" fun _ ↦ none
    pure (a, d))

/-- A disjunction of tests is true where one of them is, the left ({lit}`orLeftT`) or the right
({lit}`orRightT`): in the context of the right test and the left. Proved by deciding the left. -/
def orTrue (P : Prog) (S : Defs) (left : Bool) : Step :=
  (if left then "orLeftT" else "orRightT", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let o := P.o
    let Γ := [treeTy, treeTy]
    let a : Internal.Thm := ⟨0, Γ, [truth o (if left then v 1 else v 0)],
      truth o (pc P "Prelude.or" [v 1, v 0])⟩
    let some d := decideIn K (fun Γ ↦ atPos 0 Γ)
        (if left then K.hypFalse 0 else K.byHyp 0) (K.solve 3) a.ctx a.hyps a.concl
      | dbgTrace "orTrue: not proved" fun _ ↦ none
    pure (a, d))

/-- A name the erasure writes is excluded from the abbreviated names ({lit}`Defs3.kwsT`): it is
reserved, the implementation's or a numeral. Closed; proved by the disjunct that holds
({name}`orTrue`), by normalization, the index's presence by {name}`isSomeIndexOfCons`, which does
not duplicate the rest's index, and the reading of numerals unfolded. -/
def atomExcluded (P : Prog) (S : Defs) (name : String) (n : Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let φ := truth P.o (pc P "Prelude.or" [pc P "Prelude.isSome" [pc P "Reader.indexOf" [n,
        pc P "Reader.reservedNames" []]], pc P "Prelude.or" [pc P "implName" [n],
          pc P "Prelude.isSome" [pc P "Reader.numeral" [call D.children [] [n]]]]])
    let K : Kit := { K with more := ["isSomeIndexOfCons", "indexOfNil"] }
    let rs := K.rules [] ++ [.delta (P.idx "Reader.numeral")]
    let reserved := pc P "Prelude.isSome" [pc P "Reader.indexOf" [n,
      pc P "Reader.reservedNames" []]]
    let impl := pc P "implName" [n]
    let num := pc P "Prelude.isSome" [pc P "Reader.numeral" [call D.children [] [n]]]
    -- a test's truth by its value's, the test normalized alone ({lit}`truthOfEq`)
    let byTest (t : Term) : Deducer :=
      applyThm K "truthOfEq" (fun _ ↦ [t]) [fun Γ Φ ψ ↦
        dEq (fun Γ _ t u ↦ byMode .full K.G K.E 0 rs Γ [] t u) Γ Φ ψ] dHyp
    -- the instance's conclusion the goal as written
    let byLast : Deducer := dHyp
    -- the disjunct that holds: reserved, else the implementation's, else a numeral
    let disj : Deducer := fun Γ Φ ψ ↦
      (applyThm K "orLeftT" (fun _ ↦ [pc P "Prelude.or" [impl, num], reserved])
        [byTest reserved] byLast Γ Φ ψ).orElse fun _ ↦
      applyThm K "orRightT" (fun _ ↦ [pc P "Prelude.or" [impl, num], reserved]) [fun Γ Φ ψ ↦
        (applyThm K "orLeftT" (fun _ ↦ [num, impl]) [byTest impl] byLast Γ Φ ψ).orElse fun _ ↦
        applyThm K "orRightT" (fun _ ↦ [num, impl]) [byTest num] byLast Γ Φ ψ] byLast Γ Φ ψ
    let some d := disj [] [] φ | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (⟨0, [], [], φ⟩, d))

/-- Atoms' names not abbreviated, each the test of its abbreviation's presence decided, present
refuted by the abbreviations' coherence with the keywords, the hypothesis of index {lit}`hKw`
({lit}`Defs3.kwsT`) at the name, which is reserved, the implementation's or a numeral, by the
name's lemma among {lit}`lemmas` or the walk's atoms' ({lit}`atomExcluded`). -/
def plainAtoms (K : Kit) (T : Defs3) (names : List Term) (nums : List Tree → Term) (hKw : ℕ)
    (k : Deducer) (lemmas : List (Term × String) := []) : Deducer :=
  let P := K.P
  let lastFalse : Deducer := fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
  -- the name's being reserved, the implementation's or a numeral, at the erasure's atoms by their
  -- lemmas ({lit}`atomExcluded`, and those given), else by normalization
  let table := lemmas ++ (walkAtoms P).zipIdx.map fun (n, i) ↦ (n, s!"atomExcluded{i}")
  let excluded (n : Term) : Deducer := fun Γ Φ ψ ↦
    match (table.find? (·.1 == n)).map (·.2) with
    | some nm => K.cutThm nm (fun _ ↦ []) (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ
    | none => K.solve 3 Γ Φ ψ
  names.foldr (fun n k ↦
    decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [n, nums Γ]]) k
      (linkK K s!"an atom abbreviated {showT n}" <|
        dRwHyp (evalRw K.G K.E [.delta (T.q + 5 + 2 * nFolds)] .head) hKw
          (K.allEΓ (fun _ ↦ n) (K.impE (K.solve 3) (K.impE (excluded n) lastFalse))))) k

/-- The erasure's binding of a fixed field's variable {lit}`x` to the head of the children
remaining, and of the children remaining to their tail, around a rest {lit}`r`. -/
def fieldStep (P : Prog) (x r : Term) : Term :=
  let aT := pc P "Datatype.aT" []
  let aC := pc P "Datatype.aC" []
  pc P "Datatype.sLet" [x, aT, pc P "Datatype.sHeadOf" [aC],
    pc P "Datatype.sLet" [aC, pc P "Datatype.sList" [aT], pc P "Datatype.sTailOf" [aC], r]]

/-- The negation of a test's truth. -/
def notTest (o : ℕ) (t : Term) : Term := notT o (truth o t)

/-- The name of the children remaining, as the reader reads it. -/
def fieldsName (P : Prog) : Term := atomNameT (pc P "Datatype.aC" [])

/-- The test that the name of the children remaining is an atom's name, the reader's comparison of
names. -/
def namedFields (P : Prog) (cs : Term) : Term :=
  apps ((primT Kernel.Prim.equal).getD Term.star)
    [fieldsName P, nodeT (Term.pair (numeral 0) cs)]

/-- An equation of a stage function at a builder's syntax, named {lit}`name`, in a context, where
each of a list of tests fails: its left side in the normal form of the rules, its right side the
one given, in that normal form, or the left side's normal form with the builders and the rules
{lit}`extra` unfolded,
under the equations of the tests' failures; proved by deciding each test, true refuting its
hypothesis, then both sides by normalization. -/
def builderEq (name : String) (P : Prog) (S : Defs) (Γ : List Tree) (tests : List Term)
    (lhs : Term) (extra : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule)
    (rhs : Option Term := none) : Step :=
  (name, fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let rs : List Internal.NormRule := (builders.map fun nm ↦ .delta (P.idx nm)) ++ extra P ix E
    -- the tests' failures' equations past a first hypothesis, which supplies no rule
    let fails ← tests.mapM fun t ↦ do
      let (X, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [t])
      pure (Term.eq X bnilT)
    let fails := Term.star :: fails
    let r ← match rhs with
      | some r => (evalRw K.G K.E (K.rules []) .full Γ [] r).map Prod.fst
      | none => (evalRw K.G K.E (K.rules fails ++ rs) .full Γ fails lhs).map Prod.fst
    -- the left side in the normal form of the rules, as a rule it rewrites there
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ [] lhs
    let a : Internal.Thm := ⟨0, Γ, tests.map (notTest P.o), Term.eq l r⟩
    let decisions : Deducer → Deducer := fun k ↦
      tests.zipIdx.foldr (fun (t, i) k ↦
        decideIn K (fun _ ↦ t) k (linkK K s!"{name}: test {i} true" fun Γ Φ ψ ↦
          dImpE K.L i (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) k
    let some d := decisions (linkK K s!"{name}: the sides" fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ rs) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

/-- The resolution of a fixed field's binding ({name}`fieldStep`) of an atom's name, in the scope
headed by the children remaining's name, where the binder is not that name and the rest's
resolution, in the scope extended by the two bindings, is present: in the context of the rest, the
binder's characters, the scope's tail, the type abbreviations and the definitions' names, the
normal form of the resolution with the tail's resolution's equation ({lit}`tailRes`) and the rest's
resolution's label, which leaves its value folded; proved by
deciding the comparison of the names, true refuting the hypothesis, then the sides by
normalization with that equation. -/
def stepRes (P : Prog) (S : Defs) : Step :=
  ("stepRes", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let Γ := [treeTy, list treeTy, list treeTy, list treeTy, list treeTy]
    let x := nodeT (Term.pair (numeral 1) (v 1))
    let lhs := pc P "Reader.resolve" [v 3, v 4, fieldStep P x (v 0),
      consT treeTy (fieldsName P) (v 2)]
    let σ : List Term := [v 2, v 1, v 3, v 4]
    let some (Internal.Entry.language tr) := E[ix "tailRes"]? | none
    let (X, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (call D.lab [] [namedFields P (v 1)])
    -- the equations past a first hypothesis, which supplies no rule
    let fails := [Term.star, Term.eq X bnilT]
    let (tl, tr') ← (Internal.eqParts (Internal.instTerm [] σ tr.concl))
    let (tl', _) ← evalRw K.G K.E (K.rules fails) .full Γ fails tl
    let (tr'', _) ← evalRw K.G K.E (K.rules fails) .full Γ fails tr'
    let Φ := fails ++ [Term.eq tl' tr'']
    -- the left side in the normal form of the walk's rules, the resolution at a binding folded
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let (r, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ lhs
    let a : Internal.Thm := ⟨0, Γ, [notTest P.o (namedFields P (v 1))], Term.eq l r⟩
    let some d := decideIn K (fun _ ↦ namedFields P (v 1))
        (linkK K "stepRes: the resolution" <|
          applyThm K "tailRes" (fun _ ↦ σ) [K.byHyp 0] <| normLastK K fun Γ Φ ψ ↦
          dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ) Γ (rwHyps (K.rules Φ) Φ) t u)
            Γ Φ ψ)
        (linkK K "stepRes: the binder named as the children" fun Γ Φ ψ ↦
          dImpE K.L 0 (K.solve 3) (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
        a.ctx a.hyps a.concl
      | dbgTrace "stepRes: not proved" fun _ ↦ none
    pure (a, d))

/-- The resolution of a fixed field's binding of the children remaining's name itself, in the scope
headed by that name: in the context of the rest, the scope's tail, the type abbreviations and the
definitions' names, its normal form with the reader's steps and the head's and the tail's builders
unfolded, the tail's term then the variable bound at the head. Proved by normalization with the
same rules. -/
def stepResC (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("stepResC", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let Γ := [treeTy, list treeTy, list treeTy, list treeTy]
    let x := nodeT (Term.pair (numeral 1) (call D.children [] [pc P "Datatype.aC" []]))
    let lhs := pc P "Reader.resolve" [v 2, v 3, fieldStep P x (v 0),
      consT treeTy (fieldsName P) (v 1)]
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let unfold := resolveRules P T ix E ++ ["Datatype.sHeadOf", "Datatype.sTailOf"].map
      fun nm ↦ Internal.NormRule.delta (P.idx nm)
    let rs := K.rules [] ++ unfold
    let (r, _) ← evalRw K.G K.E rs .full Γ [] lhs
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := linkK K "stepResC: the sides" (fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "stepResC: not proved" fun _ ↦ none
    pure (a, d))

/-- The tests that the atoms of the erasure's bindings are abbreviated, at the numeral
abbreviations of index {lit}`nums`. -/
def atomTests (P : Prog) (nums : Term) : List Term :=
  (walkAtoms P).map fun a ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [a, nums]]

/-- The stage functions' equations at the erasure's builders of bindings: the expansion of the
numeral abbreviations at a binding, its keyword not abbreviated, the binding of the parts'
expansions, and at the closed builders, their atoms not abbreviated, the builder itself, folded; the
reader's resolution at a binding, the reader's case of bindings at the parts' resolutions; at the
head of the children remaining, the scope's head their name, and at their tail, the scope's second
their name and its head another, the kernel's terms; the reader's types of the annotations. -/
def bindEqs (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  let en (nums t : Term) : Term := pc P "Reader.expandNums" [nums, t]
  let sLet (x a e b : Term) : Term := pc P "Datatype.sLet" [x, a, e, b]
  let aC := pc P "Datatype.aC" []
  let step3 : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun _ _ _ ↦ [.delta (T.argIdx 3)]
  let res : Prog → (String → ℕ) → Array Internal.Entry → List Internal.NormRule :=
    fun P ix E ↦ resolveRules P T ix E
  let aT := pc P "Datatype.aT" []
  let closed := [("aT", aT), ("aC", aC), ("listT", pc P "Datatype.sList" [aT]),
    ("head", pc P "Datatype.sHeadOf" [aC]), ("tail", pc P "Datatype.sTailOf" [aC])]
  -- context of a binding: the body v0, the term v1, the annotation v2, the binder v3, then the
  -- numeral abbreviations v4, or the scope v4, the type abbreviations v5 and the names v6
  let get (t : Term) : Term := pc P "Prelude.get" [t]
  let both (a b : Term) : Term := pc P "Reader.both" [a, b]
  -- the reader's case of a binding: the binder an atom, the annotation's type, the body's
  -- resolution in the scope extended by the binder's name and the term's present, the application
  -- of the abstraction of the body to the term
  let letCaseT : Term :=
    let (x, a, e, b, sc, tys, names) := (v 3, v 2, v 1, v 0, v 4, v 5, v 6)
    let rA := pc P "Reader.readType" [tys, a]
    let rB := pc P "Reader.resolve" [tys, names, b,
      consT treeTy (pc P "Reader.nameOf" [x]) sc]
    let rE := pc P "Reader.resolve" [tys, names, e, sc]
    condT treeTy (call D.lab [] [pc P "Reader.isAtom" [x]])
      (condT treeTy (call D.lab [] [both rA (both rB rE)])
        (pc P "Prelude.some" [pc P "Reader.app" [pc P "Reader.node2"
          [leafT (numeral Kernel.Label.lam), get rA, get rB], get rE]])
        (pc P "Prelude.none" []))
      (pc P "Prelude.none" [])
  [builderEq "letNums" P S [treeTy, treeTy, treeTy, treeTy, list treeTy]
      [pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev" [pc P "Reader.kwLet" [], v 4]]]
      (en (v 4) (sLet (v 3) (v 2) (v 1) (v 0))) step3
      (sLet (en (v 4) (v 3)) (en (v 4) (v 2)) (en (v 4) (v 1)) (en (v 4) (v 0)))] ++
  closed.map (fun (nm, c) ↦ builderEq s!"{nm}Nums" P S [list treeTy] (atomTests P (v 0))
    (en (v 0) c) step3 c) ++
  [builderEq "letRes" P S [treeTy, treeTy, treeTy, treeTy, list treeTy, list treeTy,
      list treeTy] []
      (pc P "Reader.resolve" [v 5, v 6, sLet (v 3) (v 2) (v 1) (v 0), v 4]) res letCaseT,
    -- the scope's tail v0, the type abbreviations v1, the names v2
    builderEq "headRes" P S [list treeTy, list treeTy, list treeTy] []
      (pc P "Reader.resolve" [v 1, v 2, pc P "Datatype.sHeadOf" [aC],
        consT treeTy (fieldsName P) (v 0)]) res,
    -- the scope's tail v0, its head's characters v1, the type abbreviations v2, the names v3
    builderEq "tailRes" P S [list treeTy, list treeTy, list treeTy, list treeTy]
      [namedFields P (v 1)]
      (pc P "Reader.resolve" [v 2, v 3, pc P "Datatype.sTailOf" [aC],
        consT treeTy (nodeT (Term.pair (numeral 0) (v 1)))
          (consT treeTy (fieldsName P) (v 0))]) res] ++
  []

/-- The lookup of a list of trees at a successor index is the rest's at the index, its sides as
written ({lit}`nthConsSucc` states them in normal form): an instance at a numeral normalizes,
without itself, to the lookup as the numeral's normal form leaves it. Proved by normalization, with
the rules of {lit}`nthConsSucc`'s proof. -/
def nthSuccRaw (P : Prog) : Step :=
  ("nthSuccRaw", fun ix E ↦ do
    let rs := [.thm (ix "rAddOne") [], .thm (ix "rCmpSucc") [],
      .thm (ix "rIterSucc") [list treeTy]] ++ vRules P ix
    let Γ := [bitsTy, list treeTy, treeTy]
    let l := pc P "Prelude.nth" [consT treeTy (v 2) (v 1), leafT (call D.succ [] [v 0])]
    let r := pc P "Prelude.nth" [v 1, leafT (v 0)]
    let some d := byMode .full P.G E 0 rs Γ [] l r
      | dbgTrace "nthSuccRaw: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The element of index 1 of a list of trees of {lit}`depth` elements before a rest, at least two:
in the context of the rest and the second element, the normal form of the lookup, in which the
other elements no longer occur, is the second element present. Proved by the lookup's equation at
a successor as written ({name}`nthSuccRaw`) at the index's predecessor, the empty bitstring. -/
def nthOne (P : Prog) (S : Defs) (depth : ℕ) : Step :=
  (s!"nthOne{depth}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Γ := [list treeTy, treeTy]
    let filler := leafT bnilT
    -- the elements after the second, fillers, before the rest
    let tail := (List.range (depth - 2)).foldr (fun _ t ↦ consT treeTy filler t) (v 0)
    let xs := consT treeTy (v 1) tail
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ []
      (pc P "Prelude.nth" [consT treeTy filler xs, leafT (numeral 1)])
    let (r, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (pc P "Prelude.some" [v 1])
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := K.cutThm "nthSuccRaw" (fun _ ↦ [bnilT, xs, filler]) (normLastK K K.byNorm)
        a.ctx a.hyps a.concl
      | dbgTrace s!"nthOne{depth}: not proved" fun _ ↦ none
    pure (a, d))

/-- The element of index 3 of a list of trees of {lit}`depth` elements before a rest, at least
four: in the context of the rest and the fourth element, the normal form of the lookup, in which
the other elements no longer occur, is the fourth element present. Proved by the lookup's equation
at a successor as written ({name}`nthSuccRaw`) at the index 2, then the lookup at that index of the
list's rest. -/
def nthThree (P : Prog) (S : Defs) (depth : ℕ) : Step :=
  (s!"nthThree{depth}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, [s!"nthTwo{depth - 1}"]⟩
    let Γ := [list treeTy, treeTy]
    let filler := leafT bnilT
    let tail := (List.range (depth - 4)).foldr (fun _ t ↦ consT treeTy filler t) (v 0)
    let xs := consT treeTy filler (consT treeTy filler (consT treeTy (v 1) tail))
    let (l, _) ← evalRw K.G K.E (K.rules []) .full Γ []
      (pc P "Prelude.nth" [consT treeTy filler xs, leafT (numeral 3)])
    let (r, _) ← evalRw K.G K.E (K.rules []) .full Γ [] (pc P "Prelude.some" [v 1])
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := K.cutThm "nthSuccRaw" (fun _ ↦ [numeral 2, xs, filler])
        (normLastK K K.byNorm) a.ctx a.hyps a.concl
      | dbgTrace s!"nthThree{depth}: not proved" fun _ ↦ none
    pure (a, d))

/-- The elements of a list's term built by its constructors, or nothing. -/
def listElemsT (t : Term) : Option (List Term) :=
  RoseTree.para (fun l (cs : List (Term × Option (List Term))) ↦ match l, cs with
    | .arr 0 _, _ => some []
    | .pair, [_, (_, r)] => r
    | .arr 1 _, [(p, r)] => match p.children with
      | [h, _] => r.map (h :: ·)
      | _ => none
    | _, _ => none) t

/-- The children of a tree's term built by its constructors, or nothing. -/
def nodeKidsT (t : Term) : Option (List Term) :=
  match t.label, t.children with
  | .arr 2 _, [p] => match p.children with
    | [_, cs] => listElemsT cs
    | _ => none
  | _, _ => none

/-- The typing's binding of a clause's variable at a type present, where the variable is a
clause's ({lit}`Typing.clauseVar`), extends the scope by the variable's entry: in the context of
the scope's continuation, the optional type, the variable and the typing environment. Proved by
deciding the type's presence and the variable's test, either false refuting its hypothesis, then
by normalization with the binding unfolded. -/
def bindVarEq (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("bindVarEq", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let o := P.o
    let Γ := [exp treeTy treeTy, treeTy, treeTy, T.envTy]
    let (k, ty, x, env) := (v 0, v 1, v 2, v 3)
    let isSome := pc P "Prelude.isSome" [ty]
    let isVar := pc P "Typing.clauseVar" [env, x]
    let a : Internal.Thm := ⟨0, Γ, [truth o isSome, truth o isVar],
      Term.eq (pc P "Typing.bindVar" [env, x, ty, k])
        (Term.app k (pc P "Typing.abbr" [pc P "Typing.atomName" [x], pc P "Prelude.get" [ty]]))⟩
    let refute (h : ℕ) (msg : String) : Deducer :=
      linkK K s!"bindVarEq: {msg}" (K.hypFalse h)
    let sides : Deducer := fun Γ Φ ψ ↦
      let rs := K.rules Φ ++ [.delta (P.idx "Typing.bindVar")]
      dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 rs Γ (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ
    -- the tests at the statement's variables, counted from the context's outer end
    let tyAt := atPos 2
    let isVarAt (Γ : List Tree) : Term := pc P "Typing.clauseVar" [atPos 0 Γ, atPos 1 Γ]
    let some d := decideIn K (fun Γ ↦ pc P "Prelude.isSome" [tyAt Γ])
        (refute 0 "the type absent") (decideIn K isVarAt (refute 1 "not a clause's variable")
          (linkK K "bindVarEq: the sides" sides))
        a.ctx a.hyps a.concl
      | dbgTrace "bindVarEq: not proved" fun _ ↦ none
    pure (a, d))

/-- The rebuilding of a list of elements of type {lit}`a` by the library's case analysis of lists at
the result type {lit}`B`, the first component of the fold whose second is the case's value, is the
list, whatever the pair of cases: in the context of the list and the pair. The fold's steps are
read off the case analysis's normal form; proved by induction on the list. -/
def lcaseRebuild (P : Prog) (S : Defs) (name : String) (a : Tree) (B : Tree := treeTy) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let Γ₀ := [list a, B, exp a (exp (list a) B)]
    let (tN, _) ← evalRw K.G K.E (K.rules []) .full Γ₀ []
      (apps (lcaseT a B) [v 0, v 1, v 2])
    let [p] := tN.children | none
    let [lr, _] := p.children | none
    let [N, C, _] := lr.children | none
    let .lam A := N.label | none
    let Γ := [list a, A]
    let l := Term.fst (Term.app (Term.listRec N C (v 0)) (v 1))
    let some d := Internal.byListIndHyp K.G K.E 0 0 1 (K.rules []) 4096 Γ [] l (v 0)
      | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l (v 0)⟩, d))

/-- The equations evaluating the kernel's case analysis of lists and the lookup of an
environment's element of index 1. -/
def evalMore : List String := apNames "apLcase" 3 ++ ["spFst", "nthOne2", "nthOne3"]

/-- The kernel's term of a binding's value resolved, the child of the present resolution on the
right side of the equation {lit}`name`. -/
def boundTerm (E : Array Internal.Entry) (ix : String → ℕ) (name : String) : Option Term := do
  let some (Internal.Entry.language b) := E[ix name]? | none
  let (_, r) ← Internal.eqParts b.concl
  let [k] ← nodeKidsT r | none
  pure k

/-- The list value of the trees' type over a list of values. -/
def treeList (P : Prog) (xs : Term) : Term :=
  pc P "Eval.ofList" [leafT (numeral Kernel.Label.tyTree), xs]

/-- The kernel's term of the head of the children remaining ({lit}`headRes`), in an environment
whose first value is the list value of a construction of a tree's quotation and a rest, converges
to the quotation. In the context of the environment's rest, the list's rest, the tree and the
relation's context. Proved at the level 5, the evaluation by the case analysis's and the lookup's
equations ({name}`evalMore`). -/
def headConv (P : Prog) (S : Defs) : Step :=
  ("headConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let hK ← boundTerm E ix "headRes"
    let Γ := [list treeTy, list treeTy, treeTy, Defs3.ctxTy]
    let env := consT treeTy (treeList P (consT treeTy (pc P "Eval.valQuote" [v 2]) (v 1))) (v 0)
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 4)) (v 0)
      (sh 1 env) hK)) (Term.lam treeTy (Term.eq (v 0) (pc P "Eval.valQuote" [v 3])))⟩
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let some d := dConv K.L K.G K.E S lv (pc P "Eval.valQuote" [v 2])
        (linkK K "headConv stable" K.byNorm) (linkK K "headConv value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace "headConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's term of the tail of the children remaining ({lit}`tailRes`), in an environment of
a value before the list value of a construction of a tree's quotation and a rest, converges to the
rest's list value. In the context of the value, the environment's rest, the list's rest, the tree
and the relation's context. Proved at the level 5, as {name}`headConv`. -/
def tailConv (P : Prog) (S : Defs) : Step :=
  ("tailConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let tK ← boundTerm E ix "tailRes"
    let Γ := [treeTy, list treeTy, list treeTy, treeTy, Defs3.ctxTy]
    let env := consT treeTy (v 0) (consT treeTy
      (treeList P (consT treeTy (pc P "Eval.valQuote" [v 3]) (v 2))) (v 1))
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 5)) (v 0)
      (sh 1 env) tK)) (Term.lam treeTy (Term.eq (v 0) (treeList P (v 3))))⟩
    let lv : Term := (5 : ℕ).rec zeroN fun _ t ↦ succN t
    let some d := dConv K.L K.G K.E S lv (treeList P (v 2))
        (linkK K "tailConv stable" K.byNorm) (linkK K "tailConv value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace "tailConv: not proved" fun _ ↦ none
    pure (a, d))

/-- The arguments of an application spine, in order. -/
def spineArgs (t : Term) : List Term :=
  RoseTree.para (fun l (cs : List (Term × List Term)) ↦ match l, cs with
    | .app, [(_, rf), (x, _)] => rf ++ [x]
    | _, _ => []) t

/-- The arguments of the first application of a definition to three arguments within a term,
outermost first, or nothing. -/
def apps3Of (j : ℕ) (t : Term) : Option (Term × Term × Term) :=
  RoseTree.para (fun l (cs : List (Term × Option (Term × Term × Term))) ↦
    match cs.findSome? (·.2) with
    | some r => some r
    | none => match l, cs.map Prod.fst with
      | .app, [f, z] => match f.label, f.children with
        | .app, [g, y] => match g.label, g.children with
          | .app, [h, x] => match h.label with
            | .defn k _ => if k == j then some (x, y, z) else none
            | _ => none
          | _, _ => none
        | _, _ => none
      | _, _ => none) t

/-- The quotations of a list of trees, each of whose memberships the test of a field's type holds
of ({lit}`Typing.fieldOk`), are related at the field's type ({lit}`Typing.fieldTy`), present, the
relation's markers the typing environment's: in the context of the list, for all field types'
forms, typing environments and relation's contexts. By induction on the list, at a construction
the head's test decided, false refuting the hypothesis, true the head's quotation related by
{name}`fieldRel` and the rest's by the induction hypothesis. -/
def quotesFieldRel (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("quotesFieldRel", fun ix E ↦ do
    let P' := { P with folded := P.folded ++ fieldFolded }
    let K : Kit := ⟨P', S, E, ix, []⟩
    let L := K.L
    let o := P.o
    let all (A : Tree) (t : Term) : Term := Internal.Logic.all o A (Term.lam A t)
    let imp := Internal.Logic.imp o
    -- under the quantifiers: the relation's context v0, the environment v1, the field type's form
    -- v2, the list v3
    let ms := pc P "Typing.envMs" [v 1]
    let mem := Term.lam treeTy (pc P "Typing.memberships" [sh 1 ms, v 0])
    -- each child's memberships a list of trees
    let okT := Term.lam (list treeTy) (Term.lam treeTy (pc P "Prelude.and"
      [pc P "Typing.fieldOk" [sh 2 ms, v 4, v 1], v 0]))
    let oks := foldrT (list treeTy) treeTy okT (leafT (numeral 1)) (mapListsT mem (v 3))
    let ty := pc P "Typing.fieldTy" [v 1, v 2]
    let φ := all treeTy <| all T.envTy <| all Defs3.ctxTy <|
      imp (Term.eq (Term.snd (v 0)) ms) <| imp (truth o (pc P "Prelude.isSome" [ty])) <|
      imp (truth o oks) <| S.allL (T.relT (v 0) (pc P "Prelude.get" [ty])) (quotesT P (v 3))
    let intros (k : Deducer) : Deducer :=
      dAllI L <| dAllI L <| dAllI L <| dImpI L <| dImpI L <| dImpI L k
    let d₀ ← linkK K "quotesFieldRel: empty" (intros (K.solve 3)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: context the rest, the head, then the quantified field type, environment
    -- and relation's context; hypotheses the induction hypothesis, the markers, the type's
    -- presence and the tests
    let cons : Deducer := intros fun Γ₁ Φ₁ ψ₁ ↦
      let pos (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + k)
      let (R, Ev, raw, t) := (pos 0, pos 1, pos 2, pos 4)
      -- the markers' hypothesis rewrites their premises to reflexive equations
      let (hS, hOk) := (Φ₁.length - 2, Φ₁.length - 1)
      let msΓ (Γ : List Tree) : Term := pc P "Typing.envMs" [Ev Γ]
      (decideIn K (fun Γ ↦ pc P "Typing.fieldOk" [msΓ Γ, raw Γ,
          pc P "Typing.memberships" [msΓ Γ, t Γ]])
        (linkK K "quotesFieldRel: the head's test" (K.hypFalse hOk)) <|
      K.norm <| dConjI L
        (linkK K "quotesFieldRel: the head" <|
          applyThm K "fieldRel" (fun Γ ↦ [t Γ, raw Γ, Ev Γ, R Γ])
            [K.byNorm, K.byHyp hS, K.solve 3] fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)
        (linkK K "quotesFieldRel: the rest" fun Γ Φ ψ ↦
          dAllE L K.G K.E 0 (raw Γ) (K.allEΓ Ev <| K.allEΓ R <| K.impE K.byNorm <|
            K.impE (K.byHyp hS) <| K.impE (K.byHyp hOk) fun Γ Φ ψ ↦
              K.byHyp (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)) Γ₁ Φ₁ ψ₁
    let d₁ ← linkK K "quotesFieldRel: a construction" cons [list treeTy, treeTy]
      [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The erasure's binding of the remaining children's variable to the children remaining. -/
def restStep (P : Prog) (x r : Term) : Term :=
  let aT := pc P "Datatype.aT" []
  let aC := pc P "Datatype.aC" []
  pc P "Datatype.sLet" [x, pc P "Datatype.sList" [aT], aC, r]

/-- The resolution of the remaining children's variable's binding of an atom's name, in the scope
headed by the children remaining's name: in the context of the rest, the binder's characters, the
scope's tail, the type abbreviations and the definitions' names, its left side in the normal form
of the walk's rules, the binding at the resolution folded, its right side the normal form with the
reader's case of bindings and steps unfolded, the rest's resolution, in the scope extended by the
binder's name, folded. Proved by normalization. -/
def restVarRes (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("restVarRes", fun ix E ↦ do
    let P := walkProg P
    let K : Kit := ⟨P, S, E, ix, walkMore ix E⟩
    let Γ := [treeTy, list treeTy, list treeTy, list treeTy, list treeTy]
    let x := nodeT (Term.pair (numeral 1) (v 1))
    let lhs := pc P "Reader.resolve" [v 3, v 4, restStep P x (v 0),
      consT treeTy (fieldsName P) (v 2)]
    let Kw : Kit := { K with more := walkRules ix E }
    let (l, _) ← evalRw Kw.G Kw.E (Kw.rules []) .full Γ [] lhs
    let unfold := resolveRules P T ix E
    let (r, _) ← evalRw K.G K.E (K.rules [] ++ unfold) .full Γ [] lhs
    let a : Internal.Thm := ⟨0, Γ, [], Term.eq l r⟩
    let some d := linkK K "restVarRes: the sides" (fun Γ Φ ψ ↦
        dEq (fun Γ Φ t u ↦ byMode .full K.G K.E 0 (K.rules Φ ++ unfold) Γ
          (rwHyps (K.rules Φ) Φ) t u) Γ Φ ψ) a.ctx a.hyps a.concl
      | dbgTrace "restVarRes: not proved" fun _ ↦ none
    pure (a, d))

/-- The kernel's variable of index 0 converges to the environment's first value: in the context of
the environment's rest, the value and the relation's context. Proved at the level 2. -/
def var0Conv (P : Prog) (S : Defs) : Step :=
  ("var0Conv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, evalMore⟩
    let Γ := [list treeTy, treeTy, Defs3.ctxTy]
    let env := consT treeTy (v 1) (v 0)
    let a : Internal.Thm := ⟨0, Γ, [], S.conv (Term.lam nat (S.evN (Term.fst (v 3)) (v 0)
      (sh 1 env) var0T)) (Term.lam treeTy (Term.eq (v 0) (v 2)))⟩
    let lv : Term := succN (succN zeroN)
    let some d := dConv K.L K.G K.E S lv (v 1)
        (linkK K "var0Conv stable" K.byNorm) (linkK K "var0Conv value" (K.norm K.byNorm))
        a.ctx a.hyps a.concl
      | dbgTrace "var0Conv: not proved" fun _ ↦ none
    pure (a, d))

/-- The walk of a clause's fields sound ({name}`walkφ`), by induction on the fixed fields'
variables. With none: the field types none, else the typing's walk absent; the constructor's
remaining children's field decided. Without it: the remaining children's variables and the
children remaining none, else the typing's walk or the constructor's test failing, and the walk the
body's erasure, sound by the body's hypothesis. -/
def walk (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("walk", fun ix E ↦ do
    let P₀ := P
    -- the kernel's typing kept folded: its hypothesis is split at the kernel's terms alone
    let P := { walkProg P with folded := (walkProg P).folded ++ ["Check.typeIn"] }
    let w ← walkParts ⟨P, S, E, ix, []⟩ T
    -- the resolution at a binding kept folded, for its equation at a field's ({lit}`stepRes`)
    let K : Kit := ⟨P, S, E, ix, walkRules ix E⟩
    let L := K.L
    let φ := walkφ P S T w
    let childT ← primT Kernel.Prim.child
    -- the walk's steps unfolded
    let steps : List Internal.NormRule := ["Typing.bindRest", "Typing.bindVar"].map fun nm ↦
      .delta (P.idx nm)
    let refute (msg : String) (h : ℕ) : Deducer := linkK K s!"walk: {msg}" fun Γ Φ ψ ↦
      (K.hypFalse h Γ Φ ψ).orElse fun _ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h (dFalse L dHyp) Γ Φ ψ
    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
    -- a hypothesis with the walk's steps unfolded, the goal by it
    let byStep (h : ℕ) : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ h ++ steps) .full) h
        (dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) dHyp) Γ Φ ψ
    -- the hypotheses after the introductions, each quantifier adding the truth of its variable,
    -- after the induction hypothesis where it is the first: the markers, the keywords, the
    -- body's soundness, the walk's typing, the constructor's test, the environment's relation,
    -- the context's names, the resolution and the kernel's typing
    let (hTy, hOk, hEnv, hCx, hRes, hKer) := (10, 11, 12, 13, 14, 15)
    -- the closed builders' expansions, cut in after the atoms' decisions, each its equation in
    -- the normal form of the rules
    let negated₀ : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
    let closedEqs (k : Deducer) : Deducer :=
      ["aTNums", "aCNums", "listTNums", "headNums", "tailNums"].foldr (fun nm k ↦
        applyThm K nm (fun Γ ↦ [atPos 2 Γ]) ((walkAtoms P).map fun _ ↦ negated₀) <|
          normLastK K k) k
    let intros (o : ℕ) (k : Deducer) (plain : Bool := true) : Deducer :=
      dImpI L <| dImpI L <| dImpI L <| dImpI L <| dImpI L <|
        (List.range 5).foldr (fun _ k ↦ dAllI L k) <| (List.range 6).foldr (fun _ k ↦ dImpI L k) <|
        if plain then plainAtoms K T (walkAtoms P) (atPos 2) (1 + o) (closedEqs k) else k
    -- the empty walk: in the context after the quantifiers, the relation's context at position
    -- 0 to the body's erasure at 9, then the field types, the children, the environment, the
    -- named context and the kernel's context
    let nilCase : Deducer := intros 0 fun Γ₀ Φ₀ ψ₀ ↦
      let c := atPos 6
      let (fts, ts, rvs) := (atPos 10, atPos 11, atPos 7)
      let cx (Γ : List Tree) : Term := consT treeTy (fieldsEntry P) (atPos 13 Γ)
      let env (Γ : List Tree) : Term := consT treeTy (pc P "Eval.ofList"
        [leafT (numeral Kernel.Label.tyTree), quotesT P (ts Γ)]) (atPos 12 Γ)
      let kc (Γ : List Tree) : Term := consT treeTy (listTK P (atPos 3 Γ)) (atPos 14 Γ)
      -- the body's hypothesis at the walk's contexts
      let body : Deducer := linkK K "walk: the body" <|
        dAllE L K.G K.E 4 (cx Γ₀) <| K.allEΓ env <| K.allEΓ kc <|
        K.impE (K.byHyp hEnv) <| K.impE (byStep hTy) <| K.impE (K.byHyp hRes) <|
        K.impE (K.byHyp hKer) <| K.impE (K.byHyp hCx) <| fun Γ Φ ψ ↦
          dRwBy (evalRw K.G K.E (K.rules Φ ++ steps) .full) byLast Γ Φ ψ
      let noRest : Deducer := fun Γ Φ ψ ↦ K.listCase treeTy (rvs Γ)
        (fun Γ Φ ψ ↦ K.listCase treeTy (ts Γ) body (refute "children remaining" hOk) Γ Φ ψ)
        (refute "a remaining variable" hTy) Γ Φ ψ
      -- the remaining children's variable, of position pR: the binding of it to the children
      -- remaining at the list of the raw field type's type around the body
      let E' := atPos 5
      let raw (Γ : List Tree) : Term := apps childT [c Γ, leafT (numeral 3)]
      let nums := atPos 2
      let cx0 := atPos 13
      let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
      let aC := pc P "Datatype.aC" []
      let aT := pc P "Datatype.aT" []
      let restVar (pR : ℕ) : Deducer :=
        let r := atPos pR
        let bodyEx (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ, atPos 9 Γ]
        -- the binding at the binder's expansion, an atom of the characters csB
        let restFlow (csB : List Tree → Term) : Deducer :=
          let bodyRes (Γ : List Tree) : Term := pc P "Reader.resolve" [atPos 3 Γ, atPos 1 Γ,
            bodyEx Γ, consT treeTy (nodeT (Term.pair (numeral 0) (csB Γ)))
              (consT treeTy (fieldsName P) (scopeOf P (nums Γ) (cx0 Γ)))]
          -- the walk's steps at the remaining variable: the binding of the remaining variables
          -- unfolded, the variable's at the top
          let unfoldRest : List Internal.NormRule := [.delta (P.idx "Typing.bindRest")]
          let presentTy : Deducer := fun Γ Φ ψ ↦
            let iTy := Φ.length - 1
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ hRes) .full) hRes (fun Γ₀ Φ ψ ↦ do
              let (g, kc, x) ← apps3Of (P.idx "Check.typeIn") (← Φ[hKer]?)
              let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ x
              let [f, e] ← nodeKidsT y | none
              let [B, rB] ← nodeKidsT f | none
              let [Pg, F] := ψ.children | none
              let [body] := F.children | none
              let [f₁, _] := body.children | none
              let [fs, env] := f₁.children | none
              let [lvl] := fs.children | none
              let [_, dR] := lvl.children | none
              let [R] := dR.children | none
              let lower (u : Term) : Term := Term.subst u fun j ↦ v (j - 1)
              let (R, env) := (lower R, lower env)
              let w (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) u
              -- the typing's binding's arguments, its type the variable's entry's
              let hN ← Φ[iTy]?
              let some [envB, xB, tyB, kB] := (appsOf K.G (P.idx "Typing.bindVar") hN).head?.map
                  spineArgs
                | dbgTrace "walk: no binding of the remaining variable" fun _ ↦ none
              let entry (Γ : List Tree) : Term := pc P "Typing.abbr"
                [pc P "Typing.atomName" [r Γ], pc P "Prelude.get" [w tyB Γ]]
              let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
              let yv (Γ : List Tree) : Term := atPos Γ₀.length Γ
              let qY (Γ : List Tree) : Term := treeList P (quotesT P (ts Γ))
              let isQ (q : List Tree → Term) (Γ : List Tree) : Term :=
                Term.lam treeTy (Term.eq (v 0) (sh 1 (q Γ)))
              let fieldA (Γ : List Tree) : Term :=
                pc P "Prelude.get" [pc P "Typing.fieldTy" [E' Γ, raw Γ]]
              -- the children's quotations related at the raw field type's list type
              let relY : Deducer := K.cutThm "relOfListT" (fun Γ ↦ [quotesT P (ts Γ)]) <|
                K.allEΓ (fun _ ↦ leafT (numeral Kernel.Label.tyTree)) <| K.allEΓ (w R) <|
                K.allEΓ fieldA <|
                K.impE (linkK K "walk: the children's quotations related" <|
                  K.cutThm "quotesFieldRel" (fun Γ ↦ [ts Γ]) <| K.allEΓ raw <|
                  -- the markers the hypothesis of index 0 as written, which supplies no rule
                  K.allEΓ E' <| K.allEΓ (w R) <| K.impE dHyp <|
                  K.impE (linkK K "walk: the raw type present" (K.solve 3)) <|
                  K.impE (linkK K "walk: the remaining children's test" (K.byHyp hOk))
                    byLast)
                  byLast
              let envOk : Deducer := applyThm K "envTCons" (fun Γ ↦ [yv Γ, entry Γ, w env Γ,
                  cx Γ, w R Γ])
                [K.byHyp hEnv, linkK K "walk: the remaining children related" relY] byLast
              let cxOk : Deducer :=
                decideIn K (fun Γ ↦ pc P "Typing.nameOk" [E' Γ, pc P "Typing.atomName" [r Γ]])
                  (refute "the remaining variable's name not admitted" hTy) <|
                applyThm K "cxTCons" (fun Γ ↦ [pc P "Prelude.get" [w tyB Γ],
                    pc P "Typing.atomName" [r Γ], E' Γ, cx Γ])
                  [linkK K "walk: the remaining variable's name admitted" (K.solve 3),
                    K.byHyp hCx] byLast
              -- the typing's binding rewritten by its equation ({lit}`bindVarEq`)
              let bound (k : Deducer) : Deducer :=
                decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, r Γ])
                  (refute "the remaining variable at its node" hTy) <|
                applyThm K "bindVarEq" (fun Γ ↦ [w kB Γ, w tyB Γ, w xB Γ, w envB Γ])
                  [K.solve 3, K.solve 3] <| normLastK K k
              let bodyAt (iTr : ℕ) : Deducer := fun Γ Φ ψ ↦
                (dAllE L K.G K.E 4 (consT treeTy (entry Γ) (cx Γ)) <|
                K.allEΓ (fun Γ ↦ consT treeTy (yv Γ) (w env Γ)) <|
                K.allEΓ (fun Γ ↦ consT treeTy (w B Γ) (w kc Γ)) <|
                K.impE (linkK K "walk: the extended environment" envOk) <|
                K.impE (linkK K "walk: the body's typing"
                  (bound fun Γ Φ ψ ↦ K.byHyp iTy Γ Φ ψ)) <|
                K.impE (linkK K "walk: the body resolved" (K.solve 3)) <|
                K.impE (linkK K "walk: the body's kernel typing" (K.byHyp iTr)) <|
                K.impE (linkK K "walk: the extended context's names" cxOk) <|
                linkK K "walk: the body's soundness" fun Γ Φ ψ ↦
                  let iC := Φ.length - 1
                  dRwBy (evalRw K.G K.E (K.rules Φ ++ unfoldRest) .full)
                    (bound fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ iC) .full) iC
                      (dRwBy (evalRw K.G K.E (K.rules Φ) .full) dHyp) Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
              (applyThm K "letTyped" (fun _ ↦ [e, rB, B, kc, g]) [K.byHyp hKer] <| K.conjE <|
                fun Γ Φ ψ ↦
                let iTr := Φ.length - 2
                applyThm K "letConv" (fun Γ ↦ [w env Γ, w e Γ, w rB Γ, w B Γ, isQ qY Γ,
                    w Pg Γ, w R Γ])
                  [linkK K "walk: the children's value" <|
                    K.cutThm "var0Conv" (fun Γ ↦ [atPos 12 Γ, qY Γ, w R Γ]) byLast,
                    linkK K "walk: the remaining variable's binding" <| dAllI L <| dImpI L <|
                      normLastK K (bodyAt iTr)] byLast Γ Φ ψ) Γ₀ Φ ψ) Γ Φ ψ
          let present : Deducer := fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ hTy ++ unfoldRest) .full) hTy presentTy Γ Φ ψ
          applyThm K "letNums" (fun Γ ↦ [atPos 9 Γ, aC, pc P "Datatype.sList" [aT], r Γ,
            nums Γ]) [negated] <| normLastK K <|
          applyThm K "restVarRes" (fun Γ ↦ [bodyEx Γ, csB Γ, scopeOf P (nums Γ) (cx0 Γ),
            atPos 3 Γ, atPos 1 Γ]) [] <| normLastK K <|
          decideOpt K bodyRes (linkK K "walk: the body unresolved" fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ hRes) .full) hRes
                (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
            (linkK K "walk: the body resolved" present)
        -- the binder an atom of the characters of position pC, its characters fixed by its being
        -- a source form's; abbreviated, the abbreviation's value an atom's or the resolution
        -- refuted
        let atomCase (pC : ℕ) : Deducer :=
          let cs := atPos pC
          let charsFix (k : Deducer) : Deducer := fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ 3) .full) 3 (fun Γ Φ ψ ↦
              dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
                -- the head an atom, its characters fixed
                dImpE L (Φ.length - 2) (linkK K "walk: the remaining variable an atom"
                  (K.solve 3)) (fun Γ Φ ψ ↦
                let fixedHead := Φ.length - 1
                (K.cutThm "charsFixedEq" (fun Γ ↦ [cs Γ, nums Γ]) <|
                  K.impE (fun Γ Φ ψ ↦ K.byHyp fixedHead Γ Φ ψ) <| normLastK K k) Γ Φ ψ)
                Γ Φ ψ) Γ Φ ψ) Γ Φ ψ
          let abbrevOf (Γ : List Tree) : Term := pc P "Prelude.get"
            [pc P "Reader.lookupAbbrev" [nodeT (Term.pair (numeral 0) (cs Γ)), nums Γ]]
          let unresolved : Deducer :=
            applyThm K "letNums" (fun Γ ↦ [atPos 9 Γ, aC, pc P "Datatype.sList" [aT], r Γ,
              nums Γ]) [negated] <| normLastK K fun Γ Φ ψ ↦
            dRwHyp (evalRw K.G K.E (K.rulesEx Φ hRes ++ [.thm (ix "letRes") []]) .full) hRes
              (dFalse L dHyp) Γ Φ ψ
          let abbreviated : Deducer := fun Γ₄ Φ₄ ψ₄ ↦ K.treeNode (abbrevOf Γ₄) (normLastK K
              fun Γ Φ ψ ↦
            let pA := Γ.length - 1
            dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
              if bs.map Oitavem.rank == some 1 then restFlow (atPos pA)
              else linkK K s!"walk: the remaining abbreviation's label {bs.map Oitavem.rank}"
                unresolved)
              3 [] (v 1) Γ Φ ψ) Γ₄ Φ₄ ψ₄
          charsFix <| decideIn K (fun Γ ↦ pc P "Prelude.isSome"
              [pc P "Reader.lookupAbbrev" [nodeT (Term.pair (numeral 0) (cs Γ)), nums Γ]])
            (restFlow cs) (linkK K "walk: the remaining variable abbreviated" abbreviated)
        decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Typing.fieldTy" [E' Γ, raw Γ]])
          (refute "the raw field type absent" hTy) <|
        decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, r Γ])
          (refute "the remaining variable no clause's" hTy) <|
        fun Γ₃ Φ₃ ψ₃ ↦ K.treeNode (r Γ₃) (fun Γ Φ ψ ↦
          let pC := Γ.length - 1
          dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
            if bs.map Oitavem.rank == some 1 then atomCase pC
            else linkK K s!"walk: the remaining variable's label {bs.map Oitavem.rank}"
              (anyClash K))
            3 [] (v 1) Γ Φ ψ) Γ₃ Φ₃ ψ₃
      let rest : Deducer := linkK K "walk: the remaining children's variable" fun Γ Φ ψ ↦
        K.listCase treeTy (rvs Γ) (refute "no remaining variable" hTy)
          (fun Γ Φ ψ ↦ K.listCase treeTy (atPos (Γ.length - 1) Γ) (restVar (Γ.length - 2))
            (refute "a second remaining variable" hTy) Γ Φ ψ) Γ Φ ψ
      K.listCase treeTy (fts Γ₀)
        (decideIn K (fun Γ ↦ apps childT [c Γ, leafT (numeral 2)]) noRest rest)
        (refute "a field type remaining" hTy) Γ₀ Φ₀ ψ₀
    let r₀ : Option Internal.Deriv := linkK K "walk: no fields" nilCase (walkCtx T).tail []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a fixed field and the rest: in the context after the quantifiers, the relation's context at
    -- position 0 to the body's erasure at 9, the field's variable at 10 and the rest at 11, then
    -- the field types, the children, the environment, the named context and the kernel's context
    let o := 1
    let (cTy, cOk, cEnv, cCx, cRes, cKer) := (hTy + o, hOk + o, hEnv + o, hCx + o, hRes + o,
      hKer + o)
    let consBody : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let (E', vx, fts, ts) := (atPos 5, atPos 10, atPos 12, atPos 13)
      let ms (Γ : List Tree) : Term := pc P "Typing.envMs" [E' Γ]
      -- the field type ft and the rest of the field types, of positions pF and pF + 1
      let fieldCase (pF : ℕ) : Deducer := fun Γ₁ Φ₁ ψ₁ ↦
        let ft := atPos pF
        let fieldTy (Γ : List Tree) : Term := pc P "Typing.fieldTy" [E' Γ, ft Γ]
        -- the children: the first t1 and the rest, of positions pT and pT + 1
        let childCase (pT : ℕ) : Deducer := fun Γ₂ Φ₂ ψ₂ ↦
          let t1 := atPos pT
          let nums := atPos 2
          -- the walk's erasure at a list of the fixed fields' variables, in the current context
          let erAt (xs : List Tree → Term) (Γ : List Tree) : Term :=
            Term.subst w.er fun j ↦ if j = 0 then xs Γ else atPos (10 - j) Γ
          let cx0 := atPos 15
          -- a negation, its antecedent refuted by normalization
          let negated : Deducer := dImpI L fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ
          -- the variable an atom, of characters at position pC; its name not abbreviated, nor the
          -- children remaining's; the resolution rewritten by the bindings' equations
          let atomCase (pC : ℕ) : Deducer := fun Γ₃ Φ₃ ψ₃ ↦
            -- the variables' characters fixed split at the head, the head's characters'
            -- equation, by which the expansion's lookup of the binder's name reads its characters;
            -- the index of the rest's characters fixed given to k
            let charsFix (k : ℕ → Deducer) : Deducer := fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ (2 + o)) .full) (2 + o) (fun Γ Φ ψ ↦
                dConjE L (Φ.length - 1) (fun Γ Φ ψ ↦
                  let iR := Φ.length - 1
                  -- the head an atom, its characters fixed
                  dImpE L (Φ.length - 2) (linkK K "walk: the variable an atom" (K.solve 3))
                    (fun Γ Φ ψ ↦
                  let fixedHead := Φ.length - 1
                  (K.cutThm "charsFixedEq" (fun Γ ↦ [atPos pC Γ, nums Γ]) <|
                    K.impE (fun Γ Φ ψ ↦ K.byHyp fixedHead Γ Φ ψ) <| normLastK K (k iR))
                    Γ Φ ψ) Γ Φ ψ)
                  Γ Φ ψ) Γ Φ ψ
            -- the binding at the binder's expansion, an atom of the characters cs: abbreviated,
            -- the abbreviation's value
            let binderFlow (cs : List Tree → Term) : Deducer :=
              -- the resolution by the builders' equations: the expansion at the two bindings and
              -- at the closed builders, the resolution at the tail of the children remaining; the
              -- rest's resolution decided present
              let aC := pc P "Datatype.aC" []
              let aT := pc P "Datatype.aT" []
              let tail := pc P "Datatype.sTailOf" [aC]
              let inner (Γ : List Tree) : Term := pc P "Datatype.sLet"
                [aC, pc P "Datatype.sList" [aT], tail, erAt (atPos 11) Γ]
              let restRes (Γ : List Tree) : Term := pc P "Reader.resolve" [atPos 3 Γ, atPos 1 Γ,
                pc P "Reader.expandNums" [nums Γ, erAt (atPos 11) Γ],
                consT treeTy (fieldsName P) (consT treeTy (nodeT (Term.pair (numeral 0) (cs Γ)))
                  (consT treeTy (fieldsName P) (scopeOf P (nums Γ) (cx0 Γ))))]
              let restEx (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ,
                erAt (atPos 11) Γ]
              -- the rest's resolution present, the binding's resolution by its equation
              -- ({lit}`stepRes`), then the resolution's, the kernel's typing's and the goal's
              -- normal forms
              -- the rest resolved: the kernel's term of the binding in normal form, the
              -- application of an abstraction over the field's type, of the binding of the children
              -- remaining around the rest's term, to the head's term; the kernel's typing split at
              -- the two bindings ({lit}`letTyped`)
              let present (iR : ℕ) : Deducer := fun Γ Φ ψ ↦
                  dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes) .full) cRes (fun Γ₀ Φ ψ ↦ do
                    let (g, c, x) ← apps3Of (P.idx "Check.typeIn") (← Φ[cKer]?)
                    let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ x
                    let [f, hK] ← nodeKidsT y | none
                    let [A, b] ← nodeKidsT f | none
                    let [f₂, tK] ← nodeKidsT b | none
                    let [B, r] ← nodeKidsT f₂ | none
                    -- the goal's predicate, relation's context and environment, the latter two
                    -- lowered past the level's binder; a definition's arguments stored last first
                    let [Pg, F] := ψ.children | none
                    let [body] := F.children | none
                    let [f₁, _] := body.children | none
                    let [fs, env] := f₁.children | none
                    let [lvl] := fs.children | none
                    let [_, dR] := lvl.children | none
                    let [R] := dR.children | none
                    let lower (u : Term) : Term := Term.subst u fun j ↦ v (j - 1)
                    let (R, env) := (lower R, lower env)
                    -- a term of this context in a context extending it
                    let w (u : Term) (Γ : List Tree) : Term := sh (Γ.length - Γ₀.length) u
                    let ft := atPos pF
                    let fts' := atPos (pF + 1)
                    let t1 := atPos pT
                    let ts' := atPos (pT + 1)
                    let quote (u : Term) : Term := pc P "Eval.valQuote" [u]
                    let byLast : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
                    -- the field's value and the children remaining's, the variables after this
                    -- context
                    let xv (Γ : List Tree) : Term := atPos Γ₀.length Γ
                    let yv (Γ : List Tree) : Term := atPos (Γ₀.length + 1) Γ
                    let fieldA (Γ : List Tree) : Term :=
                      pc P "Prelude.get" [pc P "Typing.fieldTy" [E' Γ, ft Γ]]
                    let entryA (Γ : List Tree) : Term :=
                      pc P "Typing.abbr" [pc P "Typing.atomName" [vx Γ], fieldA Γ]
                    let cx (Γ : List Tree) : Term := consT treeTy (fieldsEntry P) (cx0 Γ)
                    -- the environment related to the named context extended by the two entries
                    let relX : Deducer := applyThm K "fieldRel" (fun Γ ↦ [t1 Γ, ft Γ, E' Γ, w R Γ])
                      [linkK K "walk: fieldRel's markers" K.byNorm,
                        linkK K "walk: fieldRel's type" (K.solve 3),
                        linkK K "walk: fieldRel's test" (K.solve 3)]
                      (linkK K "walk: fieldRel's conclusion" byLast)
                    let relY : Deducer := K.cutThm "relOfListT" (fun Γ ↦ [quotesT P (ts' Γ)]) <|
                      K.allEΓ (fun _ ↦ leafT (numeral Kernel.Label.tyTree)) <| K.allEΓ (w R) <|
                      K.allEΓ (fun _ ↦ tyTreeT) <|
                      K.impE (K.cutThm "quotesRel" (fun Γ ↦ [ts' Γ]) (K.allEΓ (w R) byLast)) byLast
                    let envOk : Deducer :=
                      applyThm K "envTCons" (fun Γ ↦ [yv Γ, fieldsEntry P,
                        consT treeTy (xv Γ) (w env Γ), consT treeTy (entryA Γ) (cx Γ), w R Γ])
                        [applyThm K "envTCons" (fun Γ ↦ [xv Γ, entryA Γ, w env Γ, cx Γ, w R Γ])
                          [K.byHyp cEnv, linkK K "walk: the field related" relX] byLast,
                        linkK K "walk: the children related" relY] byLast
                    let fieldsNm : Term := pc P "Typing.boundName" [pc P "Typing.kwFields" []]
                    -- the children's name, the implementation's, decided whether the typing
                    -- admits it as a binder's
                    let cxOk : Deducer := fun Γ Φ ψ ↦
                      let cons : Deducer :=
                      applyThm K "cxTCons" (fun Γ ↦ [pc P "Typing.tyList" [pc P "Typing.tyT" []],
                        fieldsNm, E' Γ, consT treeTy (entryA Γ) (cx Γ)])
                        [linkK K "walk: the children's name admitted" (K.solve 3),
                          -- the variable's name decided admitted, else the variable no clause's
                          decideIn K (fun Γ ↦ pc P "Typing.nameOk" [E' Γ,
                              pc P "Typing.atomName" [vx Γ]])
                            (refute "the variable's name not admitted" cTy) <|
                          applyThm K "cxTCons" (fun Γ ↦ [fieldA Γ,
                          pc P "Typing.atomName" [vx Γ], E' Γ, cx Γ])
                          [linkK K "walk: the variable's name admitted" (K.solve 3),
                            linkK K "walk: the context's names before" (K.byHyp cCx)]
                          (linkK K "walk: the variable's entry" byLast)]
                        (linkK K "walk: the children's entry" byLast)
                      decideIn K (fun Γ ↦ pc P "Typing.nameOk" [E' Γ, fieldsNm]) cons cons Γ Φ ψ
                    -- the induction hypothesis at the rest: its premises the walk's, the field
                    -- types and children remaining, the environment extended by the field's value,
                    -- the named context by the two entries and the kernel's by the field's type
                    let ih (iTr : ℕ) : Deducer :=
                      dImpE L 0 (linkK K "walk: the markers" K.byNorm) <|
                      K.impE (linkK K "walk: the keywords" (K.byHyp 2)) <|
                      K.impE (linkK K "walk: the rest's characters" (K.byHyp iR)) <|
                      K.impE (linkK K "walk: the remaining variables' characters" (K.byHyp 4)) <|
                      K.impE (linkK K "walk: the body" (K.byHyp 5)) <|
                      K.allEΓ fts' <| K.allEΓ ts' <|
                      K.allEΓ (fun Γ ↦ consT treeTy (xv Γ) (w env Γ)) <|
                      K.allEΓ (fun Γ ↦ consT treeTy (entryA Γ) (consT treeTy (fieldsEntry P)
                        (cx0 Γ))) <|
                      K.allEΓ (fun Γ ↦ consT treeTy (w A Γ) (w c Γ)) <|
                      K.impE (linkK K "walk: the rest's typing" <|
                        -- the variable's test decided again at its node
                        decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, vx Γ])
                          (refute "the field's variable at its node" cTy) fun Γ Φ ψ ↦ do
                        -- the binding of the field's variable in the walk's typing, by its
                        -- equation ({lit}`bindVarEq`) at its arguments in the typing's normal form
                        let (hN, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ (← Φ[cTy]?)
                        let some [env', x', ty', k'] := (appsOf K.G (P.idx "Typing.bindVar")
                            hN).head?.map spineArgs
                          | dbgTrace "walk: no binding" fun _ ↦ none
                        (applyThm K "bindVarEq" (fun _ ↦ [k', ty', x', env'])
                          [linkK K "walk: the field's type present" (K.solve 3),
                            linkK K "walk: a clause's variable" (K.solve 3)] <|
                          normLastK K fun Γ Φ ψ ↦ K.byHyp cTy Γ Φ ψ) Γ Φ ψ) <|
                      K.impE (linkK K "walk: the rest's test" (K.byHyp cOk)) <|
                      K.impE (linkK K "walk: the environment" envOk) <|
                      K.impE (linkK K "walk: the context's names" cxOk) <|
                      K.impE (linkK K "walk: the rest resolved" (K.solve 3)) <|
                      K.impE (linkK K "walk: the rest's kernel typing" (K.byHyp iTr)) <|
                      linkK K "walk: the rest's soundness" fun Γ Φ ψ ↦
                        -- the goal's type at the walk's binding by its equation, as the typing's
                        let iC := Φ.length - 1
                        (decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, vx Γ])
                          (refute "the field's variable at its node" cTy) fun Γ Φ ψ ↦ do
                          let (gN, _) ← evalRw K.G K.E (K.rules Φ) .full Γ Φ ψ
                          let some [env', x', ty', k'] := (appsOf K.G (P.idx "Typing.bindVar")
                              gN).head?.map spineArgs
                            | dbgTrace s!"walk: no binding in the goal" fun _ ↦ none
                          (applyThm K "bindVarEq" (fun _ ↦ [k', ty', x', env'])
                            [K.solve 3, K.solve 3] <| normLastK K fun Γ Φ ψ ↦
                            dRwHyp (evalRw K.G K.E (K.rulesEx Φ iC) .full) iC
                              (dRwBy (evalRw K.G K.E (K.rules Φ) .full) dHyp) Γ Φ ψ) Γ Φ ψ)
                          Γ Φ ψ
                    -- the bindings' convergence ({lit}`letConv`): the head's value the field's
                    -- quotation ({lit}`headConv`), the tail's the rest's list value
                    -- ({lit}`tailConv`), each its equation's variable
                    let isQ (q : List Tree → Term) (Γ : List Tree) : Term :=
                      Term.lam treeTy (Term.eq (v 0) (sh 1 (q Γ)))
                    let qX (Γ : List Tree) : Term := quote (t1 Γ)
                    let qY (Γ : List Tree) : Term := treeList P (quotesT P (ts' Γ))
                    let inner (iTr : ℕ) : Deducer := dAllI L <| dImpI L <| normLastK K <|
                      applyThm K "letConv" (fun Γ ↦ [consT treeTy (xv Γ) (w env Γ), w tK Γ, w r Γ,
                        w B Γ, isQ qY Γ, w Pg Γ, w R Γ])
                        [linkK K "walk: the tail's value" <|
                          K.cutThm "tailConv" (fun Γ ↦ [xv Γ, atPos 14 Γ, quotesT P (ts' Γ), t1 Γ,
                            w R Γ]) byLast,
                          linkK K "walk: the rest's binding" <| dAllI L <| dImpI L <| normLastK K <|
                            ih iTr] byLast
                    (applyThm K "letTyped" (fun _ ↦ [hK, b, A, c, g]) [K.byHyp cKer] <| K.conjE <|
                      fun Γ Φ ψ ↦
                      applyThm K "letTyped" (fun _ ↦ [tK, r, B, consT treeTy A c, g])
                        [K.byHyp (Φ.length - 2)] (K.conjE fun Γ Φ ψ ↦
                        let iTr := Φ.length - 2
                        applyThm K "letConv" (fun Γ ↦ [w env Γ, w hK Γ, w b Γ, w A Γ, isQ qX Γ,
                          w Pg Γ, w R Γ])
                          [linkK K "walk: the head's value" <|
                            K.cutThm "headConv" (fun Γ ↦ [atPos 14 Γ, quotesT P (ts' Γ), t1 Γ,
                              w R Γ]) byLast,
                            linkK K "walk: the field's binding" (inner iTr)] byLast Γ Φ ψ) Γ Φ ψ)
                      Γ₀ Φ ψ) Γ Φ ψ
              -- the binder the children's name: the names' equality ({lit}`equalSound`), the
              -- characters' equation read off the children of its sides, without it, by which the
              -- binder's name starts as the implementation's names do and is no clause's variable,
              -- refuting the walk's typing with its steps unfolded, the names' equality excluded,
              -- which the characters' equation would rewrite back
              let resolved : Deducer := charsFix fun iR ↦
                applyThm K "letNums" (fun Γ ↦ [inner Γ, pc P "Datatype.sHeadOf" [aC], aT, vx Γ,
                  nums Γ]) [negated] <| normLastK K <|
                applyThm K "letNums" (fun Γ ↦ [erAt (atPos 11) Γ, tail, pc P "Datatype.sList" [aT],
                  aC, nums Γ]) [negated] <| normLastK K <|
                applyThm K "stepRes" (fun Γ ↦ [restEx Γ, cs Γ, scopeOf P (nums Γ) (cx0 Γ),
                  atPos 3 Γ, atPos 1 Γ]) [negated] <| normLastK K <|
                (fun Γ Φ ψ ↦
                  (decideOpt K restRes (linkK K "walk: the rest unresolved" fun Γ Φ ψ ↦
                    dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes) .full) cRes
                      (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
                  (linkK K "walk: the rest resolved" (present iR)) : Deducer) Γ Φ ψ)
              resolved
            let cs := atPos pC
            -- the walk's typing refuted with its steps unfolded, the names' equality and its
            -- image excluded, which the characters' equation would rewrite back
            let refuteTy (iEq iIm : ℕ) : Deducer := fun Γ Φ ψ ↦
              let rs := (K.rules Φ).filter (fun
                  | .hyp j => j ≠ cTy ∧ j ≠ iEq ∧ j ≠ iIm
                  | _ => true) ++ steps
              dRwHyp (evalRw K.G K.E rs .full) cTy (dFalse L dHyp) Γ Φ ψ
            -- the binder the children's name: the names' equality ({lit}`equalSound`), the
            -- characters' equation read off the children of its sides, by which the binder's
            -- name starts as the implementation's names do and is no clause's variable
            let childrenNamed : Deducer :=
              let childrenT := (primT Kernel.Prim.children).getD Term.star
              K.cutThm "equalSound" (fun _ ↦ [fieldsName P]) <|
              K.allEΓ (fun Γ ↦ nodeT (Term.pair (numeral 0) (cs Γ))) <|
              K.impE (linkK K "walk: the names equal" (K.solve 3)) fun Γ Φ ψ ↦
                let iEq := Φ.length - 1
                K.image iEq (fun t ↦ apps childrenT [t]) (fun Γ Φ ψ ↦ do
                  -- the image's equation from the characters to the binder's, reversed
                  let iIm := Φ.length - 1
                  let (chs, _) ← Internal.eqParts (← Φ[iIm]?)
                  let rev := Term.eq (cs Γ) chs
                  let dR ← K.byNorm Γ Φ rev
                  -- the name's admission decided, the variable's test false either way
                  dCut rev dR (decideIn K (fun Γ ↦ pc P "Typing.nameOk" [E' Γ,
                    pc P "Typing.atomName" [vx Γ]]) (refuteTy iEq iIm) (refuteTy iEq iIm))
                    Γ Φ ψ) Γ Φ ψ
            -- the binder abbreviated: the abbreviation's value split; an atom's, the binding at
            -- it, its name the children's or not; any other label, the binding unresolved, the
            -- reader's case of bindings testing the binder an atom ({lit}`letRes`)
            let abbrevOf (Γ : List Tree) : Term := pc P "Prelude.get"
              [pc P "Reader.lookupAbbrev" [nodeT (Term.pair (numeral 0) (cs Γ)), nums Γ]]
            let unresolved : Deducer := charsFix fun _ ↦
              applyThm K "letNums" (fun Γ ↦ [pc P "Datatype.sLet" [pc P "Datatype.aC" [],
                  pc P "Datatype.sList" [pc P "Datatype.aT" []],
                  pc P "Datatype.sTailOf" [pc P "Datatype.aC" []], erAt (atPos 11) Γ],
                pc P "Datatype.sHeadOf" [pc P "Datatype.aC" []], pc P "Datatype.aT" [], vx Γ,
                nums Γ]) [negated] <| normLastK K fun Γ Φ ψ ↦
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes ++ [.thm (ix "letRes") []]) .full) cRes
                (dFalse L dHyp) Γ Φ ψ
            -- characters naming the children remaining, their equation with the children's
            -- name's, cut in by a derivation of its own, the names' equality and its image
            -- local to it, which the equation would rewrite back
            let charsNamed (csT : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
              let childrenT ← primT Kernel.Prim.children
              let (chs, _) ← evalRw K.G K.E (K.rules []) .full Γ []
                (call D.children [] [fieldsName P])
              let φ := Term.eq (csT Γ) chs
              let d ← (K.cutThm "equalSound" (fun _ ↦ [fieldsName P]) <|
                K.allEΓ (fun Γ ↦ nodeT (Term.pair (numeral 0) (csT Γ))) <|
                K.impE (linkK K "walk: the names equal" (K.solve 3)) fun Γ Φ ψ ↦
                  K.image (Φ.length - 1) (fun t ↦ apps childrenT [t]) K.byNorm Γ Φ ψ) Γ Φ φ
              dCut φ d k Γ Φ ψ
            -- the abbreviation the children's name: the binding resolved by its equation there
            -- ({lit}`stepResC`), the rest's resolution decided present, the kernel's term split
            -- as {lit}`present` splits it, its tail's term applied to the binder, a tree, untyped:
            -- the kernel's typing at it, unfolded, refuted
            let abbrevNamed (pA : ℕ) : Deducer :=
              let aC := pc P "Datatype.aC" []
              let aT := pc P "Datatype.aT" []
              let inner (Γ : List Tree) : Term := pc P "Datatype.sLet"
                [aC, pc P "Datatype.sList" [aT], pc P "Datatype.sTailOf" [aC], erAt (atPos 11) Γ]
              let restEx (Γ : List Tree) : Term := pc P "Reader.expandNums" [nums Γ,
                erAt (atPos 11) Γ]
              let restResC (Γ : List Tree) : Term := pc P "Reader.resolve" [atPos 3 Γ,
                atPos 1 Γ, restEx Γ, consT treeTy (fieldsName P) (consT treeTy (fieldsName P)
                  (consT treeTy (fieldsName P) (scopeOf P (nums Γ) (cx0 Γ))))]
              let Pu := walkProg P₀
              let Ku : Kit := ⟨Pu, S, E, ix, walkRules ix E⟩
              let untyped : Deducer := fun Γ Φ ψ ↦
                dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes) .full) cRes (fun Γ₀ Φ ψ ↦ do
                  let (g, c, x) ← apps3Of (P.idx "Check.typeIn") (← Φ[cKer]?)
                  let (y, _) ← evalRw K.G K.E (K.rules Φ) .full Γ₀ Φ x
                  let [f, hK] ← nodeKidsT y | none
                  let [A, b] ← nodeKidsT f | none
                  let [f₂, tK] ← nodeKidsT b | none
                  let [B, r] ← nodeKidsT f₂ | none
                  (applyThm K "letTyped" (fun _ ↦ [hK, b, A, c, g])
                    [linkK K "walk: the binder's binding typed" (K.byHyp cKer)] <| K.conjE <|
                    fun Γ Φ ψ ↦
                    (applyThm K "letTyped" (fun _ ↦ [tK, r, B, consT treeTy A c, g])
                      [K.byHyp (Φ.length - 2)] <| K.conjE <|
                    linkK K "walk: the tail's term at the binder typed" fun Γ Φ ψ ↦
                      dRwHyp (evalRw Ku.G Ku.E (Ku.rulesEx Φ (Φ.length - 1)) .full)
                        (Φ.length - 1) (dFalse L dHyp) Γ Φ ψ) Γ Φ ψ) Γ₀ Φ ψ) Γ Φ ψ
              charsNamed (atPos pA) <| charsFix fun _ ↦
              applyThm K "letNums" (fun Γ ↦ [inner Γ, pc P "Datatype.sHeadOf" [aC], aT, vx Γ,
                nums Γ]) [negated] <| normLastK K <|
              applyThm K "letNums" (fun Γ ↦ [erAt (atPos 11) Γ, pc P "Datatype.sTailOf" [aC],
                pc P "Datatype.sList" [aT], aC, nums Γ]) [negated] <| normLastK K <|
              applyThm K "stepResC" (fun Γ ↦ [restEx Γ, scopeOf P (nums Γ) (cx0 Γ), atPos 3 Γ,
                atPos 1 Γ]) [] <| normLastK K <|
              decideOpt K restResC (linkK K "walk: the rest at the binder unresolved"
                  fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ cRes) .full) cRes
                    (fun Γ Φ ψ ↦ K.hypFalse (Φ.length - 1) Γ Φ ψ) Γ Φ ψ)
                (linkK K "walk: the binder's kernel typing" untyped)
            let abbreviated : Deducer := fun Γ₄ Φ₄ ψ₄ ↦ K.treeNode (abbrevOf Γ₄) (normLastK K
                fun Γ Φ ψ ↦
              let pA := Γ.length - 1
              dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
                if bs.map Oitavem.rank == some 1 then
                  decideIn K (fun Γ ↦ namedFields P (atPos pA Γ)) (binderFlow (atPos pA))
                    (linkK K "walk: the abbreviation the children's name" (abbrevNamed pA))
                else linkK K s!"walk: the abbreviation's label {bs.map Oitavem.rank}" unresolved)
                3 [] (v 1) Γ Φ ψ) Γ₄ Φ₄ ψ₄
            (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [pc P "Reader.lookupAbbrev"
                [nodeT (Term.pair (numeral 0) (cs Γ)), nums Γ]])
              (decideIn K (fun Γ ↦ namedFields P (cs Γ)) (binderFlow cs)
                (linkK K "walk: the binder the children's name" childrenNamed))
              (linkK K "walk: the binder abbreviated" abbreviated)) Γ₃ Φ₃ ψ₃
          let byLabel : Deducer := fun Γ₃ Φ₃ ψ₃ ↦ K.treeNode (vx Γ₃) (fun Γ Φ ψ ↦
            let pC := Γ.length - 1
            dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
              if bs.map Oitavem.rank == some 1 then atomCase pC
              else linkK K s!"walk: the variable's label {bs.map Oitavem.rank}" (anyClash K))
              3 [] (v 1) Γ Φ ψ) Γ₃ Φ₃ ψ₃
          (decideIn K (fun Γ ↦ pc P "Typing.fieldOk" [ms Γ, ft Γ,
              pc P "Typing.memberships" [ms Γ, t1 Γ]])
            (refute "the field's test" cOk) byLabel) Γ₂ Φ₂ ψ₂
        (decideIn K (fun Γ ↦ pc P "Prelude.isSome" [fieldTy Γ])
          (refute "the field's type absent" cTy) <|
        decideIn K (fun Γ ↦ pc P "Typing.clauseVar" [E' Γ, vx Γ])
          (refute "the field's variable" cTy) <| fun Γ Φ ψ ↦
        K.listCase treeTy (ts Γ) (refute "no child for the field" cOk)
          (fun Γ Φ ψ ↦ childCase (Γ.length - 2) Γ Φ ψ) Γ Φ ψ) Γ₁ Φ₁ ψ₁
      K.listCase treeTy (fts Γ₀) (refute "no field type for the variable" cTy)
        (fun Γ Φ ψ ↦ fieldCase (Γ.length - 2) Γ Φ ψ) Γ₀ Φ₀ ψ₀
    let consCase : Deducer := intros o consBody
    let r₁ : Option Internal.Deriv := linkK K "walk: a field" consCase
        (list treeTy :: treeTy :: (walkCtx T).tail) [Internal.weakenElem φ]
        (Internal.listConsAt 1 treeTy φ)
    let consProved := r₁.isSome
    let some d₀ := r₀
      | dbgTrace s!"walk: the empty walk not proved; the construction {consProved}" fun _ ↦ none
    let some d₁ := r₁
      | dbgTrace "walk: the construction not proved" fun _ ↦ none
    pure (⟨0, walkCtx T, [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The names the development of the soundness at case analyses is stated after: those of
{name}`decodeAfter`, the datum's, the decoding's and the constants' relations'. -/
def caseNames (P : Prog) (S : Defs) (T : Defs3) : Option (List String) := do
  let names ← decodeAfter P S T
  pure (names ++ (datumDev3 P S T).map (·.1) ++ (decodeDev3 P S T).map (·.1) ++
    (foldsDev3 P S T).map (·.1))

/-- The development of the soundness at case analyses' walks of their clauses' fields: the
constructors' tests, the bindings' equations and convergence, the lookups' and the typing's
equations, and the walk ({name}`walk`). -/
def caseDev (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [ctorsLabel P S, labelFilter P S, ctorUnique P S, covers P S, dropNil P S,
    headDropMap P S, letConv P S, fieldRel P S T, quotesRel P S T,
    letTyped P S, isSomeIndexOfCons P S, truthOfEq P S, orTrue P S true, orTrue P S false] ++
  (walkAtoms P).zipIdx.map (fun (n, i) ↦ atomExcluded P S s!"atomExcluded{i}" n) ++
  bindEqs P S T ++
  [stepRes P S, stepResC P S T, nthSuccRaw P, nthOne P S 2, nthOne P S 3, headConv P S,
    tailConv P S, bindVarEq P S T, restVarRes P S T, var0Conv P S, quotesFieldRel P S T,
    lcaseRebuild P S "lcaseRebuild" treeTy, lcaseRebuild P S "lcaseRebuildL" (list treeTy),
    walk P S T]

/-- The development of {name}`caseDev`, after the declarations of {name}`caseNames`, stored as the
certificate {lit}`datatype-case`. -/
def caseCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List Stored.Cert) := do
  let some names := caseNames P S T | throw "the base is not stated"
  certifyAfter P names "datatype-case" (caseDev P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
