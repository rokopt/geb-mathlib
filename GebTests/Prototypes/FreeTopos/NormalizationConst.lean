/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.NormalizationBase -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.NormalizationBase -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Convergence of the evaluator's folds

Lemmas of the internal language on lists of related values and on the evaluator's folds of trees,
proved after the development of the base ({lit}`baseDev`), whose declarations the certificate
{lit}`bootstrap/certificates/normalization-const.cert` stores.

A convergence is stable: from some level of fuel on, a function of the fuel has one value, which a
predicate holds of. The convergences of a function at each element of a list combine into one of
the list of the values ({lit}`allConv`), at the sum of the thresholds, and the list value of
values each related at a type is related at the list type ({lit}`relOfList`). The evaluator's fold
of trees and its fold whose step sees the node, at a step related at the step's type, converge at
every tree to a value related at the result type ({lit}`foldConv`, {lit}`paraConv`), by induction
on trees, as {name}`Geb.Kernel.Eval.foldVal_rel` states of the evaluator in Lean.

The proofs rewrite by equations proved here: the application at the spine of a constant applied
to fewer arguments than it takes, the fusion of a fold with parameters over a node's children with
the application of the folds to the parameters, and the rebuilding of a tree by a fold whose values
pair the tree with the value.

## Main definitions

* {lit}`allConvLemma`, {lit}`relOfListLemma` — lists of convergences and of related values.
* {lit}`foldConvLemma` — the convergence of a fold of trees at related steps.
* {lit}`constDev` — the development.

## Implementation notes

A lemma proved by induction states its formula in a context of the induction's variable alone,
the other variables quantified within the formula, since the step of a fold is a closed term. A
universal introduction adds truth as a hypothesis, so that the indices of later hypotheses count
it.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, convergence, fold, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Normalization

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open Internal (Term NormRule Entry Deriv Decl)
open scoped FinEnum

namespace Kit

variable (K : Kit)

/-- A universal hypothesis's instance, normalized, the last hypothesis. -/
def instN (h : ℕ) (t : List Tree → Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  dAllE K.L K.G K.E h (t Γ) (fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (K.rules Φ.dropLast) .full) (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ

/-- A stability hypothesis shifted to a later threshold, the sum of its threshold and another on
its right ({lit}`stabR`) or on its left ({lit}`stabL`), cut in after the hypotheses. -/
def shift (h : ℕ) (left : Bool) (j : List Tree → Term) (k : Deducer) : Deducer :=
  fun Γ Φ ψ ↦ do
    let (F, n, w) ← stabParts K.P.o K.S.q (← Φ[h]?)
    let name := if left then "stabL" else "stabR"
    let some (Entry.language a) := K.E[K.ix name]? | none
    let σ := [j Γ, n, w, F]
    dCut (Internal.instTerm [] σ a.concl) (nd (.apply (K.ix name) [] σ) [nd (.hyp h)]) k Γ Φ ψ

/-- The last hypothesis normalized, the last hypothesis. -/
def normLast (k : Deducer) : Deducer := fun Γ Φ ψ ↦
  dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1) k Γ Φ ψ

/-- The last hypothesis, a convergence, unfolded and its threshold, value, stability and relation
added, the stability and the relation the last two hypotheses. -/
def convE (k : Deducer) : Deducer := K.unfoldConv (K.exE (K.exE (K.conjE k)))

/-- The goal found among the hypotheses, each normalized in turn, without a trace. -/
def anyHyp : Deducer := fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦
  (List.range Φ.length).findSome? fun h ↦
    dRwHyp (evalRw K.G K.E (K.rulesEx Φ h) .full) h dHyp Γ Φ ψ

/-- Truth, conjunctions, hypotheses and equations, after normalization, to a depth. -/
def auto (d : ℕ) : Deducer := d.rec (fun _ _ _ ↦ none) fun _ rec ↦ K.norm fun Γ Φ ψ ↦
  if ψ == Internal.Logic.tt K.P.o then some Internal.Logic.trueI else
  match defnParts ψ with
  | some (i, _, _) =>
    if i = K.P.o + 1 then dConjI K.L rec rec Γ Φ ψ else K.anyHyp Γ Φ ψ
  | none => (K.anyHyp Γ Φ ψ).orElse fun _ ↦ K.byNorm Γ Φ ψ

/-- A convergence proved by its threshold, its value, the stability and the relation. -/
def conv (n w : List Tree → Term) (stable related : Deducer) : Deducer := fun Γ Φ ψ ↦
  dConv K.L K.G K.E K.S (n Γ) (w Γ) stable related Γ Φ ψ

end Kit

/-- The type of trees, of lists of a type and of functions, as the checker builds them: the type
of trees the leaf of its label's numeral. -/
def tyT : Term := leafT (numeral Kernel.Label.tyTree)

/-- The type of lists of a type. -/
def tyL (P : Prog) (A : Term) : Term := pc P "Check.tyList" [A]

/-- The type of functions from a type to a type. -/
def tyA (P : Prog) (A B : Term) : Term := pc P "Check.tyArrow" [A, B]

/-- The node of label zero over a list of trees. -/
def node0 (cs : Term) : Term := nodeT (Term.pair (numeral 0) cs)

/-- Every element of a list satisfying a predicate satisfies every predicate it implies; by
induction on the list. -/
def allMonoLemma (P : Prog) (S : Defs) : Step :=
  ("allMono", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let all := Internal.Logic.all P.o
    let imp := Internal.Logic.imp P.o
    let PrTy := exp treeTy omega
    -- under the two predicates: the second v0, the first v1, the list v2
    let φ := all PrTy (Term.lam PrTy (all PrTy (Term.lam PrTy (imp (S.allL (v 1) (v 2))
      (imp (all treeTy (Term.lam treeTy (imp (Term.app (v 2) (v 0)) (Term.app (v 1) (v 0)))))
        (S.allL (v 0) (v 2)))))))
    let d₀ ← dAllI L (dAllI L (dImpI L (dImpI L (K.solve 2)))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: the head's by the implication, the rest's by the induction hypothesis
    let cons : Deducer := dAllI L (dAllI L (dImpI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let hA := Φ₁.length - 2
      let hM := Φ₁.length - 1
      let Pr (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 1)
      let Q (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      let head (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 3)
      let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₁ hA) .full) hA (K.conjE fun Γ Φ ψ ↦
        let hPc := Φ.length - 2
        let hPr := Φ.length - 1
        K.norm (dConjI L
          (dAllE L K.G K.E hM (head Γ) (K.impE (K.byHyp hPc) last))
          (dAllE L K.G K.E 0 (Pr Γ) (K.allEΓ Q (K.impE (K.byHyp hPr) (K.impE dHyp last)))))
          Γ Φ ψ) Γ₁ Φ₁ ψ₁)))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The hypothesis of induction on trees at a list of children, a formula in a context of a tree
holding at each, as every element of the list satisfying the formula; by induction on the list,
the head's formula and the rest's hypothesis read off the hypothesis's equation of lists. -/
def roseAllFor (P : Prog) (S : Defs) (name : String) (φ : Term) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let ψ := Internal.Logic.imp P.o (Internal.roseHyp 0 1 φ) (S.allL (Term.lam treeTy φ) (v 0))
    let d₀ ← dImpI L (K.solve 3) [] [] (Term.subst ψ (Internal.instVar
      (Term.arr 0 [treeTy] Term.star)))
    -- hypotheses: the induction hypothesis, the construction's, the heads' equation, the head's
    -- formula, the rests' equation; then the rest's formulas
    let cons : Deducer := dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let h := Φ₁.length - 1
      let tl : Deducer := fun Γ Φ ψ ↦
        dImpE L 0 K.byNorm (K.norm (dConjI L (K.byHyp 3) (K.byHyp 5))) Γ Φ ψ
      K.image h (fun t ↦ call D.headD [omega] [Term.eq Term.star Term.star, t])
        (K.trueOf (K.image h (fun t ↦ call D.tail [omega] [t]) tl)) Γ₁ Φ₁ ψ₁
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem ψ] (Internal.listConsAt 1 treeTy ψ)
    pure (⟨0, [list treeTy], [], ψ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Convergences of a function's values at each element of a list combined: its values at the
elements collected, by the evaluator's {lit}`allSomeT`, converge to the node of values each of
which the predicate holds of; by induction on the list. -/
def allConvLemma (P : Prog) (S : Defs) : Step :=
  ("allConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let all := Internal.Logic.all P.o
    let imp := Internal.Logic.imp P.o
    let FTy := exp nat (exp treeTy treeTy)
    let PrTy := exp treeTy omega
    -- under the function and the predicate: the predicate v0, the function v1, the list v2
    let hyp : Term := S.allL (Term.lam treeTy
      (S.conv (Term.lam nat (apps (v 3) [v 0, v 1])) (v 1))) (v 2)
    let concl : Term := S.conv
      (Term.lam nat (pc P "Eval.allSomeT" [pc P "Eval.mapT" [Term.app (v 2) (v 0), v 3]]))
      (Term.lam treeTy (S.allL (v 1) (call D.children [] [v 0])))
    let φ := all FTy (Term.lam FTy (all PrTy (Term.lam PrTy (imp hyp concl))))
    -- the empty list: the empty node at once
    let d₀ ← dAllI L (dAllI L (dImpI L (K.conv (fun _ ↦ zeroN) (fun _ ↦ node0 (nilT treeTy))
      (K.byNorm) ((K.solve 2))))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: the head's convergence and the rest's, by the induction hypothesis, both
    -- shifted to the sum of their thresholds
    let cons : Deducer := dAllI L (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      -- context past the list's head and rest: the function, the predicate
      let F (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 1)
      let Pr (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      -- the convergence at the sum, from the two stabilities shifted to it
      let fin (n₁ w₁ n₂ w₂ : List Tree → Term) (r₁ r₂ : ℕ) : Deducer := fun Γ Φ ψ ↦
        let a₁ := Φ.length - 2
        let a₂ := Φ.length - 1
        K.conv (fun Γ ↦ S.add (n₁ Γ) (n₂ Γ))
          (fun Γ ↦ node0 (consT treeTy (w₁ Γ) (call D.children [] [w₂ Γ])))
          (K.instN a₁ (fun _ ↦ v 0) (K.instN a₂ (fun _ ↦ v 0) (K.byNorm)))
          (K.norm ((dConjI L (K.byHyp r₁) (K.byHyp r₂)))) Γ Φ ψ
      -- the rest's threshold and value, by the induction hypothesis at the function and the
      -- predicate, after the head's
      let rest (Γ₃ : List Tree) (s₁ r₁ hr : ℕ) : Deducer :=
        let n₁ (Γ : List Tree) : Term := v (Γ.length - Γ₃.length + 1)
        let w₁ (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
        let after : Deducer := fun Γ₄ Φ₄ ψ₄ ↦
          let n₂ (Γ : List Tree) : Term := v (Γ.length - Γ₄.length + 1)
          let w₂ (Γ : List Tree) : Term := v (Γ.length - Γ₄.length)
          let s₂ := Φ₄.length - 2
          let r₂ := Φ₄.length - 1
          K.shift s₁ false n₂ (K.shift s₂ true n₁ (fin n₁ w₁ n₂ w₂ r₁ r₂)) Γ₄ Φ₄ ψ₄
        dAllE L K.G K.E 0 (F Γ₃) (K.allEΓ Pr (K.impE (K.byHyp hr)
          (K.unfoldConv (K.exE (K.exE (K.conjE after))))))
      -- the head's threshold and value
      let head (hc hr : ℕ) : Deducer :=
        dRwHyp (evalRw K.G K.E [.delta (S.q + 2)] .head) hc (K.exE (K.exE (K.conjE
          fun Γ₃ Φ₃ ψ₃ ↦ rest Γ₃ (Φ₃.length - 2) (Φ₃.length - 1) hr Γ₃ Φ₃ ψ₃)))
      dRwHyp (evalRw K.G K.E (K.rules Φ₁) .full) (Φ₁.length - 1) (K.conjE fun Γ₂ Φ₂ ψ₂ ↦
        head (Φ₂.length - 2) (Φ₂.length - 1) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The list value of values each related at a type is related at the list type; by induction on
the list, the rest's list value's test decided by its relation from the induction hypothesis. -/
def relOfListLemma (P : Prog) (S : Defs) : Step :=
  ("relOfList", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let all := Internal.Logic.all P.o
    let imp := Internal.Logic.imp P.o
    -- under the definitions and the type: the type v0, the definitions v1, the list v2
    let φ := all (list treeTy) (Term.lam (list treeTy) (all treeTy (Term.lam treeTy
      (imp (S.allL (S.rel (v 1) (v 0)) (v 2))
        (Term.app (S.rel (v 1) (tyL P (v 0))) (pc P "Eval.ofList" [v 0, v 2]))))))
    let d₀ ← dAllI L (dAllI L (dImpI L ((K.auto 3)))) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := dAllI L (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let A (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      let Dv (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 1)
      -- the head's relation and the rest's, then the rest's list value's by the induction
      -- hypothesis, its test and its elements' relations
      K.normLast (K.conjE fun Γ₂ Φ₂ ψ₂ ↦
        dAllE L K.G K.E 0 (Dv Γ₂) (K.allEΓ A (K.impE (K.byHyp (Φ₂.length - 1))
          (K.normLast (K.conjE fun Γ₃ Φ₃ ψ₃ ↦
            K.splitHyp (Φ₃.length - 2) ((K.auto 4)) 8 Γ₃ Φ₃ ψ₃)))) Γ₂ Φ₂ ψ₂)
        Γ₁ Φ₁ ψ₁))
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The type of the application of values to values. -/
def apTy : Tree := exp treeTy (exp treeTy treeTy)

/-- The fusion of a fold with parameters over the children with the application to the
parameters: the map of the folds applied, by induction on the children. The fold is that of the
evaluator's function {lit}`val` of an application, a result type and a step, at a tree; the map
of the applications is taken through {lit}`post` where the fold's values are pairs. -/
def fusLemma (P : Prog) (name val : String) (post : Term → Term := id) : Step :=
  (name, fun ix E ↦ do
    let rs := vRules P ix
    -- context: the tree or the children, the step, the type, the application
    let Γt := [treeTy, treeTy, treeTy, apTy]
    let Γ := [list treeTy, treeTy, treeTy, apTy]
    let (C, s, Fp) ← firstFoldApp (weakNF P (baseNorm P) 0 Γt (pc P val [v 3, v 2, v 1, v 0]))
    let θ ← defnObjs D.mapApp s
    let lhs := post (call D.mapApp θ [Term.listRec (nilT C) (consT C (Term.roseRec C s (v 1))
      (v 0)) (v 0), Fp])
    let rhs := pc P "Eval.mapT" [Term.lam treeTy (pc P val [v 4, v 3, v 2, v 0]), v 0]
    let some l := nfE P.G E rs Γ lhs | dbgTrace s!"{name}: left" fun _ ↦ none
    let some r := nfE P.G E rs Γ rhs | dbgTrace s!"{name}: right" fun _ ↦ none
    let some d := Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l r
      | dbgTrace s!"{name}: {(firstDiff l r).map fun (a, b) ↦ s!"{showT a}\n  vs {showT b}"}"
          fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l r⟩, d))

/-- The fold's formula at a tree, the variable of index 0: for all definitions, result types and
steps related at the step's type, the fold's value at the tree, by the application at each level,
converges to a value related at the result type. -/
def foldφ (P : Prog) (S : Defs) (val : String) : Term :=
  let all := Internal.Logic.all P.o
  let imp := Internal.Logic.imp P.o
  -- under the definitions, the type and the step: the step v0, the type v1, the definitions v2
  all (list treeTy) (Term.lam (list treeTy) (all treeTy (Term.lam treeTy (all treeTy
    (Term.lam treeTy (imp (Term.app (S.rel (v 2) (tyA P tyT (tyA P (tyL P (v 1)) (v 1)))) (v 0))
      (S.conv (Term.lam nat (pc P val [Term.snd (S.levelN (v 3) (v 0)), v 2, v 1, v 4]))
        (S.rel (v 2) (v 1)))))))))

/-- The fold computes at a step related to a step: by induction on trees, the children's values
converging together by {lit}`allConv`, the step's application to the node's label and then to the
list value of the children's values each converging. -/
def foldConvLemma (P : Prog) (S : Defs) (name val : String) (arg : Term → Term → Term)
    (more : List String) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, (name ++ "Fus") :: more⟩
    let φ := foldφ P S val
    let L := K.L
    let pv : List Term → Term := pc P val
    -- after the definitions, the type, the step and its relation are introduced: the context
    -- Γ₁, the step, the type, the definitions, the children and the label innermost first
    let body (Γ₁ : List Tree) (hAll hf : ℕ) : Deducer :=
      let at₁ (k d : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + k + d)
      let f := at₁ 0
      let A := at₁ 1
      let Dv := at₁ 2
      let cs := at₁ 3
      let l := at₁ 4
      -- the children's convergences at the step, and the function of the fuel and the child
      let Q (Γ : List Tree) : Term := Term.lam treeTy (S.conv (Term.lam nat (pv
        [Term.snd (S.levelN (Dv 2 Γ) (v 0)), A 2 Γ, f 2 Γ, v 1])) (S.rel (Dv 1 Γ) (A 1 Γ)))
      let F (Γ : List Tree) : Term := Term.lam nat (Term.lam treeTy (pv
        [Term.snd (S.levelN (Dv 2 Γ) (v 1)), A 2 Γ, f 2 Γ, v 0]))
      let mono : Deducer := dAllI L (dImpI L (K.normLast fun Γ Φ ψ ↦
        dAllE L K.G K.E (Φ.length - 1) (Dv 0 Γ) (K.allEΓ (A 0) (K.allEΓ (f 0)
          (K.impE (K.byHyp hf) (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)))) Γ Φ ψ))
      -- the final convergence: the thresholds' sum, the value w
      let fin (N n₁ n₂ w : List Tree → Term) (sC s₁ s₂ rw : ℕ) : Deducer :=
        K.shift sC false n₁ (fun Γ Φ ψ ↦ K.shift (Φ.length - 1) false n₂ (K.shift s₁ true N
          (fun Γ Φ ψ ↦ K.shift (Φ.length - 1) false n₂ (K.shift s₂ true
            (fun Γ ↦ S.add (N Γ) (n₁ Γ)) (fun Γ Φ ψ ↦
              let a := Φ.length
              K.conv (fun Γ ↦ S.add (S.add (N Γ) (n₁ Γ)) (n₂ Γ)) w
                (K.instN (a - 4) (fun _ ↦ v 0) (K.instN (a - 2) (fun _ ↦ v 0)
                  (K.instN (a - 1) (fun _ ↦ v 0) (K.byNorm))))
                ((K.byHyp rw)) Γ Φ ψ)) Γ Φ ψ)) Γ Φ ψ)
      -- the step's value at the label, then at the list value of the children's values
      let applied (ΓC : List Tree) (sC rC : ℕ) : Deducer :=
        let N := fun Γ ↦ v (Γ.length - ΓC.length + 1)
        let r := fun Γ ↦ v (Γ.length - ΓC.length)
        let lbl (Γ : List Tree) : Term := pc P "Eval.valQuote" [arg (l 0 Γ) (cs 0 Γ)]
        let lst (Γ : List Tree) : Term := pc P "Eval.ofList" [A 0 Γ, call D.children [] [r Γ]]
        fun Γ Φ ψ ↦ dRwHyp (evalRw K.G K.E (K.rulesEx Φ hf) .full) hf (fun Γ Φ ψ ↦
          K.allEΓ lbl (K.impE ((K.norm (dExI L K.G K.E (arg (l 0 Γ) (cs 0 Γ))
            K.byNorm))) (K.convE fun Γ₂ Φ₂ ψ₂ ↦
              let n₁ := fun Γ ↦ v (Γ.length - Γ₂.length + 1)
              let s₁ := Φ₂.length - 2
              K.normLast (K.allEΓ lst (K.impE (K.cutThm "relOfList" (fun Γ ↦ [call D.children []
                  [r Γ]]) (K.allEΓ (Dv 0) (K.allEΓ (A 0) (K.impE (K.byHyp rC)
                    (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)))))
                (K.convE fun Γ₃ Φ₃ ψ₃ ↦
                  let n₂ := fun Γ ↦ v (Γ.length - Γ₃.length + 1)
                  let w := fun Γ ↦ v (Γ.length - Γ₃.length)
                  fin N n₁ n₂ w sC s₁ (Φ₃.length - 2) (Φ₃.length - 1) Γ₃ Φ₃ ψ₃)))
              Γ₂ Φ₂ ψ₂)) Γ Φ ψ) Γ Φ ψ
      K.cutThm "allMono" (fun Γ ↦ [cs 0 Γ]) (K.allEΓ (fun _ ↦ Term.lam treeTy φ) (K.allEΓ Q
        (K.impE (K.byHyp hAll) (K.impE (mono) (fun Γ Φ ψ ↦
          let hQ := Φ.length - 1
          K.cutThm "allConv" (fun Γ ↦ [cs 0 Γ]) (K.allEΓ F (K.allEΓ (fun Γ ↦ S.rel (Dv 0 Γ)
            (A 0 Γ)) (K.impE ((K.byHyp hQ))
              (K.convE fun ΓC ΦC ψC ↦
              applied ΓC (ΦC.length - 2) (ΦC.length - 1) ΓC ΦC ψC)))) Γ Φ ψ)))))
    let node : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      -- the children the innermost variable of the node's context
      K.cutThm (name ++ "All") (fun Γ ↦ [v (Γ.length - 2)]) (K.impE dHyp (fun Γ Φ ψ ↦
        let hAll := Φ.length - 1
        dAllI L (dAllI L (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
          body Γ₁ hAll (Φ₁.length - 1) Γ₁ Φ₁ ψ₁))) Γ Φ ψ)) Γ₀ Φ₀ ψ₀
    let d ← node [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ]
      (Internal.roseNodeAt 2 treeTy bitsTy φ)
    pure (⟨0, [treeTy], [], φ⟩, nd (.roseIndHyp 2 0 1) [d]))

/-- The application's equations at a constant applied to fewer arguments than it takes, one for
each number of arguments it has been applied to, named by the tag and that number. The constant is
the head built from {lit}`ntys` type variables; the context holds the arguments, the last
innermost, the types, and the functions of the level below. -/
def apConstLemmas (P : Prog) (tag : String) (head : List Term → Term) (ntys nargs : ℕ) :
    List Step :=
  (List.range nargs).map fun j ↦
    let Γ := List.replicate (j + 1) treeTy ++ List.replicate ntys treeTy ++ [fnsTy]
    let arg (i : ℕ) : Term := v (j - i)
    let tys := (List.range ntys).map fun i ↦ v (j + 1 + i)
    let f := (List.range j).foldl (fun acc i ↦
      nodeT (Term.pair (numeral Kernel.Label.app)
        (consT treeTy acc (consT treeTy (arg i) (nilT treeTy))))) (head tys)
    genEq P s!"{tag}{j}" Γ (pc P "Eval.apStep" [v (j + 1 + ntys), f, arg j])
      [P.idx "Eval.apStep"]

/-- A constant of a label over types. -/
def constNode (lbl : ℕ) (tys : List Term) : Term :=
  nodeT (Term.pair (numeral lbl) (tys.foldr (consT treeTy) (nilT treeTy)))

/-- The names of the application's equations of a tag, for a number of arguments. -/
def apNames (tag : String) (nargs : ℕ) : List String :=
  (List.range nargs).map fun j ↦ s!"{tag}{j}"

/-- The rebuilding of a value by the fold of its spine, a fold whose value at a node pairs the
node rebuilt with the spine. -/
def spineLemmas (P : Prog) : List Step :=
  match firstFoldApp (weakNF P (baseNorm P) 0 [treeTy] (pc P "Eval.spine" [v 0])) with
  | some (CP, sP, FP) => match Internal.expParts CP with
    | some (FX, _) => rebuildLemmas P "sp" FX
        (fun x F ↦ Term.fst (Term.app (Term.roseRec CP sP x) F)) []
        (Term.app (Term.roseRec CP sP (v 0)) FP) FP none
    | none => []
  | none => []

/-- The rebuilding of a tree by the fold of the evaluator's function {lit}`val` of an
application, a result type and a step, a fold whose value at a node pairs the node rebuilt with the
value. -/
def paraRebuild (P : Prog) (tag val : String) : List Step :=
  let Γt := [treeTy, treeTy, treeTy, apTy]
  match firstFoldApp (weakNF P (baseNorm P) 0 Γt (pc P val [v 3, v 2, v 1, v 0])) with
  | some (C, s, Fp) => match Internal.expParts C with
    | some (FX, _) => rebuildLemmas P tag FX
        (fun x F ↦ Term.fst (Term.app (Term.roseRec C s x) F)) Γt.tail
        (Term.app (Term.roseRec C s (v 0)) Fp) Fp none
    | none => []
  | none => []

/-- The children rebuilt by a fold of the evaluator's function {lit}`val` whose values pair the
node rebuilt with the value: the first components of the map of the folds applied are the
children, by induction on the children with the rebuilding {lit}`fstName` of each. -/
def kidsLemma (P : Prog) (name val fstName : String) : Step :=
  (name, fun ix E ↦ do
    let rs := .thm (ix fstName) [] :: vRules P ix
    let Γt := [treeTy, treeTy, treeTy, apTy]
    let Γ := [list treeTy, treeTy, treeTy, apTy]
    let (C, s, Fp) ← firstFoldApp (weakNF P (baseNorm P) 0 Γt (pc P val [v 3, v 2, v 1, v 0]))
    let θ ← defnObjs D.mapApp s
    let lhs := Term.listRec (nilT treeTy) (consT treeTy (Term.fst (v 1)) (v 0))
      (call D.mapApp θ [Term.listRec (nilT C) (consT C (Term.roseRec C s (v 1)) (v 0)) (v 0),
        Fp])
    let some l := nfE P.G E rs Γ lhs | dbgTrace s!"{name}: left" fun _ ↦ none
    let some d := Internal.byListIndHyp P.G E 0 0 1 rs 4096 Γ [] l (v 0)
      | dbgTrace s!"{name}: {(firstDiff l (v 0)).map fun (a, b) ↦ s!"{showT a}\n  vs {showT b}"}"
          fun _ ↦ none
    pure (⟨0, Γ, [], Term.eq l (v 0)⟩, d))

/-- The constants' development: the lemmas on lists of convergences, and each constant's
relation at its type. -/
def constDev (P : Prog) (S : Defs) : List Step :=
  [allMonoLemma P S, allConvLemma P S, relOfListLemma P S] ++
  apConstLemmas P "apFold" (constNode Kernel.Label.fold) 1 2 ++
  apConstLemmas P "apPara" (constNode Kernel.Label.para) 1 2 ++ spineLemmas P ++
  [roseAllFor P S "foldConvAll" (foldφ P S "Eval.foldVal"),
    fusLemma P "foldConvFus" "Eval.foldVal",
    foldConvLemma P S "foldConv" "Eval.foldVal"
      (fun l _ ↦ nodeT (Term.pair l (nilT treeTy))) [],
    roseAllFor P S "paraConvAll" (foldφ P S "Eval.paraVal"),
    fusLemma P "paraConvFus" "Eval.paraVal" fun L ↦
      Term.listRec (nilT treeTy) (consT treeTy (Term.snd (v 1)) (v 0)) L] ++
  paraRebuild P "pv" "Eval.paraVal" ++
  [kidsLemma P "pvKids" "Eval.paraVal" "pvFst",
    foldConvLemma P S "paraConv" "Eval.paraVal" (fun l cs ↦ nodeT (Term.pair l cs))
      ["pvFst", "pvKids"]]

end GebTests.Prototypes.FreeTopos.Normalization

end
