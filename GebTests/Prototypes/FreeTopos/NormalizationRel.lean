/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.NormalizationConst -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.NormalizationConst -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The constants' relations

Each constant of the kernel, at its type, related to itself by the relation of the internal
language, proved after the development of the convergence lemmas ({lit}`constDev`), whose
declarations the certificate {lit}`bootstrap/certificates/normalization-rel.cert` stores. They are
the cases of the fundamental lemma in which a term
is a constant, whose value is the constant itself.

A constant's relation at a function type unfolds to the convergence of its application to each
related argument. Applied to fewer arguments than it takes, a constant converges at once to its
partial application; applied to all of them, it computes as the evaluator's function of the
constant, one level of fuel below, which converges by the convergence lemmas: the folds of trees
by {lit}`foldConv` and {lit}`paraConv`, the right fold of lists by induction on the list
({lit}`foldrConv`), and iteration by induction on the count's bits, generalized over the start
({lit}`iterConv`). Case analysis of lists decides the list value's label and children, and each
primitive computes on the trees its arguments quote; the node primitive's list argument has
every element's unquotation ({lit}`unquoteAll`), and the children primitive's value is the list of
the children's quotations ({lit}`quoteAll`).

## Main definitions

* {lit}`relFoldLemma` — the fold and the fold whose step sees the node.
* {lit}`foldrConvLemma`, {lit}`relFoldrLemma` — the right fold of lists.
* {lit}`iterConvLemma`, {lit}`relIterLemma` — iteration.
* {lit}`relLcaseLemma` — case analysis of lists.
* {lit}`relPrimLemma` — the primitives.
* {lit}`relDev` — the development.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, constants, primitives, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Normalization

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open Internal (Term NormRule Entry Deriv Decl)
open scoped FinEnum

/-- A constant of one type argument applied to its first argument converges at once to the
partial application; applied to a tree as well, it converges as the evaluator's function
{lit}`val` does at the tree, one level below, by the lemma {lit}`conv`. The constant of label
{lit}`lbl` is related at the type {lit}`Check.foldTy`. -/
def relFoldLemma (P : Prog) (S : Defs) (name conv tag : String) (lbl : ℕ) : Step :=
  (name, fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, apNames tag 2 ++ ["spFst"]⟩
    let L := K.L
    let nd (A : Term) : Term := nodeT (Term.pair (numeral lbl) (consT treeTy A (nilT treeTy)))
    -- context: the type, the definitions
    let a : Internal.Thm := ⟨0, [treeTy, list treeTy], [],
      Term.app (S.rel (v 1) (pc P "Check.foldTy" [v 0])) (nd (v 0))⟩
    let body : Deducer := K.norm (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let at₁ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + k)
      let f := at₁ 0
      let A := at₁ 1
      let Dv := at₁ 2
      let hf := Φ₁.length - 1
      let full : Deducer := fun Γ₂ Φ₂ ψ₂ ↦
        let t (Γ : List Tree) : Term := v (Γ.length - Γ₂.length)
        K.cutThm conv (fun Γ ↦ [t Γ]) (K.allEΓ Dv (K.allEΓ A (K.allEΓ f (K.impE (K.byHyp hf)
          (K.convE fun Γ₃ Φ₃ ψ₃ ↦
            let n := fun Γ ↦ v (Γ.length - Γ₃.length + 1)
            let w := fun Γ ↦ v (Γ.length - Γ₃.length)
            K.conv (fun Γ ↦ succN (n Γ)) w
              (K.instN (Φ₃.length - 2) (fun _ ↦ v 0) K.byNorm)
              ((K.byHyp (Φ₃.length - 1))) Γ₃ Φ₃ ψ₃))))) Γ₂ Φ₂ ψ₂
      K.conv (fun _ ↦ succN zeroN) (fun Γ ↦ pc P "Eval.valApp" [nd (A Γ), f Γ])
        (K.byNorm)
        (K.norm (dAllI L (dImpI L (K.normLast (K.exE (full)))))) Γ₁ Φ₁ ψ₁))
    let some d := body a.ctx a.hyps a.concl | dbgTrace s!"{name}: not proved" fun _ ↦ none
    pure (a, d))

namespace Kit

variable (K : Kit)

/-- The stability hypothesis h shifted, each threshold of the list added on its right in turn,
the final hypothesis's index passed on. -/
def shiftRights (js : List (List Tree → Term)) : (ℕ → Deducer) → ℕ → Deducer :=
  js.foldr (fun j rest k h ↦ K.shift h false j (fun Γ Φ ψ ↦ rest k (Φ.length - 1) Γ Φ ψ))
    fun k h ↦ k h

/-- Convergences combined, each value computed from the previous ones: the thresholds
{lit}`ns` of the stabilities {lit}`ss` shifted to their sum, the threshold i's on its left by the
sum of those before it and on its right by each after it; the value {lit}`w` related by the
hypothesis {lit}`rw`; the goal's threshold the sum, or its successor where the values are
computed a level below. -/
def sumAll (ns : List (List Tree → Term)) (ss : List ℕ) (w : List Tree → Term) (rw : ℕ)
    (succ : Bool := false) : Deducer :=
  -- the sums of the thresholds before each, the first's empty
  let sumOf (xs : List (List Tree → Term)) : Option (List Tree → Term) :=
    xs.foldl (fun acc n ↦ some (match acc with
      | some a => fun Γ ↦ K.S.add (a Γ) (n Γ)
      | none => n)) none
  let sum := (sumOf ns).getD fun _ ↦ zeroN
  let total (Γ : List Tree) : Term := if succ then succN (sum Γ) else sum Γ
  let finish (hs : List ℕ) : Deducer :=
    K.conv total w (hs.foldr (fun h k ↦ K.instN h (fun _ ↦ v 0) k) (K.byNorm))
      ((K.byHyp rw))
  -- the stabilities shifted in turn, the final indices collected
  let step (i h : ℕ) (k : ℕ → Deducer) : Deducer :=
    let rights := ns.drop (i + 1)
    match sumOf (ns.take i) with
    | some pre => K.shift h true pre (fun Γ Φ ψ ↦ K.shiftRights rights k (Φ.length - 1) Γ Φ ψ)
    | none => K.shiftRights rights k h
  (ss.zipIdx.foldr (fun (h, i) rest hs ↦ step i h fun h' ↦ rest (hs ++ [h'])) finish) []

/-- Three convergences combined, as {lit}`sumAll`. -/
def sum3 (N n₁ n₂ w : List Tree → Term) (sC s₁ s₂ rw : ℕ) : Deducer :=
  K.sumAll [N, n₁, n₂] [sC, s₁, s₂] w rw false

/-- The last hypothesis, a relation at a function type, normalized and instantiated at a term
whose relation the first deducer proves, its convergence unfolded. -/
def applyRel (x : List Tree → Term) (px k : Deducer) : Deducer :=
  K.normLast (K.allEΓ x (K.impE px (K.convE k)))

/-- A hypothesis decided by case analysis of the data its weak head normal form is blocked on,
bits, bitstrings and variables of lists of trees, to a depth: each case refuted where the
hypothesis reduces to falsity, else proved by k. -/
def splitHypL (h : ℕ) (k : Deducer) (depth : ℕ) : Deducer := (Nat.rec
  (motive := fun _ ↦ Deducer) (fun Γ Φ ψ ↦ (K.hypFalse h Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ)
  (fun _ rec Γ Φ ψ ↦ (K.hypFalse h Γ Φ ψ).orElse fun _ ↦ do
    let (t, _) ← evalRw K.G K.E (K.rulesEx Φ h) .head Γ Φ (← Φ[h]?)
    let some X := (blocking t).reverse.find? fun X ↦
        let ty := Internal.typeIn K.G 0 Γ X
        ty = some bitsTy ∨ ty = some bitTy ∨ (ty = some (list treeTy) ∧ isVar X)
      | k Γ Φ ψ
    let ty := Internal.typeIn K.G 0 Γ X
    if ty = some bitTy then K.bitCase X rec rec Γ Φ ψ
    else if ty = some bitsTy then K.listCase bitTy X rec rec Γ Φ ψ
    else K.listCase treeTy X rec rec Γ Φ ψ) depth)

/-- The partial application of a value: convergence at fuel one to the value {lit}`w`. -/
def part (w : List Tree → Term) (k : Deducer) : Deducer :=
  K.conv (fun _ ↦ succN zeroN) w (K.byNorm) k

/-- The relation of a constant of three arguments at its function type, unfolded: its first two
applications converge at once to partial applications, and the third is proved by
{lit}`last`, given the variables of the first two arguments; the hypotheses of the three
arguments' relations are those of indices 1, 3 and 5, each universal introduction adding truth
as a hypothesis before them. -/
def three (nd : List Tree → Term) (last : (List Tree → Term) → (List Tree → Term) → Deducer) :
    Deducer :=
  let vApp (f x : Term) : Term := pc K.P "Eval.valApp" [f, x]
  K.norm (dAllI K.L (dImpI K.L fun Γ₁ Φ₁ ψ₁ ↦
    let a₁ (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
    let second : Deducer := K.norm (dAllI K.L (dImpI K.L fun Γ₂ Φ₂ ψ₂ ↦
      let a₂ (Γ : List Tree) : Term := v (Γ.length - Γ₂.length)
      K.part (fun Γ ↦ vApp (vApp (nd Γ) (a₁ Γ)) (a₂ Γ))
        (K.norm (dAllI K.L (dImpI K.L (last a₁ a₂)))) Γ₂ Φ₂ ψ₂))
    K.part (fun Γ ↦ vApp (nd Γ) (a₁ Γ)) second Γ₁ Φ₁ ψ₁))

/-- A convergence lemma cut in at terms, instantiated at further terms with its antecedents proved
by the given deducers, its convergence's value one level below the goal's: the goal's threshold
the successor of the lemma's. -/
def below (name : String) (σ : List Tree → List Term) (ts : List (List Tree → Term))
    (antes : List Deducer) : Deducer :=
  let fin : Deducer := K.convE fun Γ₄ Φ₄ ψ₄ ↦
    let n := fun Γ ↦ v (Γ.length - Γ₄.length + 1)
    let w := fun Γ ↦ v (Γ.length - Γ₄.length)
    K.conv (fun Γ ↦ succN (n Γ)) w
      (K.instN (Φ₄.length - 2) (fun _ ↦ v 0) (K.byNorm))
      (K.byHyp (Φ₄.length - 1)) Γ₄ Φ₄ ψ₄
  let withAntes := antes.foldr (fun p k ↦ K.impE p k) fin
  K.cutThm name σ (ts.foldr (fun t k ↦ K.allEΓ t k) withAntes)

end Kit

/-- The right fold's formula at a list of values: for all definitions, types and steps and starts
related at theirs, if every value is related at the element type, the right fold of the values
converges to a value related at the result type. The elements' predicate is stated as the
relation at the list type states it, applied to its variable. -/
def foldrφ (P : Prog) (S : Defs) : Term :=
  let all := Internal.Logic.all P.o
  let imp := Internal.Logic.imp P.o
  -- under the five quantifiers: the start v0, the step v1, the result type v2, the element type
  -- v3, the definitions v4, the list v5
  let body := imp (Term.app (S.rel (v 4) (tyA P (v 3) (tyA P (v 2) (v 2)))) (v 1))
    (imp (Term.app (S.rel (v 4) (v 2)) (v 0))
      (imp (S.allL (Term.lam treeTy (Term.app (S.rel (v 5) (v 4)) (v 0))) (v 5))
      (S.conv (Term.lam nat (pc P "Eval.foldrVal" [Term.snd (S.levelN (v 5) (v 0)), v 2, v 1,
        v 6])) (S.rel (v 4) (v 2)))))
  all (list treeTy) (Term.lam (list treeTy) (all treeTy (Term.lam treeTy (all treeTy
    (Term.lam treeTy (all treeTy (Term.lam treeTy (all treeTy (Term.lam treeTy body)))))))))

/-- The right fold computes at a step and a start related at theirs: by induction on the values,
the rest's fold converging by the induction hypothesis, the step's application to the head and
then to the rest's value each converging. -/
def foldrConvLemma (P : Prog) (S : Defs) : Step :=
  ("foldrConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let φ := foldrφ P S
    let intro (k : List Tree → Deducer) : Deducer :=
      dAllI L (dAllI L (dAllI L (dAllI L (dAllI L (dImpI L (dImpI L (dImpI L fun Γ Φ ψ ↦
        k Γ Γ Φ ψ)))))))
    let d₀ ← intro (fun _ ↦ K.conv (fun _ ↦ zeroN) (fun Γ ↦ v (Γ.length - Γ.length))
      (K.byNorm) (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 2) Γ Φ ψ)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := intro fun Γ₁ Γ Φ ψ ↦
      let at₁ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + k)
      let hg := Φ.length - 3
      let hz := Φ.length - 2
      K.normLast (K.conjE (fun Γ Φ ψ ↦
        let hx := Φ.length - 2
        let hr := Φ.length - 1
        dAllE L K.G K.E 0 (at₁ 4 Γ) (K.allEΓ (at₁ 3) (K.allEΓ (at₁ 2) (K.allEΓ (at₁ 1)
          (K.allEΓ (at₁ 0) (K.impE (K.byHyp hg) (K.impE (K.byHyp hz) (K.impE (K.byHyp hr)
            (K.convE fun Γ₂ Φ₂ ψ₂ ↦
              let n₁ := fun Γ ↦ v (Γ.length - Γ₂.length + 1)
              let a := fun Γ ↦ v (Γ.length - Γ₂.length)
              let s₁ := Φ₂.length - 2
              let ra := Φ₂.length - 1
              dRwHyp (evalRw K.G K.E (K.rulesEx Φ₂ hg) .full) hg (K.allEΓ (at₁ 6)
                (K.impE (K.byHyp hx) (K.convE fun Γ₃ Φ₃ ψ₃ ↦
                  let n₂ := fun Γ ↦ v (Γ.length - Γ₃.length + 1)
                  let s₂ := Φ₃.length - 2
                  K.applyRel a (K.byHyp ra) (fun Γ₄ Φ₄ ψ₄ ↦
                    let n₃ := fun Γ ↦ v (Γ.length - Γ₄.length + 1)
                    let w := fun Γ ↦ v (Γ.length - Γ₄.length)
                    K.sum3 n₁ n₂ n₃ w s₁ s₂ (Φ₄.length - 2) (Φ₄.length - 1) Γ₄ Φ₄ ψ₄)
                    Γ₃ Φ₃ ψ₃))) Γ₂ Φ₂ ψ₂)))))))) Γ Φ ψ)) Γ Φ ψ
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The right fold of lists is related at its type: applied to a step and a start it converges
at once to the partial applications, and applied to a list value as well, to the right fold of
the list's values, by {lit}`foldrConv`. -/
def relFoldrLemma (P : Prog) (S : Defs) : Step :=
  ("relFoldr", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, apNames "apFoldr" 3 ++ ["spFst"]⟩
    -- context: the result type, the element type, the definitions
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy], [],
      Term.app (S.rel (v 2) (pc P "Check.foldrTy" [v 1, v 0]))
        (constNode Kernel.Label.foldr [v 1, v 0])⟩
    -- the type variables, from the lemma's context: the definitions, the element type, the
    -- result type
    let at₀ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - 3 + k)
    let nd (Γ : List Tree) : Term := constNode Kernel.Label.foldr [at₀ 1 Γ, at₀ 0 Γ]
    -- the list value's test decided, and the right fold of its elements
    let last (g z : List Tree → Term) : Deducer := fun Γ₃ Φ₃ ψ₃ ↦
      let xs (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
      let elems (Γ : List Tree) : Term :=
        call D.children [] [pc P "Prelude.get" [pc P "Eval.listOf" [xs Γ]]]
      K.normLast (K.conjE fun Γ₄ Φ₄ ψ₄ ↦
        K.splitHyp (Φ₄.length - 2) (K.below "foldrConv" (fun Γ ↦ [elems Γ])
          [at₀ 2, at₀ 1, at₀ 0, g, z] [K.byHyp 1, K.byHyp 3, K.byHyp (Φ₄.length - 1)]) 8
          Γ₄ Φ₄ ψ₄) Γ₃ Φ₃ ψ₃
    let body : Deducer := K.three nd last
    let some d := body a.ctx a.hyps a.concl | dbgTrace "relFoldr: not proved" fun _ ↦ none
    pure (a, d))

/-- The iteration's formula at a bitstring, the count: for all definitions, types, steps related
at the type's endofunctions and starts related at the type, the iteration of the step the count's
number of times from the start converges to a value related at the type. -/
def iterφ (P : Prog) (S : Defs) : Term :=
  let all := Internal.Logic.all P.o
  let imp := Internal.Logic.imp P.o
  -- under the four quantifiers: the start v0, the step v1, the type v2, the definitions v3, the
  -- count v4
  let body := imp (Term.app (S.rel (v 3) (tyA P (v 2) (v 2))) (v 1))
    (imp (Term.app (S.rel (v 3) (v 2)) (v 0))
      (S.conv (Term.lam nat (pc P "Eval.iterVal" [Term.snd (S.levelN (v 4) (v 0)), v 2, v 1,
        leafT (v 5)])) (S.rel (v 3) (v 2))))
  all (list treeTy) (Term.lam (list treeTy) (all treeTy (Term.lam treeTy (all treeTy
    (Term.lam treeTy (all treeTy (Term.lam treeTy body)))))))

/-- Iteration computes at a step and a start related at theirs: by induction on the count's bits,
the rest's iteration converging from the start and then from its value, by the induction
hypothesis generalized over the start, and the step applied once or twice. -/
def iterConvLemma (P : Prog) (S : Defs) : Step :=
  ("iterConv", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let φ := iterφ P S
    let intro (k : List Tree → Deducer) : Deducer :=
      dAllI L (dAllI L (dAllI L (dAllI L (dImpI L (dImpI L fun Γ Φ ψ ↦ k Γ Γ Φ ψ)))))
    let d₀ ← intro (fun _ ↦ K.conv (fun _ ↦ zeroN) (fun _ ↦ v 0) (K.byNorm)
      (fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [bitTy] Term.star)))
    let cons : Deducer := intro fun Γ₁ Γ Φ ψ ↦
      let at₁ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + k)
      let hs := Φ.length - 2
      let hz := Φ.length - 1
      -- the step applied to the last value, its convergence unfolded
      let applyS (w : List Tree → Term) (rw : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ hs) .full) hs (K.allEΓ w (K.impE (K.byHyp rw)
          (K.convE k))) Γ Φ ψ
      -- the rest's iteration from a start related by the hypothesis rz
      let rest (z : List Tree → Term) (rz : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
        dAllE L K.G K.E 0 (at₁ 3 Γ) (K.allEΓ (at₁ 2) (K.allEΓ (at₁ 1) (K.allEΓ z
          (K.impE (K.byHyp hs) (K.impE (K.byHyp rz) (K.convE k)))))) Γ Φ ψ
      let nv (Γ' : List Tree) : (List Tree → Term) × (List Tree → Term) :=
        (fun Γ ↦ v (Γ.length - Γ'.length + 1), fun Γ ↦ v (Γ.length - Γ'.length))
      rest (at₁ 0) hz (fun Γ₂ Φ₂ ψ₂ ↦
        let (n₁, w₁) := nv Γ₂
        let (s₁, r₁) := (Φ₂.length - 2, Φ₂.length - 1)
        rest w₁ r₁ (fun Γ₃ Φ₃ ψ₃ ↦
          let (n₂, w₂) := nv Γ₃
          let (s₂, r₂) := (Φ₃.length - 2, Φ₃.length - 1)
          let once : Deducer := applyS w₂ r₂ fun Γ₄ Φ₄ ψ₄ ↦
            let (n₃, w₃) := nv Γ₄
            K.sumAll [n₁, n₂, n₃] [s₁, s₂, Φ₄.length - 2] w₃ (Φ₄.length - 1) false Γ₄ Φ₄ ψ₄
          let twice : Deducer := applyS w₂ r₂ fun Γ₄ Φ₄ ψ₄ ↦
            let (n₃, w₃) := nv Γ₄
            let s₃ := Φ₄.length - 2
            applyS w₃ (Φ₄.length - 1) (fun Γ₅ Φ₅ ψ₅ ↦
              let (n₄, w₄) := nv Γ₅
              K.sumAll [n₁, n₂, n₃, n₄] [s₁, s₂, s₃, Φ₅.length - 2] w₄ (Φ₅.length - 1) false
                Γ₅ Φ₅ ψ₅) Γ₄ Φ₄ ψ₄
          let either : Deducer := fun Γ Φ ψ ↦ (once Γ Φ ψ).orElse fun _ ↦ twice Γ Φ ψ
          K.bitCase (at₁ 5 Γ₃) either either Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ Φ ψ
    let d₁ ← cons [bitsTy, bitTy] [Internal.weakenElem φ] (Internal.listConsAt 1 bitTy φ)
    pure (⟨0, [bitsTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Iteration is related at its type: applied to a step and a start it converges at once to the
partial applications, and applied to a quoted count as well, to the iteration, by
{lit}`iterConv` at the count's label. -/
def relIterLemma (P : Prog) (S : Defs) : Step :=
  ("relIter", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, apNames "apIter" 3 ++ ["spFst"]⟩
    -- context: the type, the definitions
    let a : Internal.Thm := ⟨0, [treeTy, list treeTy], [],
      Term.app (S.rel (v 1) (pc P "Check.iterTy" [v 0])) (constNode Kernel.Label.iter [v 0])⟩
    -- the type variables, from the lemma's context: the definitions, the type
    let at₀ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - 2 + k)
    let nd (Γ : List Tree) : Term := constNode Kernel.Label.iter [at₀ 0 Γ]
    -- the count a quotation, iterated its label's number of times
    let last (s z : List Tree → Term) : Deducer := K.normLast (K.exE fun Γ₃ Φ₃ ψ₃ ↦
      let t (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
      K.below "iterConv" (fun Γ ↦ [call D.lab [] [t Γ]]) [at₀ 1, at₀ 0, s, z]
        [K.byHyp 1, K.byHyp 3] Γ₃ Φ₃ ψ₃)
    let body : Deducer := K.three nd last
    let some d := body a.ctx a.hyps a.concl | dbgTrace "relIter: not proved" fun _ ↦ none
    pure (a, d))

/-- Case analysis of lists is related at its type: applied to a list value and a value it
converges at once to the partial applications, and applied to a function as well, by the list
value's label and children: the empty list's value the second argument, and a construction's the
function applied to the head and then to the rest, the rest's relation read off the list's. -/
def relLcaseLemma (P : Prog) (S : Defs) : Step :=
  ("relLcase", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, apNames "apLcase" 3 ++ ["spFst"]⟩
    -- context: the result type, the element type, the definitions
    let a : Internal.Thm := ⟨0, [treeTy, treeTy, list treeTy], [],
      Term.app (S.rel (v 2) (pc P "Check.lcaseTy" [v 1, v 0]))
        (constNode Kernel.Label.lcase [v 1, v 0])⟩
    let at₀ (k : ℕ) (Γ : List Tree) : Term := v (Γ.length - 3 + k)
    let nd (Γ : List Tree) : Term := constNode Kernel.Label.lcase [at₀ 1 Γ, at₀ 0 Γ]
    -- the empty list: the second argument at once
    let nilLeaf (n : List Tree → Term) : Deducer :=
      K.conv (fun _ ↦ succN zeroN) n (K.byNorm) (K.byHyp 3)
    -- a construction: the function at the head and then at the rest, the list value's
    -- children
    let childT := (primT Kernel.Prim.child).getD Term.star
    let consLeaf (xs : List Tree → Term) (hall : ℕ) : Deducer := fun Γ Φ ψ ↦
      let x (Γ' : List Tree) : Term := apps childT [xs Γ', leafT bnilT]
      let xs' (Γ' : List Tree) : Term := apps childT [xs Γ', leafT (numeral 1)]
      let atRest : Deducer := fun Γ₄ Φ₄ ψ₄ ↦
        let n₁ := fun Γ ↦ v (Γ.length - Γ₄.length + 1)
        let s₁ := Φ₄.length - 2
        K.normLast (K.allEΓ xs' (K.impE (K.auto 4) (K.convE fun Γ₅ Φ₅ ψ₅ ↦
            let n₂ := fun Γ ↦ v (Γ.length - Γ₅.length + 1)
            let w := fun Γ ↦ v (Γ.length - Γ₅.length)
            K.sumAll [n₁, n₂] [s₁, Φ₅.length - 2] w (Φ₅.length - 1) true Γ₅ Φ₅ ψ₅)))
          Γ₄ Φ₄ ψ₄
      let headX := K.allEΓ x (K.impE (K.auto 4) (K.convE atRest))
      -- the elements' relations split into the head's and the rest's
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ hall) .full) hall (K.conjE fun Γ Φ ψ ↦
        dRwHyp (evalRw K.G K.E (K.rulesEx Φ 5) .full) 5 headX Γ Φ ψ) Γ Φ ψ
    -- the list value's relation, its test decided by its label and children
    let last (xs n : List Tree → Term) : Deducer := fun Γ₃ Φ₃ ψ₃ ↦
      let split : Deducer := fun Γ₄ Φ₄ ψ₄ ↦
        let leaf : Deducer := fun Γ Φ ψ ↦
          (nilLeaf n Γ Φ ψ).orElse fun _ ↦ consLeaf xs (Φ₄.length - 1) Γ Φ ψ
        K.treeNode (xs Γ₄) (K.splitHypL (Φ₄.length - 2) leaf 24) Γ₄ Φ₄ ψ₄
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ₃ 1) .full) 1 (K.conjE split)
        Γ₃ Φ₃ ψ₃
    let some d := K.three nd last a.ctx a.hyps a.concl
      | dbgTrace "relLcase: not proved" fun _ ↦ none
    pure (a, d))

/-- The quotations of a list of trees, each related at the tree type; by induction on the list. -/
def quoteAllLemma (P : Prog) (S : Defs) : Step :=
  ("quoteAll", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let quotes (ws : Term) : Term :=
      pc P "Eval.mapT" [Term.lam treeTy (pc P "Eval.valQuote" [v 0]), ws]
    -- under the definitions: the definitions v0, the list v1
    let φ := Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy)
      (S.allL (S.rel (v 0) tyT) (quotes (v 1))))
    let d₀ ← dAllI L (K.auto 3) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    let cons : Deducer := dAllI L fun Γ₁ Φ₁ ψ₁ ↦
      let Dv (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      let w (Γ : List Tree) : Term := v (Γ.length - Γ₁.length + 2)
      K.norm (dConjI L (fun Γ Φ ψ ↦ dExI L K.G K.E (w Γ) K.byNorm Γ Φ ψ)
        (dAllE L K.G K.E 0 (Dv Γ₁) fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ)) Γ₁ Φ₁ ψ₁
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- Values each related at the tree type are quotations, so their unquotations are all present:
some list of the quoted trees; by induction on the list. -/
def unquoteAllLemma (P : Prog) (S : Defs) : Step :=
  ("unquoteAll", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    let unquotes (ws : Term) : Term := pc P "Eval.allSomeT"
      [pc P "Eval.mapT" [Term.lam treeTy (pc P "Eval.unquote" [v 0]), ws]]
    -- under the definitions: the definitions v0, the list v1
    let φ := Internal.Logic.all P.o (list treeTy) (Term.lam (list treeTy)
      (Internal.Logic.imp P.o (S.allL (Term.lam treeTy (Term.app (S.rel (v 1) tyT) (v 0))) (v 1))
        (Internal.Logic.ex P.o treeTy (Term.lam treeTy
          (Term.eq (unquotes (v 2)) (pc P "Prelude.some" [v 0]))))))
    let d₀ ← dAllI L (dImpI L (dExI L K.G K.E (node0 (nilT treeTy)) K.byNorm)) [] []
      (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
    -- a construction: the head a quotation, the rest's unquotations some list by the induction
    -- hypothesis, the list the quoted tree before it
    let cons : Deducer := dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
      let Dv (Γ : List Tree) : Term := v (Γ.length - Γ₁.length)
      K.normLast (K.conjE fun Γ₂ Φ₂ ψ₂ ↦
        let hq := Φ₂.length - 2
        let hr := Φ₂.length - 1
        dExE L K.G K.E hq (fun Γ₃ Φ₃ ψ₃ ↦
          let u (Γ : List Tree) : Term := v (Γ.length - Γ₃.length)
          dAllE L K.G K.E 0 (Dv Γ₃) (K.impE (K.byHyp hr) (K.exE (K.normLast fun Γ₄ Φ₄ ψ₄ ↦
            let r (Γ : List Tree) : Term := v (Γ.length - Γ₄.length)
            dExI L K.G K.E (node0 (consT treeTy (u Γ₄) (call D.children [] [r Γ₄])))
              (K.byNorm) Γ₄ Φ₄ ψ₄))) Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)
    let d₁ ← cons [list treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
    pure (⟨0, [list treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The shape of a primitive's type: from a tree to a tree (0), from two trees to a tree (1), the
node primitive's (2), and the children primitive's (3). -/
def primShape (k : ℕ) : ℕ :=
  if k = Kernel.Prim.node then 2 else if k = Kernel.Prim.children then 3
  else if k = Kernel.Prim.label ∨ k = Kernel.Prim.arity ∨ k = Kernel.Prim.log2 then 0 else 1

/-- A primitive's type, by its shape. -/
def primTy (P : Prog) (k : ℕ) : Term := match primShape k with
  | 0 => tyA P tyT tyT
  | 1 => tyA P tyT (tyA P tyT tyT)
  | 2 => tyA P tyT (tyA P (tyL P tyT) tyT)
  | _ => tyA P tyT (tyL P tyT)

/-- The constant of a primitive. -/
def primConst (k : ℕ) : Term := constNode Kernel.Label.prim [leafT (numeral k)]

/-- The number of arguments of a primitive, by its shape. -/
def primArgs (k : ℕ) : ℕ := if primShape k = 0 ∨ primShape k = 3 then 1 else 2

/-- A primitive is related at its type: each argument related at the tree type a quotation, the
list argument of the node primitive a list value whose test and whose elements' unquotations are
decided; the value the evaluator's at fuel one, related at the tree type as a quotation, or, for
the children primitive, at the list type by {lit}`relOfList` and {lit}`quoteAll`. -/
def relPrimLemma (P : Prog) (S : Defs) (k : ℕ) : Step :=
  (s!"relPrim{k}", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, apNames s!"apPrim{k}" (primArgs k) ++ ["spFst"]⟩
    let L := K.L
    let a : Internal.Thm :=
      ⟨0, [list treeTy], [], Term.app (S.rel (v 0) (primTy P k)) (primConst k)⟩
    let Dv (Γ : List Tree) : Term := v (Γ.length - 1)
    let childT := (primT Kernel.Prim.child).getD Term.star
    let vApp (f x : Term) : Term := pc P "Eval.valApp" [f, x]
    -- the value at fuel one of an application, and its relation at the tree type
    let W (f x : List Tree → Term) (Γ : List Tree) : Term :=
      pc P "Prelude.get" [apps (Term.snd (S.levelN (Dv Γ) (succN zeroN))) [f Γ, x Γ]]
    let relT (f x : List Tree → Term) : Deducer := K.norm fun Γ Φ ψ ↦
      dExI L K.G K.E (apps childT [W f x Γ, leafT bnilT]) K.byNorm Γ Φ ψ
    let fin (f x : List Tree → Term) (rel : Deducer) : Deducer :=
      K.conv (fun _ ↦ succN zeroN) (W f x) (K.byNorm) (rel)
    -- an argument related at the tree type, a quotation: its variable, and the quoted tree
    let argT (k : (List Tree → Term) → (List Tree → Term) → Deducer) : Deducer :=
      dAllI L (dImpI L fun Γa Φa ψa ↦
        let x (Γ : List Tree) : Term := v (Γ.length - Γa.length)
        K.normLast (K.exE fun Γt Φt ψt ↦
          k x (fun Γ ↦ v (Γ.length - Γt.length)) Γt Φt ψt) Γa Φa ψa)
    let nd : List Tree → Term := fun _ ↦ primConst k
    let body : Deducer := match primShape k with
      | 0 => argT fun x _ ↦ fin nd x (relT nd x)
      | 1 => argT fun x _ ↦ K.part (fun Γ ↦ vApp (nd Γ) (x Γ)) (K.norm (argT fun y _ ↦
          fin (fun Γ ↦ vApp (nd Γ) (x Γ)) y (relT (fun Γ ↦ vApp (nd Γ) (x Γ)) y)))
      | 2 => argT fun x _ ↦ K.part (fun Γ ↦ vApp (nd Γ) (x Γ)) (K.norm (dAllI L (dImpI L
          fun Γc Φc ψc ↦
            let cs (Γ : List Tree) : Term := v (Γ.length - Γc.length)
            let f (Γ : List Tree) : Term := vApp (nd Γ) (x Γ)
            let elems (Γ : List Tree) : Term :=
              call D.children [] [pc P "Prelude.get" [pc P "Eval.listOf" [cs Γ]]]
            K.normLast (K.conjE fun Γd Φd ψd ↦
              K.splitHyp (Φd.length - 2) (K.cutThm "unquoteAll" (fun Γ ↦ [elems Γ])
                (K.allEΓ Dv (K.impE (K.byHyp (Φd.length - 1))
                  (K.exE (K.normLast (fin f cs (relT f cs))))))) 8
                Γd Φd ψd) Γc Φc ψc)))
      | _ => argT fun x t ↦
          let elems (Γ : List Tree) : Term := call D.children [] [t Γ]
          let quotes (Γ : List Tree) : Term :=
            pc P "Eval.mapT" [Term.lam treeTy (pc P "Eval.valQuote" [v 0]), elems Γ]
          let last : Deducer := fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ
          fin nd x (K.cutThm "relOfList" (fun Γ ↦ [quotes Γ]) (K.allEΓ Dv
            (K.allEΓ (fun _ ↦ tyT) (K.impE (K.cutThm "quoteAll" (fun Γ ↦ [elems Γ])
              (K.allEΓ Dv last)) last))))
    let some d := K.norm body a.ctx a.hyps a.concl
      | dbgTrace s!"relPrim{k}: not proved" fun _ ↦ none
    pure (a, d))

/-- The primitives' indices. -/
def primIndices : List ℕ := List.range 14

/-- The constants' relations at their types. -/
def relDev (P : Prog) (S : Defs) : List Step :=
  [relFoldLemma P S "relFold" "foldConv" "apFold" Kernel.Label.fold,
    relFoldLemma P S "relPara" "paraConv" "apPara" Kernel.Label.para] ++
  apConstLemmas P "apFoldr" (constNode Kernel.Label.foldr) 2 3 ++
  [foldrConvLemma P S, relFoldrLemma P S] ++
  apConstLemmas P "apIter" (constNode Kernel.Label.iter) 1 3 ++
  [iterConvLemma P S, relIterLemma P S] ++
  apConstLemmas P "apLcase" (constNode Kernel.Label.lcase) 2 3 ++ [relLcaseLemma P S] ++
  [quoteAllLemma P S, unquoteAllLemma P S] ++
  primIndices.flatMap fun k ↦
    apConstLemmas P s!"apPrim{k}" (fun _ ↦ primConst k) 0 (primArgs k) ++ [relPrimLemma P S k]

end GebTests.Prototypes.FreeTopos.Normalization

end
