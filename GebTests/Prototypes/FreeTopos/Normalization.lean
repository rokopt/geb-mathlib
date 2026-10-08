/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.NormalizationRel -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.NormalizationRel -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Well-typed terms evaluate

The fundamental lemma of the logical relation between the evaluator's values and the kernel's
types, for the type checker and the evaluator written in Geb, {lit}`bootstrap/check.geb` and
{lit}`bootstrap/eval.geb`, translated to the internal language: one theorem, proved by induction on
rose trees over all terms, that a term to which the checker gives a type in a context evaluates,
in an environment related to the context and with definitions related to the types of the
globals, to a value related at that type. It is the internal counterpart of
{name}`Geb.Kernel.Eval.fundamental`, the evaluator's adequacy proved in Lean in the manner of
{cite}`Tait1967`.

The relation is the fold of the type tree into the predicates on values, and its conclusion is a
stable convergence: from some level of fuel on, the evaluation has one value, which the relation
holds of. At a node, the label is decided by case analysis of its bits and the children by their
number, labels without a rule refuted by the typing; each rule's case decides the data the typing
waits on, takes the children's convergences from the induction hypothesis, shifts their thresholds
to their sum, and converges a level above it. A constant's value is the constant itself, related at
its type by the lemmas of {lit}`NormalizationRel`.

## Main definitions

* {lit}`fundamentalDeriv` — the derivation of the lemma's induction step.
* {lit}`fundamentalThm` — the lemma.
* {lit}`certificates` — the developments of the base, the convergence lemmas, the constants'
  relations and the lemma.

## Implementation notes

The derivation is found by deducers over the theorems of the developments before it. The
developments' declarations are stored in the certificates under {lit}`bootstrap/certificates/`,
whose check by the internal language's checker ({name}`Geb.FreeTopos.Internal.checkDev`)
{lit}`GebTests.Prototypes.FreeTopos.Certified.Normalization` states.

## References

* {cite}`Tait1967`, for the logical relation and its fundamental lemma.

## Tags

internal language, logical relation, fundamental lemma, evaluator, type checker, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Normalization

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open Geb.FreeTopos.Tactics (nthOf)
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-- The derivation of the fundamental lemma's induction step, found by deducers over the
theorems of the developments before it, each with its name, where they find one. -/
def fundamentalDeriv (P : Prog) (S : Defs) (base : List (String × Internal.Thm)) :
    Option Deriv :=
  let G := P.G
  let E : Array Entry := (base.map fun (_, a) ↦ Entry.language a).toArray
  let names := base.map (·.1)
  let ix (name : String) : ℕ := (names.findIdx? (· == name)).getD 0
  let L : Conn := ⟨P.o, logicBase⟩
  let φ := fundamental P S
  let rsV (Φ : List Internal.Term) : List NormRule := eqHyps Φ ++ addLemmaRules ix ++ vRules P ix
  -- the typing hypothesis, after the induction hypothesis, the four variables' truths and the
  -- relations of the definitions and of the environment
  let hT := 7
  let refute : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw G E (rsV Φ ++ [.delta (P.idx "Check.checkNode")]) .head) hT
      (dFalse L dHyp) Γ Φ ψ
  -- the children split to the label's arity: each other number refuted, and the arity's case
  -- by valid
  let refuteF : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw G E (rsV Φ ++ [.delta (P.idx "Check.checkNode")]) .full) hT
      (dFalse L dHyp) Γ Φ ψ
  let refuteT : Deducer := fun Γ Φ ψ ↦ (refuteF Γ Φ ψ).orElse fun _ ↦
    let h := ((Φ[hT]?).bind fun ψ ↦ evalRw G E (rsV Φ ++ [.delta (P.idx "Check.checkNode")])
      .head Γ Φ ψ).map fun (p : Internal.Term × Deriv) ↦ showT p.1
    dbgTrace s!"refute: {h}" fun _ ↦ none
  let arity (valid : Deducer) : ℕ → Internal.Term → Deducer := fun k ↦ k.rec
    (fun X ↦ dListCase L G E (ix "listCases") treeTy X valid refuteT)
    fun _ rec X ↦ dListCase L G E (ix "listCases") treeTy X refuteT (rec (v 0))
  let rules (Φ : List Internal.Term) : List NormRule :=
    rsV Φ ++ [.delta (S.q + 5), .thm (ix "rebTail") [omega]]
  -- the rules but the hypothesis of index i
  let rulesEx (Φ : List Internal.Term) (i : ℕ) : List NormRule :=
    (rules Φ).filter fun r ↦ match r with
      | .hyp j => j ≠ i
      | _ => true
  let norm : Deducer → Deducer := fun k Γ Φ ψ ↦ dRwBy (evalRw G E (rules Φ) .full) k Γ Φ ψ
  let byNorm : Deducer := fun Γ Φ ψ ↦ (dEq (byMode .full G E 0 (rules Φ)) Γ Φ ψ).orElse fun _ ↦
    let nf (t : Internal.Term) : String := ((Internal.eval G E 0 (rules Φ) 4096 .full Γ Φ t).map
      fun (r : Internal.Term × Deriv × Bool) ↦ showT r.1).getD "none"
    match Internal.eqParts ψ with
    | some (a, b) => dbgTrace s!"unequal: {nf a}\n  vs {nf b}" fun _ ↦ none
    | none => none
  let allEΓ (t : List Tree → Internal.Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
    dAllE L G E (Φ.length - 1) (t Γ) k Γ Φ ψ
  let impE (kp k : Deducer) : Deducer := fun Γ Φ ψ ↦ dImpE L (Φ.length - 1) kp k Γ Φ ψ
  let unfoldConv (k : Deducer) : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw G E [.delta (S.q + 2)] .head) (Φ.length - 1) k Γ Φ ψ
  let exE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dExE L G E (Φ.length - 1) k Γ Φ ψ
  let conjE (k : Deducer) : Deducer := fun Γ Φ ψ ↦ dConjE L (Φ.length - 1) k Γ Φ ψ
  -- a tree term a node of new variables, its label and its children, by the lemma treeNode
  let dTreeNode (X : Internal.Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
    let some (Entry.language c) := E[ix "treeNode"]? | none
    let φX := Internal.instTerm [] [X] c.concl
    dCut φX (nd (.apply (ix "treeNode") [] [X])) (exE (exE k)) Γ Φ ψ
  -- the typing hypothesis decided by case analysis of the data its reduction waits on, bitstrings
  -- empty or a bit before a rest and bits zero or one, to a depth: each case refuted where the
  -- hypothesis reduces to falsity, else proved by k
  let splitWith (trees : Bool) (b ar : ℕ) (k : Deducer) : ℕ → Deducer := fun depth ↦ depth.rec
    (fun Γ Φ ψ ↦ ((refute Γ Φ ψ).orElse fun _ ↦ refuteF Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ)
    fun _ rec Γ Φ ψ ↦ ((refute Γ Φ ψ).orElse fun _ ↦ refuteF Γ Φ ψ).orElse fun _ ↦ do
      -- the formulas to decide: the typing hypothesis, then each child's typing, the children
      -- those of the arity's case
      let ψT ← Φ[hT]?
      let kids : List Internal.Term :=
        (List.range ar).map fun p ↦ v (Γ.length - b + 2 * (ar - 1 - p) + 1)
      let ty (c : Internal.Term) : Internal.Term := truth P.o (pc P "Prelude.isSome"
        [pc P "Check.typeIn" [v (Γ.length - 3), v (Γ.length - 5), c]])
      let goals := ψT :: kids.map ty
      -- a tree variable only where introduced past the arity's case, of length b
      let fresh (X : Internal.Term) : Bool := match X.label with
        | .var i => i + b < Γ.length
        | _ => true
      let tree (X : Internal.Term) : Bool :=
        trees ∧ Internal.typeIn G 0 Γ X = some treeTy ∧ fresh X
      let other (X : Internal.Term) : Bool :=
        let ty := Internal.typeIn G 0 Γ X
        ty = some bitsTy ∨ ty = some bitTy ∨
          (trees ∧ ty = some (list treeTy) ∧ isVar X ∧ fresh X)
      -- a tree the reduction waits on before any bitstring or list, so that a type's label and
      -- children are those of its node
      let found := goals.findSome? fun g ↦ do
        let (t, _) ← evalRw G E (rsV Φ) .head Γ Φ g
        let bs := (blocking t).reverse
        (bs.find? tree).orElse fun _ ↦ bs.find? other
      let some X := found | k Γ Φ ψ
      let ty := Internal.typeIn G 0 Γ X
      if ty = some bitTy then
        dBitCase L (ix "bitCases") X rec rec Γ Φ ψ
      else if ty = some treeTy then
        -- the tree a node of a new label and new children
        dTreeNode X rec Γ Φ ψ
      else if ty = some bitsTy then dListCase L G E (ix "listCases") bitTy X rec rec Γ Φ ψ
      else dListCase L G E (ix "listCases") treeTy X rec rec Γ Φ ψ
  let split := splitWith false
  -- truth, conjunctions and equations, after normalization
  let solve : ℕ → Deducer := fun d ↦ d.rec (fun _ _ _ ↦ none) fun _ rec ↦ norm fun Γ Φ ψ ↦
    if ψ == Internal.Logic.tt P.o then some Internal.Logic.trueI else
    match defnParts ψ with
    | some (i, _, _) => if i = P.o + 1 then dConjI L rec rec Γ Φ ψ else none
    | none => byNorm Γ Φ ψ
  -- the induction hypothesis at the child of position p, the formula at it cut in, normalized
  let dChild (p : ℕ) (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
    let (L₀, R₀) ← Internal.eqParts (← Φ[0]?)
    let A := nthOf L₀ p
    let B := nthOf R₀ p
    let (A', dA, _) ← Internal.eval G E 0 (rules Φ) 4096 .full Γ Φ A
    let (B', dB, _) ← Internal.eval G E 0 (rules Φ) 4096 .full Γ Φ B
    let (_, dAh, _) ← Internal.eval G E 0 [.hyp 0] 4096 .weak Γ Φ A
    let i₁ := Φ.length
    let q ← k Γ (Φ ++ [Term.eq A' B', A']) ψ
    pure (nd (.cut (Term.eq A' B')) [nd (.convFrom (Term.eq A B))
      [nd .cong [dA, dB], nd .join [dAh, nd .refl]],
      nd (.cut A') [nd .conv [nd (.rwHyp i₁ false), nd .join [nd .refl, nd .refl]], q]])
  -- the induction hypothesis at a child, instantiated at the globals' types, the definitions, the
  -- context and the environment, its antecedents proved: the definitions' and the environment's
  -- relations by kEnv, the typing by normalization; the conclusion, convergence, unfolded and its
  -- witnesses and parts added after the hypotheses
  let dIH (p : ℕ) (c env : List Tree → Internal.Term) (kEnv : Deducer) (k : Deducer) : Deducer :=
    dChild p (allEΓ (fun Γ ↦ v (Γ.length - 3)) (allEΓ (fun Γ ↦ v (Γ.length - 4)) (allEΓ c
      (allEΓ env (impE dHyp (impE kEnv (impE (solve 2) (unfoldConv (exE (exE (conjE k)))))))))))
  -- a universal hypothesis's instance, normalized, the last hypothesis
  let instN (h : ℕ) (t : List Tree → Internal.Term) (k : Deducer) : Deducer := fun Γ Φ ψ ↦
    dAllE L G E h (t Γ) (fun Γ Φ ψ ↦
      dRwHyp (evalRw G E (rules Φ.dropLast) .full) (Φ.length - 1) k Γ Φ ψ) Γ Φ ψ
  -- stability shifted to a later threshold, the sum of the hypothesis's threshold and another
  -- on its right (stabR) or on its left (stabL), cut in after the hypotheses
  let shift (h : ℕ) (left : Bool) (j : List Tree → Internal.Term) (k : Deducer) : Deducer :=
    fun Γ Φ ψ ↦ do
      let (F, n, w) ← stabParts P.o S.q (← Φ[h]?)
      let name := if left then "stabL" else "stabR"
      let some (Entry.language a) := E[ix name]? | none
      let σ := [j Γ, n, w, F]
      dCut (Internal.instTerm [] σ a.concl) (nd (.apply (ix name) [] σ) [nd (.hyp h)]) k Γ Φ ψ
  -- the last hypothesis's stability shifted
  let shiftLast (left : Bool) (j : List Tree → Internal.Term) (k : Deducer) : Deducer :=
    fun Γ Φ ψ ↦ shift (Φ.length - 1) left j k Γ Φ ψ
  -- the child of a position among k, in a context grown from the arity's case's of length base
  let child (k base p : ℕ) (Γ : List Tree) : Internal.Term :=
    v (Γ.length - base + 2 * (k - 1 - p) + 1)
  let cΓ (Γ : List Tree) : Internal.Term := v (Γ.length - 5)
  let eΓ (Γ : List Tree) : Internal.Term := v (Γ.length - 6)
  -- a hypothesis normalized, then the goal normalized and found among the hypotheses
  let byHyp (h : ℕ) : Deducer := fun Γ Φ ψ ↦
    (dRwHyp (evalRw G E (rulesEx Φ h) .full) h (norm dHyp) Γ Φ ψ).orElse fun _ ↦
      let nf (t : Internal.Term) : Option Internal.Term :=
        (evalRw G E (rulesEx Φ h) .full Γ Φ t).map Prod.fst
      let d := ((Φ[h]?).bind nf).bind fun a ↦ (nf ψ).bind fun b ↦ firstDiff a b
      dbgTrace s!"byHyp {h}: {d.map fun (a, b) ↦
        s!"{showT a}\n  vs {showT b}"}" fun _ ↦ none
  -- the index of the child of the arity's case, its label's leaf
  let index (b : ℕ) (Γ : List Tree) : Internal.Term := leafT (call D.lab [] [child 1 b 0 Γ])
  let K : Kit := ⟨P, S, E, ix, []⟩
  -- an application: the function's and the argument's hypotheses; the argument's type the
  -- function type's domain, by the equality's soundness; the function value's relation at the
  -- function type applied to the argument value, its application's threshold and value; the
  -- three thresholds' sum, the children evaluated a level above it and the application at it
  -- the type of the child of a position among two
  let tyAt (b p : ℕ) (Γ : List Tree) : Internal.Term :=
    pc P "Prelude.get" [pc P "Check.typeIn" [v (Γ.length - 3), cΓ Γ, child 2 b p Γ]]
  -- the hypothesis last cut in normalized, without itself
  let normLast (k : Deducer) : Deducer := fun Γ Φ ψ ↦
    (dRwHyp (evalRw G E (rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1) k Γ Φ ψ).orElse fun _ ↦
      let r := (Φ[Φ.length - 1]?).bind fun h ↦ evalRw G E (rulesEx Φ (Φ.length - 1)) .full Γ Φ h
      dbgTrace s!"normLast: {r.isSome} {(Φ[Φ.length - 1]?).map fun t ↦ showT t}
        {(Φ[Φ.length - 1]?).map fun t ↦ (Internal.typeIn G 0 Γ t).isSome}" fun _ ↦ none
  -- a component of a pair: the pair's type a product of new types; the child's hypothesis, its
  -- value's relation at the product type unfolded to a pair of related components, the component
  -- the witness
  let proj (b : ℕ) (second : Bool) : Deducer :=
    let tp (Γ : List Tree) : Internal.Term :=
      pc P "Prelude.get" [pc P "Check.typeIn" [v (Γ.length - 3), cΓ Γ, child 1 b 0 Γ]]
    split b 1 (norm fun Γ₀ Φ₀ ψ₀ ↦
      K.cutThm "isProdInv" (fun Γ ↦ [tp Γ]) (impE (solve 2) (exE (exE (normLast
        (split b 1 (norm (
    dIH 0 cΓ eΓ dHyp (fun Γ₁ Φ₁ ψ₁ ↦
      let s₀ := Φ₁.length - 2
      dRwHyp (evalRw G E (rules Φ₁.dropLast) .full) (Φ₁.length - 1)
        (exE (exE (conjE (conjE fun Γ Φ ψ ↦
          -- context: the second component, the first
          dConv L G E S (succN (v (Γ.length - Γ₁.length + 1))) (if second then v 0 else v 1)
            (instN s₀ (fun _ ↦ succN (v 0)) (byNorm))
            (norm ((fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦
              dRwHyp (evalRw G E (rules Φ.dropLast) .full) (Φ.length - (if second then 1 else 2))
                dHyp Γ Φ ψ))) Γ Φ ψ)))) Γ₁ Φ₁ ψ₁))) 24))))) Γ₀ Φ₀ ψ₀) 24
  -- after the function type's inversion: the tests decided again, the children's hypotheses
  let afterInv (b : ℕ) : Deducer := splitWith false b 2 (norm (
    dIH 0 cΓ eΓ dHyp (fun Γ₁ Φ₁ ψ₁ ↦
      let sf := Φ₁.length - 2
      let rf := Φ₁.length - 1
      dIH 1 cΓ eΓ dHyp (fun Γ₂ Φ₂ ψ₂ ↦
        let sx := Φ₂.length - 2
        let rx := Φ₂.length - 1
        -- the variables past Γ₂: the application's value and threshold
        let nf (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length + 3)
        let nx (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length + 1)
        let wx (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length)
        let ty (Γ : List Tree) (p : ℕ) : Internal.Term := tyAt b p Γ
        -- the argument's type equal to the function type's domain
        let childT := (primT Kernel.Prim.child).getD Term.star
        K.cutThm "equalSound" (fun Γ ↦ [ty Γ 1]) (allEΓ (fun Γ ↦
            apps childT [ty Γ 0, leafT bnilT]) (impE (solve 2) (normLast fun Γ₃ Φ₃ ψ₃ ↦
          let eqA := Φ₃.length - 1
          -- the function value's relation, at the argument value
          dRwHyp (evalRw G E (rulesEx Φ₃ rf) .full) rf (fun Γ Φ ψ ↦
            dAllE L G E (Φ.length - 1) (wx Γ) (impE (byHyp rx) (unfoldConv (exE (exE (conjE
              fun Γ Φ ψ ↦
                let sa := Φ.length - 2
                let ra := Φ.length - 1
                let na (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length - 1)
                let wa (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length - 2)
                let sum (Γ : List Tree) : Internal.Term := S.add (S.add (nf Γ) (nx Γ)) (na Γ)
                let _ := eqA
                shift sf false nx (shift (Φ.length) false na (shift sx true nf
                  (shift (Φ.length + 2) false na (shift sa true (fun Γ ↦ S.add (nf Γ) (nx Γ))
                    (fun Γ Φ ψ ↦
                      let f₂ := Φ.length - 4
                      let x₂ := Φ.length - 2
                      let a₁ := Φ.length - 1
                      dConv L G E S (succN (sum Γ)) (wa Γ)
                        (instN f₂ (fun _ ↦ succN (v 0)) (instN x₂ (fun _ ↦ succN (v 0))
                          (instN a₁ (fun _ ↦ v 0) (byNorm))))
                        ((byHyp ra)) Γ Φ ψ))))) Γ Φ ψ)))))
              Γ Φ ψ) Γ₃ Φ₃ ψ₃)))
        Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁))) 40
  let appCase (b : ℕ) : Deducer := splitWith false b 2 (norm fun Γ₀ Φ₀ ψ₀ ↦
    -- the function's type an arrow of new types
    K.cutThm "isArrowInv" (fun Γ ↦ [tyAt b 0 Γ])
      (impE (solve 2) (exE (exE (normLast (afterInv b))))) Γ₀ Φ₀ ψ₀) 40
  -- the type of the child of a position among three
  let tyAt3 (b p : ℕ) (Γ : List Tree) : Internal.Term :=
    pc P "Prelude.get" [pc P "Check.typeIn" [v (Γ.length - 3), cΓ Γ, child 3 b p Γ]]
  -- a conditional: the three children's hypotheses; the condition's type the tree type and the
  -- branches' types equal, by the equality's soundness; the condition's value a quotation, its
  -- label empty or not selecting the second branch's value or the first's; the thresholds' sum
  let condCase (b : ℕ) : Deducer := splitWith false b 3 (norm (
    dIH 0 cΓ eΓ dHyp fun Γ₁ Φ₁ ψ₁ ↦
      let sc := Φ₁.length - 2
      let rc := Φ₁.length - 1
      dIH 1 cΓ eΓ dHyp (fun Γ₂ Φ₂ ψ₂ ↦
        let sa := Φ₂.length - 2
        let ra := Φ₂.length - 1
        dIH 2 cΓ eΓ dHyp (fun Γ₃ Φ₃ ψ₃ ↦
          let sb := Φ₃.length - 2
          let rb := Φ₃.length - 1
          -- the variables at Γ₃, and past it the condition's quoted tree
          let at3 (k : ℕ) (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₃.length + k)
          let nc := at3 5
          let na := at3 3
          let wa := at3 2
          let nb := at3 1
          let wb := at3 0
          let branch (second : Bool) : Deducer :=
            -- the stabilities shifted to the sum, the condition's on the right twice, the first
            -- branch's on the left and the right, the second's on the left
            shift sc false na (shiftLast false nb (shift sa true nc
              (shiftLast false nb (shift sb true (fun Γ ↦ S.add (nc Γ) (na Γ))
                (fun Γ Φ ψ ↦
                  let c₂ := Φ.length - 4
                  let a₂ := Φ.length - 2
                  let b₁ := Φ.length - 1
                  dConv L G E S (succN (S.add (S.add (nc Γ) (na Γ)) (nb Γ)))
                    (if second then wb Γ else wa Γ)
                    (instN c₂ (fun _ ↦ succN (v 0)) (instN a₂ (fun _ ↦ succN (v 0))
                      (instN b₁ (fun _ ↦ succN (v 0)) (byNorm))))
                    ((byHyp (if second then rb else ra))) Γ Φ ψ)))))
          -- the condition's type the tree type: its value a quotation
          K.cutThm "equalSound" (fun Γ ↦ [tyAt3 b 0 Γ]) (allEΓ (fun _ ↦ leafT bnilT)
            (impE (solve 2) (normLast (fun Γ₄ Φ₄ ψ₄ ↦
              dRwHyp (evalRw G E (rulesEx Φ₄ rc) .full) rc (exE (fun Γ Φ ψ ↦
                -- the branches' types equal
                K.cutThm "equalSound" (fun Γ ↦ [tyAt3 b 2 Γ]) (allEΓ (fun Γ ↦ tyAt3 b 1 Γ)
                  (impE (solve 2) (normLast (fun Γ Φ ψ ↦
                    dRwHyp (evalRw G E (rulesEx Φ rb) .full) rb (fun Γ Φ ψ ↦
                      -- the quoted tree's label: empty selects the second branch
                      let q := v (Γ.length - Γ₃.length - 1)
                      let X := (nfE G E (rsV Φ) Γ (call D.lab [] [q])).getD Term.star
                      K.listCase bitTy X ((branch true))
                        ((branch false)) Γ Φ ψ) Γ Φ ψ)))) Γ Φ ψ)) Γ₄ Φ₄ ψ₄))))
            Γ₃ Φ₃ ψ₃) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁)) 40
  -- a construction of a list: the tail's type a list type of new element type, the children's
  -- hypotheses; the head's type that element type, by the equality's soundness; the tail's value
  -- a list value, its test decided, whose elements are related; the construction's value a list
  -- value whose elements are the head and the tail's
  let consAfter (b : ℕ) : Deducer :=
    dIH 0 cΓ eΓ dHyp fun Γ₁ Φ₁ ψ₁ ↦
      let sx := Φ₁.length - 2
      dIH 1 cΓ eΓ dHyp (fun Γ₂ Φ₂ ψ₂ ↦
        let sxs := Φ₂.length - 2
        let rxs := Φ₂.length - 1
        let at2 (k : ℕ) (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length + k)
        let nx := at2 3
        let wx := at2 2
        let nxs := at2 1
        let wxs := at2 0
        let w (Γ : List Tree) : Internal.Term := nodeT (Term.pair (numeral Kernel.Label.cons)
          (consT treeTy (wx Γ) (consT treeTy (wxs Γ) (nilT treeTy))))
        let fin : Deducer := fun Γ Φ ψ ↦
          let x₁ := Φ.length - 2
          let xs₁ := Φ.length - 1
          dConv L G E S (succN (S.add (nx Γ) (nxs Γ))) (w Γ)
            (instN x₁ (fun _ ↦ succN (v 0)) (instN xs₁ (fun _ ↦ succN (v 0))
              (byNorm)))
            ((K.auto 5)) Γ Φ ψ
        -- the tail's value a list value: its test decided, its elements related
        let afterList : Deducer := conjE fun Γ Φ ψ ↦
          K.splitHyp (Φ.length - 2) (shift sx false nxs (shift sxs true nx fin)) 8 Γ Φ ψ
        let afterEq : Deducer := fun Γ Φ ψ ↦
          dRwHyp (evalRw G E (rulesEx Φ rxs) .full) rxs afterList Γ Φ ψ
        let childT := (primT Kernel.Prim.child).getD Term.star
        K.cutThm "equalSound" (fun Γ ↦ [tyAt b 0 Γ]) (allEΓ (fun Γ ↦
            apps childT [tyAt b 1 Γ, leafT bnilT]) (impE (solve 2) (normLast afterEq)))
          Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
  let consCase (b : ℕ) : Deducer := splitWith false b 2 (norm fun Γ₀ Φ₀ ψ₀ ↦
    K.cutThm "isListInv" (fun Γ ↦ [tyAt b 1 Γ])
      (impE (solve 2) (exE (normLast (splitWith false b 2 (norm (consAfter b)) 40))))
      Γ₀ Φ₀ ψ₀) 40
  -- the primitive's index, its label's normal form compared with the numerals
  let primName (b : ℕ) (Γ : List Tree) (Φ : List Internal.Term) : Option String := do
    let (t, _) ← evalRw G E (rules Φ) .full Γ Φ (call D.lab [] [child 1 b 0 Γ])
    let k ← (List.range 14).find? fun j ↦
      (evalRw G E (rules Φ) .full Γ Φ (numeral j)).map Prod.fst == some t
    pure s!"relPrim{k}"
  -- the bits of the primitive's index decided, each variable of a bit or of bits among its
  -- normal form split in turn, to a depth
  let decideIndex (b : ℕ) (k : Deducer) : ℕ → Deducer := fun depth ↦ depth.rec k
    fun _ rec Γ Φ ψ ↦ do
      let (t, _) ← evalRw G E (rules Φ) .full Γ Φ (call D.lab [] [child 1 b 0 Γ])
      let vars := RoseTree.para (fun (l : Internal.Label) cs ↦
        (match l with
          | .var i => [Term.var i]
          | _ => []) ++ cs.flatMap (·.2)) t
      match vars.find? fun X ↦ Internal.typeIn G 0 Γ X = some bitTy with
      | some X => dBitCase L (ix "bitCases") X rec rec Γ Φ ψ
      | none => match vars.find? fun X ↦ Internal.typeIn G 0 Γ X = some bitsTy with
        | some X => dListCase L G E (ix "listCases") bitTy X rec rec Γ Φ ψ
        | none => k Γ Φ ψ
  -- a constant: its typing decided, its value itself at fuel one, related by the constant's
  -- lemma at the instance σ, the lemma named by the context and the hypotheses
  let constCase (lbl ar : ℕ) (name : List Tree → List Internal.Term → Option String)
      (σ : ℕ → List Tree → List Internal.Term) (b : ℕ) : Deducer :=
    splitWith false b ar ((if lbl = Kernel.Label.prim then fun k ↦ decideIndex b k 8 else id)
      (norm fun Γ Φ ψ ↦
      -- a primitive's value the node over the leaf of its index's label
      let kids := (List.range ar).map fun p ↦
        if lbl = Kernel.Label.prim then leafT (call D.lab [] [child ar b p Γ]) else child ar b p Γ
      let nd := nodeT (Term.pair (numeral lbl) (kids.foldr (consT treeTy) (nilT treeTy)))
      match name Γ Φ with
      | some nm =>
        dConv L G E S (succN zeroN) nd (byNorm)
          (K.cutThm nm (σ b) (fun Γ Φ ψ ↦ byHyp (Φ.length - 1) Γ Φ ψ)) Γ Φ ψ
      | none => dbgTrace "constant: no lemma" fun _ ↦ none)) 40
  let Dv (Γ : List Tree) : Internal.Term := v (Γ.length - 4)
  let cases : List (ℕ × (ℕ → Deducer)) :=
    [(Kernel.Label.quote, fun b ↦ norm fun Γ Φ ψ ↦
      let c₀ := child 1 b 0 Γ
      dConv L G E S (succN zeroN) (pc P "Eval.valQuote" [c₀]) byNorm
        (norm (dExI L G E c₀ byNorm)) Γ Φ ψ),
     (Kernel.Label.unit, fun _ ↦ norm fun Γ Φ ψ ↦
      dConv L G E S (succN zeroN) (pc P "Eval.valUnit" []) byNorm (norm byNorm) Γ Φ ψ),
     (Kernel.Label.nil, fun b ↦ split b 0 (norm <| fun Γ Φ ψ ↦
      dConv L G E S (succN zeroN) (nodeT (Term.pair (numeral Kernel.Label.nil)
          (consT treeTy (child 1 b 0 Γ) (nilT treeTy)))) (byNorm)
        (norm ((solve 4))) Γ Φ ψ) 24),
     (Kernel.Label.fst, fun b ↦ proj b false), (Kernel.Label.snd, fun b ↦ proj b true),
     (Kernel.Label.app, appCase), (Kernel.Label.cond, condCase),
     (Kernel.Label.cons, consCase),
     (Kernel.Label.fold, fun b ↦ constCase Kernel.Label.fold 1 (fun _ _ ↦ some "relFold")
       (fun b Γ ↦ [child 1 b 0 Γ, Dv Γ]) b),
     (Kernel.Label.para, fun b ↦ constCase Kernel.Label.para 1 (fun _ _ ↦ some "relPara")
       (fun b Γ ↦ [child 1 b 0 Γ, Dv Γ]) b),
     (Kernel.Label.iter, fun b ↦ constCase Kernel.Label.iter 1 (fun _ _ ↦ some "relIter")
       (fun b Γ ↦ [child 1 b 0 Γ, Dv Γ]) b),
     (Kernel.Label.foldr, fun b ↦ constCase Kernel.Label.foldr 2 (fun _ _ ↦ some "relFoldr")
       (fun b Γ ↦ [child 2 b 1 Γ, child 2 b 0 Γ, Dv Γ]) b),
     (Kernel.Label.lcase, fun b ↦ constCase Kernel.Label.lcase 2 (fun _ _ ↦ some "relLcase")
       (fun b Γ ↦ [child 2 b 1 Γ, child 2 b 0 Γ, Dv Γ]) b),
     (Kernel.Label.prim, fun b ↦ constCase Kernel.Label.prim 1 (primName b)
       (fun _ Γ ↦ [Dv Γ]) b),
     -- an abstraction: its closure, related at the function type by the body's hypothesis in
     -- the context and the environment each extended, the environments' relation by envCons
     (Kernel.Label.lam, fun b ↦ split b 0 (norm fun Γ₀ Φ₀ ψ₀ ↦
      let A₀ := child 2 b 0 Γ₀
      let B₀ := child 2 b 1 Γ₀
      let clo := pc P "Eval.valClo" [eΓ Γ₀, A₀, B₀]
      dConv L G E S (succN zeroN) clo byNorm (norm (dAllI L (dImpI L fun Γ₁ Φ₁ ψ₁ ↦
        -- context: the argument; the extended context and environment
        let cA (Γ : List Tree) : Internal.Term := consT treeTy (child 2 b 0 Γ) (cΓ Γ)
        let eY (Γ : List Tree) : Internal.Term :=
          consT treeTy (v (Γ.length - Γ₁.length)) (eΓ Γ)
        let envOk : Deducer := fun Γ _ _ ↦
          let σ := [v (Γ.length - Γ₁.length), child 2 b 0 Γ, eΓ Γ, cΓ Γ, v (Γ.length - 4)]
          some (nd (.apply (ix "envCons") [] σ) [nd (.hyp 6), nd (.hyp (Φ₁.length - 1))])
        dIH 1 cA eY envOk (fun Γ Φ ψ ↦
          let s := Φ.length - 2
          let r := Φ.length - 1
          let n := v (Γ.length - Γ₁.length - 1)
          let w := v (Γ.length - Γ₁.length - 2)
          dConv L G E S (succN n) w (instN s (fun _ ↦ v 0) (byNorm))
            ((byHyp r)) Γ Φ ψ) Γ₁ Φ₁ ψ₁))) Γ₀ Φ₀ ψ₀) 24),
     -- a variable: the environment's relation at its index, a value and its relation
     (Kernel.Label.var, fun b ↦ split b 0 (norm <| fun Γ₀ Φ₀ ψ₀ ↦
      dRwHyp (evalRw G E [.delta (S.q + 4)] .head) 6 (fun Γ Φ ψ ↦
        dAllE L G E (Φ.length - 1) (index b Γ) (impE (byHyp hT)
          (exE (conjE <| fun Γ Φ ψ ↦
        let w := v (Γ.length - Γ₀.length - 1)
        dRwHyp (evalRw G E (rules Φ.dropLast.dropLast) .full) (Φ.length - 2) (fun Γ Φ ψ ↦
          dConv L G E S (succN zeroN) w (byNorm)
            ((byHyp (Φ.length - 2))) Γ Φ ψ) Γ Φ ψ))) Γ Φ ψ) Γ₀ Φ₀ ψ₀) 0),
     -- a reference: the definitions' relation at its index, a definition, its evaluation's
     -- threshold and value and the value's relation; the definition evaluated a level below
     (Kernel.Label.ref, fun b ↦ split b 0 (norm <| fun Γ₀ Φ₀ ψ₀ ↦
      dRwHyp (evalRw G E [.delta (S.q + 7)] .head) 5 (fun Γ Φ ψ ↦
        dAllE L G E (Φ.length - 1) (index b Γ) (impE (byHyp hT)
          (exE (conjE fun Γ₁ Φ₁ ψ₁ ↦
        let e := Φ₁.length - 2
        unfoldConv (exE (exE (conjE fun Γ Φ ψ ↦
          let s := Φ.length - 2
          let r := Φ.length - 1
          -- context: the value, the threshold, introduced past Γ₁
          let n := v (Γ.length - Γ₁.length - 1)
          let w := v (Γ.length - Γ₁.length - 2)
          dRwHyp (evalRw G E (rulesEx Φ e) .full) e (fun Γ Φ ψ ↦
            dConv L G E S (succN n) w (instN s (fun _ ↦ v 0) (byNorm))
              ((byHyp r)) Γ Φ ψ) Γ Φ ψ))) Γ₁ Φ₁ ψ₁))) Γ Φ ψ) Γ₀ Φ₀ ψ₀)
        0),
     (Kernel.Label.pair, fun b ↦ split b 2 (norm <| fun Γ₀ Φ₀ ψ₀ ↦
      -- the children's hypotheses, each adding its threshold and value and the stability and the
      -- relation, the last two hypotheses
      dIH 0 cΓ eΓ dHyp (fun Γ₁ Φ₁ ψ₁ ↦
        let h₀ := Φ₁.length - 2
        let r₀ := Φ₁.length - 1
        dIH 1 cΓ eΓ dHyp (fun Γ₂ Φ₂ ψ₂ ↦
          let h₁ := Φ₂.length - 2
          let r₁ := Φ₂.length - 1
          -- context: the second value, its threshold, the first value, its threshold
          let n₀ (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length + 3)
          let n₁ (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length + 1)
          let w₀ (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length + 2)
          let w₁ (Γ : List Tree) : Internal.Term := v (Γ.length - Γ₂.length)
          shift h₀ false n₁ (shift h₁ true n₀ (fun Γ Φ ψ ↦
            let s₀ := Φ.length - 2
            let s₁ := Φ.length - 1
            dConv L G E S (succN (S.add (n₀ Γ) (n₁ Γ))) (pc P "Eval.valPair" [w₀ Γ, w₁ Γ])
              (instN s₀ (fun _ ↦ succN (v 0)) (instN s₁ (fun _ ↦ succN (v 0))
                (byNorm)))
              (norm ((dExI L G E (w₀ Γ) (dExI L G E (w₁ Γ)
                (dConjI L (solve 2) (dConjI L (dRwHyp (evalRw G E (rules Φ) .full) r₀ dHyp)
                  (dRwHyp (evalRw G E (rules Φ) .full) r₁ dHyp)))))))
              Γ Φ ψ)) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁) Γ₀ Φ₀ ψ₀) 24)]
  let leaf (bs : Option (List Bool)) : Deducer := fun Γ Φ ψ ↦
    let r? := bs.map Oitavem.rank
    let k? : Option ℕ := bs.bind fun bs ↦ arityOf' (Oitavem.rank bs)
    (if k?.isSome then none else refute Γ Φ ψ).orElse fun _ ↦
      match k? with
      | some k =>
        let valid : Deducer := fun Γ Φ ψ ↦
          match (r?.bind fun r ↦ cases.find? fun (c : ℕ × (ℕ → Deducer)) ↦ c.1 = r) with
          | some (_, c) => match c Γ.length Γ Φ ψ with
            | some d => some d
            | none => dbgTrace s!"case failed: {r?}: {showT ψ}" fun _ ↦ none
          | none => dbgTrace s!"open valid: {r?}" fun _ ↦ some (nd .refl)
        (arity valid k (v (Γ.length - 2)) Γ Φ ψ).orElse fun _ ↦
          dbgTrace s!"arity failed: {bs.map Oitavem.rank}" fun _ ↦ none
      | none =>
        let h := ((Φ[hT]?).bind fun ψ ↦ evalRw G E (rsV Φ ++ [.delta (P.idx "Check.checkNode")])
          .head Γ Φ ψ).map fun (p : Internal.Term × Deriv) ↦ showT p.1
        dbgTrace s!"not refuted: {bs.map Oitavem.rank} {h}" fun _ ↦ none
  let intros : Deducer → Deducer := fun k ↦ dAllI L (dAllI L (dAllI L (dAllI L
    (dImpI L (dImpI L (dImpI L k))))))
  let node := Internal.roseNodeAt 2 treeTy bitsTy φ
  intros (fun Γ Φ ψ ↦ dBits L G E (ix "listCases") (ix "bitCases") leaf 4 [] (v 5) Γ Φ ψ)
    [list treeTy, bitsTy] [Internal.roseHyp 0 1 φ] node

/-- The fundamental lemma at the extended program: its formula over a tree. -/
def fundamentalThm (P : Prog) (S : Defs) : Internal.Thm := ⟨0, [treeTy], [], fundamental P S⟩

/-- The developments of the fundamental lemma in the extended program, each with the name of its
certificate: the base, the convergence lemmas, the constants' relations, and the lemma itself, by
induction on rose trees, each proved after the theorems of those before it; the reason where a
lemma is not proved. -/
def certificates (P : Prog) (S : Defs) : Except String (List (String × List Decl)) := do
  let some base := baseDev P S | throw "the base is not stated"
  let (n₁, E₁, ds₁) ← developAfter [] #[] base
  let (n₂, E₂, ds₂) ← developAfter n₁ E₁ (constDev P S)
  let (n₃, E₃, ds₃) ← developAfter n₂ E₂ (relDev P S)
  let thms := n₃.zip (E₃.toList.filterMap Entry.language?)
  let some d := fundamentalDeriv P S thms | throw "the fundamental lemma is not proved"
  pure [("normalization-base", ds₁), ("normalization-const", ds₂), ("normalization-rel", ds₃),
    ("normalization", [Decl.language (fundamentalThm P S) (nd (.roseIndHyp 2 0 1) [d])])]

end GebTests.Prototypes.FreeTopos.Normalization

end
