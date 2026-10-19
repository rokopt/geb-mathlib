/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeApp -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeApp -- shake: keep
public import GebTests.Prototypes.FreeTopos.DatatypeApply -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.DatatypeApply -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at abstractions over lists of binders

The soundness of the datatype language's stage-1 compiler
({lit}`GebTests.Prototypes.FreeTopos.DatatypeBase`) at an abstraction over a list of binders, from
that at an abstraction over one ({lit}`GebTests.Prototypes.FreeTopos.DatatypeApp`). The expansion
writes an abstraction over a list of binders as the abstractions over each binder in turn, each
over a list of one, so that the soundness at the expanded form follows from that at an abstraction
over any one binder by induction on the list, and the soundness at the source form from that at
its expansion. An abstraction over no binders has no expansion, so that the hypothesis of the
expansion's presence refutes that case.

## Main definitions

* {lit}`nest` — the soundness at the abstractions over each binder of a list in turn, by
  induction on the list.
* {lit}`lamCase` — the soundness at an abstraction at source forms.
* {lit}`lamCertificates` — the development, after the base's, the atom's, the list's, the
  abstraction's over one binder and the stage functions' at applications.

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

/-- A hypothesis decided by case analysis of the bits its weak head normal form is blocked on, by
the rules with the definitions {lit}`unfold` unfolded as well, to a depth: a case refuted where
that form is falsity; where it is blocked on no bits, or at the depth, refuted by normalization,
else proved by k. Unlike {name}`Kit.splitHyp`, which normalizes the hypothesis in full at each
case, it decides the head first, which a hypothesis about forms whose parts are variables needs,
its normal form in full being of a size the decisions alone bound. -/
def splitHead (K : Kit) (h : ℕ) (k : Deducer) (depth : ℕ) (unfold : List ℕ := []) : Deducer :=
  let rs (Φ : List Term) : List Internal.NormRule :=
    K.rulesEx Φ h ++ (unfold ++ [K.P.idx "charsFixed"]).map Internal.NormRule.delta
  let refute : Deducer := fun Γ Φ ψ ↦
    dRwHyp (evalRw K.G K.E (rs Φ) .full) h (dFalse K.L dHyp) Γ Φ ψ
  (Nat.rec (motive := fun _ ↦ Deducer) (fun Γ Φ ψ ↦ (refute Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ)
  (fun _ rec Γ Φ ψ ↦ do
    let (t, _) ← evalRw K.G K.E (rs Φ) .head Γ Φ (← Φ[h]?)
    if t == Internal.Logic.ff K.P.o then
      dRwHyp (evalRw K.G K.E (rs Φ) .head) h (dFalse K.L dHyp) Γ Φ ψ
    else
    let some X := (blocking t).reverse.find? fun X ↦
        let ty := Internal.typeIn K.G 0 Γ X
        ty = some bitsTy ∨ ty = some bitTy
      | (refute Γ Φ ψ).orElse fun _ ↦ k Γ Φ ψ
    if Internal.typeIn K.G 0 Γ X = some bitTy then K.bitCase X rec rec Γ Φ ψ
    else K.listCase bitTy X rec rec Γ Φ ψ) depth)

/-- The form of an abstraction over a list of one binder, any tree, in a body, the elements of a
context of the binder and the body, the outermost first. -/
def lamBinderForm (P : Prog) : Term := listNode [kwAtom P "Reader.kwLam", listNode [v 1], v 0]

/-- The soundness at an abstraction over one binder, any tree, at expanded forms, given that at
the body. -/
def lamBinderThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  kwThm P S T "Reader.kwLam" 2 [false, true] true (lamBinderForm P)

/-- The soundness at an abstraction over one binder, any tree, at expanded forms: the binder a node,
its label and children decided; a name at an annotation, the label that of lists and the children
two, the soundness at an abstraction over one binder ({lit}`lamOneCase`), the binder rewritten to
its node; any other binder refutes the typing's hypothesis. -/
def lamBinder (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamBinder", fun ix E ↦ do
    let W₀ := kwKit P S T ix E 2 [false, true] "Reader.kwLam" true
    let W := { W₀ with K := { W₀.K with more := W₀.K.more ++ ["rawListR"] } }
    let K := W.K
    let a := lamBinderThm P S T
    -- the statement's hypotheses introduced, after the decisions' variables and hypotheses, and
    -- the typing's refuted
    let bad (msg : String) : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let W' := { W with n := Γ₀.length, ihs := List.replicate Φ₀.length true }
      W'.intro "Reader.kwLam" (linkK K s!"lamBinder: {msg}" fun Γ Φ ψ ↦
        let h := W'.hyp 6
        splitHead K h (fun _ _ _ ↦ none) 8 W.ks Γ Φ ψ) Γ₀ Φ₀ ψ₀
    -- the binder a name at an annotation: the abstraction over it sound, the goal's binder and the
    -- labels written as bits
    let good (px pA : ℕ) : Deducer := fun Γ Φ ψ ↦
      let bits := [D.bnil, D.b0, D.b1].map Internal.NormRule.delta
      let rs := eqHyps Φ ++ bits
      linkK K "lamBinder: the binder's abstraction" (W.cutApply "lamOneCase"
        (fun Γ ↦ [atPos 1 Γ, atPos pA Γ, atPos px Γ]) [K.byHyp 0] fun Γ Φ ψ ↦
          dRwHyp (evalRw K.G K.E bits .full) (Φ.length - 1)
            (dRwBy (evalRw K.G K.E rs .full) dHyp) Γ Φ ψ) Γ Φ ψ
    let decide : Deducer := K.treeNode (v 1) fun Γ₁ Φ₁ ψ₁ ↦
      let pcs := Γ₁.length - 1
      K.listCase bitTy (v 1) (bad "the label empty") (fun Γ₂ Φ₂ ψ₂ ↦
        K.bitCase (v 1) (bad "the label's first bit zero") (K.listCase bitTy (v 0)
          (fun Γ₃ Φ₃ ψ₃ ↦ K.listCase treeTy (atPos pcs Γ₃) (bad "no children") (fun Γ₄ Φ₄ ψ₄ ↦
            let px := Γ₄.length - 2
            K.listCase treeTy (v 0) (bad "one child") (fun Γ₅ Φ₅ ψ₅ ↦
              let pA := Γ₅.length - 2
              K.listCase treeTy (v 0) (good px pA) (bad "more children") Γ₅ Φ₅ ψ₅) Γ₄ Φ₄ ψ₄)
            Γ₃ Φ₃ ψ₃)
          (bad "the label long")) Γ₂ Φ₂ ψ₂) Γ₁ Φ₁ ψ₁
    let some d := decide a.ctx a.hyps a.concl
      | dbgTrace "lamBinder: not proved" fun _ ↦ none
    pure (a, d))

/-- The abstractions over each binder of a list in turn, the first outermost, each over a list of
one binder, around a body: the expansion's writing of an abstraction over the list. -/
def nestT (P : Prog) (bs body : Term) : Term :=
  foldrT treeTy treeTy (Term.lam treeTy (Term.lam treeTy
    (listNode [kwAtom P "Reader.kwLam", listNode [v 1], v 0]))) body bs

/-- The soundness at the abstractions over each binder of a list in turn around a body, given that
at the body, in the context of the list and the body, by induction on the list: at the empty list
the body itself, and at a binder before a list the abstraction over the binder of those over the
list, by {lit}`lamBinder`. The forms are compared after β-reduction and the folds' reductions. -/
def nest (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("nest", fun ix E ↦ do
    let K : Kit := ⟨P, S, E, ix, []⟩
    let L := K.L
    -- the last hypothesis and the goal reduced, the goal found among the hypotheses
    let red : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E Translation.baseRules .full) (Φ.length - 1)
        (dRwBy (evalRw K.G K.E Translation.baseRules .full) dHyp) Γ Φ ψ
    let φ := Internal.Logic.imp P.o (expandedAt P S T (v 1))
      (expandedAt P S T (nestT P (v 0) (v 1)))
    let some d₀ := dImpI L red [treeTy] []
        (Term.subst φ (Internal.instVar (Term.arr 0 [treeTy] Term.star)))
      | dbgTrace "nest: nil" fun _ ↦ none
    -- the hypothesis of induction at the body's soundness, then the abstraction over the binder
    -- of those over the rest of the list, by the soundness at an abstraction over one binder
    let lamAt : Deducer := fun Γ Φ ψ ↦ do
      let some (Internal.Entry.language b) := K.E[K.ix "lamBinder"]? | none
      let σ := [nestT P (v 0) (v 2), v 1]
      dCut (Internal.instTerm [] σ b.concl)
        (nd (.apply (K.ix "lamBinder") [] σ) [nd (.hyp (Φ.length - 1))]) red Γ Φ ψ
    let some d₁ := dImpI L (dImpE L 0 dHyp lamAt)
        [list treeTy, treeTy, treeTy] [Internal.weakenElem φ] (Internal.listConsAt 1 treeTy φ)
      | dbgTrace "nest: cons" fun _ ↦ none
    pure (⟨0, [list treeTy, treeTy], [], φ⟩, nd (.listIndHyp 0 1) [d₀, d₁]))

/-- The names of the equations of the stage functions at an abstraction at source forms. -/
def lamSrcEqs (ix : String → ℕ) (E : Array Internal.Entry) : List String :=
  ((List.range nFolds).map fun k ↦ kwEqName "Reader.kwLam" 2 k ++ "/src").filter
    fun nm ↦ 0 < ix nm ∧ ix nm < E.size

/-- The soundness at an abstraction at source forms, given that at the body. -/
def lamSrcThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  kwThm P S T "Reader.kwLam" 2 [false, true]

/-- The soundness at an abstraction at source forms: the elements' expansions present, generalized;
the binders, as the expansion reads them from the expanded list of binders, decided: none, the
expansion is absent, which refutes the hypothesis of its presence; a binder and the rest, the
expansion is the abstraction over the binder of those over the rest, sound by {lit}`nest` at the
expanded body, sound by {lit}`expSound`, its statement instantiated at the statement's variables
and its antecedents the statement's. -/
def lamCase (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("lamCase", fun ix E ↦ do
    let W₀ := kwKit P S T ix E 2 [false, true]
    let W := { W₀ with K := { W₀.K with more := W₀.K.more ++ lamSrcEqs ix E ++ ["rawListR"] } }
    let K := W.K
    let a := lamSrcThm P S T
    let opt (c : ℕ) (Γ : List Tree) : Term := W.inΓ (atPos c) Γ (W.expansion (v nQ))
    -- the last hypothesis, the soundness at the expansion, at the statement's variables
    let atStatement : Deducer := fun Γ Φ ψ ↦
      dAllE K.L K.G K.E (Φ.length - 1) (W.qv 1 Γ) (((List.range (nQ - 1)).foldr
        (fun j k ↦ K.allEΓ (W.qv (j + 2)) k) <|
        (List.range W.nH).foldr (fun i k ↦ K.impE (linkK K s!"lam: antecedent {i}"
          (K.byHyp (W.hyp i))) k)
          (linkK K "lam: the conclusion" fun Γ Φ ψ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ))) Γ Φ ψ
    -- the binders none: the expansion absent
    let none_ : Deducer := linkK K "lam: no binders" fun Γ Φ ψ ↦
      (K.hypFalse (W.hyp 5) Γ Φ ψ).orElse fun _ ↦ W.hypFalseU (W.hyp 5) Γ Φ ψ
    -- the binders a binder and the rest: the expanded body sound, the nesting sound
    let cons : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let pH := Γ₀.length - 2
      let pT := Γ₀.length - 1
      let yT (Γ : List Tree) : Term := pc P "Prelude.get" [pc P "Datatype.expandExpr"
        [W.qv 3 Γ, atPos 1 Γ]]
      linkK K "lam: the expanded body" (W.cutApply "expSound" (fun Γ ↦ [atPos 1 Γ]) [dHyp] <|
        K.allEΓ (W.qv 3) <| K.impE (linkK K "lam: the body's expansion" (K.solve 3)) <|
        linkK K "lam: the nesting" (W.cutApply "nest"
          (fun Γ ↦ [consT treeTy (atPos pH Γ) (atPos pT Γ), yT Γ])
          [fun Γ Φ ψ ↦ (dHyp Γ Φ ψ).orElse fun _ ↦ K.byHyp (Φ.length - 1) Γ Φ ψ] <|
        K.impE (fun Γ Φ ψ ↦ dHyp Γ Φ ψ) atStatement)) Γ₀ Φ₀ ψ₀
    -- the binders' expansion at pB, generalized by the first decision, whose position the
    -- second's case analysis of its labels moves from the end of the context
    let binders (pB : ℕ) : Deducer := fun Γ Φ ψ ↦
      let bs := ((evalRw K.G K.E (K.rules Φ) .full Γ Φ
        (pc P "Datatype.bindersTx" [atPos pB Γ])).map Prod.fst).getD Term.star
      K.listCase treeTy bs none_ cons Γ Φ ψ
    let decisions : Deducer :=
      W.present "element 1's expansion" (opt 0) 5 fun Γ Φ ψ ↦
        (W.present "element 2's expansion" (opt 1) 5 (binders (Γ.length - 1)) : Deducer) Γ Φ ψ
    let some d := W.intro "Reader.kwLam" decisions a.ctx a.hyps a.concl
      | dbgTrace "lamCase: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at abstractions over lists of binders. -/
def lamDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  kwEqs P T "Reader.kwLam" 2 (lamBinderForm P) true ++
    [lamBinder P S T, nest P S T] ++
    kwEqs P T "Reader.kwLam" 2 (tag := "/src") ++ [lamCase P S T]

/-- The development of the soundness at abstractions over lists of binders, after the base's,
the atom's, the list's, the abstraction's over one binder and the stage functions' at
applications, stored as the certificate {lit}`datatype-lam`. -/
def lamCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (appDev3 P S T).map (·.1) ++ (stagesDev3 P S T).map (·.1))
    "datatype-lam" (lamDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
