/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.DatatypeLists
public meta import GebTests.Prototypes.FreeTopos.DatatypeLists -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The datatype language's soundness at every tree

The soundness of the datatype language's stage-1 compiler at every tree, by induction on rose
trees ({lit}`sound`): at a node, the soundness at each child the hypothesis of induction, read as
the soundness at every element of the children ({lit}`datatypeRoseAll`); the node's label decided,
an atom's by {name}`GebTests.Prototypes.FreeTopos.Datatypes.atomCase`, a list's by
{name}`GebTests.Prototypes.FreeTopos.Datatypes.listCase`, and any other refuted by the typing, the
expansion of such a node being the leaf 0, which no type is given. The statement takes as
hypotheses the soundness at the lists headed by the keywords whose forms later developments prove
sound ({name}`GebTests.Prototypes.FreeTopos.Datatypes.laterKeywords`).

## Main definitions

* {lit}`soundThm` — the soundness at every tree, given that at the lists headed by the later
  keywords.
* {lit}`sound` — its proof.
* {lit}`soundCertificates` — the development, after those of the soundness at atoms, at lists and
  at applications.

## References

* {cite}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, soundness, rose trees, induction
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Datatypes

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.Weakening
open scoped FinEnum

open Internal (Term)
open GebTests.Prototypes.FreeTopos.Normalization

/-- The soundness at every tree, the variable of index 0, given that at every list headed by a
keyword of {name}`laterKeywords`. -/
def soundThm (P : Prog) (S : Defs) (T : Defs3) : Internal.Thm :=
  ⟨0, [treeTy], laterKeywords.map (headedφ P S T), datatypeφ P S T⟩

/-- The soundness at every tree ({name}`soundThm`), by induction on rose trees: at a node, the
hypothesis of induction the soundness at every child ({lit}`datatypeRoseAll`); the node's label
decided, an atom's by {name}`atomCase`, a list's by {name}`listCase`, any other refuted, the
statement's hypotheses introduced, by the tests of the node's expansion, typing and source form
decided ({name}`splitSolve`). -/
def sound (P : Prog) (S : Defs) (T : Defs3) : Step :=
  ("sound", fun ix E ↦ do
    let K := appKit P S ix E
    let L := K.L
    let a := soundThm P S T
    let nH := (datatypeParts P S T (v nQ)).1.length
    let unfold := ((List.range nFolds).map T.argIdx ++
      ["Typing.synList", "Reader.resolveList"].map P.idx).map Internal.NormRule.delta
    -- the last hypothesis renormalized and the goal normalized, the one the other
    let closeLast : Deducer := fun Γ Φ ψ ↦
      dRwHyp (evalRw K.G K.E (K.rulesEx Φ (Φ.length - 1)) .full) (Φ.length - 1)
        (K.norm dHyp) Γ Φ ψ
    -- the instance of a theorem at terms of the context, its hypotheses proved, cut in
    let cutApply (name : String) (σ : List Tree → List Term) (prems : List Deducer)
        (k : Deducer) : Deducer := fun Γ Φ ψ ↦ do
      let some (Internal.Entry.language b) := K.E[K.ix name]? | none
      let ds ← (b.hyps.zip prems).mapM fun (h, d) ↦ d Γ Φ (Internal.instTerm [] (σ Γ) h)
      dCut (Internal.instTerm [] (σ Γ) b.concl) (nd (.apply (K.ix name) [] (σ Γ)) ds) k Γ Φ ψ
    -- context: the children, the label; hypotheses: the later keywords' soundness, the
    -- hypothesis of induction
    let kids (Γ : List Tree) : Term := atPos 1 Γ
    -- a node of another label refuted: the statement's hypotheses introduced, the tests of its
    -- expansion, its typing and its source form decided until one of them is false
    let refute : Deducer := fun Γ₀ Φ₀ ψ₀ ↦
      let hyp (i : ℕ) : ℕ := Φ₀.length + nQ + i
      ((List.range nQ).foldr (fun _ k ↦ dAllI L k)
        ((List.range nH).foldr (fun _ k ↦ dImpI L k)
          (linkK K "sound: a node of another label" <| dFalse L <| splitSolve K
            (fun Φ ↦ K.rules Φ ++ unfold) (fun _ ↦ [hyp 5, hyp 6, hyp 4]) 24
            ((List.range nFolds).map T.foldIdx) .full))) Γ₀ Φ₀ ψ₀
    let step : Deducer := fun Γ Φ ψ ↦
      let nL := laterKeywords.length
      (cutApply "datatypeRoseAll" (fun Γ ↦ [kids Γ]) [] <|
        K.impE dHyp <| fun Γ Φ ψ ↦
        let X := ((evalRw K.G K.E (K.rules Φ) .full Γ Φ (atPos 0 Γ)).map Prod.fst).getD
          (atPos 0 Γ)
        dBits L K.G K.E (ix "listCases") (ix "bitCases") (fun bs ↦
          match bs.map Oitavem.rank with
          | some 1 => linkK K "sound: an atom" <|
              cutApply "atomCase" (fun Γ ↦ [kids Γ]) [] closeLast
          | some 2 => linkK K "sound: a list" <|
              cutApply "listCase" (fun Γ ↦ [kids Γ])
                (List.replicate (nL + 1) dHyp) closeLast
          | _ => refute) 2 [] X Γ Φ ψ) Γ Φ ψ
    let some d := (do
        let d₁ ← step [list treeTy, bitsTy] (a.hyps.map Internal.weaken2 ++
          [Internal.roseHyp 0 1 a.concl]) (Internal.roseNodeAt 2 treeTy bitsTy a.concl)
        pure (nd (.roseIndHyp 2 0 1) [d₁]))
      | dbgTrace "sound: not proved" fun _ ↦ none
    pure (a, d))

/-- The development of the soundness at every tree: the hypothesis of induction on rose trees at
the soundness as the soundness at every child, and the soundness. -/
def soundDev3 (P : Prog) (S : Defs) (T : Defs3) : List Step :=
  [roseAllFor P S "datatypeRoseAll" (datatypeφ P S T), sound P S T]

/-- The development of the soundness at every tree ({name}`soundDev3`), after the base's, the
atom's, the list's, the stage functions' at applications, the applications', the list
expansion's, the soundness at applications', at abstractions, at representations and at lists',
stored as the certificate {lit}`datatype-sound`. -/
def soundCertificates (P : Prog) (S : Defs) (T : Defs3) (before : List Internal.Thm) :
    Except String (List (String × List Internal.Decl)) := do
  let some names := listNames P S T | throw "the base is not stated"
  certifyAfter P (names ++ (stagesDev3 P S T).map (·.1) ++ (applyDev3 P S T).map (·.1) ++
    (expansionDev3 P S T).map (·.1) ++ (assemblyDev3 P S T).map (·.1) ++
    (appDev3 P S T).map (·.1) ++ (lamDev3 P S T).map (·.1) ++ (dataDev3 P S T).map (·.1) ++
    (listsDev3 P S T).map (·.1))
    "datatype-sound" (soundDev3 P S T) before

end GebTests.Prototypes.FreeTopos.Datatypes

end
