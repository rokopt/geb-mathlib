/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Weakening -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Weakening -- shake: keep

set_option doc.verso true in
/-!
# Substitution preserves types

The kernel's type checker written in Geb preserves types by substitution, proved in the internal
language about the translation of the programs: for every environment {lit}`G`, contexts
{lit}`c1` and {lit}`c`, type {lit}`a` and terms {lit}`u` and {lit}`t`, if the checker infers the
type {lit}`a` for {lit}`u` in {lit}`c`, then the type it infers for {lit}`t` with {lit}`u`,
weakened past {lit}`c1`, substituted for the variable below {lit}`c1`, in the context of
{lit}`c1` and {lit}`c`, is the type it infers for {lit}`t` in the context of {lit}`c1`,
{lit}`a` and {lit}`c`. The substitution of Gödel's T for the innermost variable is the instance
at the empty {lit}`c1`. The program is the weakening proof's, with the statement's two sides as
definitions.

The statement is an equation between two functions, into the subobject classifier, of the
environment, the contexts, the type and the substituted term: the implication of the equation of
the two sides by the typing of the substituted term, and truth. It is proved by induction on rose
trees with the induction hypothesis, as weakening is, each case by extensionality and the
introduction of the implication, under its antecedent, which rewrites the substituted term's type
to the type. At a label whose case depends on its children's types, the induction hypothesis's
instances at the children are implications with that antecedent, whose conclusions modus ponens
cuts in. At the substituted variable, the substituted term's type in the context of {lit}`c1` and
{lit}`c` is its type in {lit}`c`, by weakening past a list of types; the lookups before, at and
past the substituted variable's index are the lookup in the context with it, by induction on
{lit}`c1`, with lemmas on the successors of bitstrings.

## Main definitions

* {lit}`substitution` — the statement.
* {lit}`development` — the lemmas, each with its proof, after the weakening proof's and the
  weakening theorem.
* {lit}`bySubLabels` — the proof at a construction.

## Tags

internal language, type checker, substitution, induction, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Substitution

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-! The program. -/

/-- The two sides of the statement, as definitions of the program: the type of a term with a
term, weakened past a context's first part, substituted for the variable below it, in the
context without that variable, and the term's type in the context with it; and the two sides of
the lemmas on the variable's case, the lookups at a variable's index before, at and past the
substituted one, with the substituted term's type at it, and the lookup in the context with the
substituted variable, and the same lookups past the head of the first part. -/
def statement : String := "
(def sbL (lam ((t T) (G Ts) (c1 Ts) (c Ts) (a T) (u T))
  (typeIn G (append c1 c) (trav (substVar u) t (length c1)))))
(def sbR (lam ((t T) (G Ts) (c1 Ts) (c Ts) (a T) (u T)) (typeIn G (append c1 (cons a c)) t)))
(def svL (lam ((c1 Ts) (c Ts) (a T) (t T))
  (if (lt (label t) (length c1)) (nth (append c1 c) (label t))
    (if (eq (label t) (length c1)) (some a) (nth (append c1 c) (sub (label t) 1))))))
(def svR (lam ((c1 Ts) (c Ts) (a T) (t T)) (nth (append c1 (cons a c)) (label t))))
(def svS (lam ((c1 Ts) (m Ts) (a T) (y T) (t T))
  (if (lt (label t) (length c1)) (nth m (label t))
    (if (eq (label t) (length c1)) (some a) (nth (cons y m) (label t))))))
(def svT (lam ((c1 Ts) (m Ts) (a T) (y T) (t T))
  (if (lt (label t) (length c1)) (nth m (label t))
    (if (eq (label t) (length c1)) (some a) (nth m (sub (label t) 1))))))"

/-- The program: the weakening proof's, and the statement. -/
def programText : String := Weakening.programText ++ "\n" ++ statement

/-! The statement. -/

/-- A term under the abstractions of the environment, the contexts' two parts, the type and the
substituted term, innermost last. -/
def lams5 (b : Term) : Term :=
  Term.lam (list treeTy) (Term.lam (list treeTy) (Term.lam (list treeTy)
    (Term.lam treeTy (Term.lam treeTy b))))

/-- The statement's function of the environment, the contexts, the type and the substituted term,
in a context of a term: the implication of the equation of the two sides by the typing of the
substituted term. -/
def subF (P : Prog) : Term :=
  -- under the abstractions: the term, the environment, the contexts, the type and the term
  let typed := Term.eq (apps (call (P.idx "Check.typeIn") [] []) [v 4, v 2, v 0])
    (apps (call (P.idx "Prelude.some") [] []) [v 1])
  let side (name : String) : Term := apps (call (P.idx name) [] []) [v 5, v 4, v 3, v 2, v 1, v 0]
  lams5 (Internal.Logic.imp P.o typed (Term.eq (side "sbL") (side "sbR")))

/-- The statement: the implication, as a function of the environment, the contexts, the type and
the substituted term, is truth. -/
def substitution (P : Prog) : Internal.Thm :=
  ⟨0, [treeTy], [], Term.eq (subF P) (lams5 (Internal.Logic.tt P.o))⟩

/-! The development. -/

/-- The rules of the lemmas at successors and of the variable's case, before
{name}`rulesNth`. -/
def rulesSub (P : Prog) (ix : String → ℕ) : List NormRule :=
  [.thm (ix "svStepP") [], .thm (ix "eqSuccP") [], .thm (ix "nilSucc") [],
    .thm (ix "eqZeroSucc") [], .thm (ix "subSucc") [], .thm (ix "dblSucc") [],
    .thm (ix "predSucc") [], .thm (ix "condSucc₁") [bitsTy], .thm (ix "condSucc₁") [ordTy],
    .thm (ix "rebD") []] ++ rulesNth P ix

/-- The weakening theorem, and its instance below no part of the context: the type of a term
weakened past a context's first part, in the context, is its type in the rest. -/
def weakeningSteps (P : Prog) : List Step :=
  let wkZ := weakThm P 0 [treeTy, list treeTy, list treeTy, list treeTy]
    (apps (call (P.idx "Check.typeIn") [] [])
      [v 1, apps (call (P.idx "Prelude.append") [] []) [v 2, v 3],
        apps (call (P.idx "Equations.wk") [] [])
          [apps (call (P.idx "Prelude.length") [] []) [v 2], v 0]])
    (apps (call (P.idx "Check.typeIn") [] []) [v 1, v 3, v 0])
  let a := weakening P
  [step "weakening" a (fun ix E ↦
      Internal.byRoseIndHyp 2 0 1 (byLabels P ix E) a.ctx [] (sides a).1 (sides a).2),
    step "wkZero" wkZ (fun ix E ↦ do
      -- the weakening's sides at the term, applied to the environment, no first part, the
      -- context's first part as the inserted types, and the rest
      let α := [v 1, nilT treeTy, v 2, v 3]
      let F := apps (Term.app (call (P.idx "wkL") [] []) (v 0)) α
      let H := apps (Term.app (call (P.idx "wkR") [] []) (v 0)) α
      let (_, dF, _) ← Internal.eval P.G E 0 (baseNorm P) 4096 .weak wkZ.ctx [] F
      let (_, dH, _) ← Internal.eval P.G E 0 (baseNorm P) 4096 .weak wkZ.ctx [] H
      let rw : Deriv := α.foldl (fun d _ ↦ RoseTree.node .cong [d, RoseTree.node .refl []])
        (RoseTree.node (.thm (ix "weakening") [] [v 0] false) [])
      pure (RoseTree.node (.convFrom (Term.eq F H)) [RoseTree.node .cong [dF, dH],
        RoseTree.node .join [rw, RoseTree.node .refl []]]))]

/-- The lemmas at successors: the rebuilding of a bitstring by doubling's fold; a conditional on
a successor, which is not empty, is its first branch; the predecessor, the double and the
difference with one of a successor; equality of zero and a successor, emptiness of a successor,
and equality of two successors as that of their predecessors, as functions of the first. -/
def succLemmas (P : Prog) : Option (List Step) := do
  let sc (t : Term) : Term := call D.succ [] [t]
  let (zD, sD) ← (lib[D.dbl]?).bind fun d ↦ firstFold d.body
  let rebD : Internal.Thm := ⟨0, [bitsTy], [], Term.eq (Term.fst (Term.listRec zD sD (v 0))) (v 0)⟩
  let condNE := weakThm P 1 [bitsTy, x 0, x 0] (condT (x 0) (sc (v 0)) (v 1) (v 2)) (v 1)
  let predSucc := weakThm P 0 [bitsTy] (call D.pred [] [sc (v 0)]) (v 0)
  let dblSucc := weakThm P 0 [bitsTy] (call D.dbl [] [sc (v 0)]) (consT bitTy bit1T (v 0))
  let subSucc := weakThm P 0 [bitsTy] (call D.sub [] [sc (v 0), numeral 1]) (v 0)
  let eqZS := weakThm P 0 [bitsTy] (call D.eqB [] [bnilT, sc (v 0)]) bnilT
  let nilS := weakThm P 0 [bitsTy] (call D.isNil [bitTy] [sc (v 0)]) bnilT
  let eqSucc : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitsTy (call D.eqB [] [sc (v 0), sc (v 1)]))
    (Term.lam bitsTy (call D.eqB [] [v 0, v 1]))⟩
  let auto (ix : String → ℕ) (E : Array Entry) : Internal.Prover :=
    byAuto P.G E 0 (rulesSub P ix) 2 .open
  let side (a : Internal.Thm) (p : Internal.Prover) : Option Deriv :=
    p a.ctx [] (sides a).1 (sides a).2
  pure [
    step "rebD" rebD (fun _ E ↦ side rebD (byListIndWeak P.G E 0 (consT bitTy (v 1) (v 0))
      (baseNorm P))),
    step "condSucc₁" condNE (fun ix E ↦ side condNE
      (bitsCases P.G 1 (byMode .weak P.G E 1 (rulesSub P ix)))),
    step "predSucc" predSucc (fun ix E ↦ side predSucc (byBitsIndHyp P.G E (rulesSub P ix) .weak)),
    step "dblSucc" dblSucc (fun ix E ↦ side dblSucc (byBitsIndHyp P.G E (rulesSub P ix) .weak)),
    step "subSucc" subSucc (fun ix E ↦ side subSucc (bitsCases P.G 0 (auto ix E))),
    step "eqZeroSucc" eqZS (fun ix E ↦ side eqZS (bitsCases P.G 0 (auto ix E))),
    step "nilSucc" nilS (fun ix E ↦ side nilS (bitsCases P.G 0 (auto ix E))),
    -- induction on the second number, as functions of the first: at a bit before a list by
    -- case analysis of the bit, then of the first number, then of its first bit
    step "eqSucc" eqSucc (fun ix E ↦
      let bit (i : ℕ) (p : Internal.Prover) : Internal.Prover := bySplit2 3 4 i p p
      side eqSucc (Internal.byListIndWith P.G 0 0 1
        (Internal.byFunExt P.G 0 (byAuto P.G E 0 (rulesSub P ix) 8 .open))
        (Internal.byFunExt P.G 0 (bit 2 (byListSplit P.G 0 1 (auto ix E)
          (bit 1 (auto ix E))))))),
    pointwise P (rulesSub P) .open "eqSuccP" "eqSucc" bitsTy]

/-- The lemmas on the variable's case, as functions of its index: past the head of the context's
first part, the lookup below the variable is the lookup in the rest at the index before, where
the index is neither below nor at the first part's length; and the type of a variable with the
substituted term's type for the variable below the first part is its type in the context with
the substituted variable, by induction on the first part. -/
def varLemmas (P : Prog) : List Step :=
  let side (a : Internal.Thm) (p : Internal.Prover) : Option Deriv :=
    p a.ctx [] (sides a).1 (sides a).2
  let stSide (name : String) : Term := Term.lam bitsTy
    (apps (call (P.idx name) [] []) [v 1, v 2, v 3, v 4, leafT (v 0)])
  let svStep : Internal.Thm := ⟨0, [list treeTy, list treeTy, treeTy, treeTy], [],
    Term.eq (stSide "svS") (stSide "svT")⟩
  let svSide (name : String) : Term := Term.lam bitsTy
    (apps (call (P.idx name) [] []) [v 1, v 2, v 3, leafT (v 0)])
  let substNth : Internal.Thm := ⟨0, [list treeTy, list treeTy, treeTy], [],
    Term.eq (svSide "svL") (svSide "svR")⟩
  -- the index zero, or the successor of the predecessor of a bit before a bitstring
  let byIndex (ix : String → ℕ) (E : Array Entry) : Internal.Prover :=
    let auto := byAuto P.G E 0 (rulesSub P ix) 2 .open
    Internal.byFunExt P.G 0 (byListSplit P.G 0 0 auto (bySuccPred E (ix "succPredP") auto))
  [step "svStep" svStep (fun ix E ↦ side svStep (byIndex ix E)),
    pointwise P (rulesSub P) .open "svStepP" "svStep" bitsTy,
    step "substNth" substNth (fun ix E ↦ side substNth
      (Internal.byListIndWith P.G 0 0 1 (byIndex ix E) (byIndex ix E))),
    pointwise P (fun ix ↦ lemmaRules ix ++ baseNorm P) .weak "substNthP" "substNth" bitsTy]

/-- The development: the weakening proof's, the weakening theorem and its instance below no part,
and the lemmas at successors and on the variable's case. -/
def development (P : Prog) : Option (List Step) := do
  pure ((← Weakening.development P) ++ weakeningSteps P ++ (← succLemmas P) ++ varLemmas P)

/-- The rules of the proof at a label: the weakening proof's, the weakening's instance below no
part, and the variable's case. -/
def subRules (ix : String → ℕ) : List NormRule :=
  lemmaRules ix ++ [.thm (ix "wkZero") [], .thm (ix "substNthP") []]

/-! Proofs under the antecedent. -/

/-- The proof at a label: under the statement's arguments and the antecedent, whose weak normal
form rewrites, by weak reduction of the sides; or, for a label whose case depends on the
children's types, by case analysis of the list of the children to their number, the induction
hypothesis reverted and, at that number, instantiated at each child, at the arguments, and for
an abstraction's body at the first context extended by the abstraction's type, each instance's
conclusion cut in by modus ponens and rewriting after the language's rules and before the
lemmas. -/
def subLeaf (P : Prog) (lemmas : List NormRule) (E : Array Entry) (bits : Option (List Bool)) :
    Internal.Prover := fun Γ Φ t u ↦ do
  let rs := baseNorm P ++ lemmas
  -- extensionality, the implication introduced and its antecedent in weak normal form
  let under (k : ℕ → List NormRule → Internal.Prover) : Internal.Prover :=
    funExts 5 P.G (byImpI P.G E P.o logicBase fun Γ Φ t u ↦
      withWeakHyps P.G E 0 rs [Φ.length - 1] (fun ex ↦ k (Φ.length) ex) (m := .weak) Γ Φ t u)
  let plain : Internal.Prover := under fun _ ex ↦ byWeak P.G E 0 (baseNorm P ++ ex ++ lemmas)
  let k? := bits.bind fun bs ↦ arityOf (Oitavem.rank bs)
  match k? with
  | none =>
    let base : Internal.Prover := under fun _ ex ↦ byWeak P.G E 0 (baseNorm P ++ ex)
    (base Γ Φ t u).orElse fun _ ↦ plain Γ Φ t u
  | some k => do
    -- the children's list: the variable the induction hypothesis folds
    let (L, _) ← Internal.eqParts (← Φ[0]?)
    let i ← match (L.children[2]?).map (·.label) with
      | some (Internal.Label.var j) => some j
      | _ => none
    let some (_, (CR, sR, fG)) := folds P | none
    let rest : Internal.Prover := fun Γ Φ t u ↦ do
      let child (p : ℕ) : Term := v (5 + 2 * (k - 1 - p) + 1)
      let A := Term.fst (Term.app (Term.roseRec CR sR (child 0))
        (Term.rename fG fun j ↦ if j = 1 then 4 else j))
      let ih := Φ.length - 1
      under (fun hA exA ↦ withChildHyps P.G E 0 rs ih (List.range k) (fun p ↦
          [[v 4, v 3, v 2, v 1, v 0]] ++
            if p = 1 then [[v 4, consT treeTy A (v 3), v 2, v 1, v 0]] else [])
        (fun insts ↦ withWeakHyps P.G E 0 rs insts (m := .weak) fun extra ↦
          withImpElim P.o logicBase hA (extra.filterMap hypIndex) fun concls ↦
            byWeak P.G E 0 (baseNorm P ++ concls ++ exA ++ lemmas))) Γ Φ t u
    let levels : ℕ → Internal.Prover := fun m ↦ m.rec rest fun _ next ↦
      fun Γ Φ t u ↦ revertCase P.G 0 P.o logicBase 0 (Φ.length - 1) plain next Γ Φ t u
    revertCase P.G 0 P.o logicBase i 0 plain (levels (k - 1)) Γ Φ t u

/-- The proof at a construction: case analysis of the label's bits, to five of them, each case
proved by {lit}`subLeaf` with the bits of a label ending there, or none past the fourth. -/
def bySubLabels (P : Prog) (lemmas : List NormRule) (E : Array Entry) : Internal.Prover :=
  let go : ℕ → List Bool → ℕ → Internal.Prover := fun d ↦ d.rec
    (fun bs i ↦ byListSplit P.G 0 i (subLeaf P lemmas E (some bs)) (subLeaf P lemmas E none))
    fun _ rec bs i ↦ byListSplit P.G 0 i (subLeaf P lemmas E (some bs))
      (bySplit2 3 4 1 (rec (bs ++ [false]) 1) (rec (bs ++ [true]) 1))
  go 4 [] 1

/-- The proof of the statement, found and checked with the development, for the program's
definitions with the index of each named one, and the measurement: the nodes of the development's
derivations and of the statement's, and the milliseconds its proof and its check take; an error
where either fails. -/
def checkSubstitution (ds : List (List Char × Tree)) (idx : String → ℕ) : IO Unit := do
  let some P := prog? ds idx | throw (IO.userError "the program does not translate")
  let some dev := development P | throw (IO.userError "the development is not stated")
  let decls ← match developNamed dev with
    | .ok decls => pure decls
    | .error name => throw (IO.userError s!"the lemma {name} is not proved")
  let some (G, E) := Internal.checkDev P.G #[] decls
    | throw (IO.userError "the development does not check")
  let ix (name : String) : ℕ := (dev.findIdx? (·.1 == name)).getD 0
  let a := substitution P
  let t₀ ← IO.monoMsNow
  let some d := Internal.byRoseIndHyp 2 0 1
      (bySubLabels P (Internal.prepareRules E (subRules ix)) E) a.ctx [] (sides a).1 (sides a).2
    | throw (IO.userError "the statement is not proved")
  let t₁ ← IO.monoMsNow
  if !Internal.checkThms G [Decl.language a d] E then
    throw (IO.userError "the statement's derivation does not check")
  let t₂ ← IO.monoMsNow
  let devNodes := (decls.filterMap fun | Decl.language _ d => some (derivSize d) | _ => none).sum
  IO.println "development_nodes,theorem_nodes,proof_milliseconds,check_milliseconds"
  IO.println s!"{devNodes},{derivSize d},{t₁ - t₀},{t₂ - t₁}"

#eval do
  let some ds := bundled GoedelT.ProofTests.bundler.toList programText.toList
    | throw (IO.userError "the program does not read")
  checkSubstitution ds fun name ↦ (defIndex ds name.toList).getD 0

end GebTests.Prototypes.FreeTopos.Substitution

end
