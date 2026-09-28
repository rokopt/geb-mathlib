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
# Case analysis of trees and rewriting under a test

Two provers of the internal language beyond those of the weakening proof, and the lemmas that
exercise them, about the translation of the prelude, the reader, the type checker and the
expansion of the datatype language.

Case analysis of a tree variable in any context: the induction on rose trees applies to a tree
alone, so the sides at a tree of a new label and new children are proved instead, their
abstractions over the label and the children are equal functions by extensionality, and applied
to the components of the variable's unfolding they are the sides at the tree rebuilt from it,
which is the variable by Lambek's lemma; the rewriting from the rebuilt tree back to the variable
is computed from the term, occurrence by occurrence. With it, the proof by reduction splits the
variable a normal form is stuck on, whether a list, a bit or a tree.

Rewriting under a test: in the branch a conditional selects, a term may be replaced by another
that a lemma equates with it under the same test. The branch is abstracted over the term's
occurrences, the occurrences become the conditional on the test between the term and anything,
by the absorption lemma, the lemma rewrites that conditional, and absorption removes it.

The lemmas: a conditional between two lists with one head, absorption, and a conditional between
two terms of one value; the soundness of the equality of bitstrings, as the conditional on it
between its arguments being the second, and, as the test of the rewriting, a bitstring replaced by
another under the test of their equality; the children of the tree of a label and children; and a
tree the reader names by the atom {lit}`def`, the head of a definition's form, which the
case analysis of the tree, of its children and of their labels' bits proves to be that atom.

## Main definitions

* {lit}`byTreeSplit` — case analysis of a tree variable.
* {lit}`byAutoT` — proof by reduction and case analysis of the variables it is stuck on.
* {lit}`abstractTerm`, {lit}`maskRw` — the abstraction over a term's occurrences, and the
  rewriting under a test.
* {lit}`development` — the lemmas, each with its proof.

## Tags

internal language, case analysis, rose tree, conditional, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.TreeCases

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-- The program: the prelude, the reader, the type checker and the expansion of the datatype
language. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Kernel.Stage0Tests.datatype

/-! Case analysis of a tree. -/

/-- The rewriting of a term in which a tree rebuilt from the unfolding of its variable of index
{lit}`i` stands for the variable, back to the term: at each occurrence of the variable, the pair
of the unfolding's components is the unfolding, and the tree rebuilt from it is the variable,
Lambek's lemma of index {lit}`lk`. Folds' starts and steps, in contexts of their own, do not
mention it. -/
def occRewrite (lk i : ℕ) : Term → ℕ → Deriv := RoseTree.para fun l cs d ↦
  let refl : Deriv := RoseTree.node .refl []
  let j := i + d
  match l with
  | .var k =>
    if k = j then RoseTree.node .trans [RoseTree.node .cong [RoseTree.node .pairEta []],
      RoseTree.node (.thm lk [] [Term.var j] false) []]
    else refl
  | .lam _ => RoseTree.node .cong (cs.map fun (_, r) ↦ r (d + 1))
  | .natRec | .listRec => RoseTree.node .cong (cs.zipIdx.map fun ((_, r), k) ↦
      if k = 2 then r d else refl)
  | .roseRec _ => RoseTree.node .cong (cs.zipIdx.map fun ((_, r), k) ↦
      if k = 1 then r d else refl)
  | _ =>
    if cs.all fun (c, _) ↦ Internal.uses c j = 0 then refl
    else RoseTree.node .cong (cs.map fun (_, r) ↦ r d)

/-- The proof of an equation by case analysis on the tree variable of index {lit}`i`: the sides
at a tree of a new label and new children are proved by {lit}`p`, so that, by extensionality,
their abstractions over the label and the children are equal functions; applied to the
components of the variable's unfolding, they are the sides at the tree rebuilt from it, which
is the variable by Lambek's lemma, the entry of index {lit}`lk`. -/
def byTreeSplit (lk i : ℕ) (p : Internal.Prover) : Internal.Prover :=
  fun Γ Φ t u ↦ do
    let c ← Γ[i]?
    if c ≠ treeTy then none else
    let F := Internal.abstractVar i c t
    let H := Internal.abstractVar i c u
    let N₀ := nodeT (Term.pair (v 1) (v 0))
    let A := Term.app (Internal.weaken2 F) N₀
    let B := Term.app (Internal.weaken2 H) N₀
    let q ← p (list treeTy :: bitsTy :: Γ) (Φ.map Internal.weaken2) A B
    let Fl := Term.lam bitsTy (Term.lam (list treeTy) A)
    let Hl := Term.lam bitsTy (Term.lam (list treeTy) B)
    let beta : Deriv := RoseTree.node .beta []
    let refl : Deriv := RoseTree.node .refl []
    let betaBoth : Deriv := RoseTree.node .cong [beta, beta]
    let dG := RoseTree.node .funExt [RoseTree.node .conv [betaBoth,
      RoseTree.node .funExt [RoseTree.node .conv [betaBoth, q]]]]
    let U := unnodeU (v i)
    let applied (L : Term) : Term := Term.app (Term.app L (Term.fst U)) (Term.snd U)
    let χ := Term.eq (applied Fl) (applied Hl)
    let side (w : Term) : Deriv := RoseTree.node .trans [RoseTree.node .cong [beta, refl],
      RoseTree.node .trans [beta, RoseTree.node .trans [beta, occRewrite lk i w 0]]]
    let dχ := RoseTree.node .join [RoseTree.node .cong [RoseTree.node .cong
      [RoseTree.node (.rwHyp Φ.length false) [], refl], refl], refl]
    pure (RoseTree.node (.cut (Term.eq Fl Hl))
      [dG, RoseTree.node (.convFrom χ) [RoseTree.node .cong [side t, side u], dχ]])

/-- The proof of an equation by reducing both sides to one normal form, with the instances of the
hypotheses it starts with where there are any, or else by case analysis of a variable the normal
forms are stuck on, a list, a coproduct or a tree, each case the same way, to a depth; Lambek's
lemma is the entry of index {lit}`lk`. Each goal's sides are reduced once. -/
def byAutoT (G : Internal.Globals) (E : Array Entry) (n lk : ℕ) (rs : List NormRule) (d : ℕ)
    (m : Internal.Depth := .weak) : Internal.Prover := fun Γ₀ Φ₀ t₀ u₀ ↦
  let hs := Φ₀.length
  let direct : Internal.Prover := fun Γ Φ t u ↦ do
    let (t', dt, _) ← Internal.eval G E n rs 4096 m Γ Φ t
    let (u', du, _) ← Internal.eval G E n rs 4096 m Γ Φ u
    if t' = u' then some (RoseTree.node .join [dt, du]) else none
  let solve : Internal.Prover := fun Γ Φ t u ↦ (direct Γ Φ t u).orElse fun _ ↦
    if hs = 0 then none else byInsts m G E n rs hs Γ Φ t u
  (d.rec solve fun _ rec Γ Φ t u ↦ do
    let (t', dt, _) ← Internal.eval G E n rs 4096 m Γ Φ t
    let (u', du, _) ← Internal.eval G E n rs 4096 m Γ Φ u
    if t' = u' then some (RoseTree.node .join [dt, du]) else
    (if hs = 0 then none else byInsts m G E n rs hs Γ Φ t u).orElse fun _ ↦ do
    let skip (i : ℕ) : Bool := (Φ.take hs).any (mentions · i)
    let i ← ((stuckVar skip t').orElse fun _ ↦ stuckVar skip u').orElse fun _ ↦
      (stuckVar (fun _ ↦ false) t').orElse fun _ ↦ stuckVar (fun _ ↦ false) u'
    let c ← Γ[i]?
    match Internal.listPart c, Internal.coprodParts c with
    | some _, _ => byListSplit G n i rec rec Γ Φ t u
    | none, some _ => bySplit2 3 4 i rec rec Γ Φ t u
    | none, none => if c = treeTy then byTreeSplit lk i rec Γ Φ t u else none :
    Internal.Prover) Γ₀ Φ₀ t₀ u₀

/-! Rewriting under a mask. -/

/-- The abstraction, over a new variable of the type {lit}`b`, of a term's occurrences of the
term {lit}`x`: the function whose application to {lit}`x` is the term. Folds' starts and steps,
in contexts of their own, are left in place. -/
def abstractTerm (b : Tree) (x y : Term) : Term :=
  let xw := Internal.weaken1 x
  let go : Term → ℕ → Term := RoseTree.para fun l cs d ↦
    if RoseTree.node l (cs.map (·.1)) = Term.rename xw (· + d) then Term.var d else
    match l with
    | .lam _ => RoseTree.node l (cs.map fun (_, r) ↦ r (d + 1))
    | .natRec | .listRec => RoseTree.node l (cs.zipIdx.map fun ((c, r), k) ↦
        if k = 2 then r d else c)
    | .roseRec _ => RoseTree.node l (cs.zipIdx.map fun ((c, r), k) ↦
        if k = 1 then r d else c)
    | _ => RoseTree.node l (cs.map fun (_, r) ↦ r d)
  Term.lam b (go (Internal.weaken1 y) 0)

/-- The proof that a conditional of the type {lit}`a` on the test {lit}`c`, between {lit}`y` and
{lit}`d`, is the conditional between {lit}`y` with {lit}`x'` for {lit}`x` and {lit}`d`: by the
absorption lemma of index {lit}`ab`, the occurrences of {lit}`x`, of the type {lit}`b`, are the
conditional on the same test between {lit}`x` and {lit}`z`, which the masked lemma of index
{lit}`j`, at the objects {lit}`θ` and the terms {lit}`σ`, equates with the conditional between
{lit}`x'` and {lit}`z`, which absorption removes. -/
def maskRw (a b : Tree) (ab j : ℕ) (θ : List Tree) (σ : List Term) (c d x x' z y : Term) :
    Deriv :=
  let F := abstractTerm b x y
  let refl : Deriv := RoseTree.node .refl []
  let beta : Deriv := RoseTree.node .beta []
  let χ := Term.eq (condT a c (Term.app F x) d) (condT a c (Term.app F x') d)
  let dχ := RoseTree.node .join [RoseTree.node .trans
    [RoseTree.node (.thm ab [a, b] [c, d, x, z, F] true) [],
      RoseTree.node .trans [RoseTree.node .cong [refl, RoseTree.node .cong
        [refl, RoseTree.node (.thm j θ σ false) []], refl],
        RoseTree.node (.thm ab [a, b] [c, d, x', z, F] false) []]], refl]
  RoseTree.node (.convFrom χ) [RoseTree.node .cong
    [RoseTree.node .cong [refl, beta, refl], RoseTree.node .cong [refl, beta, refl]], dχ]

/-! The lemmas. -/

/-- The proof of a theorem's equation by a prover, in its context and without hypotheses. -/
def side (a : Internal.Thm) (p : Internal.Prover) : Option Deriv :=
  p a.ctx [] (sides a).1 (sides a).2

/-- The lemmas of conditionals on bitstrings: a conditional between two lists with one head is
the head before the conditional between the tails; inside the branch a test selects, a conditional
on the same test is its first branch; and the soundness of the equality of bitstrings, as the
conditional on it between its arguments being the second, as a function of the second. -/
def genericLemmas (P : Prog) : Option (List Step) := do
  let rLf ← lcaseRebuild P.G (baseNorm P)
  let X := x 0
  let Y := x 1
  let condCons := weakThm P 1 [bitsTy, list X, list X, X]
    (condT (list X) (v 0) (consT X (v 3) (v 2)) (consT X (v 3) (v 1)))
    (consT X (v 3) (condT (list X) (v 0) (v 2) (v 1)))
  let absorb : Internal.Thm := ⟨2, [bitsTy, X, Y, Y, exp Y X], [],
    Term.eq (condT X (v 0) (Term.app (v 4) (condT Y (v 0) (v 2) (v 3))) (v 1))
      (condT X (v 0) (Term.app (v 4) (v 2)) (v 1))⟩
  let eqBSound : Internal.Thm := ⟨0, [bitsTy], [], Term.eq
    (Term.lam bitsTy (condT bitsTy (call D.eqB [] [v 1, v 0]) (v 1) (v 0)))
    (Term.lam bitsTy (v 0))⟩
  let rs (ix : String → ℕ) : List NormRule :=
    baseNorm P ++ [.thm (ix "condCons") [bitTy], .thm (ix "rebLF") [bitTy, bitsTy]]
  pure [step "rebLF" rLf (fun _ E ↦ Internal.byListInd P.G E 2 0 1 (consT (x 0) (v 1) (v 0))
      (baseNorm P) 256 rLf.ctx rLf.hyps (sides rLf).1 (sides rLf).2),
    step "condCons" condCons (fun _ E ↦
      side condCons (bitsCases P.G 1 (byWeak P.G E 1 (baseNorm P)))),
    step "absorb" absorb (fun _ E ↦
      side absorb (bitsCases P.G 2 (byWeak P.G E 2 (baseNorm P)))),
    step "eqBSound" eqBSound (fun ix E ↦ side eqBSound (Internal.byListIndWith P.G 0 0 1
      (Internal.byFunExt P.G 0 (byAuto P.G E 0 (rs ix) 4 .open))
      (Internal.byFunExt P.G 0 (byAuto P.G E 0 (rs ix) 6 .open))))]

/-- A test of rewriting under a mask: a conditional between two terms of one value is that value;
the pointwise soundness of bitstring equality; under the test of the equality of two bitstrings,
the first is the second; and a tree's label rewritten under that test. -/
def maskTest (P : Prog) : List Step :=
  let X := x 0
  let condSame := weakThm P 1 [bitsTy, X] (condT X (v 0) (v 1) (v 1)) (v 1)
  let e : Term := call D.eqB [] [v 1, v 0]
  let maskEqB : Internal.Thm := ⟨0, [bitsTy, bitsTy], [], Term.eq
    (condT bitsTy e (v 1) (v 0)) (condT bitsTy e (v 0) (v 0))⟩
  let test : Internal.Thm := ⟨0, [treeTy, bitsTy, bitsTy], [], Term.eq
    (condT treeTy (call D.eqB [] [v 2, v 1]) (leafT (v 2)) (v 0))
    (condT treeTy (call D.eqB [] [v 2, v 1]) (leafT (v 1)) (v 0))⟩
  [step "condSame" condSame (fun _ E ↦
      side condSame (bitsCases P.G 1 (byWeak P.G E 1 (baseNorm P)))),
    pointwise P (fun _ ↦ baseNorm P) .weak "eqBSoundP" "eqBSound" bitsTy,
    step "maskEqB" maskEqB (fun ix E ↦ side maskEqB (byWeak P.G E 0
      (baseNorm P ++ [.thm (ix "eqBSoundP") [], .thm (ix "condSame") [bitsTy]]))),
    step "maskTest" test (fun ix _ ↦ some (maskRw treeTy bitsTy (ix "absorb") (ix "maskEqB") []
      [v 1, v 2] (call D.eqB [] [v 2, v 1]) (v 0) (v 2) (v 1) (v 1) (leafT (v 2))))]

/-- The lemmas of trees: the children of the tree of a label and children are the children, and a
tree the reader names by the atom {lit}`def` is that atom. -/
def headLemmas (P : Prog) : List Step :=
  -- stated at the empty label: the normal form of the left side does not mention the label, and
  -- a variable of the context that the left side does not mention would never be matched
  let childrenNode := weakThm P 0 [list treeTy]
    (call D.children [] [nodeT (Term.pair bnilT (v 0))]) (v 0)
  let rsU (ix : String → ℕ) : List NormRule :=
    baseNorm P ++ [.thm (ix "mapId") [], .thm (ix "mapFusion") [], .thm (ix "lambek") []]
  let rs (ix : String → ℕ) : List NormRule := baseNorm P ++ [.thm (ix "childrenNode") []] ++
    ([(bitTy, bitsTy), (bitTy, treeTy), (treeTy, bitsTy), (treeTy, treeTy)].map fun (a, b) ↦
      .thm (ix "rebLF") [a, b])
  let named (h : Term) : Term := apps (call (P.idx "named") [] []) [h, call (P.idx "kwDef") [] []]
  let headDef : Internal.Thm := ⟨0, [treeTy], [], Term.eq
    (condT treeTy (call D.lab [] [named (v 0)]) (v 0) (call (P.idx "aDef") [] []))
    (call (P.idx "aDef") [] [])⟩
  [step "childrenNode" childrenNode (fun ix E ↦
      side childrenNode (byMode .full P.G E 0 (rsU ix))),
    step "headDef" headDef (fun ix E ↦
      side headDef (byAutoT P.G E 0 (ix "lambek") (rs ix) 80 .weak))]

/-- The development: the lemmas on the unfolding of trees, the conditional lemmas, the test of
the rewriting under a test, and the lemmas of trees. -/
def development (P : Prog) : Option (List Step) := do
  pure (unfoldingThms P ++ (← genericLemmas P) ++ maskTest P ++ headLemmas P)

/-- The development found and checked, and the milliseconds each takes; an error where a lemma is
not proved or the development does not check. -/
def checkDevelopment (P : Prog) : IO Unit := do
  let some dev := development P | throw (IO.userError "the development is not stated")
  let t₀ ← IO.monoMsNow
  let decls ← match developNamed dev with
    | .ok decls => pure decls
    | .error name => throw (IO.userError s!"the lemma {name} is not proved")
  let t₁ ← IO.monoMsNow
  let some _ := Internal.checkDev P.G #[] decls
    | throw (IO.userError "the development does not check")
  let t₂ ← IO.monoMsNow
  IO.println "proof_milliseconds,check_milliseconds"
  IO.println s!"{t₁ - t₀},{t₂ - t₁}"

#eval show IO Unit from do
  let some ds := bundled GoedelT.ProofTests.bundler.toList programText.toList
    | throw (IO.userError "the program does not read")
  let some P := prog? ds fun name ↦ (defIndex ds name.toList).getD 0
    | throw (IO.userError "the program does not translate")
  checkDevelopment P

end GebTests.Prototypes.FreeTopos.TreeCases

end
