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

The lemmas that exercise two provers of the internal language,
{name}`Geb.FreeTopos.Tactics.byTreeSplit` and {name}`Geb.FreeTopos.Tactics.maskRw`, about the
translation of the prelude, the reader, the type checker and the expansion of the datatype
language.

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

* {lit}`development` — the lemmas, each with its proof.

## Tags

internal language, case analysis, rose tree, conditional, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.TreeCases

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation Geb.FreeTopos.Tactics
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Weakening
open Internal (Term NormRule Entry Deriv Decl Definition)
open scoped FinEnum

/-- The program: the prelude, the reader, the type checker and the expansion of the datatype
language. -/
def programText : String :=
  Kernel.Stage0Tests.prelude ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++
    Kernel.Stage0Tests.check ++ "\n" ++ Kernel.Stage0Tests.datatype

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
  let named (h : Term) : Term :=
    apps (call (P.idx "Reader.named") [] []) [h, call (P.idx "Reader.kwDef") [] []]
  let headDef : Internal.Thm := ⟨0, [treeTy], [], Term.eq
    (condT treeTy (call D.lab [] [named (v 0)]) (v 0) (call (P.idx "Datatype.aDef") [] []))
    (call (P.idx "Datatype.aDef") [] [])⟩
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
