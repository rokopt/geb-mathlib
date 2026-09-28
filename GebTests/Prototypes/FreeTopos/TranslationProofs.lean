/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Translation -- shake: keep
public meta import GebTests.Prototypes.FreeTopos.Translation -- shake: keep
public import GebTests.Prototypes.Proofs -- shake: keep
public meta import GebTests.Prototypes.Proofs -- shake: keep
public import Geb.Prototypes.FreeTopos.Internal.Prove -- shake: keep
public meta import Geb.Prototypes.FreeTopos.Internal.Prove -- shake: keep

set_option doc.verso true in
/-!
# The computational core's theorems, translated

The theorems of the computational core's proofs, with the programs they are about, translated
into the internal language and proved there by its prover: the prelude's appending and the
labels' addition by normalization and induction, the kernel's type checker at a quoted tree,
the metalogic's checker's accessors and a program by structural recursion by normalization,
weak head normal forms first, rewriting by Lambek's lemma, which follows from two lemmas on
lists by the uniqueness of the rose tree's fold. Each development checks, and the report prints,
for each file, the nodes of the core's certificates and of the language's derivations, the
numeral steps among the latter, and the times each checker takes.

## Main definitions

* {lit}`files` — the texts of the proof files, each after the programs it is about.
* {lit}`coreResults` — the core's results of each file: the program's definitions, and each
  theorem with its certificate.
* {lit}`treeLemmas` — the fold of a list by construction, the fusion of the rebuilding of trees
  with their unfolding, and Lambek's lemma.
* {lit}`preludeDev`, {lit}`natDev`, {lit}`checkDev`, {lit}`treeDev` — the developments.
* {lit}`reports` — the measurement.

## Tags

internal language, computational core, translation, measurement, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.TranslationProofs

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open Geb.Metalogic.ProofTests
open GebTests.Prototypes.FreeTopos.Translation (sizeK sizeM)
open scoped FinEnum

/-- The texts of the proof files, each after the programs it is about: the prelude, the labels,
the kernel's type checker, the metalogic's checker and a program by structural recursion. -/
def files : List String :=
  let pr := Kernel.Stage0Tests.prelude
  let prc := pr ++ "\n" ++ Kernel.Stage0Tests.reader ++ "\n" ++ Kernel.Stage0Tests.check
  [pr ++ "\n" ++ preludeProofs, pr ++ "\n" ++ natProofs, prc ++ "\n" ++ checkProofs,
    prc ++ "\n" ++ Metalogic.Tests.equationsGeb ++ "\n" ++ equationsProofs,
    prc ++ "\n" ++ surfaceProofs]

/-- The core's results of each file, from the texts of the bundler, the prover and the files:
the program's definitions, and each theorem with its certificate. -/
def coreResults (bundler prover : List Char) (files : List (List Char)) :
    Option (List (List Tree × List (Metalogic.Thm × Tree))) := do
  let f ← proverFn? bundler prover
  files.mapM fun text ↦ do
    let (D, rs) ← results f text
    pure (D, rs.map fun x ↦ (thmOf (x.children.getD 1 (Kernel.leaf 0)),
      x.children.getD 2 (Kernel.leaf 0)))

open Internal (Term Deriv Decl Entry NormRule Rule)

/-- The terms a rule names. -/
def ruleTerms : Rule → List Term
  | .thm _ _ σ _ | .apply _ _ σ => σ
  | .natInd _ _ s | .listInd _ _ s | .roseInd _ _ _ s => [s]
  | .cut φ | .convFrom φ => [φ]
  | _ => []

/-- The number of nodes of a derivation, the terms its rules name counted. -/
def derivSize : Deriv → ℕ := RoseTree.elim fun l rs ↦ 1 + rs.sum + ((ruleTerms l).map sizeM).sum

/-- The language's equations the normalizer applies: β, the components of pairs, and the
computation of the folds at the primitive arrows. -/
def baseRules : List NormRule := [.rule .beta, .rule .fstPair, .rule .sndPair,
  .rule (.natZero 0), .rule (.natSucc 1), .rule (.listNil 2), .rule (.listCons 3),
  .rule (.roseNode 4 2 3)]

/-- The unfolding of every definition below an index. -/
def deltas (m : ℕ) : List NormRule := (List.range m).map NormRule.delta

/-- The unfolding of every definition below an index but those of a list. -/
def deltasExcept (m : ℕ) (ks : List ℕ) : List NormRule :=
  ((List.range m).filter (· ∉ ks)).map NormRule.delta

/-- A development: each theorem with the derivation its prover computes from the entries
before it. -/
def develop (ts : List (Internal.Thm × (Array Entry → Option Deriv))) : Option (List Decl) :=
  (ts.foldl (fun acc (a, p) ↦ acc.bind fun (E, ds) ↦
    (p E).map fun d ↦ (E.push (.language a), ds ++ [.language a d])) (some (#[], []))).map
    Prod.snd

/-- The translation of a file's program and theorems: the constants, the number of definitions,
and the translated theorems. -/
def translate (D : List Tree) (rs : List (Metalogic.Thm × Tree)) :
    Option (Internal.Globals × ℕ × List Internal.Thm) := do
  let (gt, defs) ← program D
  pure (globals defs, lib.length + defs.length, ← rs.mapM fun p ↦ thm gt p.1)

/-- The sides of a translated theorem's equation. -/
def sides (a : Internal.Thm) : Term × Term :=
  (a.concl.children.getD 0 Term.star, a.concl.children.getD 1 Term.star)

/-- The proof by normalization of a theorem with rules. -/
def norm (G : Internal.Globals) (rs : List NormRule) (fuel : ℕ) (a : Internal.Thm)
    (E : Array Entry) : Option Deriv :=
  Internal.byNorm G E 0 rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The proof of a theorem by induction on its innermost list variable with a step. -/
def listInd (G : Internal.Globals) (s : Term) (rs : List NormRule) (fuel : ℕ)
    (a : Internal.Thm) (E : Array Entry) : Option Deriv :=
  Internal.byListInd G E 0 2 3 s rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The proof of a theorem by induction on its innermost natural number variable with a step. -/
def natInd (G : Internal.Globals) (s : Term) (rs : List NormRule) (fuel : ℕ)
    (a : Internal.Thm) (E : Array Entry) : Option Deriv :=
  Internal.byNatInd G E 0 0 1 s rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The prelude's development: the unit laws and the associativity of appending, and appending
the empty list twice by rewriting with the right unit law. -/
def preludeDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  let rs := baseRules ++ deltas m
  let step := consT rose (Term.var 1) (Term.var 0)
  match ts with
  | [t₀, t₁, t₂, t₃] => develop [(t₀, norm G rs 256 t₀), (t₁, listInd G step rs 256 t₁),
      (t₂, listInd G step rs 256 t₂), (t₃, norm G (baseRules ++ [.thm 1 []]) 256 t₃)]
  | _ => none

/-- Addition from zero on the natural numbers object, the lemma the left unit law rewrites by. -/
def addZeroLeftN : Internal.Thm :=
  ⟨0, [nat], [], Term.eq (call D.add [] [zeroT, Term.var 0]) (Term.var 0)⟩

/-- The labels' development: the recursion equations of addition by normalization, and the left
unit law by rewriting with addition from zero on the natural numbers object. -/
def natDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  let rs := baseRules ++ deltas m
  match ts with
  | [t₀, t₁, t₂] => develop [(t₀, norm G rs 256 t₀), (t₁, norm G rs 256 t₁),
      (addZeroLeftN, natInd G (succT (Term.var 0)) rs 256 addZeroLeftN),
      (t₂, norm G (.thm 2 [] :: baseRules ++ deltasExcept m [D.add]) 256 t₂)]
  | _ => none

/-- The least time, over three evaluations, to evaluate a Boolean, in microseconds, with its
value. -/
def timeUs (f : Unit → Bool) : IO (Bool × ℕ) := do
  let mut best := 0
  let mut b := false
  for i in [0, 1, 2] do
    let t₀ ← IO.monoNanosNow
    b ← IO.lazyPure fun _ ↦ f ()
    let t₁ ← IO.monoNanosNow
    let d := (t₁ - t₀) / 1000
    if i = 0 ∨ d < best then best := d
  pure (b, best)

/-- The type the unfolding of trees folds into: the pair of a label and the list of the
children. -/
def P : Tree := prod nat (list rose)

/-- The step of the unfolding of trees, the library's. -/
def unnodeStep : Term := match lib[D.unnode]? with
  | some d => d.body.children.headD Term.star
  | none => Term.star

/-- The unfolding of a tree. -/
def unnodeU (t : Term) : Term := Term.roseRec P unnodeStep t

/-- The fold of a list of trees by construction is the list. -/
def mapId : Internal.Thm :=
  ⟨0, [list rose], [], Term.eq (Term.listRec (nilT rose) (consT rose (Term.var 1) (Term.var 0))
    (Term.var 0)) (Term.var 0)⟩

/-- The trees rebuilt from the unfoldings of a list of trees are the rebuilt unfoldings. -/
def mapFusion : Internal.Thm :=
  ⟨0, [list rose], [], Term.eq
    (Term.listRec (nilT rose) (consT rose (nodeT (Term.var 1)) (Term.var 0))
      (Term.listRec (nilT P) (consT P (unnodeU (Term.var 1)) (Term.var 0)) (Term.var 0)))
    (Term.listRec (nilT rose) (consT rose (nodeT (unnodeU (Term.var 1))) (Term.var 0))
      (Term.var 0))⟩

/-- A tree is rebuilt from its unfolding, by Lambek's lemma. -/
def lambek : Internal.Thm :=
  ⟨0, [rose], [], Term.eq (nodeT (unnodeU (Term.var 0))) (Term.var 0)⟩

/-- The lemmas on the unfolding of trees, each with its proof: the fold by construction and the
fusion of the rebuilding with the unfolding by list induction, and Lambek's lemma by the
uniqueness of the fold, rewriting by them. -/
def treeLemmas (G : Internal.Globals) : List (Internal.Thm × (Array Entry → Option Deriv)) :=
  [(mapId, listInd G (consT rose (Term.var 1) (Term.var 0)) baseRules 64 mapId),
   (mapFusion, listInd G (consT rose (nodeT (unnodeU (Term.var 1))) (Term.var 0)) baseRules 64
      mapFusion),
   (lambek, fun E ↦ Internal.byRoseInd G E 0 4 2 3 (nodeT (Term.pair (Term.var 1) (Term.var 0)))
      (baseRules ++ [.thm 0 [], .thm 1 []]) 64 lambek.ctx (sides lambek).1 (sides lambek).2)]

/-- The proof by normalization, weak head normal forms first, of a theorem with rules. -/
def normW (G : Internal.Globals) (rs : List NormRule) (fuel : ℕ) (a : Internal.Thm)
    (E : Array Entry) : Option Deriv :=
  Internal.byNormW G E 0 rs fuel a.ctx a.hyps (sides a).1 (sides a).2

/-- The prelude's development, weak head normal forms first. -/
def preludeDevW (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  let rs := baseRules ++ deltas m
  let step := consT rose (Term.var 1) (Term.var 0)
  match ts with
  | [t₀, t₁, t₂, t₃] => develop [(t₀, normW G rs 256 t₀), (t₁, listInd G step rs 256 t₁),
      (t₂, listInd G step rs 256 t₂), (t₃, normW G (baseRules ++ [.thm 1 []]) 256 t₃)]
  | _ => none

/-- The labels' development, weak head normal forms first. -/
def natDevW (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  let rs := baseRules ++ deltas m
  match ts with
  | [t₀, t₁, t₂] => develop [(t₀, normW G rs 256 t₀), (t₁, normW G rs 256 t₁),
      (addZeroLeftN, natInd G (succT (Term.var 0)) rs 256 addZeroLeftN),
      (t₂, normW G (.thm 2 [] :: baseRules ++ deltasExcept m [D.add]) 256 t₂)]
  | _ => none

/-- The type checker's development: the quoted tree's type, weak head normal forms first,
every definition unfolded. -/
def checkDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  develop (ts.map fun t ↦ (t, normW G (baseRules ++ deltas m) 4096 t))

/-- A development of the tree lemmas and then theorems each by normalization, weak head normal
forms first, every definition unfolded and Lambek's lemma rewriting. -/
def treeDev (G : Internal.Globals) (m : ℕ) (ts : List Internal.Thm) : Option (List Decl) :=
  develop (treeLemmas G ++
    ts.map fun t ↦ (t, normW G (.thm 2 [] :: baseRules ++ deltas m) 4096 t))

/-- The numeral steps of a derivation: the computations of the natural numbers' fold at zero
and at a successor. -/
def numeralSteps : Deriv → ℕ := RoseTree.elim fun l rs ↦
  (match l with | .natZero _ | .natSucc _ => 1 | _ => 0) + rs.sum

/-- The report of a file, printed, and an error when a development does not check: the nodes of
the core's certificates and of the language's derivations, the numeral steps among the latter,
and the least of three times each checker takes, in microseconds. -/
def report (name : String) (D : List Tree) (rs : List (Metalogic.Thm × Tree))
    (dev : Internal.Globals → ℕ → List Internal.Thm → Option (List Decl)) : IO Unit := do
  match translate D rs with
  | none => throw (IO.userError s!"{name}: no translation")
  | some (G, m, ts) => match dev G m ts with
    | none => throw (IO.userError s!"{name}: no development")
    | some ds => do
      let (okC, tC) ← timeUs fun _ ↦ recheck D (rs.map fun p ↦ RoseTree.node 0
        [Kernel.leaf 0, RoseTree.node 0 [RoseTree.node 0 p.1.ctx,
          RoseTree.node 0 [p.1.eqn.ty, p.1.eqn.lhs, p.1.eqn.rhs]], p.2])
      let (okL, tL) ← timeUs fun _ ↦ Internal.checkThms G ds #[]
      if !(okC && okL) then throw (IO.userError s!"{name}: a development does not check")
      let dvs := ds.filterMap fun | Decl.language _ d => some d | _ => none
      let row := [(rs.map fun p ↦ sizeK p.2).sum, (dvs.map derivSize).sum,
        (dvs.map numeralSteps).sum, tC, tL]
      IO.println (name ++ "," ++ ",".intercalate (row.map toString))

/-- The reports of the files, from the core's results, the prelude's and the labels'
developments both by innermost normalization and weak head normal forms first. -/
def reports (core : Option (List (List Tree × List (Metalogic.Thm × Tree)))) : IO Unit := do
  match core with
  | some [(D₀, r₀), (D₁, r₁), (D₂, r₂), (D₃, r₃), (D₄, r₄)] => do
    IO.println ("file,core_nodes,language_nodes,numeral_steps,core_microseconds," ++
      "language_microseconds")
    report "prelude" D₀ r₀ preludeDev
    report "prelude-whnf" D₀ r₀ preludeDevW
    report "nat" D₁ r₁ natDev
    report "nat-whnf" D₁ r₁ natDevW
    report "check" D₂ r₂ checkDev
    report "equations" D₃ r₃ treeDev
    report "surface" D₄ r₄ treeDev
  | _ => throw (IO.userError "the core's results are missing")

#eval reports (coreResults bundler.toList prover.toList (files.map String.toList))

end GebTests.Prototypes.FreeTopos.TranslationProofs

end
