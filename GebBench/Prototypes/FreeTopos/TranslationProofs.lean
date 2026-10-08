/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.TranslationProofs

set_option doc.verso true in
/-!
# The checker's times on the theorems of Gödel's T

For each file of {lit}`GebTests.Prototypes.FreeTopos.TranslationProofs`, the nodes of the
language's derivations of its theorems, the bit steps among them, and the least of three times the
checker takes, in microseconds; and the same for the lemmas the development proves before the
theorems. The prelude's development is measured both by innermost normalization and by weak head
normal forms first.

## Main definitions

* {lit}`derivSize`, {lit}`bitSteps` — the nodes of a derivation and its bit steps.
* {lit}`report` — the measurement of a file.
* {lit}`run` — the measurements of the files.

## Tags

internal language, Gödel's T, translation, measurement, benchmark
-/

set_option doc.verso true

@[expose] public section

namespace GebBench.Prototypes.FreeTopos.TranslationProofs

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Translation
open GebTests.Prototypes.FreeTopos.TranslationProofs
open GebTests.Prototypes.FreeTopos.Translation (sizeM)
open Internal (Term Deriv Decl Rule)

/-- The terms a rule names. -/
def ruleTerms : Rule → List Term
  | .thm _ _ σ _ | .apply _ _ σ => σ
  | .natInd _ _ s | .listInd _ _ s | .roseInd _ _ _ s => [s]
  | .cut φ | .convFrom φ => [φ]
  | _ => []

/-- The number of nodes of a derivation, the terms its rules name counted. -/
def derivSize : Deriv → ℕ := RoseTree.elim fun l rs ↦ 1 + rs.sum + ((ruleTerms l).map sizeM).sum

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

/-- The bit steps of a derivation: the case analyses of bits, which only the arithmetic of the
labels performs. -/
def bitSteps : Deriv → ℕ := RoseTree.elim fun l rs ↦
  (match l with | .caseInl _ _ | .caseInr _ _ => 1 | _ => 0) + rs.sum

set_option compiler.extract_closed false in
/-- The report of a file, printed, and an error when a development does not check: the nodes of the
language's derivations of the file's theorems, the bit steps among them, and the least of three
times the checker takes, in microseconds; and a row of the same for the lemmas the development
proves before the theorems; the file's name alone where no development is computed. -/
def report (name : String) (D : List Tree) (ts : List GoedelT.Thm)
    (dev : Internal.Globals → ℕ → List Internal.Thm → Option (List Decl)) : IO Unit := do
  match translate D ts with
  | none => throw (IO.userError s!"{name}: no translation")
  | some (G, m, ts) => match dev G m ts with
    | none => IO.println s!"{name},no development"
    | some ds => do
      let k := ds.length - ts.length
      let (okA, tA) ← timeUs fun _ ↦ Internal.checkThms G (ds.take k) #[]
      let some (G₁, E₁) := Internal.checkDev G #[] (ds.take k)
        | throw (IO.userError s!"{name}: the lemmas do not check")
      let (okL, tL) ← timeUs fun _ ↦ Internal.checkThms G₁ (ds.drop k) E₁
      if !(okA && okL) then throw (IO.userError s!"{name}: a development does not check")
      let dvs (l : List Decl) : List Deriv :=
        l.filterMap fun | Decl.language _ d => some d | _ => none
      let row (xs : List ℕ) : String := ",".intercalate (xs.map toString)
      if k > 0 then
        IO.println (name ++ "-lemmas," ++ row [((dvs (ds.take k)).map derivSize).sum,
          ((dvs (ds.take k)).map bitSteps).sum, tA])
      IO.println (name ++ "," ++ row [((dvs (ds.drop k)).map derivSize).sum,
        ((dvs (ds.drop k)).map bitSteps).sum, tL])

set_option compiler.extract_closed false in
/-- The reports of the files, the prelude's development both by innermost normalization and weak
head normal forms first. -/
def reports (rs : Option (List (List Tree × List GoedelT.Thm))) : IO Unit := do
  match rs with
  | some [(D₀, t₀), (D₁, t₁), (D₂, t₂), (D₃, t₃)] => do
    IO.println "file,language_nodes,bit_steps,language_microseconds"
    report "prelude" D₀ t₀ preludeDev
    report "prelude-whnf" D₀ t₀ preludeDevW
    report "nat" D₁ t₁ natDev
    report "check" D₂ t₂ checkDev
    report "datatype" D₃ t₃ treeDev
  | _ => throw (IO.userError "the files do not read")

set_option compiler.extract_closed false in
/-- The measurements of the files. Closed terms are not extracted, so that each check runs when it
is timed rather than when the program starts. -/
def run : IO Unit :=
  reports (results Kernel.Stage0Tests.bundler.toList (files.map fun (t, k) ↦ (t.toList, k)))

end GebBench.Prototypes.FreeTopos.TranslationProofs

end
