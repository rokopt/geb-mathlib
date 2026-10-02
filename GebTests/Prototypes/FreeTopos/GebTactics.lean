/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.GebProve
public meta import GebTests.Prototypes.FreeTopos.GebProve -- shake: keep
public import GebTests.Prototypes.Stage0
public meta import GebTests.Prototypes.Stage0 -- shake: keep
public import Geb.Prototypes.FreeTopos.Tactics
public meta import Geb.Prototypes.FreeTopos.Tactics -- shake: keep

set_option doc.verso true in
/-!
# The tactics written in Geb, compared with Lean's

The tactics of the internal language written in the datatype language,
{lit}`bootstrap/free-topos/tactics.geb`, are read by the stage-0 compiler's front end with the
metalogic's checker, the translation and the prover, loaded by the kernel, and compared with the
Lean tactics they transcribe ({lit}`Geb.FreeTopos.Tactics`): the search's functions of terms and
the derivations built from terms, at the sides of the theorems of the test modules of the
internal language's derivations and logic and at their subterms, and proofs by reduction, case
analysis and search, at those theorems. Inputs are encoded as the Geb program represents them,
by the encodings of {lit}`GebTests.Prototypes.FreeTopos.Agreement.Encode`.

## Main definitions

* {lit}`tacticsProgram` — the metalogic's checker, the translation, the prover and the tactics.
* {lit}`agree` — the comparison of the loaded tactics with Lean's, at the theorems among which
  the Lean search proves some.

## Tags

internal language, prover, tactic, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.GebTactics

open Geb Geb.PartialHorn Geb.FreeTopos GebTests.Prototypes.FreeTopos.GebCheck
  GebTests.Prototypes.FreeTopos.Agreement.Encode GebTests.Prototypes.FreeTopos.GebProve
open Internal (Term Entry NormRule)
open scoped FinEnum

/-- The translation. -/
def translationGeb : String := include_str "../../../bootstrap/free-topos/translation.geb"

/-- The tactics. -/
def tacticsGeb : String := include_str "../../../bootstrap/free-topos/tactics.geb"

/-- The program: the metalogic's checker, the reader, the kernel's type checker, the
translation, the prover and the tactics. -/
def tacticsProgram : String :=
  GebCheckInternal.internalProgram ++ String.join
    ([Geb.Kernel.Stage0Tests.reader, Geb.Kernel.Stage0Tests.check, translationGeb, proveGeb,
      tacticsGeb].map (· ++ "\n"))

/-- The type of lists of lists of trees. -/
abbrev tyTss : Tree := Kernel.tList tyTs

/-- The type of a prover. -/
abbrev tyPv : Tree := arrow tyTs (arrow tyTs (arrow tyT (arrow tyT tyT)))

/-- A prover written in Geb, as the kernel denotes it. -/
abbrev PvF : Type := List Tree → List Tree → Tree → Tree → Tree

/-- Rules of the normalizer written in Geb, each with its matching, as the kernel denotes them. -/
abbrev RulesF : Type := List (Tree × (Tree → Tree → List Tree → Tree))

/-- The theorems of the test modules of the internal language's derivations and logic, with
their constants. -/
def theorems : List (Internal.Globals × Theorems) :=
  [(Internal.G, InternalDerivation.theorems), (InternalLogic.GL, InternalLogic.theorems)]

/-- The sides of the theorems' equations. -/
def sides : List Term :=
  theorems.flatMap fun (_, ts) ↦ ts.flatMap fun (a, _) ↦
    match Internal.eqParts a.concl with
    | some (t, u) => [t, u]
    | none => []

/-- The terms the comparisons run on: the sides and their subterms outside binders and folds'
starts and steps. -/
def terms : List Term := sides.flatMap Tactics.openSubterms

/-- The comparison of the loaded tactics, each found by its name as {lit}`nm` spells it, with
Lean's: the functions of terms at each term, and the proofs at each theorem. -/
def agree (P : List (List Char × Kernel.Glob)) (nm : String → List Char) : Option Bool := do
  let subs : Tree → List Tree ← fn P (nm "openSubterms") (arrow tyT tyTs)
  let stuck : (Tree → Tree) → Tree → Tree ←
    fn P (nm "stuckVar") (arrow (arrow tyT tyT) (arrow tyT tyT))
  let stuckC : (Tree → Tree) → Tree → Tree ←
    fn P (nm "stuckVarC") (arrow (arrow tyT tyT) (arrow tyT tyT))
  let ment : Tree → Tree → Tree ← fn P (nm "mentions") (arrow tyT (arrow tyT tyT))
  let appsOf : Tree → Tree → List Tree ← fn P (nm "appsOf") (arrow tyT (arrow tyT tyTs))
  let cond : Tree → Tree ← fn P (nm "condParts") (arrow tyT tyT)
  let absT : Tree → Tree → Tree → Tree ←
    fn P (nm "abstractTerm") (arrow tyT (arrow tyT (arrow tyT tyT)))
  let occ : Tree → Tree → Tree → Tree → Tree ←
    fn P (nm "occRewrite") (arrow tyT (arrow tyT (arrow tyT (arrow tyT tyT))))
  let mats : Tree → Tree → Tree → List (List Tree) ←
    fn P (nm "matchesOf") (arrow tyT (arrow tyT (arrow tyT tyTss)))
  let unnode : Tree → Tree ← fn P (nm "unnodeU") (arrow tyT tyT)
  let byMode : Tree → Tree → List Tree → Tree → RulesF → PvF ←
    fn P (nm "byMode") (arrow tyT (arrow tyT (arrow tyTs (arrow tyT (arrow tyNRs tyPv)))))
  let byCases : Tree → Tree → PvF → PvF ←
    fn P (nm "byListCases") (arrow tyT (arrow tyT (arrow tyPv tyPv)))
  let byAuto : Tree → List Tree → Tree → RulesF → Tree → Tree → PvF ← fn P (nm "byAuto")
    (arrow tyT (arrow tyTs (arrow tyT (arrow tyNRs (arrow tyT (arrow tyT tyPv))))))
  let none₀ : Tree → Tree := fun _ ↦ Kernel.leaf 0
  let byTerm := terms.all fun t ↦
    subs (encTerm t) == (Tactics.openSubterms t).map encTerm &&
    stuck none₀ (encTerm t) == encOpt ((Tactics.stuckVar (fun _ ↦ false) t).map Kernel.leaf) &&
    stuckC none₀ (encTerm t) == encOpt ((Tactics.stuckVarC (fun _ ↦ false) t).map Kernel.leaf) &&
    (List.range 3).all (fun i ↦
      ment (encTerm t) (Kernel.leaf i) == Kernel.ofBool (Tactics.mentions t i) &&
      occ (Kernel.leaf 7) (Kernel.leaf i) (encTerm t) (Kernel.leaf 0) ==
        encDeriv (Tactics.occRewrite 7 i t 0)) &&
    (List.range 4).all (fun k ↦ appsOf (Kernel.leaf k) (encTerm t) ==
      (Tactics.appsOf k t).map encTerm) &&
    cond (encTerm t) == encOpt ((Tactics.condParts t).map encCond) &&
    unnode (encTerm t) == encTerm (Tactics.unnodeU t) &&
    ((Tactics.openSubterms t).take 3).all fun x ↦
      absT (Kernel.leaf 0) (encTerm x) (encTerm t) ==
        encTerm (Tactics.abstractTerm (Kernel.leaf 0) x t) &&
      mats (encTerm x) (Kernel.leaf 1) (encTerm t) ==
        (Tactics.matchesOf x 1 t).map (·.map encTerm)
  let rules := InternalDerivation.eqns ++ [.delta 0, .delta 1]
  let byThm := theorems.flatMap fun (G, ts) ↦ (List.range ts.length).filterMap fun k ↦
    match ts[k]?, ts[k]?.bind (Internal.eqParts ·.1.concl) with
    | some (a, _), some (t, u) =>
      let E := entries ts k
      let E' := E.toList.map encEntry
      let run (p : PvF) (q : Internal.Prover) : Bool :=
        p a.ctx (a.hyps.map encTerm) (encTerm t) (encTerm u) ==
          encOpt ((q a.ctx a.hyps t u).map encDeriv)
      let modeG := byMode (Kernel.leaf 3) (encGlobals G) E' (Kernel.leaf a.arity) (plain rules)
      let modeL := Tactics.byMode .full G E a.arity rules
      some ((Tactics.byAuto G E a.arity rules 2 .weak a.ctx a.hyps t u).isSome,
        run modeG modeL &&
        run (byMode (Kernel.leaf 1) (encGlobals G) E' (Kernel.leaf a.arity) (plain rules))
          (Tactics.byMode .weak G E a.arity rules) &&
        run (byCases (encGlobals G) (Kernel.leaf a.arity) modeG)
          (Tactics.byListCases G a.arity modeL) &&
        run (byAuto (encGlobals G) E' (Kernel.leaf a.arity) (plain rules) (Kernel.leaf 2)
          (Kernel.leaf 1)) (Tactics.byAuto G E a.arity rules 2))
    | _, _ => none
  pure (byTerm && byThm.all (fun p ↦ p.2) && byThm.any (fun p ↦ p.1))

-- the tactics written in Geb compute as the Lean tactics do
#guard ((loaded GoedelT.ProofTests.bundler.toList tacticsProgram.toList).bind fun P ↦
  agree P String.toList).getD false

end GebTests.Prototypes.FreeTopos.GebTactics

end

