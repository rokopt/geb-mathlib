/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.GebTactics
public meta import GebTests.Prototypes.FreeTopos.GebTactics -- shake: keep
public import GebTests.Prototypes.FreeTopos.Benchmark
public meta import GebTests.Prototypes.FreeTopos.Benchmark -- shake: keep

set_option doc.verso true in
/-!
# The combinator prover written in Geb, compared with Lean's

The prover of the theory of an elementary topos written in the datatype language,
{lit}`bootstrap/free-topos/combinator.geb`, is read by the stage-0 compiler's front end with the
metalogic's program, loaded by the kernel, and compared with the Lean prover it transcribes
({lit}`Geb.FreeTopos.Prover`): the library's development, its typing certified by lemmas and by
the checker's oracle rules, and the benchmark's development, each of its theorems proved by the
tactic the benchmark proves it by. Inputs are encoded as the Geb program represents them, by the
encodings of {lit}`GebTests.Prototypes.FreeTopos.Agreement.Encode`.

## Main definitions

* {lit}`combinatorProgram` — the metalogic's program with the combinator prover.
* {lit}`replay` — the benchmark's development, proved by the loaded prover.

## Tags

prover, elementary topos, differential testing, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.GebCombinator

open Geb Geb.PartialHorn Geb.FreeTopos Geb.FreeTopos.Prover GebTests.Prototypes.FreeTopos.GebCheck
  GebTests.Prototypes.FreeTopos.GebTactics GebTests.Prototypes.FreeTopos.Agreement.Encode
  GebTests.Prototypes.FreeTopos.Benchmark

/-- The combinator prover. -/
def combinatorGeb : String := include_str "../../../bootstrap/free-topos/combinator.geb"

/-- The program: the metalogic's program with the combinator prover. -/
def combinatorProgram : String := tacticsProgram ++ combinatorGeb ++ "\n"

/-- A computation of the prover written in Geb, as the kernel denotes it. -/
abbrev PMF : Type := Tree → Tree → Tree

/-- The type of a computation of the prover. -/
def tyPM : Tree := arrow tyT (arrow tyT tyT)

/-- The value a step of a development written in Geb returns, with the development. -/
def parseStep (r : Tree) : Option (Tree × List Tree) :=
  if r.label == 1 then do
    let p ← r.children[0]?
    let i ← p.children[0]?
    let d ← p.children[1]?
    pure (i, d.children)
  else none

/-- The benchmark's development, each theorem proved by the loaded prover's tactic that
{lit}`benchmarkWith` proves it by, from the loaded library, a definition named by its name's
characters under {lit}`nm`. -/
def replay (G : List (List Char × Kernel.Glob)) (nm : String → List Char) :
    Option (List Tree) := do
  let pS : Tree → PMF → List Tree → Tree → List Tree → Tree ← fn G (nm "Combinator.proveSeq")
    (arrow tyT (arrow tyPM (arrow tyTs (arrow tyT (arrow tyTs tyT)))))
  let bN : List Tree → Tree → PMF ← fn G (nm "Combinator.pByNorm") (arrow tyTs (arrow tyT tyPM))
  let bLI : List Tree → Tree → Tree → Tree → Tree → PMF ← fn G (nm "Combinator.byListInduction")
    (arrow tyTs (arrow tyT (arrow tyT (arrow tyT (arrow tyT tyPM)))))
  let bLPI : List Tree → Tree → Tree → Tree → Tree → PMF ←
    fn G (nm "Combinator.byListParamInduction")
      (arrow tyTs (arrow tyT (arrow tyT (arrow tyT (arrow tyT tyPM)))))
  let bNI : List Tree → Tree → Tree → Tree → PMF ← fn G (nm "Combinator.byNatInduction")
    (arrow tyTs (arrow tyT (arrow tyT (arrow tyT tyPM))))
  let nT : List Tree → Tree → List Tree → Tree → List Tree → Tree ←
    fn G (nm "Combinator.normalizeThm")
      (arrow tyTs (arrow tyT (arrow tyTs (arrow tyT (arrow tyTs tyT)))))
  let lib : Tree → Tree ← fn G (nm "Combinator.libraryWith") (arrow tyT tyT)
  let (ix, d0) ← parseStep (lib (Kernel.leaf 1))
  let libR : Tree → List Tree ← fn G (nm "Combinator.libRules") (arrow tyT tyTs)
  let rs := libR ix
  let ds := defs.map encDefn
  let prove (a : Seq) (m : PMF) (d : List Tree) :=
    (parseStep (pS (encSeq a) m ds (Kernel.leaf 1) d)).map fun (i, d) ↦ (i.label, d)
  let delta (i : ℕ) := encRw (deltaRule i)
  let thm (j : ℕ) := encRw { src := .thm j }
  let q (a : Seq) := encEqn a.concl
  let (cn, d1) ← prove appendCNil (bN (rs ++ [delta 2]) (q appendCNil)) d0
  let (cc, d2) ← prove appendCCons (bN (rs ++ [delta 2]) (q appendCCons)) d1
  let lrs := rs ++ [thm cn, thm cc, delta 0, delta 1, delta 3]
  let (_, d3) ← prove appendNilLeft (bN lrs (q appendNilLeft)) d2
  let (an, d4) ← prove appendNil (bLI lrs (x 0) (nil (x 0)) (cons (x 0)) (q appendNil)) d3
  let (_, d5) ← prove appendAssoc (bLPI lrs (x 0) append
    (comp (cons (x 0)) (fst (prod (x 0) L) P)) (q appendAssoc)) d4
  let (k, d6) ← parseStep (nT lrs (Kernel.leaf an) ds (Kernel.leaf 1) d5)
  let k := k.label
  let (_, d7) ← prove appendNilTwice (bN (lrs ++ [thm k]) (q appendNilTwice)) d6
  let (az, d8) ← prove addCZero (bN (rs ++ [delta 6]) (q addCZero)) d7
  let (as, d9) ← prove addCSucc (bN (rs ++ [delta 6]) (q addCSucc)) d8
  let nrs := rs ++ [thm az, thm as, delta 4, delta 5, delta 7]
  let (_, d10) ← prove addZero (bN nrs (q addZero)) d9
  let (_, d11) ← prove addSucc (bN nrs (q addSucc)) d10
  let (_, d12) ← prove addZeroLeft (bNI nrs zeroN succ (q addZeroLeft)) d11
  pure d12

-- the library written in Geb is the Lean library, its typing certified by lemmas and by the
-- checker's oracle rules
#guard ((loaded Geb.Kernel.Stage0Tests.bundler.toList combinatorProgram.toList).bind fun P ↦ do
  let lib : Tree → Tree ← fn P "Combinator.libraryWith".toList (arrow tyT tyT)
  pure (lib (Kernel.leaf 1) == encLib (libraryWith true) &&
    lib (Kernel.leaf 0) == encLib (libraryWith false))).getD false

-- the benchmark's development proved by the prover written in Geb is the Lean prover's
#guard ((loaded Geb.Kernel.Stage0Tests.bundler.toList combinatorProgram.toList).map fun P ↦
  benchmark.isSome && replay P String.toList == benchmark.map (·.map encDevEntry)).getD false

end GebTests.Prototypes.FreeTopos.GebCombinator

end
