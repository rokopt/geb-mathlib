/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import GebBench

/-!
# Benchmark entry point

Run the benchmarks of `GebBench` with `lake exe geb-bench`, each table preceded by the line naming
its module, or those of the modules named with `lake exe geb-bench NAME...`, each name the module's
below `GebBench.Prototypes`, a name of no benchmark failing the run before any runs; the entry
point is outside the library's module prefix.

## Main definitions

* `benchmarks`: the benchmarks, each with its module's name.
* `main`: run the benchmarks named, or every one, rejecting a name of none.
-/

/-- The benchmarks, each with its module's name below `GebBench.Prototypes`. -/
def benchmarks : List (String × IO Unit) :=
  [("SuccinctTree", GebBench.Prototypes.SuccinctTree.run),
    ("FreeTopos.TranslationProofs", GebBench.Prototypes.FreeTopos.TranslationProofs.run),
    ("FreeTopos.Rules", GebBench.Prototypes.FreeTopos.Rules.run),
    ("FreeTopos.Certified", GebBench.Prototypes.FreeTopos.Certified.run),
    ("FreeTopos.Literals", GebBench.Prototypes.FreeTopos.Literals.run),
    ("FreeTopos.ByMachine", GebBench.Prototypes.FreeTopos.ByMachine.run),
    ("FreeTopos.Profile", GebBench.Prototypes.FreeTopos.Profile.run),
    ("InteractionNet.GraphRuntime", GebBench.Prototypes.InteractionNet.GraphRuntime.run)]

/-- Run the benchmarks the arguments name, or every one where they name none, each table preceded
by the line naming its module; fail, running none, when an argument names no benchmark. -/
public def main (args : List String) : IO UInt32 := do
  let names := benchmarks.map Prod.fst
  let unknown := args.filter (· ∉ names)
  unless unknown.isEmpty do
    IO.eprintln s!"geb-bench: no benchmark named {unknown}; the benchmarks are {names}"
    return 2
  for (name, run) in benchmarks.filter fun b ↦ args.isEmpty ∨ b.1 ∈ args do
    IO.println s!"# GebBench.Prototypes.{name}"
    run
  return 0
