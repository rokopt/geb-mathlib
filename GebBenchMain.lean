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
below `GebBench.Prototypes`; the entry point is outside the library's module prefix.

## Main definitions

* `benchmarks`: the benchmarks, each with its module's name.
* `main`: run the benchmarks named, or every one.
-/

/-- The benchmarks, each with its module's name below `GebBench.Prototypes`. -/
def benchmarks : List (String × IO Unit) :=
  [("SuccinctTree", GebBench.Prototypes.SuccinctTree.run),
    ("FreeTopos.TranslationProofs", GebBench.Prototypes.FreeTopos.TranslationProofs.run),
    ("FreeTopos.Rules", GebBench.Prototypes.FreeTopos.Rules.run),
    ("FreeTopos.Certified", GebBench.Prototypes.FreeTopos.Certified.run),
    ("FreeTopos.Literals", GebBench.Prototypes.FreeTopos.Literals.run)]

/-- Run the benchmarks the arguments name, or every one where they name none, each table preceded
by the line naming its module. -/
public def main (args : List String) : IO Unit := do
  for (name, run) in benchmarks.filter fun b ↦ args.isEmpty ∨ b.1 ∈ args do
    IO.println s!"# GebBench.Prototypes.{name}"
    run
