/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# The stage-1 compiler

The stage-1 compiler is the stage-0 compiler with the expansion of the datatype language rewritten
in the datatype language, {lit}`bootstrap/stage1/datatype.geb`. The seed cannot read the datatype
language, so the stage-0 compiler builds its image; run from that image, the stage-1 compiler
agrees with the stage-0 compiler on the programs in the datatype language and the kernel's
examples. The fixed point of the staged
self-compilation, where the stage-1 compiler compiles its own source to its own image, is
checked natively by {lit}`scripts/bootstrap.sh`, with the Lean backend.

## Main definitions

* {lit}`stage1Datatype` is the rewritten expansion and {lit}`stage1` the stage-1 compiler's
  source, joined as the host driver joins sources.
* {lit}`runImage` runs an image's definition named {lit}`main` on an input tree.

## Tags

bootstrap, stage 1, self-compilation, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Stage1Tests

open Stage0Tests

/-- The expansion of the datatype language written in the datatype language. -/
def stage1Datatype : String := include_str "../../bootstrap/stage1/datatype.geb"

/-- The stage-1 compiler's source. -/
def stage1 : String :=
  prelude ++ "\n" ++ serialize ++ "\n" ++ reader ++ "\n" ++ check ++ "\n" ++ stage1Datatype ++
    "\n" ++ modules ++ "\n" ++ compile ++ "\n"

/-- Run an image, given as a file's tree, on an input tree: apply its definition named
{lit}`main`. -/
def runImage (img input : Tree) : Option Tree := do
  runEntry (← readImage (← toBytes img)) ['m', 'a', 'i', 'n'] input

-- built by the stage-0 compiler, the stage-1 compiler agrees with the stage-0 compiler on the
-- Programs in the datatype language and the kernel's examples
#guard
  let c1 := (runMain compiler.toList (nameTree stage1.toList)).getD (leaf 0)
  c1.children.length > 0 &&
  [naturals, roses, Tests.factorial, Tests.sugar, Tests.numerals, Tests.listCase,
    "(def f (lam (x T) y))", "(defnum n m)"].all
    fun p ↦ runImage c1 (nameTree p.toList) == runMain compiler.toList (nameTree p.toList)

end Geb.Kernel.Stage1Tests

end
