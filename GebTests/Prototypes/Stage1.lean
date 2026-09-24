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

The stage-1 compiler is the stage-0 compiler with the Surface 1 expansion rewritten in
Surface 1, {lit}`bootstrap/stage1/surface.geb`. The seed cannot read Surface 1, so the stage-0
compiler builds its image; run from that image, the stage-1 compiler compiles its own source to
the same image, the fixed point of the staged self-compilation, and agrees with the stage-0
compiler on the Surface 1 programs and the kernel's examples.

## Main definitions

* {lit}`stage1Surface` is the rewritten expansion and {lit}`stage1` the stage-1 compiler's
  source, joined as the host driver joins sources.
* {lit}`runImage` runs an image's definition named {lit}`main` on an input tree.

## Tags

bootstrap, stage 1, self-compilation, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Stage1Tests

open Stage0Tests

/-- The Surface 1 expansion written in Surface 1. -/
def stage1Surface : String := include_str "../../bootstrap/stage1/surface.geb"

/-- The stage-1 compiler's source. -/
def stage1 : String :=
  prelude ++ "\n" ++ serialize ++ "\n" ++ reader ++ "\n" ++ check ++ "\n" ++ stage1Surface ++
    "\n" ++ compile ++ "\n"

/-- Run an image, given as a file's tree, on an input tree: apply its definition named
{lit}`main`. -/
def runImage (img input : Tree) : Option Tree := do
  runEntry (← readImage (← toBytes img)) ['m', 'a', 'i', 'n'] input

-- built by the stage-0 compiler, the stage-1 compiler compiles itself to the same image, and
-- agrees with the stage-0 compiler on the Surface 1 programs and the kernel's examples
#guard
  let c1 := (runMain compiler.toList (nameTree stage1.toList)).getD (leaf 0)
  c1.children.length > 0 &&
  runImage c1 (nameTree stage1.toList) == some c1 &&
  [naturals, roses, Tests.factorial, Tests.sugar, Tests.listCase, "(def f (lam (x T) y))"].all
    fun p ↦ runImage c1 (nameTree p.toList) == runMain compiler.toList (nameTree p.toList)

end Geb.Kernel.Stage1Tests

end
