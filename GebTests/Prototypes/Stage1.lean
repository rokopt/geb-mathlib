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
language, so the stage-0 compiler builds its image, the committed {lit}`bootstrap/compiler.img`,
which {lit}`scripts/bootstrap.sh` checks natively to be the stage-0 compiler's image of the
stage-1 sources; run from that image, the stage-1 compiler agrees with the stage-0 compiler on
the programs in the datatype language and the kernel's examples. The fixed point of the staged
self-compilation, where the stage-1 compiler compiles its own source to its own image, is
checked natively by the same script, with the Lean backend.

## Main definitions

* {lit}`runImage` runs an image's definition named {lit}`main` on an input tree.
* {lit}`agreesOn` compares the stage-1 compiler's image with the stage-0 compiler on a program.

## Tags

bootstrap, stage 1, self-compilation, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Stage1Tests

open Stage0Tests
open scoped FinEnum

/-- Run an image on an input tree: apply its definition named {lit}`main`. -/
def runImage (img : ByteArray) (input : Tree) : Option Tree := do
  runEntry (← readImage img) ['m', 'a', 'i', 'n'] input

/-- Whether an image of the stage-1 compiler compiles a program as the stage-0 compiler, given as
text, does. -/
def agreesOn (img : ByteArray) (compilerText p : List Char) : Bool :=
  runImage img (nameTree p) == runMain compilerText (nameTree p)

-- the stage-1 compiler, from the committed image, agrees with the stage-0 compiler on the
-- programs in the datatype language and the kernel's examples
#eval show IO Unit from do
  let img ← IO.FS.readBinFile "bootstrap/compiler.img"
  unless [naturals, roses, Tests.factorial, Tests.sugar, Tests.numerals, Tests.listCase,
      "(def f (lam (x T) y))", "(defnum n m)"].all (agreesOn img compiler.toList ·.toList) do
    throw (IO.userError "the stage-1 compiler disagrees with the stage-0 compiler")

end Geb.Kernel.Stage1Tests

end
