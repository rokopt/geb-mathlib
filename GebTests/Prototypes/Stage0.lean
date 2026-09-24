/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel -- shake: keep
public meta import Geb.Prototypes.Kernel -- shake: keep
public import GebTests.Prototypes.Kernel -- shake: keep
public meta import GebTests.Prototypes.Kernel -- shake: keep

set_option doc.verso true in
/-!
# The Geb-written stage 0

The bootstrap's Geb sources under {lit}`bootstrap/`, written in the kernel's syntax, run by
the seed and compared with the seed's own functions: the image serializer against
{name}`Geb.Kernel.writeImage`, byte for byte, on a leaf, a node of many children, labels of
zero and beyond a machine word, and the bundle of the serializer's own program; and the
stage-0 compiler, from a program's source to its image, against the seed's reader and image
writer on the programs of the kernel's examples, rejected ones included, and on its own
source, where the two agree byte for byte: the fixed point of self-compilation on images.

The sources are read at elaboration by {lit}`include_str` and converted to lists of
characters inside each {lit}`#guard`: core's {lit}`String.toList` depends on
{lit}`Classical.choice`, and a {lit}`#guard` is not a declaration.

## Main definitions

* {lit}`prelude`, {lit}`serialize`, {lit}`reader` and {lit}`compile` are the sources.
* {lit}`serializer` applies {lit}`image` to its input, and {lit}`compiler` is the stage-0
  compiler, its sources joined as {lit}`geb-kernel build` joins them.
* {lit}`seedCompile` is the seed's compilation of a program's source, the empty file when
  the program does not read.
* {lit}`samples` are the trees the serializer is compared on.

## Tags

bootstrap, stage 0, serializer, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Stage0Tests

/-- The prelude's source. -/
def prelude : String := include_str "../../bootstrap/prelude.geb"

/-- The serializer's source. -/
def serialize : String := include_str "../../bootstrap/serialize.geb"

/-- The reader's source. -/
def reader : String := include_str "../../bootstrap/reader.geb"

/-- The compiler's entry point. -/
def compile : String := include_str "../../bootstrap/compile.geb"

/-- The prelude and the serializer, applying the serializer to the input tree. -/
def serializer : String := prelude ++ serialize ++ "(def main (lam ((t T)) (image t)))"

/-- The stage-0 compiler, its sources joined, each followed by a newline, as the host driver
joins them. -/
def compiler : String := prelude ++ "\n" ++ serialize ++ "\n" ++ reader ++ "\n" ++ compile ++ "\n"

/-- The seed's compilation of a program's source: the image of its bundle, or the empty file
when it does not read. -/
def seedCompile (text : List Char) : Tree :=
  (readProgram text).elim (mk 0 []) fun ds ↦ ofBytes (writeImage (bundle ds))

/-- Trees exercising the serialization: a leaf, a label beyond a machine word, a node of many
children with labels of zero, and nested nodes. -/
def samples : List Tree :=
  [leaf 0, leaf (2 ^ 70 + 5), mk 7 ((List.range 300).map fun i ↦ leaf (i % 3)),
   mk 1 [mk 2 [leaf 3, mk 4 []], leaf 255, mk 256 [leaf 65536]]]

#guard samples.all fun t ↦ runMain serializer.toList t == some (ofBytes (writeImage t))
#guard (readProgram serializer.toList).all fun ds ↦
  runMain serializer.toList (bundle ds) == some (ofBytes (writeImage (bundle ds)))

-- the stage-0 compiler agrees with the seed on the kernel's examples, rejected ones included
#guard [Tests.factorial, Tests.size, Tests.mirror, Tests.reverseChildren, Tests.quadruple,
    Tests.isZero, Tests.listCase, Tests.sugar, "(def f (lam (x T) x)", "(def f (lam () 1))",
    "(def f (lam (x Nat) x))", "(def f (lam (x T) y))"].all fun p ↦
  runMain compiler.toList (nameTree p.toList) == some (seedCompile p.toList)
-- the fixed point: compiled by itself, the compiler is the image the seed builds of it
#guard runMain compiler.toList (nameTree compiler.toList) == some (seedCompile compiler.toList)

end Geb.Kernel.Stage0Tests

end
