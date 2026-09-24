/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel -- shake: keep
public meta import Geb.Prototypes.Kernel -- shake: keep

set_option doc.verso true in
/-!
# The Geb-written stage 0

The bootstrap's Geb sources under {lit}`bootstrap/`, written in the kernel's syntax, run by
the seed and compared with the seed's own functions: the image serializer against
{name}`Geb.Kernel.writeImage`, byte for byte, on a leaf, a node of many children, labels of
zero and beyond a machine word, and the bundle of the serializer's own program.

The sources are read at elaboration by {lit}`include_str` and converted to lists of
characters inside each {lit}`#guard`: core's {lit}`String.toList` depends on
{lit}`Classical.choice`, and a {lit}`#guard` is not a declaration.

## Main definitions

* {lit}`prelude` and {lit}`serialize` are the sources, and {lit}`serializer` the program
  applying {lit}`image` to its input.
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

/-- The prelude and the serializer, applying the serializer to the input tree. -/
def serializer : String := prelude ++ serialize ++ "(def main (lam ((t T)) (image t)))"

/-- Trees exercising the serialization: a leaf, a label beyond a machine word, a node of many
children with labels of zero, and nested nodes. -/
def samples : List Tree :=
  [leaf 0, leaf (2 ^ 70 + 5), mk 7 ((List.range 300).map fun i ↦ leaf (i % 3)),
   mk 1 [mk 2 [leaf 3, mk 4 []], leaf 255, mk 256 [leaf 65536]]]

#guard samples.all fun t ↦ runMain serializer.toList t == some (ofBytes (writeImage t))
#guard (readProgram serializer.toList).all fun ds ↦
  runMain serializer.toList (bundle ds) == some (ofBytes (writeImage (bundle ds)))

end Geb.Kernel.Stage0Tests

end
