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
type checker against the seed's checker on the bundles of the kernel's examples and of the
compiler, and on malformed terms; and the stage-0 compiler, from a program's source to its
image, against the seed's reader, checker and image writer on the programs of the kernel's
examples, rejected and ill-typed ones included, and on its own source, where the two agree
byte for byte: the fixed point of self-compilation on images.

The sources are read at elaboration by {lit}`include_str` and converted to lists of
characters inside each {lit}`#guard`: core's {lit}`String.toList` depends on
{lit}`Classical.choice`, and a {lit}`#guard` is not a declaration.

## Main definitions

* {lit}`prelude`, {lit}`serialize`, {lit}`reader`, {lit}`check` and {lit}`compile` are the
  sources.
* {lit}`checker` returns the types of a bundle's definitions, and {lit}`seedTypes` is the
  seed's answer; {lit}`malformed` are terms the checker rejects.
* {lit}`serializer` applies {lit}`image` to its input, and {lit}`compiler` is the stage-0
  compiler, its sources joined as {lit}`geb-kernel build` joins them.
* {lit}`seedCompile` is the seed's compilation of a program's source, the empty file when
  the program does not read or is ill-typed.
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

/-- The type checker's source. -/
def check : String := include_str "../../bootstrap/check.geb"

/-- The compiler's entry point. -/
def compile : String := include_str "../../bootstrap/compile.geb"

/-- The prelude and the serializer, applying the serializer to the input tree. -/
def serializer : String := prelude ++ serialize ++ "(def main (lam ((t T)) (image t)))"

/-- The stage-0 compiler, its sources joined, each followed by a newline, as the host driver
joins them. -/
def compiler : String :=
  prelude ++ "\n" ++ serialize ++ "\n" ++ reader ++ "\n" ++ check ++ "\n" ++ compile ++ "\n"

/-- The type checker, returning the types of the definitions of the bundle it is given. -/
def checker : String :=
  prelude ++ reader ++ check ++ "(def main (lam ((b T)) (checkProgram (children (child b 0)))))"

/-- The seed's types of a bundle's definitions, as the Geb checker returns them: the
optional node over the types, or the leaf of label zero when a definition is ill-typed. -/
def seedTypes (b : Tree) : Tree :=
  ((unbundle b).bind fun ds ↦ load (ds.map Prod.snd)).elim (leaf 0) fun G ↦
    mk 1 [mk 0 (G.map (·.1))]

/-- Terms the checker rejects: a node of a constructor with the wrong number of children, a
variable out of range, an annotation that is not a type, an application of a value that is
not a function, a conditional on a value that is not a tree, a label naming no constructor, a
primitive and a reference out of range, a list whose head has the wrong type, a projection of
a value that is not a pair, and a quotation of two trees. -/
def malformed : List Tree :=
  [mk 11 [leaf 0], mk 9 [leaf 0, mk 8 [leaf 1]], mk 9 [mk 5 [], mk 8 [leaf 0]],
   mk 10 [mk 11 [], mk 11 []], mk 16 [mk 11 [], mk 15 [leaf 1], mk 15 [leaf 2]], leaf 99,
   mk 22 [leaf 99], mk 23 [leaf 0], mk 20 [mk 11 [], mk 19 [leaf 0]], mk 17 [leaf 7],
   mk 13 [mk 15 [leaf 0]], mk 15 [leaf 1, leaf 2]]

/-- The seed's compilation of a program's source: the image of its bundle, or the empty file
when it does not read or is ill-typed. -/
def seedCompile (text : List Char) : Tree :=
  match readProgram text with
  | some ds => if (load (ds.map Prod.snd)).isSome then ofBytes (writeImage (bundle ds)) else mk 0 []
  | none => mk 0 []

/-- Trees exercising the serialization: a leaf, a label beyond a machine word, a node of many
children with labels of zero, and nested nodes. -/
def samples : List Tree :=
  [leaf 0, leaf (2 ^ 70 + 5), mk 7 ((List.range 300).map fun i ↦ leaf (i % 3)),
   mk 1 [mk 2 [leaf 3, mk 4 []], leaf 255, mk 256 [leaf 65536]]]

#guard samples.all fun t ↦ runMain serializer.toList t == some (ofBytes (writeImage t))
#guard (readProgram serializer.toList).all fun ds ↦
  runMain serializer.toList (bundle ds) == some (ofBytes (writeImage (bundle ds)))

-- the checker agrees with the seed on the kernel's examples, the compiler and malformed terms
#guard ([Tests.factorial, Tests.size, Tests.mirror, Tests.reverseChildren, Tests.quadruple,
    Tests.isZero, Tests.listCase, Tests.sugar, compiler].filterMap (readProgram ·.toList)
    |>.map bundle).all fun b ↦ runMain checker.toList b == some (seedTypes b)
#guard (malformed ++ [mk 9 [leaf 0, mk 8 [leaf 0]]]).all fun t ↦
  runMain checker.toList (bundle [("f".toList, t)]) == some (seedTypes (bundle [("f".toList, t)]))
#guard (malformed.map fun t ↦ seedTypes (bundle [("f".toList, t)])).all (· == leaf 0)
-- the stage-0 compiler agrees with the seed on the kernel's examples, rejected and ill-typed
-- ones included
#guard [Tests.factorial, Tests.size, Tests.mirror, Tests.reverseChildren, Tests.quadruple,
    Tests.isZero, Tests.listCase, Tests.sugar, "(def f (lam (x T) x)", "(def f (lam () 1))",
    "(def f (lam (x Nat) x))", "(def f (lam (x T) y))", "(def f (lam (x T) (add x unit)))",
    "(def f (lam (x T) (x x)))"].all fun p ↦
  runMain compiler.toList (nameTree p.toList) == some (seedCompile p.toList)
-- the fixed point: compiled by itself, the compiler is the image the seed builds of it
#guard runMain compiler.toList (nameTree compiler.toList) == some (seedCompile compiler.toList)

end Geb.Kernel.Stage0Tests

end
