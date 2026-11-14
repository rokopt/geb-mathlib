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
# The serializer's list processing

The serializer written in Geb, loaded once and run by Lean's interpreter, compared byte for
byte with the seed's image writer. The inputs exercise every final-byte alignment, the length
boundaries of labels, a wide tree, a long label and a nested tree. List processing uses data
accumulators rather than chains of continuations; the fold counting the nodes still follows
the depth of the input tree.

## Tags

serializer, bootstrap, image, stack, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.SerializerTests

#eval show IO Unit from do
  let some ds := readProgram Stage0Tests.serializer.toList
    | throw (IO.userError "the serializer does not read")
  let some globals := load (ds.map Prod.snd)
    | throw (IO.userError "the serializer does not load")
  let some f := globals.getLast?
    | throw (IO.userError "the serializer has no entry point")
  let checkImage (t : Tree) : IO Unit := do
    let some actual := (f.apply t).bind toBytes
      | throw (IO.userError "the serializer did not return bytes")
    unless actual == writeImage t do
      throw (IO.userError "the serializer disagrees with the seed's image writer")
    unless readImage actual == some t do
      throw (IO.userError "the seed does not read the serialized tree back")
  -- A zero-labelled root with n zero-labelled leaves takes 2 + 3 * n bits.
  for n in List.range 16 do
    checkImage (mk 0 (List.replicate n (leaf 0)))
  for n in [1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 65, 127, 128] do
    for a in [2 ^ n - 2, 2 ^ n - 1, 2 ^ n] do
      checkImage (leaf a)
  checkImage (mk 7 ((List.range 4096).map fun i ↦ leaf (i % 256)))
  checkImage (leaf (2 ^ 8192 + 5))
  checkImage (Nat.repeat (fun t ↦ mk 256 [leaf 0, t, leaf 65536]) 128 (leaf 7))

end Geb.Kernel.SerializerTests

end
