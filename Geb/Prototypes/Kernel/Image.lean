/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Reader
public import Geb.Prototypes.RoseTree.Packed

set_option doc.verso true in
/-!
# Bundles and images

A closed bundle is a program as one rose tree: its definitions in order, each a kernel term
referring to earlier ones by position, beside a table of their names. An image is a bundle
serialized as bytes: a header of a magic number, a format version and the number of
payload bits, followed by the bundle's serialization at word level. A file is presented to
a program as the tree whose children are the leaves of its bytes, and a program's output
tree is written back as the bytes of its children's labels.

The bundle's tree is a node of label {lit}`100` over two nodes: one of label {lit}`101`
whose children are the definitions, and one of label {lit}`102` whose children are the
names, each a node whose children are the leaves of its characters' code points. The
header is the four bytes of {lit}`GEBK`, the version byte {lit}`1`, and the bit count as
eight bytes, least significant first.

## Main definitions

* {lit}`bundle`, {lit}`unbundle` — a program's definitions as a tree, and back.
* {lit}`writeImage`, {lit}`readImage` — the image of a tree, and the tree of an image.
* {lit}`runEntry` — the application of a bundle's named definition to an input tree.
* {lit}`ofBytes`, {lit}`toBytes` — a file's bytes as a tree, and a tree's children as bytes.

## Implementation notes

The reader of an image rejects a wrong magic number or version, a bit count inconsistent
with the payload's length, a payload whose bits beyond the count are not zero, and a
payload holding anything but exactly one tree; {name}`Geb.Packed.decode` makes the last
check. The payload's codec agrees with {name}`Geb.RoseTree.wire` by test, not by proof.

## Tags

bootstrap, kernel, bundle, image, serialization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

/-- The tree of a name: the leaves of its characters' code points. -/
def nameTree (cs : List Char) : Tree := mk 0 (cs.map fun c ↦ leaf c.toNat)

/-- The name a tree holds, when every child is the leaf of a character's code point. -/
def ofNameTree (t : Tree) : Option (List Char) :=
  t.children.mapM fun c ↦
    if c.children.isEmpty && (Char.ofNat c.label).toNat == c.label then some (Char.ofNat c.label)
    else none

/-- A program's definitions as one tree. -/
def bundle (ds : List (List Char × Tree)) : Tree :=
  mk 100 [mk 101 (ds.map Prod.snd), mk 102 (ds.map fun d ↦ nameTree d.1)]

/-- A program's definitions from its tree, when the tree has the shape of a bundle. -/
def unbundle (t : Tree) : Option (List (List Char × Tree)) :=
  match t.label, t.children with
  | 100, [defs, names] =>
    if defs.label == 101 && names.label == 102 &&
        defs.children.length == names.children.length then do
      let ns ← names.children.mapM ofNameTree
      some (ns.zip defs.children)
    else none
  | _, _ => none

/-- Apply a bundle's named definition, of type {lit}`T → T`, to an input tree. -/
def runEntry (t : Tree) (name : List Char) (input : Tree) : Option Tree := do
  let ds ← unbundle t
  let G ← load (ds.map Prod.snd)
  let i ← (ds.map Prod.fst).idxOf? name
  (← G[i]?).apply input

/-- The magic number and version of the image format. -/
def imageMagic : List UInt8 := [0x47, 0x45, 0x42, 0x4B, 1]

/-- The bytes of a natural number below {lit}`2^64`, least significant first. -/
def natBytes (n : ℕ) : List UInt8 := (List.range 8).map fun i ↦ (n / 256 ^ i % 256).toUInt8

/-- The natural number of bytes, least significant first. -/
def bytesNat (bs : List UInt8) : ℕ := bs.foldr (fun b n ↦ b.toNat + 256 * n) 0

/-- The image of a tree. -/
def writeImage (t : Tree) : ByteArray :=
  let b := Packed.encode t
  ⟨(imageMagic ++ natBytes b.nbits).toArray⟩ ++ b.bytes

/-- The tree of an image, when the image is well formed. -/
def readImage (img : ByteArray) : Option Tree :=
  let bs := img.data.toList
  let nbits := bytesNat ((bs.drop 5).take 8)
  let payload := bs.drop 13
  let slack := 8 * payload.length - nbits
  if bs.take 5 == imageMagic && 13 ≤ bs.length && payload.length == (nbits + 7) / 8 &&
      payload.getLast?.all (fun b ↦ b.toNat / 2 ^ (8 - slack) == 0) then
    Packed.decode ⟨⟨payload.toArray⟩, nbits⟩
  else none

/-- A file's bytes as a tree: a node whose children are the leaves of the bytes. -/
def ofBytes (b : ByteArray) : Tree := mk 0 (b.data.toList.map fun x ↦ leaf x.toNat)

/-- A tree's children as bytes, when every child's label is below {lit}`256`. -/
def toBytes (t : Tree) : Option ByteArray :=
  (t.children.mapM fun c ↦ if c.label < 256 then some c.label.toUInt8 else none).map
    fun l ↦ ⟨l.toArray⟩

end Geb.Kernel

end
