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
serialized as bytes: a header of a magic number, a format version, a kernel profile and the
number of payload bits, followed by the bundle's serialization at word level. A file is presented to
a program as the tree whose children are the leaves of its bytes, and a program's output
tree is written back as the bytes of its children's labels.

The bundle's tree is a node of label {lit}`100` over two nodes: one of label {lit}`101`
whose children are the definitions, and one of label {lit}`102` whose children are the
names, each a node whose children are the leaves of its characters' code points. The
header is the four bytes of {lit}`GEBK`, the format byte {lit}`2`, the kernel-profile byte
{lit}`1` identifying {lit}`geb-kernel/v1`, and the bit count as eight bytes, least significant
first. The format determines the framing and payload codec; the profile determines the kernel's
types, term labels and primitives. Their versions are independent. Format {lit}`1` has no profile
byte and denotes {lit}`geb-kernel/v1` implicitly. Both formats are read; writers use format
{lit}`2`. Migration changes the header alone, retaining the bit count and payload bytes.

## Main definitions

* {lit}`bundle`, {lit}`unbundle` — a program's definitions as a tree, and back.
* {lit}`writeImage`, {lit}`readImage` — the image of a tree, and the tree of an image.
* {lit}`migrateImage` — validate an image and give it the explicit-profile header.
* {lit}`runEntry` — the application of a bundle's named definition to an input tree.
* {lit}`ofBytes`, {lit}`toBytes` — a file's bytes as a tree, and a tree's children as bytes.
* {lit}`hexBytes`, {lit}`definitionsOfHex` — the bytes a string of hexadecimal digits spells, and
  the definitions of the program whose image they are.

## Main statements

* {lit}`readImage_migrateImage` — migration preserves the decoded tree.

## Implementation notes

The reader of an image rejects a wrong magic number, unsupported format or kernel profile,
a bit count inconsistent with the payload's length, nonzero bits beyond the count, and a
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

/-- The version of the image's framing and payload codec, independently of the kernel profile. -/
def imageVersion : UInt8 := 2

/-- The supported kernel profile: byte {lit}`1` identifies {lit}`geb-kernel/v1`, the types,
term labels and primitive indices of the bootstrap kernel. -/
def imageKernelProfile : UInt8 := 1

/-- The magic number and version of the image format. -/
def imageMagic : List UInt8 := [0x47, 0x45, 0x42, 0x4B, imageVersion]

/-- The image header before the bit count, including its kernel profile. -/
def imageHeader : List UInt8 := imageMagic ++ [imageKernelProfile]

/-- The bytes of a natural number below {lit}`2^64`, least significant first. -/
def natBytes (n : ℕ) : List UInt8 := (List.range 8).map fun i ↦ (n / 256 ^ i % 256).toUInt8

/-- The natural number of bytes, least significant first. -/
def bytesNat (bs : List UInt8) : ℕ := bs.foldr (fun b n ↦ b.toNat + 256 * n) 0

/-- The image of a tree. -/
def writeImage (t : Tree) : ByteArray :=
  let b := Packed.encode t
  ⟨(imageHeader ++ natBytes b.nbits).toArray⟩ ++ b.bytes

/-- The bit count and payload after a supported header. Format {lit}`1` denotes profile
{lit}`1` implicitly; format {lit}`2` carries it explicitly. No other profile is accepted. -/
def imageBody (img : ByteArray) : Option (List UInt8) :=
  let bs := img.data.toList
  if bs.take 5 == [0x47, 0x45, 0x42, 0x4B, 1] then some (bs.drop 5)
  else if bs.take 6 == imageHeader then some (bs.drop 6)
  else none

/-- Decode an image's bit count and payload, checking its length, padding and tree encoding. -/
def readImageBody (bs : List UInt8) : Option Tree :=
  let nbits := bytesNat (bs.take 8)
  let payload := bs.drop 8
  let slack := 8 * payload.length - nbits
  if 8 ≤ bs.length && payload.length == (nbits + 7) / 8 &&
      payload.getLast?.all (fun b ↦ b.toNat / 2 ^ (8 - slack) == 0) then
    Packed.decode ⟨⟨payload.toArray⟩, nbits⟩
  else none

/-- The tree of a well-formed image with a supported format and kernel profile. -/
def readImage (img : ByteArray) : Option Tree := (imageBody img).bind readImageBody

/-- Validate an image and replace its header with the explicit-profile header, retaining its
bit count and payload bytes. Malformed images and unsupported profiles are rejected. -/
def migrateImage (img : ByteArray) : Option ByteArray := do
  let body ← imageBody img
  let _ ← readImageBody body
  return ⟨(imageHeader ++ body).toArray⟩

/-- Reading the explicit-profile header recovers the body. -/
theorem imageBody_header (body : List UInt8) :
    imageBody ⟨(imageHeader ++ body).toArray⟩ = some body := by
  simp [imageBody, imageHeader, imageMagic, imageVersion, imageKernelProfile]

/-- Migrating an accepted image preserves its decoded tree, without re-encoding the payload. -/
theorem readImage_migrateImage (img out : ByteArray) (h : migrateImage img = some out) :
    readImage out = readImage img := by
  unfold migrateImage at h
  cases hb : imageBody img with
  | none => simp [hb] at h
  | some body =>
    cases hr : readImageBody body with
    | none => simp [hb, hr] at h
    | some t =>
      simp [hb, hr] at h
      subst out
      simp [readImage, imageBody_header, hb]

/-- A file's bytes as a tree: a node whose children are the leaves of the bytes. -/
def ofBytes (b : ByteArray) : Tree := mk 0 (b.data.toList.map fun x ↦ leaf x.toNat)

/-- A tree's children as bytes, when every child's label is below {lit}`256`. -/
def toBytes (t : Tree) : Option ByteArray :=
  (t.children.mapM fun c ↦ if c.label < 256 then some c.label.toUInt8 else none).map
    fun l ↦ ⟨l.toArray⟩

/-- The value of a hexadecimal digit, the letters in lower case. -/
def hexDigit (c : Char) : Option UInt8 :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48).toUInt8
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87).toUInt8
  else none

/-- The bytes a string of hexadecimal digits spells, two digits to a byte, the fold carrying the
bytes read and the high digit of the byte being read. -/
def hexBytes (s : String) : Option ByteArray :=
  (s.toList.foldl (fun (acc : Option (ByteArray × Option UInt8)) c ↦ do
      let (bs, hi) ← acc
      let d ← hexDigit c
      match hi with
      | none => some (bs, some d)
      | some h => some (bs.push (h * 16 + d), none))
    (some (ByteArray.empty, none))).bind fun (bs, hi) ↦ if hi.isNone then some bs else none

/-- The definitions, each with its name, of the program whose image a string spells in
hexadecimal, where the string spells an image that reads to a bundle. -/
def definitionsOfHex (s : String) : Option (List (List Char × Tree)) :=
  ((hexBytes s).bind readImage).bind unbundle

end Geb.Kernel

end
