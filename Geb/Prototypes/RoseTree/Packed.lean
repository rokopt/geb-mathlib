/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.RoseTree.Spine  -- shake: keep; the docstrings' name roles need it
public import Mathlib.Tactic.NormNum

set_option doc.verso true in
/-!
# The serialization at word level

The serialization {name}`Geb.RoseTree.wire` is a list of bits. This module
writes the same bits into a byte buffer, eight per byte and least significant
first within each byte, reads them back, and recognizes them, each by
machine-word operations on the buffer rather than by list cells. The
operations are stated to agree with the list forms; the agreement is tested
rather than proved, the buffer lemmas of the core library being too few for
the proofs at present, and the measurements are the module's purpose.

A node reads as its arity in unary, a zero, the delta-coded length of its
label, the label's bits in stream order, and the children. The delta code's
fixed-width fields are written most significant bit first, as the list form
{name}`Geb.BitTree.Elias.encodeNat` writes them.

# Main definitions

* {lit}`Packed.Buf` — a byte buffer with a bit count.
* {lit}`Packed.Buf.pushBits`, {lit}`Packed.Buf.pushOnes` — writing.
* {lit}`Packed.Buf.getBit`, {lit}`Packed.Buf.readBits` — reading.
* {lit}`Packed.encode` — the serialization into a buffer.
* {lit}`Packed.stepWord`, {lit}`Packed.run` — the streaming reader, a fold over
  the buffer's words with a mode, whole payload words passed in one step.
* {lit}`Packed.recognize` — the one-counter recognizer of serialized trees.
* {lit}`Packed.decode` — the decoder, the same reader keeping a stack.
* {lit}`Packed.Buf.toList`, {lit}`Packed.Buf.ofList` — the comparison with
  the list form.

# Tags

serialization, bit buffer, machine word, recognizer, decoder
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Packed

open Geb.RoseTree (node label children elim)

/-- A byte buffer holding a number of bits, least significant bit of each
byte first; the bits beyond the count are zero. -/
structure Buf where
  /-- The bytes. -/
  bytes : ByteArray
  /-- The number of valid bits. -/
  nbits : ℕ
  deriving Inhabited

namespace Buf

/-- The empty buffer. -/
def empty : Buf := ⟨.empty, 0⟩

/-- The low {lit}`k` bits of a word, for {lit}`k ≤ 64`. -/
def mask (w : UInt64) (k : ℕ) : UInt64 :=
  if k ≥ 64 then w else w &&& ((1 <<< k.toUInt64) - 1)

/-- Append the low {lit}`k` bits of a word, least significant first, for
{lit}`k ≤ 64`. -/
def pushBits (b : Buf) (w : UInt64) (k : ℕ) : Buf :=
  let w := mask w k
  let off := b.nbits % 8
  -- Fill the partial last byte, then push whole bytes.
  let (bytes, w, rest) :=
    if off = 0 then (b.bytes, w, k) else
      let idx := b.bytes.size - 1
      let room := 8 - off
      let taken := min room k
      let patched := b.bytes.get! idx ||| ((mask w taken).toUInt8 <<< off.toUInt8)
      (b.bytes.set! idx patched, w >>> taken.toUInt64, k - taken)
  let bytes := Nat.fold ((rest + 7) / 8) (fun i _ acc ↦ acc.push (w >>> (8 * i).toUInt64).toUInt8)
    bytes
  ⟨bytes, b.nbits + k⟩

/-- Append one bit. -/
def pushBit (b : Buf) (x : Bool) : Buf := b.pushBits (if x then 1 else 0) 1

/-- Append {lit}`k` one bits. -/
def pushOnes (b : Buf) (k : ℕ) : Buf :=
  (Nat.fold (k / 64) (fun _ _ acc ↦ acc.pushBits (0 - 1) 64) b).pushBits (0 - 1) (k % 64)

/-- The low {lit}`k` bits of a word in reverse order, for {lit}`k ≤ 64`. -/
def reverseBits (w : UInt64) (k : ℕ) : UInt64 :=
  Nat.fold k (fun i _ acc ↦ acc ||| (((w >>> i.toUInt64) &&& 1) <<< (k - 1 - i).toUInt64)) 0

/-- Append the low {lit}`k` bits of a word, most significant first. -/
def pushBitsRev (b : Buf) (w : UInt64) (k : ℕ) : Buf := b.pushBits (reverseBits w k) k

/-- The bit at a position, false beyond the count. -/
def getBit (b : Buf) (i : ℕ) : Bool :=
  i < b.nbits && (b.bytes.get! (i / 8) >>> (i % 8).toUInt8) &&& 1 == 1

/-- The {lit}`k` bits from a position as a word, least significant first, for
{lit}`k ≤ 64`; bits beyond the count read as zero. -/
def readBits (b : Buf) (i : ℕ) (k : ℕ) : UInt64 :=
  let off := i % 8
  let first := i / 8
  -- Nine bytes cover any window of at most 64 bits at any offset.
  let raw := Nat.fold 9 (fun j _ acc ↦
    let byte := if first + j < b.bytes.size then b.bytes.get! (first + j) else 0
    if j = 8 then acc else acc ||| (byte.toUInt64 <<< (8 * j).toUInt64)) 0
  let ninth := if first + 8 < b.bytes.size then b.bytes.get! (first + 8) else 0
  let high := if off = 0 then 0 else ninth.toUInt64 <<< (64 - off).toUInt64
  let shifted := (raw >>> off.toUInt64) ||| high
  mask shifted k

/-- The {lit}`k` bits from a position, most significant first. -/
def readBitsRev (b : Buf) (i : ℕ) (k : ℕ) : UInt64 := reverseBits (b.readBits i k) k

/-- The bits as a list, in stream order. -/
def toList (b : Buf) : List Bool := (List.range b.nbits).map b.getBit

/-- A buffer holding a list of bits. -/
def ofList (l : List Bool) : Buf := l.foldl pushBit empty

end Buf

/-- Write the Elias delta code of a length, as {name}`Geb.BitTree.Elias.encodeNat`
lays it out: the size of the size in unary zeros and a one, the size's payload,
then the length's payload, the fixed fields most significant bit first. -/
def writeNat (b : Buf) (n : ℕ) : Buf :=
  let m := n + 1
  let s := m.log2 + 1
  let z := s.log2
  (((b.pushBits 0 z).pushBit true).pushBitsRev s.toUInt64 z).pushBitsRev m.toUInt64 (s - 1)

/-- Write a label's bits in stream order: the bits of its sentinel numeral
below the sentinel, sixty-four at a time. -/
def writeLabel (b : Buf) (a : ℕ) : Buf :=
  let m := a + 1
  let len := m.log2
  let whole := len / 64
  (Nat.fold whole (fun i _ acc ↦ acc.pushBits (m >>> (64 * i)).toUInt64 64) b).pushBits
    (m >>> (64 * whole)).toUInt64 (len % 64)

/-- Write one node's header: its arity in unary and a zero, its label's
length and its label. -/
def writeNode (b : Buf) (arity : ℕ) (a : ℕ) : Buf :=
  writeLabel (writeNat ((b.pushOnes arity).pushBit false) (a + 1).log2) a

/-- The serialization into a buffer, appended to a buffer. -/
def encodeInto (t : Geb.RoseTree ℕ) : Buf → Buf :=
  elim (fun a ks b ↦ ks.foldl (fun b k ↦ k b) (writeNode b ks.length a)) t

/-- The serialization into a buffer. -/
def encode (t : Geb.RoseTree ℕ) : Buf := encodeInto t Buf.empty

/-- A frame of the decoder's stack: a label, the number of children still to
read, and the children read so far, most recent first. -/
structure Frame where
  /-- The label. -/
  label : ℕ
  /-- The number of children still to read. -/
  remaining : ℕ
  /-- The children read so far, most recent first. -/
  done : List (Geb.RoseTree ℕ)

/-- The mode of the streaming reader: counting the ones of an arity, the
zeros of a delta code, reading the size field and the length field most
significant bit first, and passing over a payload; or finished, or failed. -/
inductive Mode where
  /-- Counting the ones of an arity. -/
  | arity (k : ℕ)
  /-- Counting the leading zeros of a delta code. -/
  | zeros (z : ℕ)
  /-- Reading the size field: bits remaining, value so far, its top bit. -/
  | size (rem acc top : ℕ)
  /-- Reading the length field: bits remaining, value so far, its top bit. -/
  | len (rem acc top : ℕ)
  /-- Passing over a payload: bits remaining, bits taken, value so far. -/
  | payload (rem taken acc : ℕ)
  /-- Finished: the last tree closed. -/
  | done
  /-- Failed. -/
  | fail
  deriving Inhabited

/-- The streaming state: the mode, the number of trees still to read, the
frames of open nodes, and the arity of the node being read. -/
structure St where
  /-- The mode. -/
  mode : Mode
  /-- The number of trees still to read. -/
  pending : ℕ
  /-- The frames of open nodes, innermost first. -/
  stack : List Frame
  /-- The arity of the node being read. -/
  arity : ℕ
  /-- The tree read, once the reader is done. -/
  result : Option (Geb.RoseTree ℕ)
  deriving Inhabited

/-- One closing step: a completed tree is appended to the frame below, and a
frame with no child remaining becomes a completed tree; a settled state is
kept. -/
def closeStep (st : Sum (List Frame × Geb.RoseTree ℕ) (List Frame)) :
    Sum (List Frame × Geb.RoseTree ℕ) (List Frame) :=
  match st with
  | Sum.inl (f :: rest, t) =>
    if f.remaining = 1 then Sum.inl (rest, node f.label (t :: f.done).reverse)
    else Sum.inr ({ f with remaining := f.remaining - 1, done := t :: f.done } :: rest)
  | st => st

/-- Close completed frames after a node completes, as many times as the stack
is deep: the remaining stack, or the finished tree when none remains. -/
def close (stack : List Frame) (t : Geb.RoseTree ℕ) :
    Sum (List Frame × Geb.RoseTree ℕ) (List Frame) :=
  Nat.fold stack.length (fun _ _ st ↦ closeStep st) (Sum.inl (stack, t))

/-- A node's header is complete: open a frame for it, or close frames with it
when it is a leaf; then continue with the next node or finish. -/
def finishNode (st : St) (label : ℕ) : St :=
  if st.arity = 0 then
    match close st.stack (node label []) with
    | Sum.inl ([], t) => { st with mode := .done, stack := [], result := some t }
    | Sum.inl (stack, _) => { st with mode := .fail, stack := stack }
    | Sum.inr stack => { st with mode := .arity 0, stack := stack }
  else { st with mode := .arity 0, stack := ⟨label, st.arity, []⟩ :: st.stack }

/-- Settle the fields that may be empty: a size of one, a length field of no
bits, an empty payload. Each of the three cases moves to a later mode, so
three passes suffice. -/
def settleOnce (st : St) : St :=
  match st.mode with
  | .size 0 acc top => { st with mode := .len (acc + top - 1) 0 (1 <<< (acc + top - 1)) }
  | .len 0 acc top => { st with mode := .payload (acc + top - 1) 0 0 }
  | .payload 0 taken acc => finishNode st (acc + (1 <<< taken) - 1)
  | _ => st

/-- Settle every empty field. -/
def settle (st : St) : St := settleOnce (settleOnce (settleOnce st))

/-- One bit of the streaming reader. -/
def stepBit (st : St) (bit : Bool) : St :=
  match st.mode with
  | .arity k => if bit then { st with mode := .arity (k + 1) } else
      if st.pending = 0 then { st with mode := .fail } else
      settle { st with mode := .zeros 0, pending := st.pending - 1 + k, arity := k }
  | .zeros z => if bit then settle { st with mode := .size z 0 (1 <<< z) }
      else { st with mode := .zeros (z + 1) }
  | .size rem acc top => settle { st with mode := .size (rem - 1) (2 * acc + bit.toNat) top }
  | .len rem acc top => settle { st with mode := .len (rem - 1) (2 * acc + bit.toNat) top }
  | .payload rem taken acc =>
      settle { st with mode := .payload (rem - 1) (taken + 1) (acc ||| (bit.toNat <<< taken)) }
  | .done => { st with mode := .fail }
  | .fail => st

/-- The low {lit}`k` bits of a word through the reader, a payload's whole
words passed over in one step. -/
def stepWord (st : St) (w : UInt64) (k : ℕ) : St :=
  match st.mode with
  | .payload rem taken acc =>
    if rem ≥ k then
      settle { st with mode := .payload (rem - k) (taken + k) (acc ||| (w.toNat <<< taken)) }
    else Nat.fold k (fun j _ st ↦ stepBit st (((w >>> j.toUInt64) &&& 1) == 1)) st
  | .fail => st
  | _ => Nat.fold k (fun j _ st ↦ stepBit st (((w >>> j.toUInt64) &&& 1) == 1)) st

/-- The initial state: one tree to read. -/
def St.init : St := ⟨.arity 0, 1, [], 0, none⟩

/-- Run the streaming reader over a buffer, sixty-four bits at a time. -/
def run (b : Buf) : St :=
  let words := b.nbits / 64
  let tail := b.nbits % 64
  let st := Nat.fold words (fun i _ st ↦ stepWord st (b.readBits (64 * i) 64) 64) St.init
  stepWord st (b.readBits (64 * words) tail) tail

/-- The recognizer: the streaming reader finishes exactly at the end. -/
def recognize (b : Buf) : Bool :=
  match (run b).mode with
  | .done => true
  | _ => false

/-- The decoder: the tree a buffer holds, when it holds exactly one. -/
def decode (b : Buf) : Option (Geb.RoseTree ℕ) :=
  match run b with
  | ⟨.done, _, _, _, r⟩ => r
  | _ => none

end Geb.Packed

end
