/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.RoseTree

/-!
# Rose-tree representation benchmark

Run with `lake exe rosebench`. Measures the cost of the operations on rose
trees of bitstrings in the two regimes the representation serves: trees of
many nodes with short labels, and trees of few nodes with long labels. The
list-form serialization and recognizer, the word-level ones, a fold, equality
and a hash are timed on each; the output is a table of nanoseconds per node,
which the manual's representation chapter records.

## Main definitions

* `main`: run every measurement and print the table.
-/

open Geb Geb.RoseTree Geb.Packed

/-- A full tree of a given branching and depth whose labels vary with a seed,
so that no two subtrees are shared. -/
def fresh (k d : ℕ) : ℕ → RoseTree ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → RoseTree ℕ) (fun seed ↦ node (seed % 200) [])
    (fun _ ih seed ↦ node (seed % 200) ((List.range k).map fun i ↦ ih (seed * k + i + 1))) d

/-- The number of nodes. -/
def size : RoseTree ℕ → ℕ := elim fun _ cs ↦ 1 + cs.sum

/-- Structural equality, by a fold on the first tree. -/
def beq : RoseTree ℕ → RoseTree ℕ → Bool := elim fun a ks u ↦
  u.label == a && u.children.length == ks.length &&
    (List.zipWith (fun k c ↦ k c) ks u.children).all id

/-- A shape-following hash. -/
def hashTree : RoseTree ℕ → UInt64 := elim fun a hs ↦ hs.foldl mixHash (hash a)

/-- Time a computation, returning its result and the elapsed nanoseconds. The
computation is a thunk, forced between the two readings of the clock, since
an argument evaluated before the call would be timed at zero. -/
def timed {α : Type} (f : Unit → α) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  let t1 ← IO.monoNanosNow
  pure (r, t1 - t0)

/-- Report one measurement as nanoseconds per node. -/
def report (regime op : String) (nodes ns : Nat) : IO Unit := do
  IO.println s!"{regime}\t{op}\t{nodes}\t{ns / 1000000} ms\t{ns / nodes} ns/node"
  (← IO.getStdout).flush

/-- Run every measurement on one tree; the list forms only when asked, since
the list form of a long label is quadratic in its length. -/
def bench (regime : String) (lists : Bool) (build : Unit → RoseTree ℕ) : IO Unit := do
  let (t, nsBuild) ← timed build
  let (n, nsSize) ← timed fun _ ↦ size t
  report regime "build" n nsBuild
  report regime "size (fold)" n nsSize
  let (p, nsPack) ← timed fun _ ↦ Packed.encode t
  report regime "encode (packed)" n nsPack
  IO.println s!"{regime}\tbits\t{p.nbits}\tbytes {p.bytes.size}"
  if lists then
    let (w, nsWire) ← timed fun _ ↦ wire t
    report regime "wire (list)" n nsWire
    let (ok1, nsVal) ← timed fun _ ↦ Geb.BitTree.Elias.validBool w
    report regime s!"validBool (list) = {ok1}" n nsVal
  let (ok2, nsRec) ← timed fun _ ↦ Packed.recognize p
  report regime s!"recognize (packed) = {ok2}" n nsRec
  let (d, nsDec) ← timed fun _ ↦ Packed.decode p
  report regime s!"decode (packed) ok = {d.isSome}" n nsDec
  let (u, _) ← timed build
  let (e, nsEq) ← timed fun _ ↦ beq t u
  report regime s!"equality = {e}" n nsEq
  let (_, nsHash) ← timed fun _ ↦ hashTree t
  report regime "hash (fold)" n nsHash

/-- A chain of a few nodes with labels of the given bit length. -/
def blob (bits : ℕ) : RoseTree ℕ :=
  node (2 ^ bits + 12345) [node (2 ^ bits + 67890) [node (2 ^ bits + 1) []], node 3 []]

/-- Run every measurement and print the table. -/
public def main (args : List String) : IO UInt32 := do
  let small := args.contains "--small"
  IO.println "regime\top\tnodes\ttotal\tper node"
  bench "syntax k=3 d=8" true fun _ ↦ fresh 3 8 1
  unless small do
    bench "syntax k=2 d=16" false fun _ ↦ fresh 2 16 1
    bench "syntax k=8 d=5" false fun _ ↦ fresh 8 5 1
  bench "blob 2^12 bits" true fun _ ↦ blob 4096
  unless small do
    bench "blob 2^16 bits" false fun _ ↦ blob 65536
    bench "blob 2^20 bits" false fun _ ↦ blob 1048576
  pure 0
