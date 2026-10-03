/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Annotation -- shake: keep
public meta import Geb.Prototypes.Kernel.Annotation -- shake: keep
public import GebTests.Prototypes.Stage0 -- shake: keep
public meta import GebTests.Prototypes.Stage0 -- shake: keep

set_option doc.verso true in
/-!
# Content identity examples

BLAKE3 meets the official test vectors, whose inputs are the bytes {lit}`i % 251` for each
position {lit}`i`, at lengths on each side of the block, chunk and tree boundaries. A CIDv1
starts with its version, codec, hash code and digest length. The identifiers of
definitions are unchanged by renaming a definition and
changed, for a definition and the definitions referring to it, by a change of its body; the
migration of the stage-0 compiler's linked bundle gives back its payloads. BLAKE3, the
migration and the linker written in Geb, {lit}`bootstrap/identity.geb`, agree with Lean's, and
migrating a bundle the Geb linker links gives back its payloads. Names, as annotations re-keyed
by identifiers and vertices, address nodes of the payloads, are unchanged in their keys by
renaming, and agree between Geb and Lean.

## Tags

BLAKE3, CID, content identity, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Identity.Tests

open Geb.Kernel.Stage0Tests

/-- The lowercase hexadecimal spelling of bytes. -/
def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b ↦
    let h := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f']
    String.ofList [h.getD (b.toNat / 16) '0', h.getD (b.toNat % 16) '0'])

/-- The input of the official test vectors of a length. -/
def input (n : ℕ) : List UInt8 := (List.range n).map fun i ↦ (i % 251).toUInt8

-- the official test vectors, at lengths about the block, chunk and tree boundaries
#guard [(0, "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"),
    (1, "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213"),
    (64, "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98"),
    (65, "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee"),
    (1023, "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11"),
    (1024, "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7"),
    (1025, "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"),
    (2048, "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a"),
    (2049, "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030"),
    (3072, "b98cb0ff3623be03326b373de6b9095218513e64f1ee2edd2525c7ad1e5cffd2"),
    (4096, "015094013f57a5277b59d8475c0501042c0b642e531b0a1c8f58d2163229e969"),
    (8192, "aae792484c8efe4f19e2ca7d371d8c467ffb10748d8a5a1ae579948f718a2a63")].all
  fun (n, h) ↦ hexOf (Blake3.hash (input n)) == h

-- a CIDv1: version 1, the codec raw, BLAKE3's code and the digest's length, then the digest
#guard (cidOf []).take 4 = [0x01, 0x55, 0x1e, 0x20]
#guard (cidOf []).drop 4 = Blake3.hash []
#guard varint 300 = [0xac, 0x02]

/-- The identifiers of a program's definitions. -/
def cidsOf (src : List Char) : Option (List (List UInt8)) :=
  (readProgram src).map fun ds ↦ (migrate (ds.map Prod.snd)).map Payload.cid

/-- Which definitions of two programs have equal identifiers. -/
def sameCids (src src' : List Char) : Option (List Bool) := do
  let xs ← cidsOf src
  let ys ← cidsOf src'
  pure ((xs.zip ys).map fun (x, y) ↦ x == y)

-- renaming a definition, and the references to it, changes no identifier
#guard sameCids "(def a (lam ((x T)) x)) (def b (lam ((y T)) (a (a y))))".toList
  "(def c (lam ((x T)) x)) (def b (lam ((y T)) (c (c y))))".toList = some [true, true]
-- a changed definition changes its identifier and those of the definitions referring to it,
-- and no other
#guard sameCids
  "(def a (lam ((x T)) x)) (def b (lam ((y T)) (a y))) (def c (lam ((x T)) x))".toList
  "(def a (lam ((x T)) 0)) (def b (lam ((y T)) (a y))) (def c (lam ((x T)) x))".toList =
  some [false, false, true]
-- equal definitions have equal identifiers, whatever their names and positions
#guard (cidsOf "(def a (lam ((x T)) x)) (def b (lam ((z T)) z))".toList).map
  (fun cs ↦ cs[0]? == cs[1]?) = some true

-- the stage-0 compiler: migrating its linked payloads gives them back
#guard match readProgram compiler.toList with
  | some ds =>
    let ps := migrate (ds.map Prod.snd)
    (migrate (link ps)).map Payload.cid == ps.map Payload.cid
  | none => false

/-- The source of content identity written in Geb. -/
def identity : String := include_str "../../../bootstrap/identity.geb"

/-- The stage-0 compiler's sources and content identity, followed by a definition. -/
def withIdentity (main : String) : String := compiler ++ identity ++ "\n" ++ main

/-- BLAKE3 written in Geb, applied to the bytes of its input's children. -/
def hasher : String := withIdentity "(def hashMain (lam ((t T)) (node 0 (blake3 (children t)))))"

/-- The migration written in Geb, applied to a bundle's definitions: the payloads, their
identifiers, the linked bundle, and whether migrating it gives the payloads back. -/
def migrator : String :=
  withIdentity <| "(def migrateMain (lam ((b T)) (let ps Ts (migrate (children (child b 0))) " ++
    "(let ds Ts (link ps) (node 0 (cons (node 0 ps) (cons (node 0 (cidsOf ps)) " ++
    "(cons (node 0 ds) (single (equal (node 0 (migrate ds)) (node 0 ps)))))))))))"

/-- Bytes as a node over their leaves. -/
def bytesTree (bs : List UInt8) : Tree := mk 0 (bs.map fun b ↦ leaf b.toNat)

/-- A payload as the Geb migration writes it: a node over the node of its imports and its
body. -/
def payloadTree (p : Payload) : Tree := mk 0 [mk 0 (p.imports.map bytesTree), p.body]

/-- What the migration written in Geb gives for a bundle's definitions, computed in Lean. -/
def expected (ds : List Tree) : Tree :=
  let ps := migrate ds
  mk 0 [mk 0 (ps.map payloadTree), mk 0 (ps.map fun p ↦ bytesTree p.cid), mk 0 (link ps), leaf 1]

-- BLAKE3 written in Geb agrees with the host binding about the block, chunk and tree boundaries
#guard [0, 1, 64, 65, 1024, 1025, 2049, 4096].all fun n ↦
  runMain hasher.toList (bytesTree (input n)) == some (bytesTree (Blake3.hash (input n)))

-- the migration and the linker written in Geb agree with Lean's, and migrating the linked
-- bundle gives the payloads back, on examples and on the prelude and serializer
#guard ["(def a (lam ((x T)) x)) (def b (lam ((y T)) (a (a y))))",
    "(def a (lam ((x T)) (quote (23 0)))) (def b (lam ((y T)) (pair (a y) (a (a y)))))",
    serializer].all fun src ↦
  match readProgram src.toList with
  | some ds =>
    runMain migrator.toList (bundle ds) == some (expected (ds.map Prod.snd))
  | none => false

/-- A note as the Geb names write it: a node of label 0 over a declared name's characters, or
of label 1 over a written name's. -/
def noteTree : Note → Tree
  | .declared n => mk 0 (n.map fun c ↦ leaf c.toNat)
  | .written n => mk 1 (n.map fun c ↦ leaf c.toNat)

/-- The names of a bundle as annotations keyed by identifiers and vertices. -/
def namesOf (ds : List (List Char × Tree)) : List ((List UInt8 × List ℕ) × Note) :=
  rekey ((migrate (ds.map Prod.snd)).map Payload.cid) (nameNotes ds)

/-- Whether every key of a bundle's names addresses a node of a payload with its identifier. -/
def namesValid (ds : List (List Char × Tree)) : Bool :=
  let ps := migrate (ds.map Prod.snd)
  let cs := ps.map fun p ↦ (p.cid, p.body)
  (rekey (cs.map Prod.fst) (nameNotes ds)).all fun ((c, v), _) ↦
    cs.any fun (c', b) ↦ c' == c && (subtree? b v).isSome

/-- The names written in Geb, applied to a bundle. -/
def namer : String :=
  withIdentity <| "(def namesMain (lam ((b T)) (let ds Ts (children (child b 0)) " ++
    "(node 0 (nameNotes (children (child b 1)) (cidsOf (migrate ds)) ds)))))"

-- the names of a bundle: each definition's at the root of its term, and each reference's at its
-- vertex
#guard ((readProgram
    "(def a (lam ((x T)) x)) (def b (lam ((y T)) (a (a y)))) (def c b)".toList).map
    nameNotes) =
  some [((0, []), .declared ['a']), ((1, []), .declared ['b']), ((1, [1, 0]), .written ['a']),
    ((1, [1, 1, 0]), .written ['a']), ((2, []), .declared ['c']), ((2, []), .written ['b'])]
-- re-keyed by identifiers, every key of the stage-0 compiler's names addresses a node of a
-- payload with that identifier
#guard (readProgram compiler.toList).all namesValid
-- renaming changes the names and no key
#guard ((readProgram "(def a (lam ((x T)) x)) (def b (lam ((y T)) (a y)))".toList).map
    fun ds ↦ (namesOf ds).map (·.1)) =
  ((readProgram "(def c (lam ((x T)) x)) (def b (lam ((y T)) (c y)))".toList).map
    fun ds ↦ (namesOf ds).map (·.1))

-- the names written in Geb agree with Lean's
#guard ["(def a (lam ((x T)) x)) (def b (lam ((y T)) (a (a y)))) (def c b)", serializer].all
  fun src ↦
  match readProgram src.toList with
  | some ds =>
    runMain namer.toList (bundle ds) == some (mk 0 ((namesOf ds).map fun ((c, v), n) ↦
      mk 0 [bytesTree c, mk 0 (v.map leaf), noteTree n]))
  | none => false

end Geb.Kernel.Identity.Tests

end
