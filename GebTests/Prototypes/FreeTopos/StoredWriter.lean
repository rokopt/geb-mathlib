/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certificates
public import GebTests.Prototypes.FreeTopos.Stored

set_option doc.verso true in
/-!
# Writing the certificates

A development of the internal language as the text of a certificate: the table of the distinct
nodes of its tree ({lit}`GebTests.Prototypes.FreeTopos.Stored`), found by a hash table, written as
its numbers in decimal, which {name}`GebTests.Prototypes.FreeTopos.Stored.declsOfText` reads back.

## Main definitions

* {lit}`treeToNats` — a tree as the table of its distinct nodes.
* {lit}`declsToText` — declarations of theorems as text.
* {lit}`generate` — the certificates of the developments
  ({name}`GebTests.Prototypes.FreeTopos.Certificates.searches`) written into a directory.

## Implementation notes

The hash table, Lean's {lit}`Std.HashMap`, depends on {lit}`Classical.choice`, so the module is
admitted to {lit}`GebMeta.classicalAllowedModules`, with the writing of the certificates, which
uses it: the module writes certificates and proves nothing, and the reading of a certificate, in
{lit}`Stored`, and the searches, in {lit}`Certificates`, are held to the strict axiom set.

## Tags

internal language, development, serialization, hash-consing, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.StoredWriter

open Geb Geb.FreeTopos
open Internal (Decl)
open PartialHorn (Tree)

/-- The distinct nodes of a tree found so far, each its label and its children's indices, with the
index of each. -/
structure Table where
  /-- The index of each node. -/
  index : Std.HashMap (ℕ × List ℕ) ℕ := {}
  /-- The nodes, in the order found. -/
  nodes : Array (ℕ × List ℕ) := #[]

/-- The index of a tree's root among the distinct nodes, each node entered after its children. -/
def intern : Tree → StateM Table ℕ := RoseTree.elim fun l cs ↦ do
  let key := (l, ← cs.mapM id)
  match (← get).index[key]? with
  | some i => pure i
  | none => modifyGet fun t ↦
    (t.nodes.size, { index := t.index.insert key t.nodes.size, nodes := t.nodes.push key })

/-- A tree as a list of natural numbers: its number of distinct nodes, then each, in an order in
which a node follows its children, as its label, its number of children and their indices; the
root last. -/
def treeToNats (t : Tree) : List ℕ :=
  let tab := ((intern t).run {}).2
  tab.nodes.size :: tab.nodes.toList.flatMap fun (l, ids) ↦ l :: ids.length :: ids

/-- A list of natural numbers as text: the numerals in decimal, separated by spaces. -/
def natsToText (ns : List ℕ) : String := " ".intercalate (ns.map toString)

/-- Declarations of theorems as text, the table of their tree, which
{name}`GebTests.Prototypes.FreeTopos.Stored.declsOfText` reads back; nothing where one is of another
kind. -/
def declsToText (ds : List Decl) : Option String :=
  (Stored.declsTree ds).map (natsToText ∘ treeToNats)

/-- The certificates of the developments written into a directory, each search timed; a line for
each certificate, its name, its number of declarations, the bytes of its text and the
milliseconds of the search that found it. The exit code is nonzero where a search fails. -/
def generate (dir : System.FilePath) : IO UInt32 := do
  IO.FS.createDirAll dir
  let mut code : UInt32 := 0
  for (name, search) in Certificates.searches do
    let t₀ ← IO.monoMsNow
    let r ← IO.lazyPure search
    let t₁ ← IO.monoMsNow
    match r with
    | .error e =>
      IO.eprintln s!"{name}: {e}"
      code := 1
    | .ok certs =>
      for (file, ds) in certs do
        match declsToText ds with
        | none =>
          IO.eprintln s!"{file}: a declaration is not of a theorem"
          code := 1
        | some text =>
          IO.FS.writeFile (dir / s!"{file}.cert") (text ++ "\n")
          IO.println s!"{file},{ds.length},{text.utf8ByteSize},{t₁ - t₀}"
  pure code

end GebTests.Prototypes.FreeTopos.StoredWriter

end
