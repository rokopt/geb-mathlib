/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation -- shake: keep
public import Std.Data.HashMap.Raw

set_option doc.verso true in
/-!
# Stored developments

The encoding of a development of the internal language, the declarations of its theorems with
their derivations, as text, in which a certificate of {lit}`bootstrap/certificates/` stores a
development ({lit}`GebTests.Prototypes.FreeTopos.StoredWriter`), to be read and checked
({lit}`GebTests.Prototypes.FreeTopos.Certified`).

A development is first a tree of natural numbers: a term's node is its label's kind over the trees
of the label's data and the node's children, a derivation's node its rule's position over the
trees of the rule's data and the node's children, a number a leaf, and a list the node of its
elements. A derivation repeats its terms many times over, so the tree is stored as the table of
its distinct nodes, each its label and its children's indices, in an order in which a node follows
its children. The distinct nodes are found by a hash table, each declaration's tree built and
entered in turn; the table is written as its numbers in decimal, separated by spaces, by
{lit}`GebTests.Prototypes.FreeTopos.StoredWriter`.

The table is read back by a paramorphism computed at each distinct node once, from its children's
values, so that the terms and derivations read share their subterms as the table does. Reading the
tree instead visits a node once for each path to it from the root, and a derivation's tree is
larger than its table by orders of magnitude.

## Main definitions

* {lit}`termTree`, {lit}`derivTree`, {lit}`declsTree` — terms, derivations and declarations as
  trees.
* {lit}`Reading`, {lit}`read` — the readings of a node as a term, a derivation, a theorem and a
  declaration, from its children's.
* {lit}`paraOfNats` — the value of a paramorphism at the tree the table of its distinct nodes
  stores, computed at each distinct node once.
* {lit}`Table`, {lit}`treeToNats`, {lit}`declsToNats` — the table of a tree's distinct nodes, of
  declarations', as natural numbers.
* {lit}`natsOfText`, {lit}`declsOfText` — the numbers and the declarations a text stores.

## Implementation notes

The hash table is Lean's {lit}`Std.HashMap.Raw`, whose insertion and lookup depend on the axioms
{lit}`propext` and {lit}`Quot.sound` alone. Its empty table is built from its fields, as eight
empty buckets, since the constructors that compute a capacity depend on {lit}`Classical.choice`.

## Tags

internal language, development, serialization, hash-consing, certificate, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Stored

open Geb Geb.FreeTopos
open Internal (Term Label Thm Rule Deriv Decl)
open PartialHorn (Tree)

/-! Developments as trees. -/

/-- The leaf of a number. -/
def leafN (n : ℕ) : Tree := RoseTree.node n []

/-- The node of a list of trees. -/
def listT (ts : List Tree) : Tree := RoseTree.node 0 ts

/-- A label's kind and its data, as trees. -/
def labelData : Label → ℕ × List Tree
  | .var i => (0, [leafN i])
  | .star => (1, [])
  | .pair => (2, [])
  | .fst => (3, [])
  | .snd => (4, [])
  | .lam a => (5, [a])
  | .app => (6, [])
  | .arr k θ => (7, [leafN k, listT θ])
  | .natRec => (8, [])
  | .listRec => (9, [])
  | .roseRec c => (10, [c])
  | .defn k θ => (11, [leafN k, listT θ])
  | .eq => (12, [])

/-- The label of a kind, read off the trees of its data: the label and the trees after them. -/
def labelOf (k : ℕ) (ts : List Tree) : Option (Label × List Tree) := match k, ts with
  | 0, i :: rest => some (.var i.label, rest)
  | 1, rest => some (.star, rest)
  | 2, rest => some (.pair, rest)
  | 3, rest => some (.fst, rest)
  | 4, rest => some (.snd, rest)
  | 5, a :: rest => some (.lam a, rest)
  | 6, rest => some (.app, rest)
  | 7, k :: θ :: rest => some (.arr k.label θ.children, rest)
  | 8, rest => some (.natRec, rest)
  | 9, rest => some (.listRec, rest)
  | 10, c :: rest => some (.roseRec c, rest)
  | 11, k :: θ :: rest => some (.defn k.label θ.children, rest)
  | 12, rest => some (.eq, rest)
  | _, _ => none

/-- A term as a tree: each node its label's kind over the trees of the label's data and the
node's children. -/
def termTree : Term → Tree :=
  RoseTree.elim fun l cs ↦ let (k, ds) := labelData l; RoseTree.node k (ds ++ cs)

/-- The children's values after the trees of a node's data, where the data leave {lit}`rest`. -/
def after {β γ : Type} (cs : List (Tree × β)) (rest : List γ) : List β :=
  (cs.drop (cs.length - rest.length)).map (·.2)

/-- A flag as a number. -/
def flagN (b : Bool) : Tree := leafN b.toNat

/-- The flag a tree is, where it is one. -/
def flagOf (t : Tree) : Option Bool := match t.label with
  | 0 => some false
  | 1 => some true
  | _ => none

/-- A rule's position among the rules and its data, as trees. -/
def ruleData : Rule → ℕ × List Tree
  | .refl => (0, [])
  | .trans => (1, [])
  | .cong => (2, [])
  | .beta => (3, [])
  | .fstPair => (4, [])
  | .sndPair => (5, [])
  | .pairEta => (6, [])
  | .unitEta => (7, [])
  | .delta => (8, [])
  | .natZero k => (9, [leafN k])
  | .natSucc k => (10, [leafN k])
  | .listNil k => (11, [leafN k])
  | .listCons k => (12, [leafN k])
  | .roseNode kn kl kc => (13, [leafN kn, leafN kl, leafN kc])
  | .caseInl kc kl => (14, [leafN kc, leafN kl])
  | .caseInr kc kr => (15, [leafN kc, leafN kr])
  | .thm j θ σ flip => (16, [leafN j, listT θ, listT (σ.map termTree), flagN flip])
  | .rwHyp i flip => (17, [leafN i, flagN flip])
  | .join => (18, [])
  | .natInd kz ks s => (19, [leafN kz, leafN ks, termTree s])
  | .listInd kn kc s => (20, [leafN kn, leafN kc, termTree s])
  | .hyp i => (21, [leafN i])
  | .cut φ => (22, [termTree φ])
  | .conv => (23, [])
  | .convFrom φ => (24, [termTree φ])
  | .propExt => (25, [])
  | .funExt => (26, [])
  | .apply j θ σ => (27, [leafN j, listT θ, listT (σ.map termTree)])
  | .natIndHyp kz ks => (28, [leafN kz, leafN ks])
  | .listIndHyp kn kc => (29, [leafN kn, leafN kc])
  | .cert c => (30, [c])
  | .certSeq c => (31, [c])
  | .roseInd kn kl kc s => (32, [leafN kn, leafN kl, leafN kc, termTree s])
  | .roseIndHyp kn kl kc => (33, [leafN kn, leafN kl, leafN kc])
  | .coprodInd kl kr => (34, [leafN kl, leafN kr])
  | .zeroInd i => (35, [leafN i])
  | .quotInd kq θ => (36, [leafN kq, listT θ])

/-- The readings of a node: as a term, its children as terms, as a derivation, as a theorem, as a
declaration of a theorem, and its children as declarations of theorems, each where the node is
one. -/
structure Reading where
  /-- The node as a term. -/
  term : Option Term
  /-- The node's children as terms. -/
  terms : Option (List Term)
  /-- The node as a derivation. -/
  deriv : Option Deriv
  /-- The node as a theorem. -/
  thm : Option Thm
  /-- The node as a declaration of a theorem. -/
  decl : Option Decl
  /-- The node's children as declarations of theorems. -/
  decls : Option (List Decl)

/-- The rule of a position, read off the data, each a node's tree and readings: the rule and the
data after them. -/
def ruleOf (k : ℕ) (ts : List (Tree × Reading)) : Option (Rule × List (Tree × Reading)) :=
  match k, ts with
  | 0, rest => some (.refl, rest)
  | 1, rest => some (.trans, rest)
  | 2, rest => some (.cong, rest)
  | 3, rest => some (.beta, rest)
  | 4, rest => some (.fstPair, rest)
  | 5, rest => some (.sndPair, rest)
  | 6, rest => some (.pairEta, rest)
  | 7, rest => some (.unitEta, rest)
  | 8, rest => some (.delta, rest)
  | 9, k :: rest => some (.natZero k.1.label, rest)
  | 10, k :: rest => some (.natSucc k.1.label, rest)
  | 11, k :: rest => some (.listNil k.1.label, rest)
  | 12, k :: rest => some (.listCons k.1.label, rest)
  | 13, kn :: kl :: kc :: rest => some (.roseNode kn.1.label kl.1.label kc.1.label, rest)
  | 14, kc :: kl :: rest => some (.caseInl kc.1.label kl.1.label, rest)
  | 15, kc :: kr :: rest => some (.caseInr kc.1.label kr.1.label, rest)
  | 16, j :: θ :: σ :: flip :: rest => do
    pure (.thm j.1.label θ.1.children (← σ.2.terms) (← flagOf flip.1), rest)
  | 17, i :: flip :: rest => do pure (.rwHyp i.1.label (← flagOf flip.1), rest)
  | 18, rest => some (.join, rest)
  | 19, kz :: ks :: s :: rest => do pure (.natInd kz.1.label ks.1.label (← s.2.term), rest)
  | 20, kn :: kc :: s :: rest => do pure (.listInd kn.1.label kc.1.label (← s.2.term), rest)
  | 21, i :: rest => some (.hyp i.1.label, rest)
  | 22, φ :: rest => do pure (.cut (← φ.2.term), rest)
  | 23, rest => some (.conv, rest)
  | 24, φ :: rest => do pure (.convFrom (← φ.2.term), rest)
  | 25, rest => some (.propExt, rest)
  | 26, rest => some (.funExt, rest)
  | 27, j :: θ :: σ :: rest => do
    pure (.apply j.1.label θ.1.children (← σ.2.terms), rest)
  | 28, kz :: ks :: rest => some (.natIndHyp kz.1.label ks.1.label, rest)
  | 29, kn :: kc :: rest => some (.listIndHyp kn.1.label kc.1.label, rest)
  | 30, c :: rest => some (.cert c.1, rest)
  | 31, c :: rest => some (.certSeq c.1, rest)
  | 32, kn :: kl :: kc :: s :: rest => do
    pure (.roseInd kn.1.label kl.1.label kc.1.label (← s.2.term), rest)
  | 33, kn :: kl :: kc :: rest => some (.roseIndHyp kn.1.label kl.1.label kc.1.label, rest)
  | 34, kl :: kr :: rest => some (.coprodInd kl.1.label kr.1.label, rest)
  | 35, i :: rest => some (.zeroInd i.1.label, rest)
  | 36, kq :: θ :: rest => some (.quotInd kq.1.label θ.1.children, rest)
  | _, _ => none

/-- A derivation as a tree: each node its rule's position over the trees of the rule's data and
the node's children. -/
def derivTree : Deriv → Tree :=
  RoseTree.elim fun r cs ↦ let (k, ds) := ruleData r; RoseTree.node k (ds ++ cs)

/-- A theorem as a tree: its arity, its context, its hypotheses and its conclusion. -/
def thmTree (a : Thm) : Tree :=
  listT [leafN a.arity, listT a.ctx, listT (a.hyps.map termTree), termTree a.concl]

/-- A declaration of a theorem as a tree, the theorem and its derivation; nothing for a
declaration of another kind. -/
def declTree : Decl → Option Tree
  | .language a d => some (listT [thmTree a, derivTree d])
  | _ => none

/-- Declarations of theorems as a tree; nothing where one is of another kind. -/
def declsTree (ds : List Decl) : Option Tree := (ds.mapM declTree).map listT

/-- The readings of a node, from its label and its children's trees and readings. -/
def read (k : ℕ) (cs : List (Tree × Reading)) : Reading where
  term := do
    let (l, rest) ← labelOf k (cs.map (·.1))
    pure (RoseTree.node l (← (after cs rest).mapM (·.term)))
  terms := cs.mapM (·.2.term)
  deriv := do
    let (r, rest) ← ruleOf k cs
    pure (RoseTree.node r (← (after cs rest).mapM (·.deriv)))
  thm := match cs with
    | [n, ctx, hyps, c] => do pure ⟨n.1.label, ctx.1.children, ← hyps.2.terms, ← c.2.term⟩
    | _ => none
  decl := match cs with
    | [a, d] => do pure (.language (← a.2.thm) (← d.2.deriv))
    | _ => none
  decls := cs.mapM (·.2.decl)

/-! Trees as tables of their distinct nodes. -/

/-- The value of a paramorphism, with the step {lit}`f`, at the tree a list of natural numbers
stores, where it stores one, with the tree: its number of distinct nodes, then each, in an order in
which a node follows its children, as its label, its number of children and their indices, the
root last; each child an index of a node read before it. The step is applied at each distinct node
once, so that the values share as the table does. -/
def paraOfNats {β : Type} (f : ℕ → List (Tree × β) → β) (ns : List ℕ) : Option (Tree × β) :=
  match ns with
  | count :: rest =>
    (Nat.rec (motive := fun _ ↦ List ℕ × Array (Tree × β) → Option (List ℕ × Array (Tree × β)))
      (fun st ↦ some st) (fun _ rec st ↦ match st.1 with
        | l :: n :: more =>
          let ks := more.take n
          if ks.length = n then do
            let cs ← ks.mapM (st.2[·]?)
            rec (more.drop n, st.2.push (RoseTree.node l (cs.map (·.1)), f l cs))
          else none
        | _ => none) count (rest, #[])).bind fun (left, nodes) ↦
      if left.isEmpty then nodes.back? else none
  | [] => none

/-- The distinct nodes of a tree found so far, each its label and its children's indices, with the
index of each. -/
structure Table where
  /-- The index of each node. -/
  index : Std.HashMap.Raw (ℕ × List ℕ) ℕ
  /-- The nodes, in the order found. -/
  nodes : Array (ℕ × List ℕ)

/-- The table of no nodes, its hash map of eight empty buckets. -/
def Table.empty : Table := ⟨⟨⟨0, Array.replicate 8 .nil⟩⟩, #[]⟩

/-- The index of a node among the distinct nodes, from its label and its children's indices,
entered where it is new. -/
def internNode (l : ℕ) (ids : List ℕ) : StateM Table ℕ := do
  match (← get).index.get? (l, ids) with
  | some i => pure i
  | none => modifyGet fun t ↦ (t.nodes.size,
    { index := t.index.insert (l, ids) t.nodes.size, nodes := t.nodes.push (l, ids) })

/-- The index of a tree's root among the distinct nodes, each node entered after its children. -/
def intern : Tree → StateM Table ℕ := RoseTree.elim fun l cs ↦ do internNode l (← cs.mapM id)

/-- A table as a list of natural numbers: its number of distinct nodes, then each, in the order
found, as its label, its number of children and their indices. -/
def Table.toNats (tab : Table) : List ℕ :=
  tab.nodes.size :: tab.nodes.toList.flatMap fun (l, ids) ↦ l :: ids.length :: ids

/-- A tree as a list of natural numbers, the table of its distinct nodes, the root last. -/
def treeToNats (t : Tree) : List ℕ := ((intern t).run Table.empty).2.toNats

/-- Declarations of theorems as a list of natural numbers, the table of their tree
({name}`declsTree`), each declaration's tree built and entered in turn, so that the tree of one
declaration alone is built at once; nothing where one is of another kind. -/
def declsToNats (ds : List Decl) : Option (List ℕ) :=
  let (ids, tab) := (ds.mapM fun d ↦ (declTree d).mapM intern).run Table.empty
  (ids.mapM id).map fun ids ↦ ((internNode 0 ids).run tab).2.toNats

/-! Lists of natural numbers as text. -/

/-- The step of reading numerals in decimal separated by spaces or newlines: the numbers read and
the numeral being read, extended by a character; nothing at a character of neither kind. -/
def readChar (st : Option (List ℕ × Option ℕ)) (c : Char) : Option (List ℕ × Option ℕ) := do
  let (ns, cur) ← st
  if c.isDigit then pure (ns, some (cur.getD 0 * 10 + (c.toNat - '0'.toNat)))
  else if c = ' ' ∨ c = '\n' then pure (match cur with
    | some n => (n :: ns, none)
    | none => (ns, none))
  else none

/-- The list of natural numbers a text spells, numerals in decimal separated by spaces or
newlines, where it spells one. -/
def natsOfText (s : String) : Option (List ℕ) := do
  let (ns, cur) ← s.toList.foldl readChar (some ([], none))
  pure (match cur with
    | some n => (n :: ns).reverse
    | none => ns.reverse)

/-- The declarations of theorems a text stores, the table of their tree, where it stores them. -/
def declsOfText (s : String) : Option (List Decl) :=
  (natsOfText s).bind (paraOfNats read) |>.bind (·.2.decls)

end GebTests.Prototypes.FreeTopos.Stored

end
