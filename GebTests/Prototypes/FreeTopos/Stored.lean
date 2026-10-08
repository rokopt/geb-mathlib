/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation -- shake: keep

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
its children; reading the table back builds each node once, its children shared. The table is
written as its numbers in decimal, separated by spaces, by
{lit}`GebTests.Prototypes.FreeTopos.StoredWriter`, which finds the distinct nodes.

## Main definitions

* {lit}`termTree`, {lit}`derivTree`, {lit}`declsTree` — terms, derivations and declarations as
  trees, and {lit}`termOfTree`, {lit}`derivOfTree`, {lit}`declsOfTree` back.
* {lit}`treeOfNats` — the tree the table of its distinct nodes stores.
* {lit}`natsOfText`, {lit}`declsOfText` — the numbers and the declarations a text stores.

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
def after {β : Type} (cs : List (Tree × β)) (rest : List Tree) : List β :=
  (cs.drop (cs.length - rest.length)).map (·.2)

/-- The term a tree is, where it is one. -/
def termOfTree : Tree → Option Term := RoseTree.para fun k cs ↦ do
  let (l, rest) ← labelOf k (cs.map (·.1))
  pure (RoseTree.node l (← (after cs rest).mapM id))

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

/-- The rule of a position, read off the trees of its data: the rule and the trees after them. -/
def ruleOf (k : ℕ) (ts : List Tree) : Option (Rule × List Tree) := match k, ts with
  | 0, rest => some (.refl, rest)
  | 1, rest => some (.trans, rest)
  | 2, rest => some (.cong, rest)
  | 3, rest => some (.beta, rest)
  | 4, rest => some (.fstPair, rest)
  | 5, rest => some (.sndPair, rest)
  | 6, rest => some (.pairEta, rest)
  | 7, rest => some (.unitEta, rest)
  | 8, rest => some (.delta, rest)
  | 9, k :: rest => some (.natZero k.label, rest)
  | 10, k :: rest => some (.natSucc k.label, rest)
  | 11, k :: rest => some (.listNil k.label, rest)
  | 12, k :: rest => some (.listCons k.label, rest)
  | 13, kn :: kl :: kc :: rest => some (.roseNode kn.label kl.label kc.label, rest)
  | 14, kc :: kl :: rest => some (.caseInl kc.label kl.label, rest)
  | 15, kc :: kr :: rest => some (.caseInr kc.label kr.label, rest)
  | 16, j :: θ :: σ :: flip :: rest => do
    pure (.thm j.label θ.children (← σ.children.mapM termOfTree) (← flagOf flip), rest)
  | 17, i :: flip :: rest => do pure (.rwHyp i.label (← flagOf flip), rest)
  | 18, rest => some (.join, rest)
  | 19, kz :: ks :: s :: rest => do pure (.natInd kz.label ks.label (← termOfTree s), rest)
  | 20, kn :: kc :: s :: rest => do pure (.listInd kn.label kc.label (← termOfTree s), rest)
  | 21, i :: rest => some (.hyp i.label, rest)
  | 22, φ :: rest => do pure (.cut (← termOfTree φ), rest)
  | 23, rest => some (.conv, rest)
  | 24, φ :: rest => do pure (.convFrom (← termOfTree φ), rest)
  | 25, rest => some (.propExt, rest)
  | 26, rest => some (.funExt, rest)
  | 27, j :: θ :: σ :: rest => do
    pure (.apply j.label θ.children (← σ.children.mapM termOfTree), rest)
  | 28, kz :: ks :: rest => some (.natIndHyp kz.label ks.label, rest)
  | 29, kn :: kc :: rest => some (.listIndHyp kn.label kc.label, rest)
  | 30, c :: rest => some (.cert c, rest)
  | 31, c :: rest => some (.certSeq c, rest)
  | 32, kn :: kl :: kc :: s :: rest => do
    pure (.roseInd kn.label kl.label kc.label (← termOfTree s), rest)
  | 33, kn :: kl :: kc :: rest => some (.roseIndHyp kn.label kl.label kc.label, rest)
  | 34, kl :: kr :: rest => some (.coprodInd kl.label kr.label, rest)
  | 35, i :: rest => some (.zeroInd i.label, rest)
  | 36, kq :: θ :: rest => some (.quotInd kq.label θ.children, rest)
  | _, _ => none

/-- A derivation as a tree: each node its rule's position over the trees of the rule's data and
the node's children. -/
def derivTree : Deriv → Tree :=
  RoseTree.elim fun r cs ↦ let (k, ds) := ruleData r; RoseTree.node k (ds ++ cs)

/-- The derivation a tree is, where it is one. -/
def derivOfTree : Tree → Option Deriv := RoseTree.para fun k cs ↦ do
  let (r, rest) ← ruleOf k (cs.map (·.1))
  pure (RoseTree.node r (← (after cs rest).mapM id))

/-- A theorem as a tree: its arity, its context, its hypotheses and its conclusion. -/
def thmTree (a : Thm) : Tree :=
  listT [leafN a.arity, listT a.ctx, listT (a.hyps.map termTree), termTree a.concl]

/-- The theorem a tree is, where it is one. -/
def thmOfTree (t : Tree) : Option Thm := match t.children with
  | [n, ctx, hyps, c] => do pure ⟨n.label, ctx.children, ← hyps.children.mapM termOfTree,
      ← termOfTree c⟩
  | _ => none

/-- A declaration of a theorem as a tree, the theorem and its derivation; nothing for a
declaration of another kind. -/
def declTree : Decl → Option Tree
  | .language a d => some (listT [thmTree a, derivTree d])
  | _ => none

/-- The declaration of a theorem a tree is, where it is one. -/
def declOfTree (t : Tree) : Option Decl := match t.children with
  | [a, d] => do pure (.language (← thmOfTree a) (← derivOfTree d))
  | _ => none

/-- Declarations of theorems as a tree; nothing where one is of another kind. -/
def declsTree (ds : List Decl) : Option Tree := (ds.mapM declTree).map listT

/-- The declarations of theorems a tree is, where it is them. -/
def declsOfTree (t : Tree) : Option (List Decl) := t.children.mapM declOfTree

/-! Trees as tables of their distinct nodes. -/

/-- The tree a list of natural numbers stores, where it stores one: its number of distinct nodes,
then each, in an order in which a node follows its children, as its label, its number of children
and their indices, the root last; each child an index of a node read before it. -/
def treeOfNats (ns : List ℕ) : Option Tree := match ns with
  | count :: rest =>
    (Nat.rec (motive := fun _ ↦ List ℕ × Array Tree → Option (List ℕ × Array Tree))
      (fun st ↦ some st) (fun _ rec st ↦ match st.1 with
        | l :: n :: more =>
          if n ≤ more.length then do
            let cs ← (more.take n).mapM (st.2[·]?)
            rec (more.drop n, st.2.push (RoseTree.node l cs))
          else none
        | _ => none) count (rest, #[])).bind fun (left, nodes) ↦
      if left.isEmpty then nodes.back? else none
  | [] => none

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
  (natsOfText s).bind treeOfNats |>.bind declsOfTree

end GebTests.Prototypes.FreeTopos.Stored

end
