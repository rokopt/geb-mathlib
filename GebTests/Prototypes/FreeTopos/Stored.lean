/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation -- shake: keep

set_option doc.verso true in
/-!
# Stored theorems

The encoding of a theorem of the internal language as a list of natural numbers, in which a
development checked in one module is carried to the modules that import it
({lit}`StoredDevelopments`), so that an importing module proves its own theorems from the stored
ones and checks only its own, and a development is checked once along the chain of modules.

A tree and a term are functions of their children's positions, which an environment cannot
store, so a theorem is stored as a list of natural numbers: a tree as its nodes in postorder,
each its label and its number of children; a term likewise, each node's label as the index of
its kind followed by its data, a tree among them as the length of its list followed by the list.
Reading a list back runs a stack of the trees or terms read so far, one node at a time, for as
many steps as the list is long.

## Main definitions

* {lit}`thmToNats`, {lit}`thmOfNats` — a theorem as a list of natural numbers, and back.

## Tags

internal language, development, serialization, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Stored

open Geb Geb.FreeTopos
open Internal (Term Label Thm)
open PartialHorn (Tree)

/-! Trees and terms as lists of natural numbers. -/

/-- A tree's nodes in postorder, each its label and its number of children. -/
def treeToNats : Tree → List ℕ := RoseTree.para fun l cs ↦ cs.flatMap (·.2) ++ [l, cs.length]

/-- A list prefixed by its length. -/
def withLength (ns : List ℕ) : List ℕ := ns.length :: ns

/-- The kind of a term's label, followed by its data. -/
def labelToNats : Label → List ℕ
  | .var i => [0, i]
  | .star => [1]
  | .pair => [2]
  | .fst => [3]
  | .snd => [4]
  | .lam a => 5 :: withLength (treeToNats a)
  | .app => [6]
  | .arr k θ => [7, k, θ.length] ++ θ.flatMap (withLength ∘ treeToNats)
  | .natRec => [8]
  | .listRec => [9]
  | .roseRec c => 10 :: withLength (treeToNats c)
  | .defn k θ => [11, k, θ.length] ++ θ.flatMap (withLength ∘ treeToNats)
  | .eq => [12]

/-- A term's nodes in postorder, each its label's kind and data and its number of children. -/
def termToNats : Term → List ℕ :=
  RoseTree.para fun l cs ↦ cs.flatMap (·.2) ++ labelToNats l ++ [cs.length]

/-- The node of a label over the last {lit}`n` elements of a stack, the topmost last. -/
def pushNode {α : Type} (l : α) (n : ℕ) (stack : List (RoseTree α)) :
    Option (List (RoseTree α)) :=
  if n ≤ stack.length then
    some (RoseTree.node l (stack.take n).reverse :: stack.drop n)
  else none

/-- The trees a list of nodes in postorder builds, the last built first. -/
def treesOfNats (ns : List ℕ) : Option (List Tree) :=
  (Nat.rec (motive := fun _ ↦ List ℕ × List Tree → Option (List Tree))
    (fun _ ↦ some []) (fun _ rec st ↦ match st.1 with
      | [] => some st.2
      | l :: n :: rest => do rec (rest, ← pushNode l n st.2)
      | [_] => none) ns.length) (ns, [])

/-- The tree a list of nodes in postorder builds, where it builds one. -/
def treeOfNats (ns : List ℕ) : Option Tree := do
  let [t] ← treesOfNats ns | none
  pure t

/-- A list prefixed by its length, read off a list: the list and the rest. -/
def readLength (ns : List ℕ) : Option (List ℕ × List ℕ) := match ns with
  | k :: rest => if k ≤ rest.length then some (rest.take k, rest.drop k) else none
  | [] => none

/-- The trees of lists prefixed by their lengths, read off a list. -/
def readTrees (k : ℕ) (ns : List ℕ) : Option (List Tree × List ℕ) :=
  k.rec (some ([], ns)) fun _ rec ↦ do
    let (ts, rest) ← rec
    let (t, rest') ← readLength rest
    pure (ts ++ [← treeOfNats t], rest')

/-- A label read off a list: the label and the rest. -/
def readLabel (ns : List ℕ) : Option (Label × List ℕ) := match ns with
  | 0 :: i :: rest => some (.var i, rest)
  | 1 :: rest => some (.star, rest)
  | 2 :: rest => some (.pair, rest)
  | 3 :: rest => some (.fst, rest)
  | 4 :: rest => some (.snd, rest)
  | 5 :: rest => do
    let (a, rest') ← readLength rest
    pure (.lam (← treeOfNats a), rest')
  | 6 :: rest => some (.app, rest)
  | 7 :: k :: m :: rest => do
    let (θ, rest') ← readTrees m rest
    pure (.arr k θ, rest')
  | 8 :: rest => some (.natRec, rest)
  | 9 :: rest => some (.listRec, rest)
  | 10 :: rest => do
    let (c, rest') ← readLength rest
    pure (.roseRec (← treeOfNats c), rest')
  | 11 :: k :: m :: rest => do
    let (θ, rest') ← readTrees m rest
    pure (.defn k θ, rest')
  | 12 :: rest => some (.eq, rest)
  | _ => none

/-- The terms a list of nodes in postorder builds, the last built first. -/
def termsOfNats (ns : List ℕ) : Option (List Term) :=
  (Nat.rec (motive := fun _ ↦ List ℕ × List Term → Option (List Term))
    (fun _ ↦ some []) (fun _ rec st ↦ match st.1 with
      | [] => some st.2
      | ns' => do
        let (l, rest) ← readLabel ns'
        let n :: rest' := rest | none
        rec (rest', ← pushNode l n st.2)) ns.length) (ns, [])

/-- The term a list of nodes in postorder builds, where it builds one. -/
def termOfNats (ns : List ℕ) : Option Term := do
  let [t] ← termsOfNats ns | none
  pure t

/-- A theorem as a list of natural numbers: its number of object variables, its context's types
and its hypotheses, each list prefixed by its number and each element by its length, and its
conclusion prefixed by its length. -/
def thmToNats (a : Thm) : List ℕ :=
  [a.arity, a.ctx.length] ++ a.ctx.flatMap (withLength ∘ treeToNats) ++
    [a.hyps.length] ++ a.hyps.flatMap (withLength ∘ termToNats) ++
    withLength (termToNats a.concl)

/-- The terms of lists prefixed by their lengths, read off a list. -/
def readTerms (k : ℕ) (ns : List ℕ) : Option (List Term × List ℕ) :=
  k.rec (some ([], ns)) fun _ rec ↦ do
    let (ts, rest) ← rec
    let (t, rest') ← readLength rest
    pure (ts ++ [← termOfNats t], rest')

/-- The theorem a list of natural numbers stores, where it stores one. -/
def thmOfNats (ns : List ℕ) : Option Thm := match ns with
  | n :: k :: rest => do
    let (ctx, rest₁) ← readTrees k rest
    let m :: rest₂ := rest₁ | none
    let (hyps, rest₃) ← readTerms m rest₂
    let (c, []) ← readLength rest₃ | none
    pure ⟨n, ctx, hyps, ← termOfNats c⟩
  | _ => none

end GebTests.Prototypes.FreeTopos.Stored

end
