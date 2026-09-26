/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Check
public import Geb.Prototypes.FreeTopos.Internal.Syntax
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The compilation of the internal language to the combinators

The typing of the internal language's terms and their compilation to arrows of the combinators,
the interpretation of the typed λ-calculus in a cartesian closed category of Part I of
{cite}`LambekScott1986` and the compilation of the categorical abstract machine of
{cite}`CousineauCurienMauny1987`, in one pass. A type is an object term built by the terminal
object, products, the initial object, coproducts, exponentials, the subobject classifier and the
data objects from object variables ({lit}`IsTy`), so that two types are equal when they are one
term. A term is compiled in an environment: an object {lit}`X` and, for each variable, an arrow from
{lit}`X` and the variable's type. A variable compiles to its arrow, a pair to the pairing, a
component to the projection after the pair, an abstraction to the currying of its body, compiled
over the product of {lit}`X` and the bound variable's type, an application to evaluation after the
pairing, a primitive arrow's application to the arrow after its argument, a fold to the composite of
the combinators' fold with the datum, and the equality of two terms to the characteristic map of the
diagonal after their pairing. A context's terms are compiled in the environment of its projections
from the product of its types ({lit}`stdEnv`). A primitive arrow is an arrow of the combinators with
the domain and codomain it names, in object parameters, which the checker's inference confirms once
({lit}`Prim.ok`), for every application at objects.

A definition of the internal language names a term in term parameters and object parameters. It
compiles to a definition of the combinators, the arrow its body compiles to from the product of
its parameters' types, and its application to the composite of that definition's operation with
the tuple of its arguments. The unfolding of a term's definitions ({lit}`unfold`) substitutes the
arguments and objects of each application into the definition's body, itself unfolded.

## Main definitions

* {lit}`IsTy` — the types.
* {lit}`compile` — the type and the arrow of a term in an environment.
* {lit}`Defn` — a definition of the internal language.
* {lit}`compileDefs` — the definitions of the combinators that definitions compile to.
* {lit}`compileEq` — the sequent an equation of two terms in a context compiles to.
* {lit}`unfold` — the unfolding of the definitions a term applies.
* {lit}`Prim`, {lit}`Globals` — the primitive arrows, and the constants a term may apply.
* {lit}`Prim.ok`, {lit}`Globals.ok` — the check that the constants are well formed and each
  primitive arrow has the types it names.

## References

* {cite}`LambekScott1986`, Part I, for the interpretation of the typed λ-calculus in a
  cartesian closed category.
* {cite}`CousineauCurienMauny1987` for the compilation of λ-terms to categorical combinators.

## Tags

internal language, typed lambda calculus, cartesian closed category, categorical combinators,
compilation, definition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree Seq op)
open Sorts
open scoped FinEnum

/-- The operations that build types, by index, with their arities: the terminal object,
products, the initial object, coproducts, exponentials, the subobject classifier, and the natural
numbers object, list objects, the rose-tree object and rose-tree objects over types of
labels. -/
def tyOps : List (ℕ × ℕ) :=
  [(4, 0), (6, 2), (13, 0), (15, 2), (22, 2), (25, 0), (29, 0), (33, 1), (37, 0), (40, 1)]

/-- Whether an object term is a type in {lit}`n` object variables: built by the operations of
{lit}`tyOps` from the variables. -/
def IsTy (n : ℕ) : Tree → Bool :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => decide (i.label < n)
    | 0, _ => false
    | k + 1, cs => decide ((k, cs.length) ∈ tyOps) && cs.all Prod.snd

/-- The factors of a product. -/
def prodParts (p : Tree) : Option (Tree × Tree) := match p.children with
  | [a, b] => if p = prod a b then some (a, b) else none
  | _ => none

/-- The summands of a coproduct. -/
def coprodParts (p : Tree) : Option (Tree × Tree) := match p.children with
  | [a, b] => if p = coprod a b then some (a, b) else none
  | _ => none

/-- The domain and codomain of an exponential. -/
def expParts (p : Tree) : Option (Tree × Tree) := match p.children with
  | [a, b] => if p = exp a b then some (a, b) else none
  | _ => none

/-- The type of labels of a rose-tree object, with the fold of the object by a step: the natural
numbers object for the rose-tree object, and the type of labels of a rose-tree object over
one. -/
def roseParts (p : Tree) : Option (Tree × (Tree → Tree)) :=
  if p = rose then some (nat, roseRec) else match p.children with
    | [a] => if p = lrose a then some (a, lroseRec a) else none
    | _ => none

/-- The element type of a list object. -/
def listPart (p : Tree) : Option Tree := match p.children with
  | [a] => if p = list a then some a else none
  | _ => none

/-- The product of a context's types, the innermost outermost: the terminal object for the empty
context, and the type itself for a context of one. -/
def ctxObj : List Tree → Tree := List.rec one fun a Γ x ↦ match Γ with
  | [] => a
  | _ :: _ => prod x a

/-- The environment over the product of {lit}`X` and {lit}`a` that extends an environment over
{lit}`X` by a variable of type {lit}`a`: the new variable is the second projection, and each
other the first projection followed by its arrow. -/
def extEnv (X a : Tree) (e : List (Tree × Tree)) : List (Tree × Tree) :=
  (snd X a, a) :: e.map fun p ↦ (comp p.1 (fst X a), p.2)

/-- The environment of a context's projections from the product of its types: the identity for a
context of one. -/
def stdEnv : List Tree → List (Tree × Tree) := List.rec [] fun a Γ e ↦ match Γ with
  | [] => [(idt a, a)]
  | _ :: _ => extEnv (ctxObj Γ) a e

/-- The tuple of arrows from {lit}`X`, the last outermost: the arrow to the terminal object for
none, and the arrow itself for one. -/
def tuple (X : Tree) : List Tree → Tree := List.rec (bang X) fun f fs p ↦ match fs with
  | [] => f
  | _ :: _ => pair p f

/-- A definition of the internal language: the number of its object parameters, the types of
its term parameters, the last first, the type of its value, and its body. -/
structure Defn where
  /-- The number of object parameters. -/
  arity : ℕ
  /-- The types of the term parameters, the last first. -/
  params : List Tree
  /-- The type of the value. -/
  type : Tree
  /-- The body, a term in the term parameters. -/
  body : Term

/-- A primitive arrow: an arrow of the combinators, with its domain and its codomain, in a number
of object parameters. -/
structure Prim where
  /-- The number of object parameters. -/
  arity : ℕ
  /-- The arrow. -/
  arrow : Tree
  /-- Its domain. -/
  dom : Tree
  /-- Its codomain. -/
  cod : Tree
deriving DecidableEq

/-- The constants a term may apply: the primitive arrows, and the definitions, the one of index
{lit}`k` the operation of index {lit}`base + k` of the combinators. -/
structure Globals where
  /-- The primitive arrows. -/
  prims : List Prim
  /-- The definitions. -/
  defs : List Defn
  /-- The index of the first definition's operation. -/
  base : ℕ

/-- The constants of {lit}`G` are well formed: each primitive arrow is a term in its object
parameters, and the types each constant names are types in them. -/
structure Globals.WF (G : Globals) : Prop where
  /-- Each primitive arrow is a term in its object parameters, between types in them. -/
  prims : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
    PartialHorn.Scoped p.arity p.arrow = true ∧ IsTy p.arity p.dom = true ∧
      IsTy p.arity p.cod = true
  /-- Each definition's parameters and value have types in its object parameters. -/
  defs : ∀ (k : ℕ) (d : Defn), G.defs[k]? = some d →
    d.params.all (IsTy d.arity) = true ∧ IsTy d.arity d.type = true

/-- One step of the compilation, at a node of a label, from the compilations of its children:
the arrow and the type of the node's term in {lit}`n` object variables, in an environment over
{lit}`X`, with the constants of {lit}`G`. -/
def compileStep (G : Globals) (n : ℕ) (l : Label)
    (cs : List (Term × (Tree → List (Tree × Tree) → Option (Tree × Tree))))
    (X : Tree) (e : List (Tree × Tree)) : Option (Tree × Tree) :=
  match l, cs with
    | .var i, [] => e[i]?
    | .star, [] => some (bang X, one)
    | .pair, [(_, t), (_, u)] => do
      let (f, a) ← t X e
      let (g, b) ← u X e
      pure (pair f g, prod a b)
    | .fst, [(_, t)] => do
      let (f, p) ← t X e
      let (a, b) ← prodParts p
      pure (comp (fst a b) f, a)
    | .snd, [(_, t)] => do
      let (f, p) ← t X e
      let (a, b) ← prodParts p
      pure (comp (snd a b) f, b)
    | .lam a, [(_, t)] =>
      if IsTy n a then do
        let (f, b) ← t (prod X a) (extEnv X a e)
        pure (curry X a f, exp a b)
      else none
    | .app, [(_, t), (_, u)] => do
      let (f, p) ← t X e
      let (a, b) ← expParts p
      let (g, a') ← u X e
      if a' = a then pure (comp (ev a b) (pair f g), b) else none
    | .arr k θ, [(_, t)] => do
      let p ← G.prims[k]?
      let (g, d) ← t X e
      if θ.length = p.arity ∧ θ.all (IsTy n) ∧ d = PartialHorn.subst θ p.dom then
        pure (comp (PartialHorn.subst θ p.arrow) g, PartialHorn.subst θ p.cod)
      else none
    | .natRec, [(_, z), (_, s), (_, m)] => do
      let (z', c) ← z one []
      let (s', c') ← s c [(idt c, c)]
      let (m', t) ← m X e
      if c' = c ∧ t = nat then pure (comp (natRec z' s') m', c) else none
    | .listRec, [(_, z), (_, s), (_, m)] => do
      let (m', t) ← m X e
      let a ← listPart t
      let (z', c) ← z one []
      let (s', c') ← s (prod a c) [(snd a c, c), (fst a c, a)]
      if c' = c then pure (comp (listRec a z' s') m', c) else none
    | .roseRec c, [(_, s), (_, m)] =>
      if IsTy n c then do
        let (m', t) ← m X e
        let (a, fold) ← roseParts t
        let (s', c') ← s (prod a (list c)) [(idt (prod a (list c)), prod a (list c))]
        if c' = c then pure (comp (fold s') m', c) else none
      else none
    | .eq, [(_, t), (_, u)] => do
      let (f, a) ← t X e
      let (g, b) ← u X e
      if a = b then pure (comp (chi (diag a)) (pair f g), omega) else none
    | .defn k θ, cs => do
      let d ← G.defs[k]?
      let rs ← cs.mapM fun c ↦ c.2 X e
      if θ.length = d.arity ∧ θ.all (IsTy n) ∧
          rs.map Prod.snd = d.params.map (PartialHorn.subst θ) then
        pure (comp (op (G.base + k) θ) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d.type)
      else none
    | _, _ => none

/-- The arrow and the type of a term in {lit}`n` object variables, in an environment over
{lit}`X`, with the constants of {lit}`G`; nothing when the term is not well typed. -/
def compile (G : Globals) (n : ℕ) :
    Term → Tree → List (Tree × Tree) → Option (Tree × Tree) :=
  RoseTree.para (compileStep G n)

/-- The definition of the combinators a definition compiles to, over the definitions before it:
an arrow in the object parameters, from the product of the term parameters' types. -/
def Defn.compile (G : Globals) (d : Defn) : Option PartialHorn.Defn := do
  let (f, c) ← Internal.compile G d.arity d.body (ctxObj d.params) (stdEnv d.params)
  if d.params.all (IsTy d.arity) ∧ c = d.type then
    pure ⟨List.replicate d.arity obj, arr, f⟩
  else none

/-- The definitions of the combinators that the definitions of {lit}`G` compile to, each over the
definitions before it. -/
def compileDefs (G : Globals) : Option (List PartialHorn.Defn) :=
  G.defs.zipIdx.mapM fun (d, i) ↦ d.compile { G with defs := G.defs.take i }

/-- The sequent of the combinators an equation of two terms of one type in a context compiles
to: the equation of their arrows from the product of the context's types, in the object
variables. -/
def compileEq (G : Globals) (n : ℕ) (Γ : List Tree) (t u : Term) : Option Seq := do
  let (f, a) ← compile G n t (ctxObj Γ) (stdEnv Γ)
  let (g, b) ← compile G n u (ctxObj Γ) (stdEnv Γ)
  if Γ.all (IsTy n) ∧ a = b then pure ⟨List.replicate n obj, [], ⟨f, g⟩⟩ else none

/-- The unfolding of the definitions a term applies, given their unfolded bodies: each
application of a definition is replaced by its unfolded body at the application's objects, with
the unfolded arguments substituted for its parameters. -/
def unfold (ubs : List Term) : Term → Term :=
  RoseTree.elim fun l cs ↦ match l with
    | .defn k θ => match ubs[k]? with
      | some b => Term.subst (Term.osubst θ b) (Term.substList cs)
      | none => RoseTree.node l cs
    | l => RoseTree.node l cs

/-- The unfolded bodies of a list of definitions, each unfolded by those before it. -/
def unfoldBodies (ds : List Defn) : List Term :=
  ds.foldl (fun ubs d ↦ ubs ++ [unfold ubs d.body]) []

/-- Whether a primitive arrow is a term in its object parameters that has, by the inference of
the checker, the domain and the codomain it names, which are types in them, with the definitions
of the combinators of {lit}`E`, and is an arrow of their signature. -/
def Prim.ok (E : ExtEnv) (p : Prim) : Bool :=
  PartialHorn.Scoped p.arity p.arrow && IsTy p.arity p.dom && IsTy p.arity p.cod &&
    PartialHorn.sortOf E.sg.toList (List.replicate p.arity obj) p.arrow == some arr &&
    match (infers E (List.replicate p.arity obj) [] inferFuel).2 p.arrow with
    | some a => a.sort == arr && a.lo == p.dom && a.hi == p.cod
    | none => false

/-- Whether the constants are well formed, the primitive arrows confirmed by the checker's
inference with the definitions of the combinators of {lit}`E`. -/
def Globals.ok (E : ExtEnv) (G : Globals) : Bool :=
  G.prims.all (Prim.ok E) && G.defs.all fun d ↦ d.params.all (IsTy d.arity) && IsTy d.arity d.type

end Geb.FreeTopos.Internal

end
