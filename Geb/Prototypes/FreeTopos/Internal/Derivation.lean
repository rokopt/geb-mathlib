/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Compile
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The derivations of the internal language

The checker of the internal language's derivations of equations. A derivation is a rose tree of
rules of two kinds. A rewriting derivation transforms a given term: the identity, a sequence of
two rewritings, congruence into each child of a node, each in its own context, and the
equations of the language applied at the term: β for functions, the components of a pair and the
η of pairs and of the terminal type, the unfolding of a definition at its arguments, the
computation of the folds of the natural numbers and of lists, and an instance of an earlier
theorem. A proof derivation proves an equation between two terms: by rewriting both to one term,
or by induction on the innermost variable of the context, of the natural numbers or of a list
type, in the form of the uniqueness of recursion: both sides agree at the start, and each is,
at a successor or a construction, the step, a term of the sides' type, applied to its own
value. The rewriting takes its
terms from the term it rewrites, so that a derivation names no term but the steps of its
inductions and the instances of the theorems it cites, and the checker computes every
substitution.

## Main definitions

* {lit}`Rule`, {lit}`Deriv` — the rules and the derivations.
* {lit}`Thm` — a theorem: an equation between two terms in a context.
* {lit}`check` — the rewriting a derivation performs, and the equations it proves.
* {lit}`checkThms` — the check of a development of theorems, each proved with those before it.

## Tags

internal language, derivation, proof checker, rewriting, induction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op)
open Sorts
open scoped FinEnum

/-- A rule of the internal language's derivations, with the data it names. -/
inductive Rule where
  /-- The identity rewriting. -/
  | refl
  /-- One rewriting after another. -/
  | trans
  /-- The rewriting of each child of a node. -/
  | cong
  /-- The application of an abstraction is its body with the argument substituted. -/
  | beta
  /-- The first component of a pair is its first term. -/
  | fstPair
  /-- The second component of a pair is its second term. -/
  | sndPair
  /-- The pair of a term's components is the term. -/
  | pairEta
  /-- A term of the terminal type is its element. -/
  | unitEta
  /-- The application of a definition is its body at the objects and arguments. -/
  | delta
  /-- The fold of zero, the primitive of index {lit}`k`, is the start. -/
  | natZero (k : ℕ)
  /-- The fold of a successor, the primitive of index {lit}`k`, is the step at the fold. -/
  | natSucc (k : ℕ)
  /-- The fold of the empty list, the primitive of index {lit}`k`, is the start. -/
  | listNil (k : ℕ)
  /-- The fold of a construction, the primitive of index {lit}`k`, is the step at the element
  and the fold of the tail. -/
  | listCons (k : ℕ)
  /-- The theorem of index {lit}`j` at objects and terms, from its left side to its right, or
  from its right to its left when {lit}`flip`. -/
  | thm (j : ℕ) (θ : List Tree) (σ : List Term) (flip : Bool)
  /-- An equation whose sides two rewritings take to one term. -/
  | join
  /-- Induction on the innermost variable, of the natural numbers, with zero and the successor
  the primitives of indices {lit}`kz` and {lit}`ks`, by the step {lit}`s`. -/
  | natInd (kz ks : ℕ) (s : Term)
  /-- Induction on the innermost variable, of a list type, with the empty list and construction
  the primitives of indices {lit}`kn` and {lit}`kc`, by the step {lit}`s`. -/
  | listInd (kn kc : ℕ) (s : Term)

/-- A derivation of the internal language. -/
abbrev Deriv : Type := RoseTree Rule

/-- A theorem: an equation between two terms in a context, in object variables. -/
structure Thm where
  /-- The number of object variables. -/
  arity : ℕ
  /-- The types of the variables, the innermost first. -/
  ctx : List Tree
  /-- The left side. -/
  lhs : Term
  /-- The right side. -/
  rhs : Term

/-- The primitive arrow zero. -/
def zeroPrim : Prim := ⟨0, zeroN, one, nat⟩

/-- The primitive arrow successor. -/
def succPrim : Prim := ⟨0, succ, nat, nat⟩

/-- The primitive arrow of the empty list of the object parameter. -/
def nilPrim : Prim := ⟨1, nil (x 0), one, list (x 0)⟩

/-- The primitive arrow of the construction of a list of the object parameter. -/
def consPrim : Prim := ⟨1, cons (x 0), prod (x 0) (list (x 0)), list (x 0)⟩

/-- The substitution of one term for the innermost variable, the others lowered by one. -/
def instVar (u : Term) : ℕ → Term := fun i ↦ match i with
  | 0 => u
  | j + 1 => Term.var j

/-- The substitution of one term for the innermost variable, the others in place. -/
def atVar0 (u : Term) : ℕ → Term := fun i ↦ match i with
  | 0 => u
  | j + 1 => Term.var (j + 1)

/-- A term in a context of a natural number variable, at the variable's successor, the primitive
of index {lit}`ks`. -/
def natSuccAt (ks : ℕ) (t : Term) : Term := Term.subst t (atVar0 (Term.arr ks [] (Term.var 0)))

/-- A term in a context of a list variable, at the construction, the primitive of index
{lit}`kc` at the element type {lit}`a`, of a new element before the variable, the new element
the next variable and the context's others raised past it. -/
def listConsAt (kc : ℕ) (a : Tree) (t : Term) : Term :=
  Term.subst t fun i ↦ match i with
    | 0 => Term.arr kc [a] (Term.pair (Term.var 1) (Term.var 0))
    | j + 1 => Term.var (j + 2)

/-- A term in a context of a list variable, weakened past a new element after the variable. -/
def weakenElem (t : Term) : Term := Term.rename t fun i ↦ match i with
  | 0 => 0
  | j + 1 => j + 2

/-- The type of a term in a context. -/
def typeIn (G : Globals) (n : ℕ) (Γ : List Tree) (t : Term) : Option Tree :=
  (compile G n t (ctxObj Γ) (stdEnv Γ)).map Prod.snd

/-- The contexts of a node's children, in the node's context: an abstraction's body extends it,
and the start and the step of a fold are in their own. -/
def childCtxs (G : Globals) (n : ℕ) (l : Label) (ts : List Term) (Γ : List Tree) :
    Option (List (List Tree)) := match l, ts with
  | .lam a, [_] => some [a :: Γ]
  | .natRec, [z, _, _] => do
    let c ← typeIn G n [] z
    pure [[], [c], Γ]
  | .listRec, [z, _, m] => do
    let c ← typeIn G n [] z
    let a ← (typeIn G n Γ m).bind listPart
    pure [[], [c, a], Γ]
  | .roseRec c, [_, _] => some [[prod nat (list c)], Γ]
  | _, ts => some (ts.map fun _ ↦ Γ)

/-- The rewriting of a term at its root by a rule of the language's equations, with the
constants of {lit}`G` and the theorems of {lit}`E`. -/
def rootStep (G : Globals) (E : Array Thm) (n : ℕ) (Γ : List Tree) (l : Rule) (t : Term) :
    Option Term := match l, t.label, t.children with
  | .beta, .app, [f, u] => match f.label, f.children with
    | .lam _, [b] => some (Term.subst b (instVar u))
    | _, _ => none
  | .fstPair, .fst, [p] => match p.label, p.children with
    | .pair, [a, _] => some a
    | _, _ => none
  | .sndPair, .snd, [p] => match p.label, p.children with
    | .pair, [_, b] => some b
    | _, _ => none
  | .pairEta, .pair, [a, b] => match a.label, a.children, b.label, b.children with
    | .fst, [p], .snd, [q] => if p = q then some p else none
    | _, _, _, _ => none
  | .unitEta, _, _ => if typeIn G n Γ t = some one then some Term.star else none
  | .delta, .defn k θ, args => (G.defs[k]?).map fun d ↦
    Term.subst (Term.osubst θ d.body) (Term.substList args)
  | .natZero kz, .natRec, [z, _, m] => match m.label, m.children with
    | .arr k [], [c] => if k = kz ∧ G.prims[kz]? = some zeroPrim ∧ c = Term.star then some z
      else none
    | _, _ => none
  | .natSucc ks, .natRec, [z, s, m] => match m.label, m.children with
    | .arr k [], [c] => if k = ks ∧ G.prims[ks]? = some succPrim then
        some (Term.subst s (instVar (Term.natRec z s c))) else none
    | _, _ => none
  | .listNil kn, .listRec, [z, _, m] => match m.label, m.children with
    | .arr k [_], [c] => if k = kn ∧ G.prims[kn]? = some nilPrim ∧ c = Term.star then some z
      else none
    | _, _ => none
  | .listCons kc, .listRec, [z, s, m] => match m.label, m.children with
    | .arr k [_], [p] => match p.label, p.children with
      | .pair, [h, tl] => if k = kc ∧ G.prims[kc]? = some consPrim then
          some (Term.subst s (Term.substList [Term.listRec z s tl, h])) else none
      | _, _ => none
    | _, _ => none
  | .thm j θ σ flip, _, _ => do
    let a ← E[j]?
    let l := Term.subst (Term.osubst θ a.lhs) (Term.substList σ)
    let r := Term.subst (Term.osubst θ a.rhs) (Term.substList σ)
    let (l, r) := if flip then (r, l) else (l, r)
    if θ.length = a.arity ∧ θ.all (IsTy n) ∧ σ.length = a.ctx.length ∧
        (σ.zip (a.ctx.map (PartialHorn.subst θ))).all (fun (u, A) ↦ typeIn G n Γ u = some A) ∧
        t = l then some r else none
  | _, _, _ => none

/-- The results of a node's rewriting and of its proving, from its children's: the rewriting of
a term in a context, and whether it proves an equation in a context. -/
abbrev Checks : Type := (List Tree → Term → Option Term) × (List Tree → Term → Term → Bool)

/-- One step of the checker, at a node of a rule, from its children's results. -/
def checkStep (G : Globals) (E : Array Thm) (n : ℕ) (l : Rule) (cs : List (Deriv × Checks)) :
    Checks :=
  (fun Γ t ↦ match l, cs with
    | .refl, [] => some t
    | .trans, [(_, c₁), (_, c₂)] => (c₁.1 Γ t).bind (c₂.1 Γ)
    | .cong, cs => do
      let Γs ← childCtxs G n t.label t.children Γ
      if cs.length = t.children.length ∧ Γs.length = t.children.length then do
        let ts ← ((cs.zip (Γs.zip t.children)).mapM fun (c, Δ, u) ↦ c.2.1 Δ u)
        pure (RoseTree.node t.label ts)
      else none
    | l, [] => rootStep G E n Γ l t
    | _, _ => none,
   fun Γ t u ↦ match l, cs with
    | .join, [(_, c₁), (_, c₂)] => match c₁.1 Γ t, c₂.1 Γ u with
      | some v, some v' => decide (v = v')
      | _, _ => false
    | .natInd kz ks s, [(_, p₀), (_, p₁), (_, p₂)] => match Γ, typeIn G n Γ t with
      | c :: Γ', some C => decide (c = nat ∧ G.prims[kz]? = some zeroPrim ∧
            G.prims[ks]? = some succPrim ∧ typeIn G n (C :: Γ') s = some C) &&
          p₀.2 Γ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
            (Term.subst u (instVar (Term.arr kz [] Term.star))) &&
          p₁.2 Γ (natSuccAt ks t) (Term.subst s (atVar0 t)) &&
          p₂.2 Γ (natSuccAt ks u) (Term.subst s (atVar0 u))
      | _, _ => false
    | .listInd kn kc s, [(_, p₀), (_, p₁), (_, p₂)] => match Γ, typeIn G n Γ t with
      | c :: Γ', some C => match listPart c with
        | some a => decide (G.prims[kn]? = some nilPrim ∧ G.prims[kc]? = some consPrim ∧
              typeIn G n (C :: a :: Γ') s = some C) &&
            p₀.2 Γ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
              (Term.subst u (instVar (Term.arr kn [a] Term.star))) &&
            p₁.2 (c :: a :: Γ') (listConsAt kc a t) (Term.subst s (atVar0 (weakenElem t))) &&
            p₂.2 (c :: a :: Γ') (listConsAt kc a u) (Term.subst s (atVar0 (weakenElem u)))
        | none => false
      | _, _ => false
    | _, _ => false)

/-- The checker: the rewriting a derivation performs on a term in a context, and whether it
proves an equation in a context. -/
def check (G : Globals) (E : Array Thm) (n : ℕ) : Deriv → Checks :=
  RoseTree.para (checkStep G E n)

/-- Whether a derivation proves a theorem with the constants of {lit}`G` and the theorems of
{lit}`E`: its context is of types, its sides have one type there, and the derivation proves
their equation. -/
def Thm.checks (G : Globals) (E : Array Thm) (a : Thm) (d : Deriv) : Bool :=
  a.ctx.all (IsTy a.arity) &&
    (match typeIn G a.arity a.ctx a.lhs, typeIn G a.arity a.ctx a.rhs with
      | some A, some B => decide (A = B)
      | _, _ => false) &&
    (check G E a.arity d).2 a.ctx a.lhs a.rhs

/-- Whether a development checks: each theorem proved by its derivation with the theorems before
it. -/
def checkThms (G : Globals) : List (Thm × Deriv) → Array Thm → Bool :=
  List.rec (fun _ ↦ true) fun e _ ih E ↦ e.1.checks G E e.2 && ih (E.push e.1)

end Geb.FreeTopos.Internal

end
