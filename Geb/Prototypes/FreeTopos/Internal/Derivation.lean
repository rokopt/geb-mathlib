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

The checker of the internal language's derivations. A judgment is a formula, a term of the
subobject classifier's type, in a context of variables and under hypotheses, formulas in the same
context. A derivation is a rose tree of rules of two kinds. A rewriting derivation transforms a
given term: the identity, a sequence of two rewritings, congruence into each child of a node,
each in its own context and under its own hypotheses, and the equations of the language applied
at the term: β for functions, the components of a pair and the η of pairs and of the terminal
type, the unfolding of a definition at its arguments, the computation of the folds of the
natural numbers and of lists, an instance of an earlier equational theorem, and an equation among
the hypotheses. A proof derivation proves a formula: an equation by rewriting both sides to one
term, or by induction in the form of the uniqueness of recursion; a hypothesis; a formula by
proving it after rewriting it or a formula that rewrites to it, or by a cut through a formula
proved first; the equality of two formulas that entail each other, and of two functions whose
applications to a new variable are equal; an instance of an earlier theorem, its hypotheses'
instances proved; and a formula by induction on the innermost variable of the natural numbers or
of a list type, with the formula's instance at the start and, under the induction hypothesis, at
a successor or a construction. These rules are the basic axioms and rules of a local set theory
({cite}`RuizHernandezSolorzano2021`, Section 3.2), a formula's comprehension the abstraction of
the formula and membership application, with the extensionality of every exponential in place of
that of power types, and with induction. The rewriting takes its terms from the term it
rewrites, so that a derivation names no term but the steps of its inductions, the formulas of
its cuts and the instances of the theorems it cites, and the checker computes every
substitution.

## Main definitions

* {lit}`Rule`, {lit}`Deriv` — the rules and the derivations.
* {lit}`Thm` — a theorem: a formula in a context under hypotheses.
* {lit}`check` — the rewriting a derivation performs, and the judgments it proves.
* {lit}`checkThms` — the check of a development of theorems, each proved with those before it.

## References

* {cite}`RuizHernandezSolorzano2021`

## Tags

internal language, derivation, proof checker, rewriting, induction, local set theory
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
  /-- The equational theorem of index {lit}`j` at objects and terms, from its left side to its
  right, or from its right to its left when {lit}`flip`. -/
  | thm (j : ℕ) (θ : List Tree) (σ : List Term) (flip : Bool)
  /-- The equation among the hypotheses of index {lit}`i`, from its left side to its right, or
  from its right to its left when {lit}`flip`. -/
  | rwHyp (i : ℕ) (flip : Bool)
  /-- An equation whose sides two rewritings take to one term. -/
  | join
  /-- An equation by induction on the innermost variable, of the natural numbers, with zero and
  the successor the primitives of indices {lit}`kz` and {lit}`ks`, by the step {lit}`s`. -/
  | natInd (kz ks : ℕ) (s : Term)
  /-- An equation by induction on the innermost variable, of a list type, with the empty list and
  construction the primitives of indices {lit}`kn` and {lit}`kc`, by the step {lit}`s`. -/
  | listInd (kn kc : ℕ) (s : Term)
  /-- The hypothesis of index {lit}`i`. -/
  | hyp (i : ℕ)
  /-- A cut through the formula {lit}`φ`, proved first and then a hypothesis. -/
  | cut (φ : Term)
  /-- A formula proved after a rewriting. -/
  | conv
  /-- A formula, the formula {lit}`φ` proved and rewritten to it. -/
  | convFrom (φ : Term)
  /-- The equality of two formulas, each proved under the other. -/
  | propExt
  /-- The equality of two functions, whose applications to a new variable are proved equal. -/
  | funExt
  /-- The theorem of index {lit}`j` at objects and terms, its hypotheses' instances proved. -/
  | apply (j : ℕ) (θ : List Tree) (σ : List Term)
  /-- A formula by induction on the innermost variable, of the natural numbers, with zero and the
  successor the primitives of indices {lit}`kz` and {lit}`ks`, under the induction hypothesis
  at the successor. -/
  | natIndHyp (kz ks : ℕ)
  /-- A formula by induction on the innermost variable, of a list type, with the empty list and
  construction the primitives of indices {lit}`kn` and {lit}`kc`, under the induction hypothesis
  at the construction. -/
  | listIndHyp (kn kc : ℕ)

/-- A derivation of the internal language. -/
abbrev Deriv : Type := RoseTree Rule

/-- A theorem: a formula in a context under hypotheses, in object variables. -/
structure Thm where
  /-- The number of object variables. -/
  arity : ℕ
  /-- The types of the variables, the innermost first. -/
  ctx : List Tree
  /-- The hypotheses. -/
  hyps : List Term
  /-- The conclusion. -/
  concl : Term

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

/-- A term weakened past a new innermost variable. -/
def weaken1 (t : Term) : Term := Term.rename t (· + 1)

/-- A term weakened past two new innermost variables. -/
def weaken2 (t : Term) : Term := Term.rename t (· + 2)

/-- The sides of an equation. -/
def eqParts (φ : Term) : Option (Term × Term) := match φ.label, φ.children with
  | .eq, [t, u] => some (t, u)
  | _, _ => none

/-- The instance of a term of a theorem at objects and terms. -/
def instTerm (θ : List Tree) (σ : List Term) (s : Term) : Term :=
  Term.subst (Term.osubst θ s) (Term.substList σ)

/-- The type of a term in a context. -/
def typeIn (G : Globals) (n : ℕ) (Γ : List Tree) (t : Term) : Option Tree :=
  (compile G n t (ctxObj Γ) (stdEnv Γ)).map Prod.snd

/-- Hypotheses in a context of an innermost variable that none of them mentions, in the context
{lit}`Γ` without it, where they are formulas. -/
def lowerHyps (G : Globals) (n : ℕ) (Γ : List Tree) (Φ : List Term) : Option (List Term) :=
  Φ.mapM fun ψ ↦
    if weaken1 (Term.rename ψ (· - 1)) = ψ ∧ typeIn G n Γ (Term.rename ψ (· - 1)) = some omega
    then some (Term.rename ψ (· - 1)) else none

/-- Whether objects and terms instantiate a theorem in a context: types for its object
variables, and terms of its context's types at them. -/
def instOk (G : Globals) (n : ℕ) (Γ : List Tree) (a : Thm) (θ : List Tree) (σ : List Term) :
    Bool :=
  decide (θ.length = a.arity) && θ.all (IsTy n) && decide (σ.length = a.ctx.length) &&
    (σ.zip (a.ctx.map (PartialHorn.subst θ))).all (fun (u, A) ↦ typeIn G n Γ u = some A)

/-- The contexts and hypotheses of a node's children, in the node's context and under its
hypotheses: an abstraction's body extends the context, the hypotheses weakened, and the start
and the step of a fold are in contexts of their own, under no hypotheses. -/
def childCtxs (G : Globals) (n : ℕ) (l : Label) (ts : List Term) (Γ : List Tree)
    (Φ : List Term) : Option (List (List Tree × List Term)) := match l, ts with
  | .lam a, [_] => some [(a :: Γ, Φ.map weaken1)]
  | .natRec, [z, _, _] => do
    let c ← typeIn G n [] z
    pure [([], []), ([c], []), (Γ, Φ)]
  | .listRec, [z, _, m] => do
    let c ← typeIn G n [] z
    let a ← (typeIn G n Γ m).bind listPart
    pure [([], []), ([c, a], []), (Γ, Φ)]
  | .roseRec c, [_, _] => some [([prod nat (list c)], []), (Γ, Φ)]
  | _, ts => some (ts.map fun _ ↦ (Γ, Φ))

/-- The rewriting of a term at its root by a rule of the language's equations, with the
constants of {lit}`G`, the theorems of {lit}`E` and the hypotheses {lit}`Φ`. -/
def rootStep (G : Globals) (E : Array Thm) (n : ℕ) (Γ : List Tree) (Φ : List Term) (l : Rule)
    (t : Term) : Option Term := match l, t.label, t.children with
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
    let lr ← if a.hyps = [] then eqParts a.concl else none
    if instOk G n Γ a θ σ ∧ t = instTerm θ σ (if flip then lr.2 else lr.1) then
      some (instTerm θ σ (if flip then lr.1 else lr.2)) else none
  | .rwHyp i flip, _, _ => do
    let lr ← (Φ[i]?).bind eqParts
    if t = (if flip then lr.2 else lr.1) then some (if flip then lr.1 else lr.2) else none
  | _, _, _ => none

/-- The results of a node's rewriting and of its proving, from its children's: the rewriting of
a term in a context under hypotheses, and whether it proves a formula in a context under
hypotheses. -/
abbrev Checks : Type :=
  (List Tree → List Term → Term → Option Term) × (List Tree → List Term → Term → Bool)

/-- One step of the checker, at a node of a rule, from its children's results. -/
def checkStep (G : Globals) (E : Array Thm) (n : ℕ) (l : Rule) (cs : List (Deriv × Checks)) :
    Checks :=
  (fun Γ Φ t ↦ match l, cs with
    | .refl, [] => some t
    | .trans, [(_, c₁), (_, c₂)] => (c₁.1 Γ Φ t).bind (c₂.1 Γ Φ)
    | .cong, cs => do
      let Γs ← childCtxs G n t.label t.children Γ Φ
      if cs.length = t.children.length ∧ Γs.length = t.children.length then do
        let ts ← ((cs.zip (Γs.zip t.children)).mapM fun (c, (Δ, Ψ), u) ↦ c.2.1 Δ Ψ u)
        pure (RoseTree.node t.label ts)
      else none
    | l, [] => rootStep G E n Γ Φ l t
    | _, _ => none,
   fun Γ Φ φ ↦ match l, cs with
    | .join, [(_, c₁), (_, c₂)] => match eqParts φ with
      | some (t, u) => match c₁.1 Γ Φ t, c₂.1 Γ Φ u with
        | some v, some v' => decide (v = v')
        | _, _ => false
      | none => false
    | .natInd kz ks s, [(_, p₀), (_, p₁), (_, p₂)] =>
      match eqParts φ, Γ with
      | some (t, u), c :: Γ' => match typeIn G n Γ t, lowerHyps G n Γ' Φ with
        | some C, some Φ' => decide (c = nat ∧ G.prims[kz]? = some zeroPrim ∧
              G.prims[ks]? = some succPrim ∧ typeIn G n Γ u = some C ∧
              typeIn G n (C :: Γ') s = some C) &&
            p₀.2 Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kz [] Term.star)))
              (Term.subst u (instVar (Term.arr kz [] Term.star)))) &&
            p₁.2 Γ Φ (Term.eq (natSuccAt ks t) (Term.subst s (atVar0 t))) &&
            p₂.2 Γ Φ (Term.eq (natSuccAt ks u) (Term.subst s (atVar0 u)))
        | _, _ => false
      | _, _ => false
    | .listInd kn kc s, [(_, p₀), (_, p₁), (_, p₂)] =>
      match eqParts φ, Γ with
      | some (t, u), c :: Γ' => match typeIn G n Γ t, listPart c, lowerHyps G n Γ' Φ with
        | some C, some a, some Φ' => decide (G.prims[kn]? = some nilPrim ∧
              G.prims[kc]? = some consPrim ∧ typeIn G n Γ u = some C ∧
              typeIn G n (C :: a :: Γ') s = some C) &&
            p₀.2 Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kn [a] Term.star)))
              (Term.subst u (instVar (Term.arr kn [a] Term.star)))) &&
            p₁.2 (c :: a :: Γ') (Φ'.map weaken2)
              (Term.eq (listConsAt kc a t) (Term.subst s (atVar0 (weakenElem t)))) &&
            p₂.2 (c :: a :: Γ') (Φ'.map weaken2)
              (Term.eq (listConsAt kc a u) (Term.subst s (atVar0 (weakenElem u))))
        | _, _, _ => false
      | _, _ => false
    | .hyp i, [] => decide (Φ[i]? = some φ)
    | .cut ψ, [(_, p), (_, q)] =>
      decide (typeIn G n Γ ψ = some omega) && p.2 Γ Φ ψ && q.2 Γ (Φ ++ [ψ]) φ
    | .conv, [(_, d), (_, p)] => match d.1 Γ Φ φ with
      | some φ' => p.2 Γ Φ φ'
      | none => false
    | .convFrom ψ, [(_, d), (_, p)] =>
      decide (typeIn G n Γ ψ = some omega ∧ d.1 Γ Φ ψ = some φ) && p.2 Γ Φ ψ
    | .propExt, [(_, p), (_, q)] => match eqParts φ with
      | some (α, β) => decide (typeIn G n Γ α = some omega ∧ typeIn G n Γ β = some omega) &&
          p.2 Γ (Φ ++ [α]) β && q.2 Γ (Φ ++ [β]) α
      | none => false
    | .funExt, [(_, p)] => match eqParts φ with
      | some (f, g) => match (typeIn G n Γ f).bind expParts with
        | some (a, _) => p.2 (a :: Γ) (Φ.map weaken1)
            (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0)))
        | none => false
      | none => false
    | .apply j θ σ, ps => match E[j]? with
      | some a => instOk G n Γ a θ σ && decide (φ = instTerm θ σ a.concl) &&
          decide (ps.length = a.hyps.length) &&
          (ps.zip a.hyps).all fun (p, h) ↦ p.2.2 Γ Φ (instTerm θ σ h)
      | none => false
    | .natIndHyp kz ks, [(_, p₀), (_, p₁)] => match Γ with
      | c :: Γ' => match lowerHyps G n Γ' Φ with
        | some Φ' => decide (c = nat ∧ G.prims[kz]? = some zeroPrim ∧
              G.prims[ks]? = some succPrim ∧ typeIn G n Γ φ = some omega) &&
            p₀.2 Γ' Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))) &&
            p₁.2 Γ (Φ ++ [φ]) (natSuccAt ks φ)
        | none => false
      | [] => false
    | .listIndHyp kn kc, [(_, p₀), (_, p₁)] => match Γ with
      | c :: Γ' => match listPart c, lowerHyps G n Γ' Φ with
        | some a, some Φ' => decide (G.prims[kn]? = some nilPrim ∧ G.prims[kc]? = some consPrim ∧
              typeIn G n Γ φ = some omega) &&
            p₀.2 Γ' Φ' (Term.subst φ (instVar (Term.arr kn [a] Term.star))) &&
            p₁.2 (c :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem φ]) (listConsAt kc a φ)
        | _, _ => false
      | [] => false
    | _, _ => false)

/-- The checker: the rewriting a derivation performs on a term in a context under hypotheses,
and whether it proves a formula in a context under hypotheses. -/
def check (G : Globals) (E : Array Thm) (n : ℕ) : Deriv → Checks :=
  RoseTree.para (checkStep G E n)

/-- Whether a derivation proves a theorem with the constants of {lit}`G` and the theorems of
{lit}`E`: its context is of types, its hypotheses and conclusion are formulas there, and the
derivation proves its conclusion under its hypotheses. -/
def Thm.checks (G : Globals) (E : Array Thm) (a : Thm) (d : Deriv) : Bool :=
  a.ctx.all (IsTy a.arity) && a.hyps.all (fun h ↦ typeIn G a.arity a.ctx h = some omega) &&
    decide (typeIn G a.arity a.ctx a.concl = some omega) &&
    (check G E a.arity d).2 a.ctx a.hyps a.concl

/-- Whether a development checks: each theorem proved by its derivation with the theorems before
it. -/
def checkThms (G : Globals) : List (Thm × Deriv) → Array Thm → Bool :=
  List.rec (fun _ ↦ true) fun e _ ih E ↦ e.1.checks G E e.2 && ih (E.push e.1)

end Geb.FreeTopos.Internal

end
