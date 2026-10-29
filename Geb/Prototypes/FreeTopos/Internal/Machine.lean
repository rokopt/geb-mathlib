/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# An environment machine reducing terms

A reduction of the internal language's terms by evaluation in environments of values
({cite}`Landin1964`), lazily and with each delayed value computed at most once
({cite}`Launchbury1993`): a term is evaluated in an environment that holds a value for each of
its variables, an abstraction to its closure, and a definition's application to its body
evaluated in the environment of its arguments' values, so that no term is substituted into
another as the reduction proceeds. The rules it computes are those of the base checker's
rewriting at the root ({name}`Geb.FreeTopos.Internal.rootStep`): β, the components of pairs, the
folds of the natural numbers, of lists and of rose trees at their constructions, the case
analysis of a coproduct at its injections, and the unfolding of the definitions that a
predicate selects.

An argument, a component of a pair, the datum of a primitive arrow and the start of a fold are
delayed: each is a node of two children, the value of a {name}`Thunk`, which the runtime
computes when the child is first read and keeps, and the term with its environment, which the
node reads back as. Logically a {name}`Thunk` is its function, so that a delayed node is the
value beside its source, and the reduction is the strict evaluation whose every delayed value
reads back to the term it delays. The recursion's value that a fold's rule substitutes into its
step is delayed so, its source the fold of the construction's datum. Every value reads back to
a term to which the evaluated term rewrites, by the base checker's rules at the root and by
congruences at children in the term's context; the reduction is sound by that rewriting, and is
not the prover's.

## Main definitions

* {lit}`VLabel`, {lit}`Val` — the values.
* {lit}`envSubst`, {lit}`readBack` — the substitution an environment stands for, and the term a
  value reads back to.
* {lit}`delayed` — the delayed value of a computation.
* {lit}`Machine`, {lit}`machine` — the evaluation of terms in environments, the weak head normal
  form of values and the normal form of a value's term, within a depth of recursion.
* {lit}`machineReduce` — the reduction of a term.

## References

* {cite}`Landin1964`, for the evaluation of expressions in environments of closures.
* {cite}`Launchbury1993`, for lazy evaluation that computes each delayed value at most once.

## Tags

internal language, abstract machine, environment, closure, lazy evaluation, reduction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)

/-- The label of a node of a value. -/
inductive VLabel where
  /-- The variable of a de Bruijn index of the reduced term's context. -/
  | free (i : ℕ)
  /-- The element of the terminal object. -/
  | star
  /-- The pair of two values. -/
  | pair
  /-- The closure of the abstraction of the term {lit}`b` over a variable of the type {lit}`a`,
  in the environment of the node's children, past which the variables are shifted by
  {lit}`k`. -/
  | clo (a : Tree) (b : Term) (k : ℕ)
  /-- The application of the primitive arrow of an index, at objects, to a value. -/
  | arr (k : ℕ) (θ : List Tree)
  /-- The application of a value to a value. -/
  | app
  /-- The first component of a value. -/
  | fst
  /-- The second component of a value. -/
  | snd
  /-- The fold of a natural number by the step {lit}`s`, from the start and of the number the
  node's first two children, in the environment of the others, shifted by {lit}`k`. -/
  | natRec (s : Term) (k : ℕ)
  /-- The fold of a list by the step {lit}`s`, from the start and of the list the node's first
  two children, in the environment of the others, shifted by {lit}`k`. -/
  | listRec (s : Term) (k : ℕ)
  /-- The fold of a rose tree into the type {lit}`c` by the step {lit}`s`, of the tree the node's
  first child, in the environment of the others, shifted by {lit}`k`. -/
  | roseRec (c : Tree) (s : Term) (k : ℕ)
  /-- The application of the definition of an index, at objects, to values. -/
  | defn (k : ℕ) (θ : List Tree)
  /-- The equality of two values. -/
  | eq
  /-- The term {lit}`t` in the environment of the node's children, shifted by {lit}`k`,
  unevaluated. -/
  | term (t : Term) (k : ℕ)
  /-- A delayed value: the value, the node's first child, of the value its second child is the
  source of, which it reads back as. -/
  | delay
  /-- The value of a computation that does not reach one. -/
  | fail

/-- A value of the machine: a tree of {lit}`VLabel`, an environment the children of a closure, of
a fold or of an unevaluated term. -/
abbrev Val : Type := RoseTree VLabel

/-- The substitution an environment stands for: the variable of an index in it its value's
term, and each later variable the variable past the environment's values shifted by
{lit}`k`. -/
def envSubst (ts : List Term) (k : ℕ) : ℕ → Term := fun i ↦
  if h : i < ts.length then ts[i] else Term.var (i - ts.length + k)

/-- One step of the reading back of a value to a term, at a node of a label, from the terms of
its children: a closure to its abstraction with the environment's terms substituted in its body,
a fold to its fold with them substituted in its step, an unevaluated term to the term with them
substituted, a delayed value to its source's term, and every other node to the node of the
term's label of the same name. -/
def readStep : VLabel → List Term → Term
  | .free i, _ => Term.var i
  | .star, _ => Term.star
  | .pair, cs => RoseTree.node .pair cs
  | .clo a b k, cs => Term.lam a (Term.subst b (Term.liftS (envSubst cs k)))
  | .arr j θ, cs => RoseTree.node (.arr j θ) cs
  | .app, cs => RoseTree.node .app cs
  | .fst, cs => RoseTree.node .fst cs
  | .snd, cs => RoseTree.node .snd cs
  | .natRec s k, z :: m :: cs =>
    Term.natRec z (Term.subst s (Term.liftS (envSubst cs k))) m
  | .natRec _ _, cs => RoseTree.node .natRec cs
  | .listRec s k, z :: m :: cs =>
    Term.listRec z (Term.subst s (Term.liftS (Term.liftS (envSubst cs k)))) m
  | .listRec _ _, cs => RoseTree.node .listRec cs
  | .roseRec c s k, m :: cs => Term.roseRec c (Term.subst s (Term.liftS (envSubst cs k))) m
  | .roseRec c _ _, cs => RoseTree.node (.roseRec c) cs
  | .defn j θ, cs => RoseTree.node (.defn j θ) cs
  | .eq, cs => RoseTree.node .eq cs
  | .term t k, cs => Term.subst t (envSubst cs k)
  | .delay, [_, c] => c
  | .delay, _ => Term.star
  | .fail, _ => Term.star

/-- The term a value reads back to. -/
def readBack : Val → Term := RoseTree.elim readStep

/-- The node of a value of a label over values. -/
abbrev vnode (l : VLabel) (cs : List Val) : Val := RoseTree.node l cs

/-- The value of a computation that does not reach one. -/
abbrev failV : Val := vnode .fail []

/-- The delayed value of a computation, the value {lit}`src` its source: the node whose first
child the runtime computes when it is first read, and keeps. -/
def delayed (th : Thunk (Option Val)) (src : Val) : Val :=
  WType.mk (.delay, 2) fun i ↦ if i.1 = 0 then th.get.getD failV else src

/-- The label of a value's node of a label of a term whose children are values in the term's
environment: the pair, the components, the application, the primitive arrows and the
equality. -/
def Label.plain? : Label → Option VLabel
  | .pair => some .pair
  | .fst => some .fst
  | .snd => some .snd
  | .app => some .app
  | .arr j θ => some (.arr j θ)
  | .eq => some .eq
  | _ => none

/-- The machine's operations at a depth of recursion: the evaluation of a term in an
environment shifted by a number, the weak head normal form of a value, and the normal form of a
value's term. -/
structure Machine where
  /-- The evaluation of a term in an environment shifted by a number. -/
  eval : Term → List Val → ℕ → Option Val
  /-- The weak head normal form of a value. -/
  whnf : Val → Option Val
  /-- The normal form of a value's term, under every constructor and none of its binders. -/
  nf : Val → Option Term

variable (G : Globals) (unfold : ℕ → Bool) (kl kc : ℕ)

/-- The delayed value of a term in an environment shifted by {lit}`k`, evaluated by
{lit}`o`. -/
def Machine.delay (o : Machine) (t : Term) (vs : List Val) (k : ℕ) : Val :=
  delayed (Thunk.mk fun _ ↦ o.eval t vs k) (vnode (.term t k) vs)

/-- One step of the evaluation of a term in an environment shifted by {lit}`k`, the subterms and
the values reduced by {lit}`o`: a variable to its value, or past the environment to a free
variable; an abstraction to its closure; a component and an application to the weak head
normal form of the node over the value of its head, the argument delayed; a fold to its weak head
normal form, its start delayed; a definition the predicate selects to its body evaluated in the
environment of its arguments, delayed; and a pair, a primitive arrow's application and an
equality to the node over its children, delayed. -/
def Machine.evalStep (o : Machine) (t : Term) (vs : List Val) (k : ℕ) : Option Val :=
  match t.label, t.children with
  | .var i, _ => some (if h : i < vs.length then vs[i] else vnode (.free (i - vs.length + k)) [])
  | .star, [] => some (vnode .star [])
  | .lam a, [b] => some (vnode (.clo a b k) vs)
  | .fst, [p] => do o.whnf (vnode .fst [← o.eval p vs k])
  | .snd, [p] => do o.whnf (vnode .snd [← o.eval p vs k])
  | .app, [f, u] => do o.whnf (vnode .app [← o.eval f vs k, o.delay u vs k])
  | .natRec, [z, s, m] => do
    o.whnf (vnode (.natRec s k) (o.delay z vs k :: (← o.eval m vs k) :: vs))
  | .listRec, [z, s, m] => do
    o.whnf (vnode (.listRec s k) (o.delay z vs k :: (← o.eval m vs k) :: vs))
  | .roseRec c, [s, m] => do o.whnf (vnode (.roseRec c s k) ((← o.eval m vs k) :: vs))
  | .defn j θ, ts =>
    let us := ts.map fun u ↦ o.delay u vs k
    match if unfold j then (G.defs[j]?).bind Definition.language? else none with
    | some d => o.eval (if θ.isEmpty then d.body else Term.osubst θ d.body) us us.length
    | none => some (vnode (.defn j θ) us)
  | l, ts => do
    let l' ← l.plain?
    some (vnode l' (ts.map fun u ↦ o.delay u vs k))

/-- One step of the weak head normal form of a value, the values reduced and the terms evaluated
by {lit}`o`: a delayed value to its value's, a component of a pair, an application of a closure,
the case analysis at an injection, and a fold at a construction, each reduced, the recursion's
value of a fold delayed, its source the fold of the construction's datum; every other value is
its own. -/
def Machine.whnfStep (o : Machine) (v : Val) : Option Val :=
  match v.label, v.children with
  | .delay, [r, _] => match r.label with
    | .fail => none
    | _ => o.whnf r
  | .fst, [p] => do
    let p' ← o.whnf p
    match p'.label, p'.children with
    | .pair, [a, _] => o.whnf a
    | _, _ => some (vnode .fst [p'])
  | .snd, [p] => do
    let p' ← o.whnf p
    match p'.label, p'.children with
    | .pair, [_, b] => o.whnf b
    | _, _ => some (vnode .snd [p'])
  | .app, [f, u] => do
    let f' ← o.whnf f
    match f'.label, f'.children with
    | .clo _ b k, env => o.whnf (← o.eval b (u :: env) k)
    | .arr j _, [p] =>
      if G.prims[j]? = some casePrim then do
        let u' ← o.whnf u
        match u'.label, u'.children with
        | .arr j' _, [w] =>
          if G.prims[j']? = some inlPrim ∨ G.prims[j']? = some inrPrim then do
            let p' ← o.whnf p
            match p'.label, p'.children with
            | .pair, [g, h] =>
              o.whnf (vnode .app [if G.prims[j']? = some inlPrim then g else h, w])
            | _, _ => some (vnode .app [f', u'])
          else some (vnode .app [f', u'])
        | _, _ => some (vnode .app [f', u'])
      else some (vnode .app [f', u])
    | _, _ => some (vnode .app [f', u])
  | .natRec s k, z :: m :: env => do
    let m' ← o.whnf m
    match m'.label, m'.children with
    | .arr j [], [c] =>
      if G.prims[j]? = some zeroPrim then do
        let c' ← o.whnf c
        match c'.label, c'.children with
        | .star, [] => o.whnf z
        | _, _ => some (vnode (.natRec s k) (z :: m' :: env))
      else if G.prims[j]? = some succPrim then do
        let src := vnode (.natRec s k) (z :: c :: env)
        let r := delayed (Thunk.mk fun _ ↦ o.whnf src) src
        o.whnf (← o.eval s (r :: env) k)
      else some (vnode (.natRec s k) (z :: m' :: env))
    | _, _ => some (vnode (.natRec s k) (z :: m' :: env))
  | .listRec s k, z :: m :: env => do
    let m' ← o.whnf m
    match m'.label, m'.children with
    | .arr j [_], [c] =>
      if G.prims[j]? = some nilPrim then do
        let c' ← o.whnf c
        match c'.label, c'.children with
        | .star, [] => o.whnf z
        | _, _ => some (vnode (.listRec s k) (z :: m' :: env))
      else if G.prims[j]? = some consPrim then do
        let c' ← o.whnf c
        match c'.label, c'.children with
        | .pair, [h, tl] => do
          let src := vnode (.listRec s k) (z :: tl :: env)
          let r := delayed (Thunk.mk fun _ ↦ o.whnf src) src
          o.whnf (← o.eval s (r :: h :: env) k)
        | _, _ => some (vnode (.listRec s k) (z :: m' :: env))
      else some (vnode (.listRec s k) (z :: m' :: env))
    | _, _ => some (vnode (.listRec s k) (z :: m' :: env))
  | .roseRec c s k, m :: env => do
    let m' ← o.whnf m
    match m'.label, m'.children with
    | .arr j _, [p] =>
      if (G.prims[j]? = some nodePrim ∨ G.prims[j]? = some lnodePrim) ∧
          G.prims[kl]? = some nilPrim ∧ G.prims[kc]? = some consPrim then do
        let p' ← o.whnf p
        match p'.label, p'.children with
        | .pair, [l, cs] =>
          let folds := vnode (.listRec (Term.arr kc [c] (Term.pair
              (Term.roseRec c (weakenStep2 s) (Term.var 1)) (Term.var 0))) k)
            (vnode (.arr kl [c]) [vnode .star []] :: cs :: env)
          let r := delayed (Thunk.mk fun _ ↦ o.whnf folds) folds
          o.whnf (← o.eval s (vnode .pair [l, r] :: env) k)
        | _, _ => some (vnode (.roseRec c s k) (m' :: env))
      else some (vnode (.roseRec c s k) (m' :: env))
    | _, _ => some (vnode (.roseRec c s k) (m' :: env))
  | _, _ => some v

/-- One step of the normal form of a value's term, the values reduced by {lit}`o`: the weak head
normal form, then the normal forms of its children in the term's context, a closure's term, a
fold's step and an unevaluated term read back unreduced. -/
def Machine.nfStep (o : Machine) (v : Val) : Option Term := do
  let w ← o.whnf v
  match w.label, w.children with
  | .natRec s k, z :: m :: env => do
    let z' ← o.nf z
    let m' ← o.nf m
    pure (Term.natRec z' (Term.subst s (Term.liftS (envSubst (env.map readBack) k))) m')
  | .listRec s k, z :: m :: env => do
    let z' ← o.nf z
    let m' ← o.nf m
    pure (Term.listRec z'
      (Term.subst s (Term.liftS (Term.liftS (envSubst (env.map readBack) k)))) m')
  | .roseRec c s k, m :: env => do
    let m' ← o.nf m
    pure (Term.roseRec c (Term.subst s (Term.liftS (envSubst (env.map readBack) k))) m')
  | .free _, cs | .star, cs | .pair, cs | .arr _ _, cs | .app, cs | .fst, cs | .snd, cs
    | .defn _ _, cs | .eq, cs => do
    pure (readStep w.label (← cs.mapM o.nf))
  | .fail, _ => none
  | _, _ => some (readBack w)

/-- The machine within a depth of recursion of {lit}`fuel`, each operation's recursive calls
made at the depth below. -/
def machine (fuel : ℕ) : Machine :=
  fuel.rec ⟨fun _ _ _ ↦ none, fun _ ↦ none, fun _ ↦ none⟩ fun _ o ↦
    ⟨Machine.evalStep G unfold o, Machine.whnfStep G kl kc o, Machine.nfStep o⟩

/-- The reduction of a term by the machine within a depth of recursion of {lit}`fuel`: the
normal form of its value in the empty environment. -/
def machineReduce (fuel : ℕ) (t : Term) : Option Term := do
  let m := machine G unfold kl kc fuel
  m.nf (← m.eval t [] 0)

end Geb.FreeTopos.Internal

end
