/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Canonical.Main
public import Geb.Prototypes.LF.Metatheory.TypeShape
public import Geb.Prototypes.LF.Rewrite

/-!
# Canonical LF problems for Canonical

The translation of a problem of canonical LF modulo rewrite rules, a context and a type to
inhabit in a signature with rules, to the input of Canonical (Norman and Avigad, "Canonical for
automated theorem proving in Lean", ITP 2025, Section 3.1), and of the terms it returns back to
canonical LF, where the checker of `Geb.LF` decides them.

The two formats agree: both are β-normal and η-long, an application is a head with its spine, and
a type is a product over parameters of an atomic type. Canonical names its variables where LF
uses de Bruijn indices: a binder of the translation is named by its depth, a constant by the name
the signature's list of names gives it, and the kind `type` by `Sort`, declared without a type so
that Canonical does not use it as a head. Canonical's expression is a type when its parameters
carry types and a term otherwise. The constants and the variables of the context are let
declarations of Canonical's problem, each with its type, or without one where the constant is not
to be used; a rewrite rule is an equation of the let declaration of its left side's head, its
pattern variables named by their indices. The problem is a declaration of the goal whose type is
the type to inhabit, its products the parameters Canonical abstracts over.

A problem may offer the search only the constants relevant to its goal (`relevant`): those of a
core and those the goal mentions, closed under adding the constants a reached constant's type
mentions, and every constant other than a type former whose type mentions only reached constants:
the term formers and rules that speak of the goal's types alone. A type former's type mentions
only the kind of types, so that admitting type formers so would admit every type. The others are
declared without types.

The translation back is by recursion on Canonical's terms, a nested structure of its own; it is
written as a `partial` function, as the repository's tooling is (`GebMeta`), and its results are
not trusted: each is checked by the checker of `Geb.LF`.

## Main definitions

* `constName`, `headName`, `toExpr` — the translation of an expression at a scope of names.
* `toRule`, `problem` — the translation of a rule and of a problem.
* `consts`, `relevant` — the constants an expression mentions, and those relevant to a goal.
* `fromTerm` — the translation of a returned term.

## Tags

logical framework, LF, Canonical, type inhabitation, experiment
-/

@[expose] public section

namespace GebExperiments.LF

open Geb Geb.LF

/-- The name of a constant: the one the list of the signature's names gives it, or one formed from
its index past the list's end, so that a declaration and its uses agree. -/
def constName (names : List String) (c : ℕ) : String := names[c]?.getD s!"c{c}"

/-- The name of a head: a variable's from the scope, the innermost first, a constant's by
`constName`. -/
def headName (names : List String) (scope : List String) : Head → String
  | .var i => scope[i]?.getD s!"?var{i}"
  | .const c => constName names c

/-- One step of the translation of an expression to an expression of Canonical at a scope of
names: a product adds a parameter, named by the depth, with its domain's type; an abstraction
adds a parameter without a type; an application is a spine; the kind `type` is `Sort`. -/
def toExprStep (names : List String) (l : Label) (cs : List (List String → Canonical.Expr))
    (scope : List String) : Canonical.Expr :=
  let x := s!"x{scope.length}"
  match l, cs with
    | .pi, [a, b] =>
      let cod := b (x :: scope)
      { cod with params := #[{ name := x, type := some (a scope) }] ++ cod.params }
    | .lam, [m] =>
      let body := m (x :: scope)
      { body with params := #[{ name := x }] ++ body.params }
    | .app h, cs =>
      { spine := { head := headName names scope h, args := (cs.map (· scope)).toArray } }
    | _, _ => { spine := { head := "Sort" } }

/-- The translation of an expression to an expression of Canonical at a scope of names. -/
def toExpr (names : List String) : Expr → List String → Canonical.Expr :=
  RoseTree.elim (toExprStep names)

/-- The constants an expression mentions. -/
def consts : Expr → List ℕ :=
  RoseTree.elim fun l cs ↦ (match l with | .app (.const c) => [c] | _ => []) ++ cs.flatten

/-- The constants of a signature relevant to a goal: those of `core` and those the goal mentions,
closed under adding the constants a reached constant's type mentions and every constant whose
type mentions only reached constants and does not end in the kind of types, the constant `tpc`;
the closure iterated as often as the signature has constants, which reaches it. -/
def relevant (sig : Sig) (tpc : ℕ) (core : List ℕ) (goal : Expr) : ℕ → Bool :=
  let typeConsts (c : ℕ) : List ℕ := (sig[c]?.map consts).getD []
  let former (c : ℕ) : Bool := (sig[c]?.map fun T ↦ (Expr.headDepth T).1) == some (some tpc)
  let step (S : List ℕ) : List ℕ := (S ++ S.flatMap typeConsts ++ (List.range sig.length).filter
    fun c ↦ !former c && (typeConsts c).all S.contains).eraseDups
  (Nat.repeat step sig.length (core ++ consts goal)).contains

/-- The name of a rule's pattern variable. -/
def patName (i : ℕ) : String := s!"p{i}"

/-- The translation of a rule, with the index of its left side's head: the left side a spine of
patterns, its variables named by their indices, and the right side a spine in their scope. -/
def toRule (names : List String) (r : Rule) : Option (ℕ × Canonical.Rule) :=
  let scope := (List.range r.vars.length).map patName
  match r.lhs.label with
    | .app (.const c) =>
      some (c, { lhs := (toExpr names r.lhs scope).spine, rhs := (toExpr names r.rhs scope).spine })
    | _ => none

/-- The name of the variable of a context at a level, the outermost at level zero. -/
def ctxName (level : ℕ) : String := s!"v{level}"

/-- The problem, named `name`, of inhabiting a type in a context, in a signature with rules,
the constants that `usable` admits given their types: `Sort`, the constants with their rules as
equations, and the context's variables are let declarations of the goal's type. -/
def problem (name : String) (names : List String) (sig : Sig) (rules : List Rule)
    (usable : ℕ → Bool) (Γ : Ctx) (goal : Expr) : Canonical.Decl :=
  let crules := rules.filterMap (toRule names)
  let constLets : List Canonical.Decl := sig.zipIdx.map fun (a, c) ↦
    { name := constName names c,
      type := if usable c then some (toExpr names a []) else none,
      equations := (crules.filter (·.1 == c)).map (·.2) |>.toArray }
  let n := Γ.length
  let scopeAt (i : ℕ) : List String := ((List.range (n - 1 - i)).map ctxName).reverse
  let ctxLets : List Canonical.Decl := Γ.zipIdx.map fun (a, i) ↦
    { name := ctxName (n - 1 - i), type := some (toExpr names a (scopeAt i)) }
  let lets := [({ name := "Sort" } : Canonical.Decl)] ++ constLets ++ ctxLets.reverse
  let typ := toExpr names goal ((List.range n).map ctxName).reverse
  { name, type := some { typ with lets := lets.toArray ++ typ.lets } }

/-- The translation of a returned term back to canonical LF at a scope of names: its parameters
are abstractions, its head a variable of the scope or a constant of the signature, and its
arguments translated in the scope of its parameters. Canonical repeats the problem's let
declarations on the term it returns; a let declaration that names `Sort`, a constant or a variable
of the scope declares nothing new and is passed over. A term with any other let declaration, or
with a head of neither kind, has no translation. -/
partial def fromTerm (names : List String) (scope : List String) (t : Canonical.Expr) :
    Option Expr := do
  if !t.lets.all fun l ↦ l.name == "Sort" || names.contains l.name || scope.contains l.name then
    none
  let scope' := t.params.foldl (fun s p ↦ p.name :: s) scope
  let h ← match scope'.idxOf? t.spine.head with
    | some i => some (Head.var i)
    | none => (names.idxOf? t.spine.head).map Head.const
  let args ← t.spine.args.toList.mapM (fromTerm names scope')
  pure (Nat.repeat Expr.lam t.params.size (Expr.app h args))

end GebExperiments.LF

end
