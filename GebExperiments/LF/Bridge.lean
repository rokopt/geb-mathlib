/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Canonical.Main
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
that Canonical does not use it as a head. The constants and the variables of the context are let
declarations of Canonical's problem, each with its type, or without one where the constant is not
to be used; a rewrite rule is a reduction rule of the let declaration of its left side's head, its
pattern variables named by their indices. The type to inhabit is the problem's type, its products
the parameters Canonical abstracts over.

The translation back is by recursion on Canonical's terms, a nested structure of its own; it is
written as a `partial` function, as the repository's tooling is (`GebMeta`), and its results are
not trusted: each is checked by the checker of `Geb.LF`.

## Main definitions

* `headName`, `toTyp` — the translation of an expression at a scope of names.
* `toRule`, `problem` — the translation of a rule and of a problem.
* `fromTerm` — the translation of a returned term.

## Tags

logical framework, LF, Canonical, type inhabitation, experiment
-/

@[expose] public section

namespace GebExperiments.LF

open Geb Geb.LF

/-- The name of a head: a variable's from the scope, the innermost first, a constant's from the
list of the signature's names. -/
def headName (names : List String) (scope : List String) : Head → String
  | .var i => scope[i]?.getD s!"?var{i}"
  | .const c => names[c]?.getD s!"?const{c}"

/-- One step of the translation of an expression to a type of Canonical at a scope of names: a
product adds a parameter, named by the depth, with its domain's type; an abstraction adds a
parameter; an application is a spine; the kind `type` is `Sort`. A term is the type's term. -/
def toTypStep (names : List String) (l : Label) (cs : List (List String → Canonical.Typ))
    (scope : List String) : Canonical.Typ :=
  let x := s!"x{scope.length}"
  match l, cs with
    | .pi, [a, b] =>
      let cod := b (x :: scope)
      { cod with params := #[⟨x⟩] ++ cod.params, paramTypes := #[some (a scope)] ++ cod.paramTypes }
    | .lam, [m] =>
      let body := m (x :: scope)
      { body with params := #[⟨x⟩] ++ body.params }
    | .app h, cs =>
      { spine := { head := headName names scope h,
                   args := (cs.map fun c ↦ (c scope).toTerm).toArray } }
    | _, _ => { spine := { head := "Sort" } }

/-- The translation of an expression to a type of Canonical at a scope of names. -/
def toTyp (names : List String) : Expr → List String → Canonical.Typ :=
  RoseTree.elim (toTypStep names)

/-- The name of a rule's pattern variable. -/
def patName (i : ℕ) : String := s!"p{i}"

/-- The translation of a rule, with the index of its left side's head: the left side a spine of
patterns, its variables named by their indices, and the right side a spine in their scope. -/
def toRule (names : List String) (r : Rule) : Option (ℕ × Canonical.Rule) :=
  let scope := (List.range r.vars.length).map patName
  match r.lhs.label with
    | .app (.const c) =>
      some (c, { lhs := (toTyp names r.lhs scope).spine, rhs := (toTyp names r.rhs scope).spine })
    | _ => none

/-- The name of the variable of a context at a level, the outermost at level zero. -/
def ctxName (level : ℕ) : String := s!"v{level}"

/-- The problem of inhabiting a type in a context, in a signature with rules, the constants that
`usable` admits given their types: `Sort`, the constants with their rules, and the context's
variables are let declarations, and the type is the problem's type. -/
def problem (names : List String) (sig : Sig) (rules : List Rule) (usable : ℕ → Bool)
    (Γ : Ctx) (goal : Expr) : Canonical.Typ :=
  let crules := rules.filterMap (toRule names)
  let constLets := sig.zipIdx.map fun (a, c) ↦
    (({ name := names[c]?.getD s!"c{c}",
        rules := (crules.filter (·.1 == c)).map (·.2) |>.toArray } : Canonical.Let),
      if usable c then some (toTyp names a []) else none)
  let n := Γ.length
  let scopeAt (i : ℕ) : List String := ((List.range (n - 1 - i)).map ctxName).reverse
  let ctxLets := Γ.zipIdx.map fun (a, i) ↦
    (({ name := ctxName (n - 1 - i) } : Canonical.Let), some (toTyp names a (scopeAt i)))
  let lets := [(({ name := "Sort" } : Canonical.Let), none)] ++ constLets ++ ctxLets.reverse
  let typ := toTyp names goal ((List.range n).map ctxName).reverse
  { typ with lets := (lets.map (·.1)).toArray ++ typ.lets,
             letTypes := (lets.map (·.2)).toArray ++ typ.letTypes }

/-- The translation of a returned term back to canonical LF at a scope of names: its parameters
are abstractions, its head a variable of the scope or a constant of the signature, and its
arguments translated in the scope of its parameters. Canonical repeats the problem's let
declarations on the term it returns; a let declaration that names `Sort`, a constant or a variable
of the scope declares nothing new and is passed over. A term with any other let declaration, or
with a head of neither kind, has no translation. -/
partial def fromTerm (names : List String) (scope : List String) (t : Canonical.Term) :
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
