/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ConcreteSyntax
public import Mathlib.Data.Fin.VecNotation

/-!
# Canonical S-expressions as a data type

[FormalSExpr] models canonical S-expressions as a family indexed by the
octet string representing them, with an atom's index
`base10 (length xs) ++ [58] ++ xs` and a list's index
`40 :: xs ++ [41]`. `CSexp` is the non-dependent form of that family and
`CSexp.render` is the index function: `58`, `40` and `41` being `:`, `(`
and `)`, the atom index is `Geb.Csexp.printVerbatim` and the list index
is the parenthesized concatenation of the children's.

The point of carrying the family separately is
`Csexp.print_eq_render_toCSexp`. `Geb.Csexp.parse_print` says the local
parser accepts what the local printer emits; it does not say the output
is a canonical S-expression. Factoring the printer through `CSexp` says
exactly that, because every `CSexp` renders to one by construction.

`Rose.toCSexp` is the other map into the family: a rose node becomes the
list whose head is its label and whose tail is its children, which is
the S-expression convention for applying a function to arguments and
agrees with the reading `Geb.Ast.toRose` fixes. It is a different
encoding of the same trees from `Ast.toCSexp`, and
`GebTests.Internal.CanonicalSExpr` exhibits a tree they spell
differently.

## Main definitions

* `CSexp` — canonical S-expressions, the W-type on `CSexp.Shape`.
* `CSexp.render` — the octet string a term is indexed by.
* `Ast.toCSexp` — the map underlying the implemented syntax.
* `Rose.toCSexp` — the label-applied-to-arguments encoding, with
  `Rose.print` its rendering and `Ast.printViaRose` its composite with
  the rose bijection.

## Main statements

* `Csexp.print_eq_render_toCSexp` — the implemented printer's output is
  the rendering of a canonical S-expression.

## References

* [FormalSExpr]
* [RFC9804]

## Tags

canonical S-expression, conformance, W-type
-/

@[expose] public section

namespace Geb

namespace CSexp

/-- The node shapes of a canonical S-expression: an atom carrying its
octets, or a list of a given length. [FormalSExpr]'s `MkCanonicalHint`
has no shape here; display hints have no counterpart in this
development, and nothing below emits one. -/
inductive Shape where
  /-- An atom, carrying its octets. -/
  | atom : List Char → Shape
  /-- A list of the given length. -/
  | list : Nat → Shape
  deriving DecidableEq

/-- The child index type: an atom has no children, a list of length `n`
has `n`. A `def` rather than an `abbrev`, so that instance search cannot
reduce past it to `Empty` or `Fin n` and select mathlib's
`Classical.choice`-dependent `FinEnum`. -/
def Arity : Shape → Type
  | .atom _ => Empty
  | .list n => Fin n

/-- Every arity is finitely enumerable. -/
instance instFinEnumArity (s : Shape) : FinEnum (Arity s) :=
  match s with
  | .atom _ => finEnumEmpty
  | .list n => finEnumFin n

end CSexp

/-- Canonical S-expressions, the non-dependent form of [FormalSExpr]'s
`CanonicalSExpr`. -/
abbrev CSexp : Type := WType CSexp.Arity

namespace CSexp

/-- An atom carrying the octets `s`. -/
def atom (s : List Char) : CSexp := WType.mk (.atom s) Empty.elim

/-- A list of `n` elements. -/
def list {n : Nat} (f : Fin n → CSexp) : CSexp := WType.mk (.list n) f

/-- The octet string a term is indexed by in [FormalSExpr]: an atom
renders as its verbatim encoding, a list as its elements' renderings
concatenated between parentheses. -/
def render : CSexp → List Char :=
  WType.elim (List Char) fun x =>
    match x with
    | ⟨.atom s, _⟩ => Csexp.printVerbatim s
    | ⟨.list n, ch⟩ => '(' :: (Fin.foldr n (fun j acc => ch j ++ acc) [] ++ [')'])

@[simp] theorem render_atom (s : List Char) :
    render (atom s) = Csexp.printVerbatim s := rfl

@[simp] theorem render_list {n : Nat} (f : Fin n → CSexp) :
    render (list f)
      = '(' :: (Fin.foldr n (fun j acc => render (f j) ++ acc) [] ++ [')']) :=
  rfl

end CSexp

namespace Ast

/-- The canonical S-expression the implemented syntax prints: a leaf is
the two-element list `(leaf label)`, a fork the three-element list
`(fork left right)`. -/
def toCSexp {k : Nat} : Ast k → CSexp :=
  WType.elim CSexp fun x =>
    match x with
    | ⟨.leaf i, _⟩ =>
      CSexp.list ![CSexp.atom Csexp.leafTok, CSexp.atom (Csexp.decOf i.val)]
    | ⟨.fork, ch⟩ =>
      CSexp.list ![CSexp.atom Csexp.forkTok, ch (0 : Fin 2), ch (1 : Fin 2)]

@[simp] theorem toCSexp_leaf {k : Nat} (i : Fin k) :
    (leaf i).toCSexp
      = CSexp.list ![CSexp.atom Csexp.leafTok, CSexp.atom (Csexp.decOf i.val)] :=
  rfl

@[simp] theorem toCSexp_fork {k : Nat} (l r : Ast k) :
    (fork l r).toCSexp
      = CSexp.list ![CSexp.atom Csexp.forkTok, l.toCSexp, r.toCSexp] :=
  rfl

end Ast

namespace Rose

/-- The canonical S-expression of a rose tree: the head is the atom of
the node's label and the tail is its children, so a node is spelled as
its label applied to its arguments. -/
def toCSexp {k : Nat} : Rose k → CSexp :=
  WType.elim CSexp fun x =>
    CSexp.list (Fin.cases (CSexp.atom (Csexp.decOf x.1.1.val)) x.2)

@[simp] theorem toCSexp_node {k : Nat} (i : Fin k) {n : Nat}
    (f : Fin n → Rose k) :
    (node i f).toCSexp
      = CSexp.list (Fin.cases (CSexp.atom (Csexp.decOf i.val))
          fun j => (f j).toCSexp) :=
  rfl

/-- Print a rose tree as a canonical S-expression. A valid syntax needs
a parser to go with this; `TODO.md` § Concrete-syntax prototype records
what that takes. -/
def print {k : Nat} (r : Rose k) : List Char := CSexp.render r.toCSexp

end Rose

namespace Ast

/-- Print an abstract syntax tree through the rose presentation. Not the
same spelling as `Geb.Csexp.print`, which prints from `Ast` directly;
see `GebTests.Internal.CanonicalSExpr`. -/
def printViaRose {k : Nat} (a : Ast k) : List Char := Rose.print a.toRose

end Ast

namespace Csexp

/-- The implemented printer's output is the rendering of a canonical
S-expression, hence a canonical S-expression by construction. -/
theorem printAst_eq_render_toCSexp {k : Nat} (a : Ast k) :
    printAst a = CSexp.render a.toCSexp :=
  Ast.ind (motive := fun a => printAst a = CSexp.render a.toCSexp)
    (fun i => by
      simp only [printAst_leaf, Ast.toCSexp_leaf, CSexp.render_list,
        Fin.foldr_succ, Fin.foldr_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, CSexp.render_atom, List.append_nil,
        List.append_assoc])
    (fun l r ihl ihr => by
      simp only [printAst_fork, Ast.toCSexp_fork, CSexp.render_list,
        Fin.foldr_succ, Fin.foldr_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, CSexp.render_atom, List.append_nil,
        List.append_assoc, ihl, ihr]) a

/-- `printAst_eq_render_toCSexp` at the syntax's printer. This is the
conformance statement `parse_print` does not make: that law says only
that the local parser accepts the local printer's output. -/
theorem print_eq_render_toCSexp {k : Nat} (a : Ast k) :
    print a = CSexp.render a.toCSexp :=
  printAst_eq_render_toCSexp a

end Csexp

end Geb
