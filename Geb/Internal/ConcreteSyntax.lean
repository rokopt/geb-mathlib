/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.W.Basic

/-!
# Concrete syntaxes for the Geb AST (prototype)

The abstract syntax is the initial algebra of `F X = Fin k + X × X`.
A concrete syntax is a pair `parse : C → Option D`, `print : D → C`
satisfying the retraction law `parse (print d) = some d`; formatter
idempotence and injectivity of `print` are corollaries, proved once
here for every syntax.

This module carries the format-independent core (the abstract syntax,
its annotated form, the rose presentation) and one worked concrete
syntax, the canonical S-expression form of [RFC9804].

Every tree type here is a `WType`, so its recursion is carried by
`WType.elim`, `WType.para` and `WType.rec`.

## Main definitions

* `Ast` — the abstract syntax, the W-type on `Ast.Shape`.
* `Ast.toRose`, `Ast.ofRose` — the two directions of the rose
  presentation's bijection with `Ast`.
* `Tree` — the abstract syntax with every node decorated by an `A`,
  with `Tree.map`, `Tree.extract`, `Tree.duplicate` its functor and
  comonad structure and `Tree.erase` the forgetful map to `Ast`.
* `Ann`, `Doc` — the annotation vocabulary and the annotated document
  type `Tree k Ann`.
* `Rose` — the rose-tree presentation of the same fixed point.
* `Retraction`, `format` — the law skeleton a concrete syntax proves.
* `Csexp.print`, `Csexp.parse` — the [RFC9804] canonical S-expression
  syntax.

## Main statements

* `Ast.ind` — the two-constructor induction principle on `Ast`.
* `Ast.ofRose_toRose`, `Ast.toRose_ofRose` — the rose presentation is
  a bijection.
* `Csexp.parse_print` — the retraction law for the S-expression syntax.
* `Geb.format_idem`, `Geb.print_injective` — the corollaries of a
  retraction, proved once for every syntax.
* `Tree.extract_duplicate`, `Tree.map_extract_duplicate`,
  `Tree.duplicate_duplicate` — the comonad laws on the annotated
  syntax, with `Tree.map_id` and `Tree.map_map` the functor laws they
  presuppose and `Tree.extract_map`, `Tree.duplicate_map` the
  naturality of the two structure maps.

## Implementation notes

`Csexp.parseAst` recurses on an explicit `Nat` bound rather than on its
input: the recursion descends only through the remainder each call
returns, which is not a form Lean's structural recursion accepts.
`Csexp.parse` supplies the input length, and `Csexp.size_le_length_printAst`
shows that bound admits every tree the printer emits.

The decimal layer (`Csexp.digitsLE`, `Csexp.ofLE`, `Csexp.decOf`,
`Csexp.digitsVal`) is written here rather than reused. mathlib's
`Nat.digits` depends on `Classical.choice`. Core's `Nat.toDigits` does
not, and uses the same explicit bound, but the retraction proof needs
the inverse direction and its lemmas — `digitsVal_decOf`,
`decOf_all_digits`, `decOf_ne_nil` — and core states none of them, so
reuse would save the encoder and leave the proof obligations untouched.
`finEnumFin` and `finEnumEmpty` are named because mathlib's `FinEnum`
instances for `Fin n` and `Empty` are `Classical.choice`-dependent.

Each `Arity` family is an `abbrev` rather than a `def`: `simp` and `rw`
match at reducible transparency, so a child function whose type reads
`Rose.Arity (i, n) → _` in a goal would not otherwise unify with a lemma
stated at `Fin n → _`.

## References

* [RFC9804]
* [UustaluVene2011]

## Tags

abstract syntax, concrete syntax, W-type, retraction, S-expression
-/

universe uA uB uC

@[expose] public section

namespace Geb

/-! ## Choice-free finite enumerations

Every `Arity` family below is finitely enumerable, which is what lets
`WType.instDecidableEq` decide equality of the corresponding tree type.
The `#guard`s in `GebTests.Internal.ConcreteSyntax` decide equality at
`Ast k` and at `Tree k Ann`. The two enumerations are named rather than
left to instance search: mathlib's `FinEnum.fin` and `FinEnum.empty` are built
by `FinEnum.ofList`, whose proof obligations depend on `Classical.choice`,
which [CONTRIBUTING.md § Constructive-only](../../CONTRIBUTING.md)
forbids. Neither construction is specific to syntax; the second module
needing a choice-free `FinEnum` moves them beside the choice-free
decidability instances in `Geb/Mathlib/Data/FinEnum.lean`. -/

/-- `Fin n` enumerated by the identity equivalence. -/
@[instance_reducible] def finEnumFin (n : Nat) : FinEnum (Fin n) := ⟨n, Equiv.refl (Fin n)⟩

/-- `Empty` enumerated by the empty equivalence. -/
@[instance_reducible] def finEnumEmpty : FinEnum Empty :=
  ⟨0, ⟨Empty.elim, Fin.elim0, fun e => e.elim, fun i => i.elim0⟩⟩

/-! ## Abstract syntax -/

namespace Ast

/-- The node shapes of the Geb abstract syntax: a leaf carrying a label
in `Fin k`, or a fork. -/
inductive Shape (k : Nat) where
  /-- A leaf, labelled by an element of `Fin k`. -/
  | leaf : Fin k → Shape k
  /-- A fork, with two children. -/
  | fork : Shape k
  deriving DecidableEq

/-- The child index type of each shape: a leaf has none, a fork has two.
`Fin 2` rather than `Bool`, so that every non-empty arity here is
enumerated by `finEnumFin`. Reducible, so that `simp`
and `rw` match a child function against the arity it was written at. -/
abbrev Arity {k : Nat} : Shape k → Type
  | .leaf _ => Empty
  | .fork => Fin 2

/-- Every arity is finitely enumerable. -/
instance instFinEnumArity {k : Nat} (s : Shape k) : FinEnum (Arity s) :=
  match s with
  | .leaf _ => finEnumEmpty
  | .fork => finEnumFin 2

end Ast

/-- The Geb abstract syntax: the initial algebra of `F X = Fin k + X × X`,
presented as the W-type on `Ast.Shape k`. -/
abbrev Ast (k : Nat) : Type := WType (Ast.Arity (k := k))

namespace Ast

/-- A leaf labelled `i`. -/
def leaf {k : Nat} (i : Fin k) : Ast k :=
  WType.mk (.leaf i) Empty.elim

/-- A fork with left child `l` and right child `r`. -/
def fork {k : Nat} (l r : Ast k) : Ast k :=
  WType.mk .fork fun b : Fin 2 => Fin.cases l (fun _ => r) b

/-- The number of nodes. -/
def size {k : Nat} : Ast k → Nat :=
  WType.elim Nat fun x =>
    match x with
    | ⟨.leaf _, _⟩ => 1
    | ⟨.fork, ch⟩ => 1 + ch (0 : Fin 2) + ch (1 : Fin 2)

/-- Induction on `Ast` in its two-constructor presentation, so that a
proof driven by it need not mention the underlying shape and arity. -/
theorem ind {k : Nat} {motive : Ast k → Prop}
    (leaf : ∀ i, motive (leaf i))
    (fork : ∀ l r, motive l → motive r → motive (fork l r)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun s f ih =>
    match s, f, ih with
    | .leaf i, f, _ => by
        have : f = Empty.elim := funext (fun e => e.elim)
        subst this; exact leaf i
    | .fork, f, ih => by
        have : (fun b : Fin 2 => Fin.cases (f (0 : Fin 2))
            (fun _ => f (1 : Fin 2)) b) = f :=
          funext fun b => match b with
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
        exact this ▸ fork (f (0 : Fin 2)) (f (1 : Fin 2))
          (ih (0 : Fin 2)) (ih (1 : Fin 2))

@[simp] theorem size_leaf {k : Nat} (i : Fin k) : (leaf i).size = 1 := rfl

@[simp] theorem size_fork {k : Nat} (l r : Ast k) :
    (fork l r).size = 1 + l.size + r.size := rfl

end Ast

/-! ## Annotated syntax -/

namespace Tree

/-- The node shapes of the annotated syntax: an `Ast.Shape` paired with
the decoration carried at that node. -/
abbrev Shape (k : Nat) (A : Type uA) : Type uA := A × Ast.Shape k

/-- The child index type of an annotated shape: that of the underlying
`Ast.Shape`, since decorating a node does not change its children. -/
abbrev Arity {k : Nat} {A : Type uA} (s : Shape k A) : Type := Ast.Arity s.2

/-- Every annotated arity is finitely enumerable. -/
instance instFinEnumArity {k : Nat} {A : Type uA} (s : Shape k A) :
    FinEnum (Arity s) :=
  Ast.instFinEnumArity s.2

end Tree

/-- `Ast k` with every node decorated by an `A`: the initial algebra of
`X ↦ A × F X`. The initial algebra rather than the terminal coalgebra,
because syntax trees are finite; the cofree comonad on `F` admits
infinitely deep trees and is the home of execution traces, not syntax. -/
abbrev Tree (k : Nat) (A : Type uA) : Type uA :=
  WType (Tree.Arity (k := k) (A := A))

namespace Tree

/-- Relabel every node along `f`. -/
def map {k : Nat} {A : Type uA} {B : Type uB} (f : A → B) :
    Tree k A → Tree k B :=
  WType.elim (Tree k B) fun x => WType.mk (f x.1.1, x.1.2) x.2

/-- The comonad counit: the decoration at the root. -/
def extract {k : Nat} {A : Type uA} (t : Tree k A) : A :=
  (WType.toSigma t).1.1

/-- The comonad comultiplication: relabel each node with the annotated
subtree rooted at it. This is the redecoration map of
[UustaluVene2011]. A paramorphism, since the new decoration at a node is
that node's own subtree. -/
def duplicate {k : Nat} {A : Type uA} : Tree k A → Tree k (Tree k A) :=
  WType.para (Tree k (Tree k A)) fun x =>
    WType.mk (WType.mk x.1 fun b => (x.2 b).1, x.1.2) fun b => (x.2 b).2

/-- Forget every decoration, recovering the bare tree. This is the fold
induced by the second projection `A × F X → F X`, not the comonad
counit. -/
def erase {k : Nat} {A : Type uA} : Tree k A → Ast k :=
  WType.elim (Ast k) fun x => WType.mk x.1.2 x.2

@[simp] theorem map_mk {k : Nat} {A : Type uA} {B : Type uB} (f : A → B)
    (s : Shape k A) (ch : Arity s → Tree k A) :
    map f (WType.mk s ch) = WType.mk (f s.1, s.2) fun b => map f (ch b) :=
  rfl

@[simp] theorem extract_mk {k : Nat} {A : Type uA} (s : Shape k A)
    (ch : Arity s → Tree k A) : extract (WType.mk s ch) = s.1 :=
  rfl

@[simp] theorem duplicate_mk {k : Nat} {A : Type uA} (s : Shape k A)
    (ch : Arity s → Tree k A) :
    duplicate (WType.mk s ch)
      = WType.mk (WType.mk s ch, s.2) fun b => duplicate (ch b) :=
  WType.para_mk _ s ch

@[simp] theorem erase_mk {k : Nat} {A : Type uA} (s : Shape k A)
    (ch : Arity s → Tree k A) :
    erase (WType.mk s ch) = WType.mk s.2 fun b => erase (ch b) :=
  rfl

/-- The first functor law: relabelling along the identity is the
identity. -/
theorem map_id {k : Nat} {A : Type uA} (t : Tree k A) : map id t = t :=
  WType.rec (motive := fun t => map id t = t)
    (fun s ch ih => by simp only [map_mk, id_eq]; exact congrArg _ (funext ih)) t

/-- The second functor law: relabelling twice is relabelling along the
composite. -/
theorem map_map {k : Nat} {A : Type uA} {B : Type uB} {C : Type uC}
    (f : A → B) (g : B → C) (t : Tree k A) :
    map g (map f t) = map (g ∘ f) t :=
  WType.rec (motive := fun t => map g (map f t) = map (g ∘ f) t)
    (fun s ch ih => by simp only [map_mk, Function.comp_apply]
                       exact congrArg _ (funext ih)) t

/-- Naturality of the counit: reading the root decoration commutes with
relabelling. -/
theorem extract_map {k : Nat} {A : Type uA} {B : Type uB} (f : A → B)
    (t : Tree k A) : extract (map f t) = f (extract t) := by
  cases t with
  | mk s ch => rfl

/-- Naturality of the comultiplication: redecorating commutes with
relabelling, the relabelling acting on each subtree. -/
theorem duplicate_map {k : Nat} {A : Type uA} {B : Type uB} (f : A → B)
    (t : Tree k A) :
    duplicate (map f t) = map (map f) (duplicate t) :=
  WType.rec (motive := fun t => duplicate (map f t) = map (map f) (duplicate t))
    (fun s ch ih => by simp only [map_mk, duplicate_mk]
                       exact congrArg _ (funext ih)) t

/-- The first comonad law: the subtree redecorating the root is the whole
tree. -/
theorem extract_duplicate {k : Nat} {A : Type uA} (t : Tree k A) :
    extract (duplicate t) = t := by
  cases t with
  | mk s ch => simp

/-- The second comonad law: taking each node's subtree and then keeping
only its root decoration recovers the original decoration. -/
theorem map_extract_duplicate {k : Nat} {A : Type uA} (t : Tree k A) :
    map extract (duplicate t) = t :=
  WType.rec (motive := fun t => map extract (duplicate t) = t)
    (fun s ch ih => by simp only [duplicate_mk, map_mk, extract_mk]
                       exact congrArg _ (funext ih)) t

/-- The third comonad law, coassociativity of the redecoration map. -/
theorem duplicate_duplicate {k : Nat} {A : Type uA} (t : Tree k A) :
    duplicate (duplicate t) = map duplicate (duplicate t) :=
  WType.rec (motive := fun t => duplicate (duplicate t) = map duplicate (duplicate t))
    (fun s ch ih => by simp only [duplicate_mk, map_mk]
                       rw [duplicate_mk]
                       exact congrArg _ (funext ih)) t

end Tree

/-- The annotation vocabulary carried at a node. Durable metadata is an
annotation value, never a lexical comment: generic parsers discard
comments, and canonical forms differ over whether they are retained. -/
@[ext] structure Ann where
  /-- A name for the annotated occurrence. -/
  name : Option String := none
  /-- Prose documentation of the annotated occurrence. -/
  doc : Option String := none
  /-- References to material bearing on the annotated occurrence. -/
  links : List String := []
  deriving Repr, DecidableEq, Inhabited

/-- An annotated Geb document. -/
abbrev Doc (k : Nat) : Type := Tree k Ann

namespace Ast

/-- Decorate every node with the empty annotation. -/
def trivialDoc {k : Nat} : Ast k → Doc k :=
  WType.elim (Doc k) fun x => WType.mk (({} : Ann), x.1) x.2

/-- Decorating every node with the empty annotation and then erasing is
the identity. -/
theorem erase_trivialDoc {k : Nat} (a : Ast k) :
    Tree.erase a.trivialDoc = a :=
  WType.rec (motive := fun a => Tree.erase (trivialDoc a) = a)
    (fun s ch ih => by simp only [trivialDoc, WType.elim_mk]
                       exact congrArg _ (funext ih)) a

end Ast

/-! ## The rose presentation and its bijection -/

namespace Rose

/-- The node shapes of the rose presentation: a label in `Fin k` and a
number of children. -/
abbrev Shape (k : Nat) : Type := Fin k × Nat

/-- The child index type of a rose shape. -/
abbrev Arity {k : Nat} (s : Shape k) : Type := Fin s.2

end Rose

/-- The rose-tree presentation: a label in `Fin k` and a finite sequence
of children, satisfying the same fixed-point equation as `Ast k`. -/
abbrev Rose (k : Nat) : Type := WType (Rose.Arity (k := k))

namespace Rose

/-- Prepend `t` to the children of `r`, keeping `r`'s label. -/
def cons {k : Nat} (t r : Rose k) : Rose k :=
  match r with
  | ⟨(i, n), f⟩ => WType.mk (i, n + 1) (Fin.cases t f)

/-- The node with label `i` and children `f`. -/
def node {k : Nat} (i : Fin k) {n : Nat} (f : Fin n → Rose k) : Rose k :=
  WType.mk (i, n) f

@[simp] theorem cons_node {k : Nat} (t : Rose k) (i : Fin k) {n : Nat}
    (f : Fin n → Rose k) :
    cons t (node i f) = node i (Fin.cases t f) := rfl

end Rose

namespace Ast

/-- The binary-to-rose direction, under the convention that the left child
of a fork is the head child and the right child carries the label and the
remaining siblings. Choosing the last child instead gives a different and
equally valid bijection, so the choice has to be fixed. -/
def toRose {k : Nat} : Ast k → Rose k :=
  WType.elim (Rose k) fun x =>
    match x with
    | ⟨.leaf i, _⟩ => Rose.node i Fin.elim0
    | ⟨.fork, ch⟩ => Rose.cons (ch (0 : Fin 2)) (ch (1 : Fin 2))

/-- The rose-to-binary direction, folding a node's children into the right
spine that carries the label at its end. -/
def ofRose {k : Nat} : Rose k → Ast k :=
  WType.elim (Ast k) fun x =>
    Fin.foldr x.1.2 (fun j acc => fork (x.2 j) acc) (leaf x.1.1)

@[simp] theorem toRose_leaf {k : Nat} (i : Fin k) :
    (leaf i).toRose = Rose.node i Fin.elim0 := rfl

@[simp] theorem toRose_fork {k : Nat} (l r : Ast k) :
    (fork l r).toRose = Rose.cons l.toRose r.toRose := rfl

@[simp] theorem ofRose_node {k : Nat} (i : Fin k) {n : Nat} (f : Fin n → Rose k) :
    ofRose (Rose.node i f) =
      Fin.foldr n (fun j acc => fork (ofRose (f j)) acc) (leaf i) :=
  rfl

theorem ofRose_cons {k : Nat} (t r : Rose k) :
    ofRose (Rose.cons t r) = fork (ofRose t) (ofRose r) := by
  obtain ⟨⟨i, n⟩, f⟩ := r
  change ofRose (Rose.cons t (Rose.node i f))
      = fork (ofRose t) (ofRose (Rose.node i f))
  simp only [Rose.cons_node, ofRose_node, Fin.foldr_succ, Fin.cases_zero,
    Fin.cases_succ]

/-- One half of the rose/binary bijection: converting to a rose tree and
back is the identity on `Ast k`. -/
theorem ofRose_toRose {k : Nat} (a : Ast k) : ofRose a.toRose = a :=
  ind (motive := fun a => ofRose a.toRose = a)
    (fun i => by simp only [toRose_leaf, ofRose_node, Fin.foldr_zero])
    (fun l r ihl ihr => by rw [toRose_fork, ofRose_cons, ihl, ihr]) a

/-- The image of a right spine under `toRose`: the fold that `ofRose`
performs on a node's children is undone one child at a time. -/
theorem toRose_foldr {k : Nat} (i : Fin k) :
    ∀ (n : Nat) (g : Fin n → Ast k),
      (Fin.foldr n (fun j acc => fork (g j) acc) (leaf i)).toRose
        = Rose.node i fun j => (g j).toRose :=
  Nat.rec
    (motive := fun n => ∀ g : Fin n → Ast k,
      (Fin.foldr n (fun j acc => fork (g j) acc) (leaf i)).toRose
        = Rose.node i fun j => (g j).toRose)
    (fun g => by
      simp only [Fin.foldr_zero, toRose_leaf]
      exact congrArg _ (funext fun j => j.elim0))
    (fun n ih g => by
      simp only [Fin.foldr_succ, toRose_fork, ih (fun j => g j.succ), Rose.cons_node]
      exact congrArg _ (funext fun j =>
        Fin.cases (motive := fun j => Fin.cases (g 0).toRose
          (fun j => (g j.succ).toRose) j = (g j).toRose) rfl (fun _ => rfl) j))

/-- The other half of the rose/binary bijection: converting from a rose
tree and back is the identity on `Rose k`. -/
theorem toRose_ofRose {k : Nat} (r : Rose k) : (ofRose r).toRose = r :=
  WType.rec (motive := fun r => (ofRose r).toRose = r)
    (fun s f ih => by
      obtain ⟨i, n⟩ := s
      change (ofRose (Rose.node i f)).toRose = Rose.node i f
      rw [ofRose_node, toRose_foldr]
      exact congrArg _ (funext ih)) r

end Ast

/-! ## Law skeletons for a concrete syntax -/

section Laws

variable {D : Type uA} {C : Type uB} (parse : C → Option D) (print : D → C)

/-- The document-level retraction law: the only law a syntax must prove. -/
def Retraction : Prop := ∀ d : D, parse (print d) = some d

/-- The formatter, defined where parsing succeeds. -/
def format (c : C) : Option C := (parse c).map print

/-- Formatter idempotence, the first corollary of a retraction:
reformatting formatted input changes nothing. -/
theorem format_idem (hr : Retraction parse print) (c : C) :
    (format parse print c).bind (format parse print)
      = format parse print c := by
  unfold format
  cases h : parse c with
  | none => simp
  | some d => simp [hr d]

/-- Injectivity of the printer, the second corollary of a retraction: a
syntax that can be parsed back cannot spell two documents alike. -/
theorem print_injective (hr : Retraction parse print) :
    Function.Injective print := by
  intro d1 d2 h
  have h1 := hr d1
  rw [h, hr d2] at h1
  exact (Option.some.inj h1).symm

end Laws

/-! ## A concrete syntax: RFC 9804 canonical S-expressions -/

namespace Csexp

/-! ### Decimal digits -/

/-- The ASCII character for a decimal digit; meaningful for `d < 10`. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal value of an ASCII digit character. -/
def charDigit (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48) else none

theorem charDigit_digitChar (d : Nat) (h : d < 10) :
    charDigit (digitChar d) = some d := by
  revert h; revert d; decide

theorem mapM_charDigit_digitChar : ∀ ds : List Nat, (∀ d ∈ ds, d < 10) →
    (ds.map digitChar).mapM charDigit = some ds :=
  List.rec (motive := fun ds => (∀ d ∈ ds, d < 10) →
      (ds.map digitChar).mapM charDigit = some ds)
    (fun _ => rfl)
    (fun d ds ih h => by
      have hd : d < 10 := h d (by simp)
      have ht : ∀ x ∈ ds, x < 10 := fun x hx => h x (by simp [hx])
      simp [List.mapM_cons, charDigit_digitChar d hd, ih ht])

/-- The value of a little-endian decimal digit list. -/
def ofLE : List Nat → Nat := List.rec 0 fun d _ ih => d + 10 * ih

@[simp] theorem ofLE_nil : ofLE [] = 0 := rfl

@[simp] theorem ofLE_cons (d : Nat) (ds : List Nat) :
    ofLE (d :: ds) = d + 10 * ofLE ds := rfl

/-- Little-endian decimal digits of `n`, on an explicit recursion bound.
Each step divides by ten, so `n` itself is always a sufficient bound. -/
def digitsLEAux : Nat → Nat → List Nat :=
  Nat.rec (fun _ => []) fun _ ih n => if n = 0 then [] else n % 10 :: ih (n / 10)

@[simp] theorem digitsLEAux_zero (n : Nat) : digitsLEAux 0 n = [] := rfl

theorem digitsLEAux_succ (f n : Nat) :
    digitsLEAux (f + 1) n =
      if n = 0 then [] else n % 10 :: digitsLEAux f (n / 10) := rfl

/-- Little-endian decimal digits. Hand-rolled rather than taken from
mathlib, whose `Nat.digits` depends on `Classical.choice`. -/
def digitsLE (n : Nat) : List Nat := digitsLEAux n n

theorem ofLE_digitsLEAux : ∀ f n : Nat, n ≤ f → ofLE (digitsLEAux f n) = n :=
  Nat.rec (motive := fun f => ∀ n : Nat, n ≤ f → ofLE (digitsLEAux f n) = n)
    (fun n hn => by
      simp only [digitsLEAux_zero, ofLE_nil]
      exact (Nat.le_zero.mp hn).symm)
    (fun f ih n hn => by
      rw [digitsLEAux_succ]
      split
      next h => simp [h]
      next h => rw [ofLE_cons, ih (n / 10) (by omega)]; omega)

theorem ofLE_digitsLE (n : Nat) : ofLE (digitsLE n) = n :=
  ofLE_digitsLEAux n n (Nat.le_refl n)

theorem digitsLEAux_lt : ∀ f n : Nat, ∀ d ∈ digitsLEAux f n, d < 10 :=
  Nat.rec (motive := fun f => ∀ n : Nat, ∀ d ∈ digitsLEAux f n, d < 10)
    (fun n d hd => by simp at hd)
    (fun f ih n d hd => by
      rw [digitsLEAux_succ] at hd
      split at hd
      next => simp at hd
      next =>
        rcases List.mem_cons.mp hd with rfl | hd'
        · omega
        · exact ih (n / 10) d hd')

theorem digitsLE_lt (n : Nat) : ∀ d ∈ digitsLE n, d < 10 := digitsLEAux_lt n n

theorem digitsLE_ne_nil {n : Nat} (h : n ≠ 0) : digitsLE n ≠ [] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [digitsLE, digitsLEAux_succ]

/-- Shortest-form decimal, big-endian, `"0"` for zero. -/
def decOf (n : Nat) : List Char :=
  if n = 0 then ['0'] else (digitsLE n).reverse.map digitChar

/-- The value of a big-endian decimal digit string, or `none` if any
character is not a digit. Leading zeros are accepted, and so is the empty
string, whose value is `0`: the parser may admit more than the printer
emits, since the retraction law constrains only the composite. -/
def digitsVal (cs : List Char) : Option Nat :=
  (cs.mapM charDigit).map fun l => ofLE l.reverse

theorem digitsVal_decOf (n : Nat) : digitsVal (decOf n) = some n := by
  unfold decOf digitsVal
  by_cases h : n = 0
  · subst h; decide
  · have hlt : ∀ d ∈ (digitsLE n).reverse, d < 10 := by
      intro d hd
      exact digitsLE_lt n d (List.mem_reverse.mp hd)
    rw [if_neg h, mapM_charDigit_digitChar _ hlt]
    simp [ofLE_digitsLE]

theorem decOf_all_digits (n : Nat) : ∀ c ∈ decOf n, (charDigit c).isSome := by
  intro c hc
  unfold decOf at hc
  by_cases h : n = 0
  · subst h; rw [if_pos rfl, List.mem_singleton] at hc; subst hc; decide
  · rw [if_neg h] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have : d < 10 := digitsLE_lt n d (List.mem_reverse.mp hd)
    simp [charDigit_digitChar d this]

theorem decOf_ne_nil (n : Nat) : decOf n ≠ [] := by
  unfold decOf
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h]
    simp [digitsLE_ne_nil h]

/-! ### Reading a decimal prefix -/

/-- Split off the longest decimal prefix. -/
def readDigits : List Char → List Char × List Char :=
  List.rec ([], []) fun c cs ih =>
    match charDigit c with
    | some _ => (c :: ih.1, ih.2)
    | none => ([], c :: cs)

@[simp] theorem readDigits_nil : readDigits [] = ([], []) := rfl

theorem readDigits_cons (c : Char) (cs : List Char) :
    readDigits (c :: cs) =
      match charDigit c with
      | some _ => (c :: (readDigits cs).1, (readDigits cs).2)
      | none => ([], c :: cs) := rfl

theorem readDigits_append : ∀ ds rest : List Char,
    (∀ c ∈ ds, (charDigit c).isSome) →
    (∀ c cs, rest = c :: cs → charDigit c = none) →
    readDigits (ds ++ rest) = (ds, rest) :=
  List.rec (motive := fun ds => ∀ rest : List Char,
      (∀ c ∈ ds, (charDigit c).isSome) →
      (∀ c cs, rest = c :: cs → charDigit c = none) →
      readDigits (ds ++ rest) = (ds, rest))
    (fun rest _ hr => by
      cases rest with
      | nil => rfl
      | cons c cs => simp [readDigits_cons, hr c cs rfl])
    (fun d ds ih rest hd hr => by
      have h1 : (charDigit d).isSome := hd d (by simp)
      have h2 : ∀ c ∈ ds, (charDigit c).isSome := fun c hc => hd c (by simp [hc])
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h1
      simp [readDigits_cons, hv, ih rest h2 hr])

/-- Read a non-empty decimal prefix and its value. -/
def readNat (cs : List Char) : Option (Nat × List Char) :=
  let (ds, r) := readDigits cs
  if ds.isEmpty then none else (digitsVal ds).map (·, r)

/-! ### Canonical verbatim atoms -/

/-- The [RFC9804] verbatim encoding of an atom, `length ":" content`. -/
def printVerbatim (s : List Char) : List Char :=
  decOf s.length ++ ':' :: s

/-- Read one verbatim atom, returning it and the remaining input. The
`n ≤ r.length` guard rejects an atom declaring more content than
follows it, rather than truncating. `parse` cannot observe the guard —
a truncating read would consume the whole remaining input, and every
position that can follow one demands more — so what the guard buys is
that `readVerbatim` reads the [RFC9804] `verbatim` production correctly
on its own. `GebTests.Internal.ConcreteSyntax` asserts that directly. -/
def readVerbatim (cs : List Char) : Option (List Char × List Char) :=
  match readNat cs with
  | some (n, ':' :: r) => if n ≤ r.length then some (r.take n, r.drop n) else none
  | _ => none

theorem readVerbatim_append (s rest : List Char) :
    readVerbatim (printVerbatim s ++ rest) = some (s, rest) := by
  have hcolon : ∀ c cs, (':' :: (s ++ rest)) = c :: cs → charDigit c = none := by
    intro c cs hc; injection hc with h1 _; subst h1; decide
  have h : readNat (printVerbatim s ++ rest)
      = some (s.length, ':' :: (s ++ rest)) := by
    unfold readNat printVerbatim
    rw [List.append_assoc, List.cons_append,
      readDigits_append _ _ (decOf_all_digits s.length) hcolon]
    simp [decOf_ne_nil s.length, digitsVal_decOf, List.isEmpty_iff]
  simp [readVerbatim, h]

/-! ### Printer -/

/-- The head atom of a leaf s-expression. -/
def leafTok : List Char := ['l', 'e', 'a', 'f']

/-- The head atom of a fork s-expression. -/
def forkTok : List Char := ['f', 'o', 'r', 'k']

/-- Print a tree in [RFC9804] canonical form. A leaf label is its
shortest-form decimal, written as a verbatim atom: canonical form admits
no other atom encoding. -/
def printAst {k : Nat} : Ast k → List Char :=
  WType.elim (List Char) fun x =>
    match x with
    | ⟨.leaf i, _⟩ =>
      '(' :: (printVerbatim leafTok ++ printVerbatim (decOf i.val) ++ [')'])
    | ⟨.fork, ch⟩ =>
      '(' :: (printVerbatim forkTok ++ ch (0 : Fin 2) ++ ch (1 : Fin 2) ++ [')'])

@[simp] theorem printAst_leaf {k : Nat} (i : Fin k) :
    printAst (Ast.leaf i)
      = '(' :: (printVerbatim leafTok ++ printVerbatim (decOf i.val) ++ [')']) :=
  rfl

@[simp] theorem printAst_fork {k : Nat} (l r : Ast k) :
    printAst (Ast.fork l r)
      = '(' :: (printVerbatim forkTok ++ printAst l ++ printAst r ++ [')']) :=
  rfl

/-! ### Parser -/

/-- One layer of the recursive descent: read a single s-expression,
delegating each child to `childParse`. -/
def parseStep (k : Nat) (childParse : List Char → Option (Ast k × List Char)) :
    List Char → Option (Ast k × List Char)
  | [] => none
  | c :: cs =>
    if c = '(' then
      match readVerbatim cs with
      | some (tok, cs1) =>
        if tok = leafTok then
          match readVerbatim cs1 with
          | some (ds, ')' :: cs2) =>
            match digitsVal ds with
            | some n => if h : n < k then some (Ast.leaf ⟨n, h⟩, cs2) else none
            | none => none
          | _ => none
        else if tok = forkTok then
          match childParse cs1 with
          | some (l, cs2) =>
            match childParse cs2 with
            | some (r, ')' :: cs3) => some (Ast.fork l r, cs3)
            | _ => none
          | none => none
        else none
      | none => none
    else none

/-- Recursive descent over the canonical form, returning the tree and the
unconsumed input. The `Nat` argument bounds the recursion: the recursion
is on the input's structure only through the remainder each call returns,
which is not a form Lean's structural recursion accepts. `parse` supplies
the input length; `size_le_length_printAst` shows that this bound admits every
tree the printer emits. Whether it admits every input the grammar accepts
is not stated, and is not needed for the retraction law. -/
def parseAst (k : Nat) : Nat → List Char → Option (Ast k × List Char) :=
  Nat.rec (fun _ => none) fun _ ih => parseStep k ih

@[simp] theorem parseAst_zero (k : Nat) (cs : List Char) :
    parseAst k 0 cs = none := rfl

@[simp] theorem parseAst_succ (k f : Nat) :
    parseAst k (f + 1) = parseStep k (parseAst k f) := rfl

/-- The parser inverts the printer on printed input, given fuel at least
the tree's node count, and returns the unconsumed remainder. -/
theorem parseAst_printAst {k : Nat} (a : Ast k) :
    ∀ (f : Nat) (rest : List Char), a.size ≤ f →
      parseAst k f (printAst a ++ rest) = some (a, rest) :=
  Ast.ind (motive := fun a => ∀ (f : Nat) (rest : List Char), a.size ≤ f →
      parseAst k f (printAst a ++ rest) = some (a, rest))
    (fun i f rest hf => by
      cases f with
      | zero => simp at hf
      | succ f =>
        simp only [printAst_leaf, List.cons_append, parseAst_succ, parseStep,
          List.append_assoc, List.nil_append]
        rw [readVerbatim_append]
        -- reduce the match on the `some` just produced, exposing the next atom
        simp only []
        rw [readVerbatim_append]
        simp [digitsVal_decOf, i.isLt])
    (fun l r ihl ihr f rest hf => by
      cases f with
      | zero => simp at hf
      | succ f =>
        have hl : l.size ≤ f := by simp at hf; omega
        have hr : r.size ≤ f := by simp at hf; omega
        simp only [printAst_fork, List.cons_append, parseAst_succ, parseStep,
          List.append_assoc, List.nil_append]
        rw [readVerbatim_append]
        have hne : forkTok ≠ leafTok := by decide
        simp only [if_neg hne]
        rw [ihl f _ hl]
        -- reduce the match on the `some` just produced, exposing the second child
        simp only []
        rw [ihr f _ hr]
        simp) a

/-- A tree's node count bounds the length of its printed form, so the
input length is fuel enough for `parseAst` to read anything `printAst`
emits. -/
theorem size_le_length_printAst {k : Nat} (a : Ast k) : a.size ≤ (printAst a).length :=
  Ast.ind (motive := fun a => a.size ≤ (printAst a).length)
    (fun i => by simp [printAst_leaf])
    (fun l r ihl ihr => by
      simp only [Ast.size_fork, printAst_fork, List.length_cons,
        List.length_append]
      omega) a

/-! ### The two syntax maps and the retraction law -/

/-- The printer of the canonical S-expression syntax. A concrete syntax
needs a deterministic printer, not a normative canonical form; that this
one also emits the format's canonical spelling is incidental rather than
required. -/
def print {k : Nat} (a : Ast k) : List Char := printAst a

/-- The parser of the canonical S-expression syntax, rejecting trailing
input. -/
def parse (k : Nat) (cs : List Char) : Option (Ast k) :=
  match parseAst k cs.length cs with
  | some (a, []) => some a
  | _ => none

/-- The retraction law for the canonical S-expression syntax: printing a
tree and parsing the result returns that tree. -/
theorem parse_print {k : Nat} (a : Ast k) : parse k (print a) = some a := by
  unfold parse print
  rw [show printAst a = printAst a ++ [] by simp,
    parseAst_printAst a _ [] (by simpa using size_le_length_printAst a)]

/-! ### The generic corollaries, instantiated here -/

/-- `parse_print` in the form the generic corollaries consume. -/
theorem retraction (k : Nat) : Retraction (parse k) (print (k := k)) :=
  parse_print

/-- `Geb.format_idem` at this syntax. -/
theorem format_idem (k : Nat) (c : List Char) :
    (format (parse k) print c).bind (format (parse k) print)
      = format (parse k) print c :=
  Geb.format_idem _ _ (retraction k) c

/-- `Geb.print_injective` at this syntax. -/
theorem print_injective (k : Nat) : Function.Injective (print (k := k)) :=
  Geb.print_injective _ _ (retraction k)

end Csexp

end Geb
