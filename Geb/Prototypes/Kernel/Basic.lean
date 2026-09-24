/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.W.Basic
public import Geb.Prototypes.RoseTree.Basic
public import Mathlib.Data.Fin.VecNotation
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The bootstrap kernel

The kernel language of the bootstrap is System T {cite}`Goedel1958` over rose trees with
natural-number labels: simple types built from the one base type of trees by the unit type,
products, function types and lists; λ-terms with de Bruijn indices; quoted trees, a
conditional on labels, lists with their right fold, the fold of trees and the iteration of a
label's value at every type; and primitive operations on labels and children. A tree is a
label with a list of trees, and the fold of trees is that recursion: a node's result is
computed from the leaf of its label and the list of its children's results. Its terms and its
types are themselves rose trees, the label of a node naming its constructor, so a program is
a value of the language.

A term's meaning is its denotation in Lean: the base type denotes {name}`Geb.RoseTree` at
{lit}`ℕ`, a function type the Lean function type, and the fold the fold
{name}`Geb.RoseTree.elim`. The type checker and the evaluator are one fold over the term,
{lit}`infer`, which returns the term's type together with its denotation, or nothing when the
term is ill-typed. The evaluator therefore agrees with the denotation by construction; a
machine that runs the kernel is proved correct against {lit}`infer`.

The labels of the constructors:

* types: {lit}`0` the base type, {lit}`1` the unit type, {lit}`2` products over two
  children, {lit}`3` function types over a domain and a codomain, {lit}`4` lists over their
  elements' type;
* terms: {lit}`8` a variable over a leaf whose label is its de Bruijn index, {lit}`9` an
  abstraction over its domain type and its body, {lit}`10` an application, {lit}`11` the
  unit value, {lit}`12` a pair, {lit}`13` and {lit}`14` its projections, {lit}`15` a quoted
  tree, {lit}`16` a conditional on whether a tree's label is non-zero, {lit}`17` the fold of
  trees over its result type, {lit}`18` iteration over its result type, {lit}`19` the empty
  list over its elements' type, {lit}`20` the list of a head and a tail, {lit}`21` the right
  fold of lists over the elements' type and the result type, {lit}`22` a primitive over a
  leaf whose label is its index in {lit}`prims`, and {lit}`23` a reference over a leaf whose
  label is its index in the global environment.

## Main definitions

* {lit}`tT`, {lit}`tUnit`, {lit}`tProd`, {lit}`tArrow`, {lit}`tList` — the types.
* {lit}`Ty.den` — the denotation of a type.
* {lit}`Ty.IsTy` — the recognizer of types.
* {lit}`Ctx.den`, {lit}`Ctx.var` — contexts, their denotations and variable lookup.
* {lit}`prims` — the primitives, with their types and denotations.
* {lit}`infer` — the type checker and evaluator.
* {lit}`Glob.apply`, {lit}`run` — the application of a global or a closed program from
  trees to trees.

## Implementation notes

The fold over a term needs the children as trees, to read type annotations, quoted trees
and indices, as well as their results, so {lit}`infer` is the paramorphism
{name}`Geb.RoseTree.para`, which computes each child's result once. A result is a
function of the global environment and the context, so a node's meaning is computed once
per application of its parent's meaning. The conditional evaluates one branch.

## References

* {cite}`Goedel1958`
* {cite}`GirardLafontTaylor1989`, Section 7.4.2, for the functions System T defines.

## Tags

bootstrap, kernel, System T, rose tree, denotational semantics, type checking
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

open scoped FinEnum

/-- The kernel's values: rose trees with natural-number labels. -/
abbrev Tree : Type := RoseTree ℕ

/-- The leaf with a label. -/
def leaf (n : ℕ) : Tree := RoseTree.node n []

/-- A node of two children, over a vector so that its denotation unfolds definitionally. -/
def node2 (l : ℕ) (a b : Tree) : Tree := WType.mk (l, 2) ![a, b]

/-- The base type of trees. -/
def tT : Tree := leaf 0

/-- The unit type. -/
def tUnit : Tree := leaf 1

/-- The product type. -/
def tProd (A B : Tree) : Tree := node2 2 A B

/-- The function type. -/
def tArrow (A B : Tree) : Tree := node2 3 A B

/-- The list type. -/
def tList (A : Tree) : Tree := WType.mk (4, 1) ![A]

namespace Ty

/-- The denotation of a type. Trees of other shapes denote the unit type; the checker
rejects them as annotations. -/
def den : Tree → Type :=
  WType.elim Type fun ⟨(l, k), g⟩ ↦
    match l, k, g with
    | 0, 0, _ => Tree
    | 2, 2, g => g 0 × g 1
    | 3, 2, g => g 0 → g 1
    | 4, 1, g => List (g 0)
    | _, _, _ => Unit

/-- The recognizer of types. -/
def IsTy : Tree → Bool :=
  RoseTree.elim fun l rs ↦
    match l, rs with
    | 0, [] | 1, [] => true
    | 2, [a, b] | 3, [a, b] => a && b
    | 4, [a] => a
    | _, _ => false

/-- A type read as a function type, with the equation of denotations. -/
def arrow? : (F : Tree) → Option (Σ' A B : Tree, den F = (den A → den B))
  | WType.mk (3, 2) g => some ⟨g 0, g 1, rfl⟩
  | _ => none

/-- A type read as a product type, with the equation of denotations. -/
def prod? : (P : Tree) → Option (Σ' A B : Tree, den P = (den A × den B))
  | WType.mk (2, 2) g => some ⟨g 0, g 1, rfl⟩
  | _ => none

/-- A type read as a list type, with the equation of denotations. -/
def list? : (L : Tree) → Option (Σ' A : Tree, den L = List (den A))
  | WType.mk (4, 1) g => some ⟨g 0, rfl⟩
  | _ => none

end Ty

/-- A context: the types of the variables, the innermost first. -/
abbrev Ctx : Type := List Tree

namespace Ctx

/-- The denotation of a context: the product of its types' denotations. -/
def den (Γ : Ctx) : Type := Γ.foldr (fun A E ↦ Ty.den A × E) Unit

/-- The type and denotation of the variable of a de Bruijn index. -/
def var : (Γ : Ctx) → ℕ → Option (Σ A : Tree, Γ.den → Ty.den A) :=
  List.rec (fun _ ↦ none) fun A _ ih n ↦
    Nat.casesOn n (some ⟨A, Prod.fst⟩) fun m ↦ (ih m).map fun p ↦ ⟨p.1, p.2 ∘ Prod.snd⟩

end Ctx

/-- A global: a type with a value of it. -/
abbrev Glob : Type := Σ A : Tree, Ty.den A

/-- The meaning of a term in a context: its type and its denotation. -/
abbrev Meaning (Γ : Ctx) : Type := Σ A : Tree, Γ.den → Ty.den A

/-- The truth values of the conditional and the comparisons: label zero is false. -/
def ofBool (b : Bool) : Tree := leaf (if b then 1 else 0)

/-- The primitives, by index: the label of a tree, the number of its children, a child by
index (the leaf of label zero when out of range), a node from the label of a tree and a list
of children, the list of a tree's children, arithmetic on labels (subtraction truncated,
division and remainder by zero as in {lit}`Nat`), comparison of labels, equality of trees,
and the base-two logarithm of a label, rounded down and zero at zero. The table is only
extended, so that an index names one primitive in every version. -/
def prims : List Glob :=
  let binL (f : ℕ → ℕ → ℕ) : Glob :=
    ⟨tArrow tT (tArrow tT tT), fun a b : Tree ↦ leaf (f a.label b.label)⟩
  [⟨tArrow tT tT, fun t : Tree ↦ leaf t.label⟩,
   ⟨tArrow tT tT, fun | WType.mk (_, k) _ => leaf k⟩,
   ⟨tArrow tT (tArrow tT tT), fun
      | WType.mk (_, k) g, i => if h : i.label < k then g ⟨i.label, h⟩ else leaf 0⟩,
   ⟨tArrow tT (tArrow (tList tT) tT), fun (l : Tree) (cs : List Tree) ↦ RoseTree.node l.label cs⟩,
   ⟨tArrow tT (tList tT), fun t : Tree ↦ t.children⟩,
   binL (· + ·), binL (· - ·), binL (· * ·), binL (· / ·), binL (· % ·),
   ⟨tArrow tT (tArrow tT tT), fun a b : Tree ↦ ofBool (a.label == b.label)⟩,
   ⟨tArrow tT (tArrow tT tT), fun a b : Tree ↦ ofBool (decide (a.label < b.label))⟩,
   ⟨tArrow tT (tArrow tT tT), fun a b : Tree ↦ ofBool (decide (a = b))⟩,
   ⟨tArrow tT tT, fun t : Tree ↦ leaf t.label.log2⟩]

/-- The type of the fold of trees at result type {lit}`A`. -/
def foldTy (A : Tree) : Tree := tArrow (tArrow tT (tArrow (tList A) A)) (tArrow tT A)

/-- The fold of trees: a node's result is the step applied to the leaf of its label and to
the list of its children's results. -/
def foldDen (A : Tree) : Ty.den (foldTy A) := fun (f : Tree → List (Ty.den A) → Ty.den A) ↦
  RoseTree.elim fun l rs ↦ f (leaf l) rs

/-- The type of the right fold of lists with elements of type {lit}`A` at result type
{lit}`B`. -/
def foldrTy (A B : Tree) : Tree :=
  tArrow (tArrow A (tArrow B B)) (tArrow B (tArrow (tList A) B))

/-- The right fold of lists. -/
def foldrDen (A B : Tree) : Ty.den (foldrTy A B) :=
  fun (g : Ty.den A → Ty.den B → Ty.den B) (z : Ty.den B) (xs : List (Ty.den A)) ↦ xs.foldr g z

/-- The type of iteration at result type {lit}`A`. -/
def iterTy (A : Tree) : Tree := tArrow (tArrow A A) (tArrow A (tArrow tT A))

/-- Iteration: the step applied as many times as the label of the tree. -/
def iterDen (A : Tree) : Ty.den (iterTy A) := fun s z n ↦ Nat.repeat s n.label z

/-- The meaning of a term, as a function of the global environment and the context. -/
abbrev Sem : Type := List Glob → (Γ : Ctx) → Option (Meaning Γ)

/-- The meaning of a global or a primitive, constant in the context. -/
def constant {Γ : Ctx} (g : Glob) : Meaning Γ := ⟨g.1, fun _ ↦ g.2⟩

/-- One node of the checker-evaluator: the node's label, and each child as a tree with its
meaning. -/
def inferStep (l : ℕ) (cs : List (Tree × Sem)) : Sem := fun G Γ ↦
  match l, cs with
  | 8, [(n, _)] => Γ.var n.label
  | 9, [(A, _), (_, b)] =>
    if Ty.IsTy A then (b G (A :: Γ)).map fun m ↦ ⟨tArrow A m.1, fun e a ↦ m.2 (a, e)⟩
    else none
  | 10, [(_, f), (_, x)] => do
    let mf ← f G Γ
    let mx ← x G Γ
    let ⟨A, B, h⟩ ← Ty.arrow? mf.1
    if hx : mx.1 = A then
      some ⟨B, fun e ↦ cast h (mf.2 e) (cast (congrArg Ty.den hx) (mx.2 e))⟩
    else none
  | 11, [] => some ⟨tUnit, fun _ ↦ ()⟩
  | 12, [(_, a), (_, b)] => do
    let ma ← a G Γ
    let mb ← b G Γ
    some ⟨tProd ma.1 mb.1, fun e ↦ (ma.2 e, mb.2 e)⟩
  | 13, [(_, p)] => do
    let mp ← p G Γ
    let ⟨A, _, h⟩ ← Ty.prod? mp.1
    some ⟨A, fun e ↦ (cast h (mp.2 e)).1⟩
  | 14, [(_, p)] => do
    let mp ← p G Γ
    let ⟨_, B, h⟩ ← Ty.prod? mp.1
    some ⟨B, fun e ↦ (cast h (mp.2 e)).2⟩
  | 15, [(t, _)] => some ⟨tT, fun _ ↦ t⟩
  | 16, [(_, c), (_, a), (_, b)] => do
    let mc ← c G Γ
    let ma ← a G Γ
    let mb ← b G Γ
    if hc : mc.1 = tT then
      if hb : mb.1 = ma.1 then
        some ⟨ma.1, fun e ↦
          if (cast (congrArg Ty.den hc) (mc.2 e)).label ≠ 0 then ma.2 e
          else cast (congrArg Ty.den hb) (mb.2 e)⟩
      else none
    else none
  | 17, [(A, _)] => if Ty.IsTy A then some (constant ⟨foldTy A, foldDen A⟩) else none
  | 18, [(A, _)] => if Ty.IsTy A then some (constant ⟨iterTy A, iterDen A⟩) else none
  | 19, [(A, _)] => if Ty.IsTy A then some ⟨tList A, fun _ ↦ ([] : List (Ty.den A))⟩ else none
  | 20, [(_, x), (_, xs)] => do
    let mx ← x G Γ
    let mxs ← xs G Γ
    let ⟨A, h⟩ ← Ty.list? mxs.1
    if hx : mx.1 = A then
      some ⟨tList A, fun e ↦ cast (congrArg Ty.den hx) (mx.2 e) :: cast h (mxs.2 e)⟩
    else none
  | 21, [(A, _), (B, _)] =>
    if Ty.IsTy A && Ty.IsTy B then some (constant ⟨foldrTy A B, foldrDen A B⟩) else none
  | 22, [(k, _)] => prims[k.label]?.map constant
  | 23, [(n, _)] => G[n.label]?.map constant
  | _, _ => none

/-- The type checker and evaluator: the type and denotation of a term in a global
environment and a context, or nothing when the term is ill-typed. -/
def infer (G : List Glob) (Γ : Ctx) (t : Tree) : Option (Meaning Γ) :=
  RoseTree.para inferStep t G Γ

/-- Apply a global of type {lit}`T → T` to an input tree. -/
def Glob.apply (g : Glob) (input : Tree) : Option Tree :=
  if h : g.1 = tArrow tT tT then some (cast (congrArg Ty.den h) g.2 input) else none

/-- Apply a closed program of type {lit}`T → T` to an input tree. -/
def run (G : List Glob) (t input : Tree) : Option Tree := do
  let m ← infer G [] t
  Glob.apply ⟨m.1, m.2 ()⟩ input

end Geb.Kernel

end
