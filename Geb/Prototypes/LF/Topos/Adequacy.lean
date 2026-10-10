/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Internal.Semantics
public import Geb.Prototypes.LF.Metatheory.Substitution
public import Geb.Prototypes.LF.Topos.Signature
import Mathlib.Tactic.NormNum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The adequacy of the representation of the internal language

The representation of a fragment of the internal language by the signature
{name}`Geb.LF.Topos.sig` is adequate ({cite}`HarperLicata2007`, Section 3.2): the encoding of a
term of the language, typed by {lit}`Geb.FreeTopos.Internal.compile`, is a canonical LF term of
{lit}`tm A` for the encoding {lit}`A` of its type in the encoding of its context; decoding inverts
encoding; and every canonical LF term of {lit}`tm A` in such a context decodes to a term of the
language of the type that {lit}`A` encodes, whose encoding it is. The language's object variables
are LF variables of {lit}`tp`, outermost in the encoding of a context, and the encoding of a type
mentioning them depends on the number of variables of terms in scope, its offset: the object
variable of index {lit}`j` is the LF variable of index {lit}`off + j`. The fragment's types are
those built from the terminal object, binary products, exponentials, the subobject classifier, the
natural numbers object, list objects, the rose-tree object of natural-number labels, rose-tree
objects of labels of any type, binary coproducts and the initial object, and its terms the
variables, the element of the terminal object, pairs and their components, abstraction and
application, zero and the successor, the empty list and the construction of a list, the
constructions of rose trees, the injections into a coproduct, the case analysis of a pair of
functions, the folds of the natural numbers, of lists and of rose trees, equality, and the
applications of definitions.

A definition of the language is a constant of an extension of the signature past its own
declarations, at the position a table of the indices names ({lit}`ExtConst`), declared as the
product over the kind of types, one for each object parameter, of the products over the families
of terms of its parameters' types into the family of terms of its value's type ({lit}`defTy`);
an extension declaring them so is {lit}`SigExt`. An application of the definition is the
constant applied to the encodings of the objects, the outermost parameter's first, and then to
the encodings of the terms, the first parameter's first ({lit}`decDefn`).

The encoding of terms ({lit}`enc`) is computed from the compilation, which supplies the types
that the constants of the signature take as arguments; decoding ({lit}`dec`) forgets them. The
fold of the signature is the fold of the language: its start a term of the fold's context and its
step an LF abstraction over the value, whose body is the language's step, a term of the context
extended by the value, so that both may mention the variables around the fold.

## Main definitions

* {lit}`encTy`, {lit}`decTy` — the encoding of the fragment's types, and its inverse.
* {lit}`enc`, {lit}`dec` — the encoding of the fragment's terms, and its inverse.
* {lit}`ExtConst`, {lit}`defTy`, {lit}`SigExt` — the constants past the signature, the
  declaration of a definition, and an extension of the signature that declares the definitions.

## Main statements

* {lit}`decTy_encTy` — decoding inverts the encoding of types.
* {lit}`encTy_rename` — renaming moves the encoding of a type from one offset to another.
* {lit}`encTy_checks` — encoded types are canonical terms of {lit}`tp` in contexts whose
  variables past the offset are of {lit}`tp`.
* {lit}`tyComplete` — every canonical term of {lit}`tp` is an encoded type.
* {lit}`dec_enc` — decoding inverts the encoding of terms.

## References

* {cite}`HarperLicata2007`, Section 3.2, for adequacy.

## Tags

logical framework, LF, adequacy, Mitchell–Bénabou language, definition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

variable {sg : Sig}

/-- One step of the encoding of a type of the fragment at an offset, at a node of an operation's
label, from its children, each paired with its encoding: the object variable of index {lit}`j`
is the LF variable of index {lit}`off + j`, past the {lit}`off` variables of terms in scope; the
terminal object, a product, an exponential, the subobject classifier, the natural numbers
object, a list object, the rose-tree objects, the initial object and a coproduct, the operations
of indices 4, 6, 22, 25, 29, 33, 37, 40, 13 and 15 of the combinators, are the constants of the
same names. -/
def encTyStep (off l : ℕ) (cs : List (PartialHorn.Tree × Option Expr)) : Option Expr :=
  match l, cs with
    | 0, [(i, _)] => match i.children with
      | [] => some (Expr.var (off + i.label))
      | _ :: _ => none
    | 5, [] => some one
    | 7, [(_, a), (_, b)] => do pure (prod (← a) (← b))
    | 23, [(_, a), (_, b)] => do pure (exp (← a) (← b))
    | 26, [] => some omega
    | 30, [] => some nat
    | 34, [(_, a)] => do pure (list (← a))
    | 38, [] => some rose
    | 41, [(_, a)] => do pure (lrose (← a))
    | 14, [] => some initial
    | 16, [(_, a), (_, b)] => do pure (coprod (← a) (← b))
    | _, _ => none

/-- The encoding of a type of the fragment as a canonical term of {lit}`tp`, at an offset. -/
def encTy (off : ℕ) : PartialHorn.Tree → Option Expr := RoseTree.para (encTyStep off)

/-- One step of the decoding of a canonical term of {lit}`tp` at an offset, at a node of a label,
from its children's decodings: a variable past the offset is the object variable of its index
less the offset. -/
def decTyStep (off : ℕ) (l : Label) (cs : List (Option PartialHorn.Tree)) :
    Option PartialHorn.Tree :=
  match l, cs with
    | .app (.var i), [] => if off ≤ i then some (PartialHorn.var (i - off)) else none
    | .app (.const 1), [] => some FreeTopos.one
    | .app (.const 2), [a, b] => do pure (FreeTopos.prod (← a) (← b))
    | .app (.const 3), [a, b] => do pure (FreeTopos.exp (← a) (← b))
    | .app (.const 4), [] => some FreeTopos.omega
    | .app (.const 5), [] => some FreeTopos.nat
    | .app (.const 30), [a] => do pure (FreeTopos.list (← a))
    | .app (.const 37), [] => some FreeTopos.rose
    | .app (.const 42), [a] => do pure (FreeTopos.lrose (← a))
    | .app (.const 49), [] => some FreeTopos.zero
    | .app (.const 48), [a, b] => do pure (FreeTopos.coprod (← a) (← b))
    | _, _ => none

/-- The decoding of a canonical term of {lit}`tp` as a type of the fragment, at an offset. -/
def decTy (off : ℕ) : Expr → Option PartialHorn.Tree := RoseTree.elim (decTyStep off)

/-- The encodings of the fragment's types, one constructor at a time. -/
theorem encTy_node (off l : ℕ) (cs : List PartialHorn.Tree) :
    encTy off (RoseTree.node l cs) = encTyStep off l (cs.map fun c ↦ (c, encTy off c)) :=
  RoseTree.para_node _ l cs

/-- The steps of the encoding that have a value. -/
theorem encTyStep_eq_some {off l : ℕ} {cs : List (PartialHorn.Tree × Option Expr)} {A : Expr}
    (h : encTyStep off l cs = some A) :
    (l = 0 ∧ ∃ i x, cs = [(RoseTree.node i [], x)] ∧ A = Expr.var (off + i)) ∨
      (l = 5 ∧ cs = [] ∧ A = one) ∨
      (l = 7 ∧ ∃ a b, cs.map Prod.snd = [some a, some b] ∧ A = prod a b) ∨
      (l = 23 ∧ ∃ a b, cs.map Prod.snd = [some a, some b] ∧ A = exp a b) ∨
      (l = 26 ∧ cs = [] ∧ A = omega) ∨ (l = 30 ∧ cs = [] ∧ A = nat) ∨
      (l = 34 ∧ ∃ a, cs.map Prod.snd = [some a] ∧ A = list a) ∨ (l = 38 ∧ cs = [] ∧ A = rose) ∨
      (l = 41 ∧ ∃ a, cs.map Prod.snd = [some a] ∧ A = lrose a) ∨
      (l = 14 ∧ cs = [] ∧ A = initial) ∨
      (l = 16 ∧ ∃ a b, cs.map Prod.snd = [some a, some b] ∧ A = coprod a b) := by
  unfold encTyStep at h
  split at h
  · next i x =>
    split at h
    · next hi =>
      refine .inl ⟨rfl, i.label, x, ?_, (Option.some.inj h).symm⟩
      rw [← hi, RoseTree.node_label_children]
    · exact absurd h (by simp)
  · exact .inr (.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩)
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inl ⟨rfl, a, b, by rw [List.map_cons, List.map_cons, List.map_nil, ha, hb],
      (Option.some.inj h).symm⟩))
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inl ⟨rfl, a, b,
      by rw [List.map_cons, List.map_cons, List.map_nil, ha, hb], (Option.some.inj h).symm⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩)))))
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, a,
      by rw [List.map_cons, List.map_nil, ha], (Option.some.inj h).symm⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl,
      (Option.some.inj h).symm⟩)))))))
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, a,
      by rw [List.map_cons, List.map_nil, ha], (Option.some.inj h).symm⟩))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl,
      (Option.some.inj h).symm⟩)))))))))
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, a, b,
      by rw [List.map_cons, List.map_cons, List.map_nil, ha, hb], (Option.some.inj h).symm⟩)))))))))
  · exact absurd h (by simp)

/-- The encodings of a node that have a value: an object variable, or an operation of the
fragment whose children have encodings. -/
theorem encTy_node_eq_some {off l : ℕ} {cs : List PartialHorn.Tree} {A : Expr}
    (h : encTy off (RoseTree.node l cs) = some A) :
    (l = 0 ∧ ∃ i, cs = [RoseTree.node i []] ∧ A = Expr.var (off + i)) ∨
      (l = 5 ∧ cs = [] ∧ A = one) ∨
      (l = 7 ∧ ∃ a b, cs.map (encTy off) = [some a, some b] ∧ A = prod a b) ∨
      (l = 23 ∧ ∃ a b, cs.map (encTy off) = [some a, some b] ∧ A = exp a b) ∨
      (l = 26 ∧ cs = [] ∧ A = omega) ∨ (l = 30 ∧ cs = [] ∧ A = nat) ∨
      (l = 34 ∧ ∃ a, cs.map (encTy off) = [some a] ∧ A = list a) ∨
      (l = 38 ∧ cs = [] ∧ A = rose) ∨
      (l = 41 ∧ ∃ a, cs.map (encTy off) = [some a] ∧ A = lrose a) ∨
      (l = 14 ∧ cs = [] ∧ A = initial) ∨
      (l = 16 ∧ ∃ a b, cs.map (encTy off) = [some a, some b] ∧ A = coprod a b) := by
  rw [encTy_node] at h
  have hsnd : (cs.map fun c ↦ (c, encTy off c)).map Prod.snd = cs.map (encTy off) := by
    rw [List.map_map]
    rfl
  have hnil : (cs.map fun c ↦ (c, encTy off c)) = [] → cs = [] := List.map_eq_nil_iff.mp
  rcases encTyStep_eq_some h with ⟨rfl, i, x, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
      ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ |
      ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩
  · obtain ⟨c, hc, h₁⟩ := List.map_eq_singleton_iff.mp hcs
    exact .inl ⟨rfl, i, by rw [hc, (Prod.mk.inj h₁).1], rfl⟩
  · exact .inr (.inl ⟨rfl, hnil hcs, rfl⟩)
  · exact .inr (.inr (.inl ⟨rfl, a, b, hsnd ▸ hcs, rfl⟩))
  · exact .inr (.inr (.inr (.inl ⟨rfl, a, b, hsnd ▸ hcs, rfl⟩)))
  · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, hnil hcs, rfl⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, hnil hcs, rfl⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, a, hsnd ▸ hcs, rfl⟩))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, hnil hcs, rfl⟩)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, a, hsnd ▸ hcs, rfl⟩))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, hnil hcs,
      rfl⟩)))))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, a, b, hsnd ▸ hcs,
      rfl⟩)))))))))

/-- The decoding of a node of a canonical term of {lit}`tp`. -/
theorem decTy_node (off : ℕ) (l : Label) (cs : List Expr) :
    decTy off (RoseTree.node l cs) = decTyStep off l (cs.map (decTy off)) :=
  RoseTree.elim_node _ l cs

/-- The encoding of an object variable. -/
theorem encTy_var (off i : ℕ) : encTy off (PartialHorn.var i) = some (Expr.var (off + i)) := rfl

/-- The decoding of a variable past the offset. -/
theorem decTy_var (off i : ℕ) : decTy off (Expr.var (off + i)) = some (PartialHorn.var i) := by
  rw [Expr.var, Expr.app, decTy_node]
  simp only [List.map_nil, decTyStep, Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]

/-- An application of a constant renames its arguments. -/
theorem rename_app_node (h : Head) (cs : List Expr) (ρ : ℕ → ℕ) :
    Expr.rename (RoseTree.node (.app h) cs) ρ =
      RoseTree.node (.app (h.rename ρ)) (cs.map fun c ↦ Expr.rename c ρ) := by
  rw [rename_node]
  exact congrArg _ (List.ext_getElem (by simp) fun k _ _ ↦ by simp [Label.binders])

/-- A list mapped to two values is of two elements, mapped to them. -/
theorem map_eq_two {α β : Type} {f : α → β} {cs : List α} {a b : β} (h : cs.map f = [a, b]) :
    ∃ c₁ c₂, cs = [c₁, c₂] ∧ f c₁ = a ∧ f c₂ = b := by
  rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨c₁, c₂, rfl, h.1, h.2⟩
  · exact absurd h (by simp)

/-- A list mapped to one value is of one element, mapped to it. -/
theorem map_eq_one {α β : Type} {f : α → β} {cs : List α} {a : β} (h : cs.map f = [a]) :
    ∃ c, cs = [c] ∧ f c = a := by
  obtain ⟨c, rfl, hc⟩ := List.map_eq_singleton_iff.mp h
  exact ⟨c, rfl, hc⟩

/-- Decoding inverts the encoding of types. -/
theorem decTy_encTy (off : ℕ) :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy off a = some A → decTy off A = some a :=
  RoseTree.ind fun l cs ih A h ↦ by
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩
    · exact decTy_var off i
    any_goals rfl
    all_goals first
      | (obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_eq_two hcs
         simp only [prod, exp, coprod, Expr.const, Expr.app, decTy_node, List.map_cons,
           List.map_nil, decTyStep, ih c₁ (by simp) a h₁, ih c₂ (by simp) b h₂,
           Option.bind_eq_bind, Option.bind_some,
           Option.pure_def]
         rfl)
      | (obtain ⟨c₁, rfl, h₁⟩ := map_eq_one hcs
         simp only [list, lrose, Expr.const, Expr.app, decTy_node, List.map_cons, List.map_nil,
           decTyStep, ih c₁ (by simp) a h₁, Option.bind_eq_bind, Option.bind_some,
           Option.pure_def]
         rfl)

/-- The encoding of types is injective. -/
theorem encTy_inj {off : ℕ} {a b : PartialHorn.Tree} {A : Expr} (ha : encTy off a = some A)
    (hb : encTy off b = some A) : a = b :=
  Option.some.inj ((decTy_encTy off a A ha).symm.trans (decTy_encTy off b A hb))

/-- A renaming that moves the variables past one offset to the same positions past another
moves the encoding of a type at the first offset to its encoding at the second. -/
theorem encTy_rename :
    ∀ (a : PartialHorn.Tree) (off : ℕ) (A : Expr), encTy off a = some A →
      ∀ (off' : ℕ) (ρ : ℕ → ℕ), (∀ i, off ≤ i → ρ i + off = i + off') →
        encTy off' a = some (A.rename ρ) :=
  RoseTree.ind fun l cs ih off A h off' ρ hρ ↦ by
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩
    · have := hρ (off + i) (Nat.le_add_right off i)
      rw [Expr.var, Expr.app, rename_app_node, Head.rename, List.map_nil,
        show ρ (off + i) = off' + i by omega]
      rfl
    any_goals rfl
    all_goals first
      | (obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_eq_two hcs
         simp only [prod, exp, coprod, Expr.const, Expr.app, rename_app_node, Head.rename,
           List.map_cons, List.map_nil, encTy_node, encTyStep, ih c₁ (by simp) off a h₁ off' ρ hρ,
           ih c₂ (by simp) off b h₂ off' ρ hρ, Option.bind_eq_bind, Option.bind_some,
           Option.pure_def])
      | (obtain ⟨c₁, rfl, h₁⟩ := map_eq_one hcs
         simp only [list, lrose, Expr.const, Expr.app, rename_app_node, Head.rename,
           List.map_cons, List.map_nil, encTy_node, encTyStep, ih c₁ (by simp) off a h₁ off' ρ hρ,
           Option.bind_eq_bind, Option.bind_some, Option.pure_def])

/-- The encoding of a type at an offset is the weakening of its encoding at a lower offset. -/
theorem encTy_add {a : PartialHorn.Tree} {off d : ℕ} {A : Expr} (h : encTy off a = some A) :
    encTy (off + d) a = some (A.rename (· + d)) :=
  encTy_rename a off A h _ _ fun i _ ↦ by omega

/-- The encoding of a type at the next offset is the weakening of its encoding by the
successor. -/
theorem encTy_succ {a : PartialHorn.Tree} {off : ℕ} {A : Expr} (h : encTy off a = some A) :
    encTy (off + 1) a = some (A.rename Nat.succ) :=
  encTy_add h

/-- The encoding of a type at a positive offset weakens its encoding at the offset below past
any variable below the offset. -/
theorem encTy_pred {a : PartialHorn.Tree} {off j : ℕ} {A : Expr} (h : encTy off a = some A)
    (hj : j < off) :
    ∃ A', encTy (off - 1) a = some A' ∧ A = A'.rename (liftR^[j] Nat.succ) := by
  refine ⟨_, encTy_rename a off A h (off - 1) (· - 1) fun i hi ↦ by omega, ?_⟩
  have h' := encTy_rename a (off - 1) _ (encTy_rename a off A h (off - 1) (· - 1)
    fun i hi ↦ by omega) off (liftR^[j] Nat.succ) fun i hi ↦ by
      rw [iterate_liftR_apply]
      split <;> omega
  exact Option.some.inj (h.symm.trans h')

/-- Substitution for a variable below the offset of an encoded type is its encoding at the offset
below. -/
theorem hsubWith_encTy (red : Expr → List Expr → Option Expr) {a : PartialHorn.Tree} {off j : ℕ}
    {A : Expr} (h : encTy off a = some A) (hj : j < off) (n : Expr) :
    ∃ A', encTy (off - 1) a = some A' ∧ hsubWith red A n j = some A' := by
  obtain ⟨A', hA', rfl⟩ := encTy_pred h hj
  exact ⟨A', hA', hsubWith_vacuous _ _ _ _⟩

/-- Renaming by the successor is renaming by the addition of one. -/
theorem rename_succ_eq_add (e : Expr) : e.rename Nat.succ = e.rename (· + 1) := rfl

/-- Renaming by the identity function. -/
theorem rename_fun_id (e : Expr) : e.rename (fun i ↦ i) = e := rename_id e

/-- Substitution for the variable of index {lit}`j` into an expression weakened past it, by
{lit}`j + 1`, gives the expression weakened by {lit}`j`. -/
theorem hsubWith_rename_add_succ (red : Expr → List Expr → Option Expr) (n e : Expr) (j : ℕ) :
    hsubWith red (e.rename (· + (j + 1))) n j = some (e.rename (· + j)) := by
  rw [rename_add_succ]
  exact hsubWith_vacuous _ _ _ _

/-- Substitution for the innermost variable into an expression weakened past it. -/
theorem hsubWith_succ₀ (red : Expr → List Expr → Option Expr) (n e : Expr) :
    hsubWith red (e.rename Nat.succ) n 0 = some e :=
  hsubWith_vacuous red e n 0

/-- Substitution for the variable of index one into an expression weakened twice. -/
theorem hsubWith_succ₁ (red : Expr → List Expr → Option Expr) (n e : Expr) :
    hsubWith red ((e.rename Nat.succ).rename Nat.succ) n 1 = some (e.rename Nat.succ) := by
  rw [rename_rename]
  exact hsubWith_rename_add_succ red n e 1

/-- Substitution for the variable of index two into an expression weakened three times. -/
theorem hsubWith_succ₂ (red : Expr → List Expr → Option Expr) (n e : Expr) :
    hsubWith red (((e.rename Nat.succ).rename Nat.succ).rename Nat.succ) n 2 =
      some ((e.rename Nat.succ).rename Nat.succ) := by
  rw [rename_rename, rename_rename, rename_rename]
  exact hsubWith_rename_add_succ red n e 2

/-- Substitution for the variable of index three into an expression weakened four times. -/
theorem hsubWith_succ₃ (red : Expr → List Expr → Option Expr) (n e : Expr) :
    hsubWith red ((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ) n 3 =
      some (((e.rename Nat.succ).rename Nat.succ).rename Nat.succ) := by
  rw [rename_rename, rename_rename, rename_rename, rename_rename, rename_rename]
  exact hsubWith_rename_add_succ red n e 3

/-- Substitution for the variable of index four into an expression weakened five times. -/
theorem hsubWith_succ₄ (red : Expr → List Expr → Option Expr) (n e : Expr) :
    hsubWith red (((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
      Nat.succ).rename Nat.succ) n 4 =
      some ((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ) := by
  simp only [rename_rename]
  exact hsubWith_rename_add_succ red n e 4

/-- Substitution for the variable of index five into an expression weakened six times. -/
theorem hsubWith_succ₅ (red : Expr → List Expr → Option Expr) (n e : Expr) :
    hsubWith red ((((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
      Nat.succ).rename Nat.succ).rename Nat.succ) n 5 =
      some (((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
        Nat.succ) := by
  simp only [rename_rename]
  exact hsubWith_rename_add_succ red n e 5

/-- The computation of the instantiation of a declaration's type along a spine of symbolic
arguments: the hereditary substitutions unfolded node by node, with the given facts about the
arguments, their checks and their closedness among them. The set of lemmas is shared by every
declaration, and a given computation uses only some of them. -/
local macro "lf_spine" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      rename_succ_eq_add, rename_add_add, hsubWith_rename_add_succ, rename_add_zero, rename_fun_id,
      $hs,*]))

/-- The computation of the instantiation of a declaration's type along a spine, in a
hypothesis. -/
local macro "lf_spine_at" h:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      rename_succ_eq_add, rename_add_add, hsubWith_rename_add_succ, rename_add_zero, rename_fun_id,
      $hs,*] at $h:ident))

/-- The encoding of a context of the fragment's types in {lit}`n` object variables: the
{lit}`n` variables of {lit}`tp`, outermost, and each type {lit}`a` the type {lit}`tm A` of an LF
variable, {lit}`A` the encoding of {lit}`a` at the offset of the variables of terms outside it. -/
def encCtx (n : ℕ) : List PartialHorn.Tree → Option Ctx :=
  List.rec (some (List.replicate n tp)) fun a Γ r ↦ do pure (tm (← encTy Γ.length a) :: (← r))

/-- The encoding of a context extended by a type. -/
theorem encCtx_cons {n : ℕ} {a : PartialHorn.Tree} {Γ : List PartialHorn.Tree} {A : Expr}
    (ha : encTy Γ.length a = some A) {ΓLF : Ctx} (h : encCtx n Γ = some ΓLF) :
    encCtx n (a :: Γ) = some (tm A :: ΓLF) := by
  change (do pure (tm (← encTy Γ.length a) :: (← encCtx n Γ))) = _
  rw [ha, h]
  rfl

/-- The encoding of the empty context is the object variables. -/
theorem encCtx_nil (n : ℕ) : encCtx n [] = some (List.replicate n tp) := rfl

/-- A term of the internal language. -/
abbrev MTerm : Type := FreeTopos.Internal.Term

/-- An environment of the compilation of the internal language: an arrow and a type for each
variable. -/
abbrev MEnv : Type := List (PartialHorn.Tree × PartialHorn.Tree)

/-- The products over each of a list of domains, the outermost first, into a body. -/
def piTele (Ds : List Expr) (R : Expr) : Expr := Ds.foldr Expr.pi R

/-- The products over a list of domains, at its first. -/
theorem piTele_cons (D : Expr) (Ds : List Expr) (R : Expr) :
    piTele (D :: Ds) R = Expr.pi D (piTele Ds R) :=
  rfl

/-- The declaration of a definition of the language: the products over the kind of types, one
for each of its object parameters, of the products over the families of terms of its
parameters' types, the outermost first, each encoded at the offset of the parameters outside it,
into the family of terms of its value's type, encoded in the scope of the parameters. -/
def defTy (d : FreeTopos.Internal.Defn) : Option Expr := do
  let ΓT ← encCtx d.arity d.params
  pure (piTele ΓT.reverse (tm (← encTy d.params.length d.type)))

/-- A constant an extension of the signature declares past it: a theorem, given by the index of
its entry, the number of its object variables and the number of its variables; a definition, given
by its index, the number of its object parameters and the number of its parameters; or the
unfolding of a definition, given likewise. -/
inductive ExtConst where
  /-- A theorem. -/
  | thm (j m p : ℕ)
  /-- A definition. -/
  | defn (kd m p : ℕ)
  /-- The unfolding of a definition. -/
  | delta (kd m p : ℕ)
deriving DecidableEq

/-- The indices of the primitive arrows of the language that the signature's constants of zero,
the successor, the empty list, the construction of a list, the constructions of rose trees, the
injections into a coproduct and the case analysis stand for, and of the theorems that an extension
of the signature declares, past it, in order. -/
structure PrimIdx where
  /-- The index of zero. -/
  zero : ℕ
  /-- The index of the successor. -/
  succ : ℕ
  /-- The index of the empty list. -/
  nil : ℕ
  /-- The index of the construction of a list. -/
  cons : ℕ
  /-- The index of the construction of a rose tree of natural-number labels. -/
  node : ℕ
  /-- The index of the construction of a rose tree of labels of a type. -/
  lnode : ℕ
  /-- The index of the left injection into a coproduct. -/
  inl : ℕ
  /-- The index of the right injection into a coproduct. -/
  inr : ℕ
  /-- The index of the case analysis of a coproduct. -/
  case : ℕ
  /-- The constants an extension of the signature declares past it, in order. -/
  ext : List ExtConst

/-- The primitive arrows of the globals at the indices are those the indices name. -/
structure PrimIdx.Valid (k : PrimIdx) (G : FreeTopos.Internal.Globals) : Prop where
  /-- Zero. -/
  zero : G.prims[k.zero]? = some FreeTopos.Internal.zeroPrim
  /-- The successor. -/
  succ : G.prims[k.succ]? = some FreeTopos.Internal.succPrim
  /-- The empty list. -/
  nil : G.prims[k.nil]? = some FreeTopos.Internal.nilPrim
  /-- The construction of a list. -/
  cons : G.prims[k.cons]? = some FreeTopos.Internal.consPrim
  /-- The construction of a rose tree of natural-number labels. -/
  node : G.prims[k.node]? = some FreeTopos.Internal.nodePrim
  /-- The construction of a rose tree of labels of a type. -/
  lnode : G.prims[k.lnode]? = some FreeTopos.Internal.lnodePrim
  /-- The left injection into a coproduct. -/
  inl : G.prims[k.inl]? = some FreeTopos.Internal.inlPrim
  /-- The right injection into a coproduct. -/
  inr : G.prims[k.inr]? = some FreeTopos.Internal.inrPrim
  /-- The case analysis of a coproduct. -/
  case : G.prims[k.case]? = some FreeTopos.Internal.casePrim

/-- The first position of a constant in a list of constants of an extension. -/
def ExtConst.find? (x : ExtConst) : List ExtConst → Option ℕ :=
  List.rec none fun y _ r ↦ if y = x then some 0 else r.map (· + 1)

/-- A constant is at the position at which it is found. -/
theorem ExtConst.find?_spec (x : ExtConst) :
    ∀ (l : List ExtConst) (i : ℕ), x.find? l = some i → l[i]? = some x := by
  intro l
  refine List.rec (motive := fun l ↦ ∀ i, x.find? l = some i → l[i]? = some x)
    (fun _ h ↦ nomatch h) (fun y l ih i h ↦ ?_) l
  change (if y = x then some 0 else (x.find? l).map (· + 1)) = some i at h
  by_cases hy : y = x
  · rw [ite_eq_left hy] at h
    obtain rfl := Option.some.inj h
    rw [hy]
    rfl
  · rw [ite_eq_right hy] at h
    obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.mp h
    exact ih i' hi'

/-- The constant past the signature that the indices name for a definition, with its numbers of
object parameters and parameters. -/
def PrimIdx.defConst (k : PrimIdx) (kd m p : ℕ) : Option ℕ :=
  ((ExtConst.defn kd m p).find? k.ext).map (sig.length + ·)

/-- An extension of the signature, with the constants of {lit}`G` and the indices {lit}`k`: the
signature is a prefix of it, it is formed, it declares one constant past the signature for each
constant of the indices' extension, none of its further declarations is a type, the definitions
the indices name, each at its first position among the indices' constants, are definitions the
language admits, their parameters and values of types and their bodies compiling to their values'
types, and are declared there as {name}`Geb.LF.Topos.defTy` declares them, and its further
declarations of terms are those definitions. -/
structure SigExt (G : FreeTopos.Internal.Globals) (k : PrimIdx) (sg : Sig) : Prop where
  /-- The extension is formed. -/
  ok : sg.ok = true
  /-- The signature is a prefix of it. -/
  pre : sig <+: sg
  /-- It declares a constant for each constant of the indices' extension. -/
  len : sg.length = sig.length + k.ext.length
  /-- Its further declarations do not end in {lit}`tp`. -/
  noTp : ∀ c T, sig.length ≤ c → sg[c]? = some T → T.headDepth.1 ≠ some 0
  /-- The definitions the indices name are admitted and declared at their positions. -/
  defs : ∀ i kd m p, k.ext[i]? = some (.defn kd m p) → ∃ d T,
    (ExtConst.defn kd m p).find? k.ext = some i ∧
    G.defs[kd]? = some (.language d) ∧ m = d.arity ∧ p = d.params.length ∧
      (FreeTopos.Internal.Definition.language d).ok G = true ∧
      (∃ cd, FreeTopos.Internal.Defn.compile G d = some cd) ∧ defTy d = some T ∧
      sg[sig.length + i]? = some T
  /-- Its further declarations ending in {lit}`tm` are definitions. -/
  tmDefs : ∀ i T, sg[sig.length + i]? = some T → T.headDepth.1 = some 6 →
    ∃ kd m p, k.ext[i]? = some (.defn kd m p)

variable {G : FreeTopos.Internal.Globals} {k : PrimIdx}

/-- A declaration of the signature is one of an extension of it. -/
theorem get_of_prefix (hpre : sig <+: sg) {c : ℕ} {T : Expr} (hc : sig[c]? = some T) :
    sg[c]? = some T := by
  obtain ⟨t, rfl⟩ := hpre
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1, hc]

/-- A declaration of the signature is one of its extension. -/
theorem SigExt.get (hsg : SigExt G k sg) {c : ℕ} {T : Expr} (hc : sig[c]? = some T) :
    sg[c]? = some T :=
  get_of_prefix hsg.pre hc

/-- A declaration of an extension below the signature's length is the signature's. -/
theorem SigExt.of_lt (hsg : SigExt G k sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
    (hlt : c < sig.length) : sig[c]? = some T := by
  obtain ⟨t, rfl⟩ := hsg.pre
  rwa [List.getElem?_append_left hlt] at hc

/-- An application of a constant checks against an atomic type that its type instantiates to
along its spine. -/
theorem judge_const {Γ : Ctx} {c : ℕ} {ms : List Expr} {T P : Expr} (hc : sg[c]? = some T)
    (hs : spine Γ T (ms.map fun m ↦ (m, judge sg m)) = some P) (hP : IsApp P = true) :
    judge sg (Expr.const c ms) Γ (.check P) = true := by
  rw [judge, Expr.const, Expr.app, judgeWith_node]
  simp only [judgeStep, hP, Bool.true_and, classOf, hc, Option.bind_some]
  rw [show spine Γ T (ms.map fun c ↦ (c, judgeWith (· == ·) sg c)) = some P from hs]
  exact beq_self_eq_true P

/-- A variable of a type checks against it. -/
theorem judge_var {Γ : Ctx} {i : ℕ} {A : Expr} (hA : IsApp A = true) (h : varType Γ i = some A) :
    judge sg (Expr.var i) Γ (.check A) = true := by
  rw [judge, Expr.var, Expr.app, judgeWith_node]
  simp only [judgeStep, hA, Bool.true_and, List.map_nil]
  rw [show classOf sg Γ (.var i) = some A from h, Option.bind_some]
  exact beq_self_eq_true A

/-- The encoding of a type in {lit}`n` object variables, at an offset, is a canonical term of
{lit}`tp` in every context whose variables past the offset are of {lit}`tp`. -/
theorem encTy_checks_of_prefix (hpre : sig <+: sg) (G : FreeTopos.Internal.Globals) {n : ℕ} :
    ∀ (a : PartialHorn.Tree) (off : ℕ) (A : Expr), encTy off a = some A →
      FreeTopos.Internal.IsTy G n a = true → ∀ Γ : Ctx,
        (∀ j < n, varType Γ (off + j) = some tp) → judge sg A Γ (.check tp) = true :=
  RoseTree.ind fun l cs ih off A h hty Γ hΓ ↦ by
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩
    · exact judge_var rfl (hΓ i (FreeTopos.Internal.isTy_var.mp hty))
    any_goals exact judge_const (T := tp) (get_of_prefix hpre rfl) rfl rfl
    all_goals first
      | (obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_eq_two hcs
         first
           | rw [show RoseTree.node 7 [c₁, c₂] = FreeTopos.prod c₁ c₂ from rfl,
               FreeTopos.Internal.isTy_prod, Bool.and_eq_true] at hty
           | rw [show RoseTree.node 23 [c₁, c₂] = FreeTopos.exp c₁ c₂ from rfl,
               FreeTopos.Internal.isTy_exp, Bool.and_eq_true] at hty
           | rw [show RoseTree.node 16 [c₁, c₂] = FreeTopos.coprod c₁ c₂ from rfl,
               FreeTopos.Internal.isTy_coprod, Bool.and_eq_true] at hty
         have ha := ih c₁ (by simp) off a h₁ hty.1 Γ hΓ
         have hb := ih c₂ (by simp) off b h₂ hty.2 Γ hΓ
         refine judge_const (T := Expr.arrow tp (Expr.arrow tp tp)) (get_of_prefix hpre rfl) ?_ rfl
         simp only [tp, Expr.const, Expr.app] at ha hb ⊢
         lf_spine [ha, hb])
      | (obtain ⟨c₁, rfl, h₁⟩ := map_eq_one hcs
         first
           | rw [show RoseTree.node 34 [c₁] = FreeTopos.list c₁ from rfl,
               FreeTopos.Internal.isTy_list] at hty
           | rw [show RoseTree.node 41 [c₁] = FreeTopos.lrose c₁ from rfl,
               FreeTopos.Internal.isTy_lrose] at hty
         have ha := ih c₁ (by simp) off a h₁ hty Γ hΓ
         refine judge_const (T := Expr.arrow tp tp) (get_of_prefix hpre rfl) ?_ rfl
         simp only [tp, Expr.const, Expr.app] at ha ⊢
         lf_spine [ha])

/-- The encoding of a type in {lit}`n` object variables, at an offset, is a canonical term of
{lit}`tp` in an extension of the signature, in every context whose variables past the offset are
of {lit}`tp`. -/
theorem encTy_checks {G' : FreeTopos.Internal.Globals} (hsg : SigExt G' k sg)
    (G : FreeTopos.Internal.Globals) {n : ℕ} (a : PartialHorn.Tree) (off : ℕ) (A : Expr)
    (h : encTy off a = some A) (hty : FreeTopos.Internal.IsTy G n a = true) (Γ : Ctx)
    (hΓ : ∀ j < n, varType Γ (off + j) = some tp) : judge sg A Γ (.check tp) = true :=
  encTy_checks_of_prefix hsg.pre G a off A h hty Γ hΓ

section Encoding

variable (G : FreeTopos.Internal.Globals) (n : ℕ) (k : PrimIdx)

open FreeTopos.Internal in
/-- One step of the encoding of a term of the internal language in {lit}`n` object variables, at
a node of a label, from its children's encodings, in an environment over {lit}`X`: each
constructor of the fragment is the constant of the same name, applied to the encodings of the
types of its children, which the compilation computes, at the offset of the environment's
variables, and of the children; an abstraction's body and a fold's step are LF abstractions, the
step over the fold's type, the type of its start, and over the element type before it for a
list, and over the pair of a label and the list of the children's values for a rose tree; zero,
the successor, the empty list and the constructions of a list and of a rose tree are the
primitive arrows the indices name. A term outside the fragment, or with a type outside it, has no
encoding. -/
def encStep (l : FreeTopos.Internal.Label)
    (cs : List (MTerm × (PartialHorn.Tree → MEnv → Option Expr)))
    (X : PartialHorn.Tree) (e : MEnv) : Option Expr :=
  match l, cs with
    | .var i, [] => some (Expr.var i)
    | .star, [] => some star
    | .pair, [(t, et), (u, eu)] => do
      let (_, a) ← compile G n t X e
      let (_, b) ← compile G n u X e
      pure (pair (← encTy e.length a) (← encTy e.length b) (← et X e) (← eu X e))
    | .fst, [(t, et)] => do
      let (_, p) ← compile G n t X e
      let (a, b) ← prodParts p
      pure (fst (← encTy e.length a) (← encTy e.length b) (← et X e))
    | .snd, [(t, et)] => do
      let (_, p) ← compile G n t X e
      let (a, b) ← prodParts p
      pure (snd (← encTy e.length a) (← encTy e.length b) (← et X e))
    | .lam a, [(t, et)] => do
      let (_, b) ← compile G n t (FreeTopos.prod X a) (extEnv X a e)
      pure (lam (← encTy e.length a) (← encTy e.length b)
        (Expr.lam (← et (FreeTopos.prod X a) (extEnv X a e))))
    | .app, [(t, et), (_, eu)] => do
      let (_, p) ← compile G n t X e
      let (a, b) ← expParts p
      pure (app (← encTy e.length a) (← encTy e.length b) (← et X e) (← eu X e))
    | .arr i [], [(_, et)] =>
      if i = k.zero then zeroAt <$> et X e else if i = k.succ then succ <$> et X e
      else if i = k.node then node <$> et X e else none
    | .arr i [a], [(_, et)] =>
      if i = k.nil then do pure (nilAt (← encTy e.length a) (← et X e))
      else if i = k.cons then do pure (cons (← encTy e.length a) (← et X e))
      else if i = k.lnode then do pure (lnode (← encTy e.length a) (← et X e)) else none
    | .arr i [a, b], [(_, et)] =>
      if i = k.inl then do pure (inl (← encTy e.length a) (← encTy e.length b) (← et X e))
      else if i = k.inr then do pure (inr (← encTy e.length a) (← encTy e.length b) (← et X e))
      else none
    | .arr i [a, b, c], [(_, et)] =>
      if i = k.case then do
        pure (case (← encTy e.length a) (← encTy e.length b) (← encTy e.length c) (← et X e))
      else none
    | .natRec, [(z, ez), (_, es), (_, em)] => do
      let (_, c) ← compile G n z X e
      pure (natRec (← encTy e.length c) (← ez X e)
        (Expr.lam (← es (FreeTopos.prod X c) (extEnv X c e))) (← em X e))
    | .listRec, [(z, ez), (_, es), (m, em)] => do
      let (_, c) ← compile G n z X e
      let (_, t) ← compile G n m X e
      let a ← listPart t
      pure (listRec (← encTy e.length a) (← encTy e.length c) (← ez X e)
        (Expr.lam (Expr.lam (← es (FreeTopos.prod (FreeTopos.prod X a) c)
          (extEnv (FreeTopos.prod X a) c (extEnv X a e))))) (← em X e))
    | .roseRec c, [(_, es), (m, em)] => do
      let (_, t) ← compile G n m X e
      match t.label, t.children with
      | 38, [] =>
        pure (roseRec (← encTy e.length c) (Expr.lam (← es (FreeTopos.prod X
          (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)))
          (extEnv X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) e))) (← em X e))
      | 41, [a] =>
        pure (lroseRec (← encTy e.length a) (← encTy e.length c) (Expr.lam (← es
          (FreeTopos.prod X (FreeTopos.prod a (FreeTopos.list c)))
          (extEnv X (FreeTopos.prod a (FreeTopos.list c)) e))) (← em X e))
      | _, _ => none
    | .eq, [(t, et), (_, eu)] => do
      let (_, a) ← compile G n t X e
      pure (eq (← encTy e.length a) (← et X e) (← eu X e))
    | .defn kd θ, cs => do
      let d ← (G.defs[kd]?).bind FreeTopos.Internal.Definition.language?
      let c ← k.defConst kd d.arity d.params.length
      if θ.length = d.arity ∧ cs.length = d.params.length then do
        let Ts ← θ.reverse.mapM (encTy e.length)
        let Ms ← cs.reverse.mapM fun x ↦ x.2 X e
        pure (Expr.const c (Ts ++ Ms))
      else none
    | _, _ => none

/-- The encoding of a term of the internal language in an environment. -/
def enc : MTerm → PartialHorn.Tree → MEnv → Option Expr := RoseTree.para (encStep G n k)

/-- The computation rule of the encoding of terms. -/
theorem enc_node (l : FreeTopos.Internal.Label) (cs : List MTerm) :
    enc G n k (RoseTree.node l cs) =
      encStep G n k l (cs.map fun c ↦ (c, enc G n k c)) :=
  RoseTree.para_node _ l cs

end Encoding

/-- The family of terms of a closed type is closed. -/
theorem tm_closed {A : Expr} (h : A.FreeBelow 0 = true) : (tm A).FreeBelow 0 = true :=
  freeBelow_node_iff.mpr ⟨(fun _ h ↦ nomatch h), fun idx hidx ↦ by
    rcases idx with _ | idx
    · exact h
    · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)⟩

/-- The family of terms renames its index. -/
theorem tm_rename (A : Expr) (ρ : ℕ → ℕ) : (tm A).rename ρ = tm (A.rename ρ) := by
  rw [tm, Expr.const, Expr.app, rename_app_node]
  rfl

/-- The kind of types is closed. -/
theorem tp_rename (ρ : ℕ → ℕ) : tp.rename ρ = tp := by
  rw [tp, Expr.const, Expr.app, rename_app_node]
  rfl

/-- The inversion of the encoding of a context extended by a type. -/
theorem encCtx_cons_inv {n : ℕ} {a : PartialHorn.Tree} {Γ : List PartialHorn.Tree} {ΓLF : Ctx}
    (h : encCtx n (a :: Γ) = some ΓLF) :
    ∃ A ΓLF', encTy Γ.length a = some A ∧ encCtx n Γ = some ΓLF' ∧ ΓLF = tm A :: ΓLF' := by
  change (do pure (tm (← encTy Γ.length a) :: (← encCtx n Γ))) = some ΓLF at h
  obtain ⟨A, hA, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ΓLF', hΓ, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨A, ΓLF', hA, hΓ, (Option.some.inj h).symm⟩

/-- The type of a variable of an encoded context, a variable of a term, is the family of terms of
the encoding of its type at the offset of the context's variables of terms. -/
theorem varType_encCtx {n : ℕ} {Γ : List PartialHorn.Tree} {ΓLF : Ctx}
    (hΓ : encCtx n Γ = some ΓLF) {i : ℕ} {a : PartialHorn.Tree} (ha : Γ[i]? = some a) :
    ∃ A, encTy Γ.length a = some A ∧ varType ΓLF i = some (tm A) := by
  refine List.rec (motive := fun Γ ↦ ∀ (ΓLF : Ctx), encCtx n Γ = some ΓLF →
      ∀ (i : ℕ) (a : PartialHorn.Tree), Γ[i]? = some a →
        ∃ A, encTy Γ.length a = some A ∧ varType ΓLF i = some (tm A))
    (fun _ _ _ _ ha ↦ absurd ha (by simp)) (fun b Γ ih ΓLF h i a ha ↦ ?_) Γ ΓLF hΓ i a ha
  obtain ⟨B, ΓLF', hB, hΓ, rfl⟩ := encCtx_cons_inv h
  rcases i with _ | i
  · obtain rfl : b = a := Option.some.inj ha
    exact ⟨B.rename (· + 1), encTy_add hB, by
      rw [varType, List.getElem?_cons_zero, Option.map_some, tm_rename]⟩
  · obtain ⟨A, hA, hv⟩ := ih _ hΓ i a ha
    exact ⟨A.rename (· + 1), encTy_add hA, by rw [varType_cons_succ, hv, Option.map_some,
      tm_rename]⟩

/-- The variables of an encoded context past its variables of terms, below the number of object
variables, are of {lit}`tp`. -/
theorem varType_encCtx_tp {n : ℕ} {Γ : List PartialHorn.Tree} {ΓLF : Ctx}
    (hΓ : encCtx n Γ = some ΓLF) {j : ℕ} (hj : j < n) :
    varType ΓLF (Γ.length + j) = some tp := by
  refine List.rec (motive := fun Γ ↦ ∀ (ΓLF : Ctx), encCtx n Γ = some ΓLF →
      ∀ (j : ℕ), j < n → varType ΓLF (Γ.length + j) = some tp)
    (fun _ h j hj ↦ ?_) (fun b Γ ih ΓLF h j hj ↦ ?_) Γ ΓLF hΓ j hj
  · obtain rfl := Option.some.inj h
    simp only [varType, List.length_nil, Nat.zero_add, List.getElem?_replicate, hj, ↓reduceIte,
      Option.map_some, tp_rename]
  · obtain ⟨B, ΓLF', hB, hΓ, rfl⟩ := encCtx_cons_inv h
    rw [List.length_cons, show Γ.length + 1 + j = Γ.length + j + 1 by omega, varType_cons_succ,
      ih _ hΓ j hj, Option.map_some, tp_rename]

/-- The types of the variables of an encoded context: the families of terms of the encodings of
the context's types, and {lit}`tp` past them. -/
theorem varType_encCtx_inv {n : ℕ} {Γ : List PartialHorn.Tree} {ΓLF : Ctx}
    (hΓ : encCtx n Γ = some ΓLF) {i : ℕ} {t : Expr} (ht : varType ΓLF i = some t) :
    (∃ a A, Γ[i]? = some a ∧ encTy Γ.length a = some A ∧ t = tm A) ∨
      (Γ.length ≤ i ∧ i < Γ.length + n ∧ t = tp) := by
  refine List.rec (motive := fun Γ ↦ ∀ (ΓLF : Ctx), encCtx n Γ = some ΓLF →
      ∀ (i : ℕ) (t : Expr), varType ΓLF i = some t →
        (∃ a A, Γ[i]? = some a ∧ encTy Γ.length a = some A ∧ t = tm A) ∨
          (Γ.length ≤ i ∧ i < Γ.length + n ∧ t = tp))
    (fun _ h i t ht ↦ ?_) (fun b Γ ih ΓLF h i t ht ↦ ?_) Γ ΓLF hΓ i t ht
  · obtain rfl := Option.some.inj h
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
    rw [List.getElem?_replicate] at ht'
    split at ht'
    · next hi =>
      obtain rfl := Option.some.inj ht'
      exact .inr ⟨Nat.zero_le _, by simpa using hi, tp_rename _⟩
    · exact absurd ht' (by simp)
  · obtain ⟨B, ΓLF', hB, hΓ, rfl⟩ := encCtx_cons_inv h
    rcases i with _ | i
    · obtain rfl : t = (tm B).rename (· + 1) := (Option.some.inj ht).symm
      exact .inl ⟨b, B.rename (· + 1), rfl, encTy_add hB, tm_rename _ _⟩
    · rw [varType_cons_succ] at ht
      obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
      rcases ih _ hΓ _ _ ht' with ⟨a, A, ha, hA, rfl⟩ | ⟨h₁, h₂, rfl⟩
      · exact .inl ⟨a, A.rename (· + 1), ha, encTy_add hA, tm_rename _ _⟩
      · exact .inr ⟨by simp only [List.length_cons]; omega, by simp only [List.length_cons]; omega,
          tp_rename _⟩

/-- The encoding of a product type. -/
theorem encTy_prod (off : ℕ) (a b : PartialHorn.Tree) :
    encTy off (FreeTopos.prod a b) =
      (encTy off a).bind fun A ↦ (encTy off b).map fun B ↦ prod A B := by
  rw [FreeTopos.prod, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy off a <;> cases encTy off b <;> rfl

/-- The encoding of a coproduct type. -/
theorem encTy_coprod (off : ℕ) (a b : PartialHorn.Tree) :
    encTy off (FreeTopos.coprod a b) =
      (encTy off a).bind fun A ↦ (encTy off b).map fun B ↦ coprod A B := by
  rw [FreeTopos.coprod, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy off a <;> cases encTy off b <;> rfl

/-- The encoding of an exponential type. -/
theorem encTy_exp (off : ℕ) (a b : PartialHorn.Tree) :
    encTy off (FreeTopos.exp a b) =
      (encTy off a).bind fun A ↦ (encTy off b).map fun B ↦ exp A B := by
  rw [FreeTopos.exp, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy off a <;> cases encTy off b <;> rfl

/-- The encoding of a list type. -/
theorem encTy_list (off : ℕ) (a : PartialHorn.Tree) :
    encTy off (FreeTopos.list a) = (encTy off a).map list := by
  rw [FreeTopos.list, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy off a <;> rfl

/-- The encoding of a rose-tree type of labels of a type. -/
theorem encTy_lrose (off : ℕ) (a : PartialHorn.Tree) :
    encTy off (FreeTopos.lrose a) = (encTy off a).map lrose := by
  rw [FreeTopos.lrose, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy off a <;> rfl

/-- An abstraction checks against a product when its body checks against the codomain in the
context extended by the domain. -/
theorem judge_lam {Γ : Ctx} {body a b : Expr} (h : judge sg body (a :: Γ) (.check b) = true) :
    judge sg (Expr.lam body) Γ (.check (Expr.pi a b)) = true := by
  rw [judge, Expr.lam, judgeWith_node]
  simp only [judgeStep, List.map_cons, List.map_nil, Expr.pi, RoseTree.label_node,
    RoseTree.children_node]
  exact h

/-- A term judged in the empty context, closed, is judged so in every context. -/
theorem judge_of_nil {M : Expr} {md : Mode} (h : judge sg M [] md = true) (Γ : Ctx) :
    judge sg M Γ md = true := by
  rw [← h]
  exact judgeWith_congr_ctx M Γ [] 0 md (fun _ hi ↦ absurd hi (Nat.not_lt_zero _))
    (judgeWith_freeBelow M [] md h)

/-- A term judged in a context of one type is judged so in every context extending it by that
type. -/
theorem judge_of_single {M a : Expr} {md : Mode} (h : judge sg M [a] md = true) (Γ : Ctx) :
    judge sg M (a :: Γ) md = true := by
  rw [← h]
  refine judgeWith_congr_ctx M (a :: Γ) [a] 1 md (fun i hi ↦ ?_)
    (judgeWith_freeBelow M [a] md h)
  rcases i with _ | i
  · rfl
  · exact absurd hi (by omega)

/-- An abstraction of the internal language with its bound variable's type replaced, where the
term is an abstraction: the decoding of an LF abstraction carries a placeholder type, which the
constant applied to it supplies. -/
def relam (a : PartialHorn.Tree) (s : MTerm) : Option MTerm :=
  match s.label, s.children with
    | .lam _, [b] => some (FreeTopos.Internal.Term.lam a b)
    | _, _ => none

/-- The replacement of an abstraction's type. -/
theorem relam_lam (a a' : PartialHorn.Tree) (b : MTerm) :
    relam a (FreeTopos.Internal.Term.lam a' b) = some (FreeTopos.Internal.Term.lam a b) := rfl

/-- The replacement of a term's type as an abstraction is defined exactly at the abstractions. -/
theorem relam_eq_some {a : PartialHorn.Tree} {s r : MTerm} :
    relam a s = some r ↔ ∃ a' b, s = FreeTopos.Internal.Term.lam a' b ∧
      r = FreeTopos.Internal.Term.lam a b := by
  constructor
  · intro h
    rw [← RoseTree.node_label_children s] at h ⊢
    unfold relam at h
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · next a' b heq hcs =>
      rw [heq, hcs]
      exact ⟨a', b, rfl, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨a', b, rfl, rfl⟩
    rfl

/-- The body of an abstraction of the internal language. -/
def lamBody (s : MTerm) : Option MTerm :=
  match s.label, s.children with
    | .lam _, [b] => some b
    | _, _ => none

/-- The body of an abstraction. -/
@[simp] theorem lamBody_lam (a : PartialHorn.Tree) (b : MTerm) :
    lamBody (FreeTopos.Internal.Term.lam a b) = some b := rfl

/-- The body of a term as an abstraction is defined exactly at the abstractions. -/
theorem lamBody_eq_some {s b : MTerm} :
    lamBody s = some b ↔ ∃ a, s = FreeTopos.Internal.Term.lam a b := by
  constructor
  · intro h
    rw [← RoseTree.node_label_children s] at h ⊢
    unfold lamBody at h
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · next a b' heq hcs =>
      rw [heq, hcs, ← Option.some.inj h]
      exact ⟨a, rfl⟩
    · exact absurd h (by simp)
  · rintro ⟨a, rfl⟩
    rfl

section Decoding

variable (k : PrimIdx)

/-- The decoding of an application of a constant past the signature, a definition the indices
name, from its arguments, each paired with its decoding at each offset: its first arguments, as
many as the definition's object parameters, the outermost first, are types, decoded at the
offset, and the rest terms, as many as its parameters, and the application decodes to the
definition at the decoded types, the innermost first, applied to the decoded terms, the last
first. -/
def decDefn (c : ℕ) (cs : List (Expr × (ℕ → Option MTerm))) (off : ℕ) : Option MTerm :=
  if sig.length ≤ c then match k.ext[c - sig.length]? with
    | some (.defn kd m p) => if cs.length = m + p then do
        let θ ← (cs.take m).mapM fun x ↦ decTy off x.1
        let args ← (cs.drop m).mapM fun x ↦ x.2 off
        pure (FreeTopos.Internal.Term.defn kd θ.reverse args.reverse)
      else none
    | _ => none
  else none

/-- One step of the decoding of a canonical LF term of the fragment at an offset, at a node of a
label, from its children, each paired with its decoding at each offset: the offset is the number
of variables of terms in scope, and grows by one under an LF abstraction; each constant is the
constructor of the same name, its type arguments dropped but for an abstraction's domain, which
is decoded as a type at the offset; an LF abstraction is an abstraction of a placeholder type,
which the constant of an abstraction applied to it replaces by the domain, and whose body is the
step of the fold applied to it, the body of the body for a list; zero, the successor, the empty
list and the constructions of a list and of rose trees are the primitive arrows the indices name,
the empty list, the construction of a list and that of a rose tree of labels of a type at the
decoded type; the folds of rose trees carry their decoded type. -/
def decStep (l : Label) (cs : List (Expr × (ℕ → Option MTerm))) (off : ℕ) : Option MTerm :=
  match l, cs with
    | .app (.var i), [] => some (FreeTopos.Internal.Term.var i)
    | .app (.const 7), [] => some FreeTopos.Internal.Term.star
    | .app (.const 8), [_, _, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.pair (← t off) (← u off))
    | .app (.const 9), [_, _, (_, t)] => FreeTopos.Internal.Term.fst <$> t off
    | .app (.const 10), [_, _, (_, t)] => FreeTopos.Internal.Term.snd <$> t off
    | .app (.const 11), [(A, _), _, (_, t)] => do relam (← decTy off A) (← t off)
    | .app (.const 12), [_, _, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.app (← t off) (← u off))
    | .app (.const 13), [(_, t)] => FreeTopos.Internal.Term.arr k.zero [] <$> t off
    | .app (.const 14), [(_, t)] => FreeTopos.Internal.Term.arr k.succ [] <$> t off
    | .app (.const 15), [(_, _), (_, z), (_, s), (_, m)] => do
      pure (FreeTopos.Internal.Term.natRec (← z off) (← lamBody (← s off)) (← m off))
    | .app (.const 16), [_, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.eq (← t off) (← u off))
    | .app (.const 31), [(A, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.nil [← decTy off A] (← t off))
    | .app (.const 32), [(A, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.cons [← decTy off A] (← t off))
    | .app (.const 33), [(_, _), (_, _), (_, z), (_, s), (_, m)] => do
      pure (FreeTopos.Internal.Term.listRec (← z off) (← lamBody (← lamBody (← s off)))
        (← m off))
    | .app (.const 38), [(_, t)] => FreeTopos.Internal.Term.arr k.node [] <$> t off
    | .app (.const 39), [(C, _), (_, s), (_, t)] => do
      pure (FreeTopos.Internal.Term.roseRec (← decTy off C) (← lamBody (← s off)) (← t off))
    | .app (.const 43), [(A, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.lnode [← decTy off A] (← t off))
    | .app (.const 44), [_, (C, _), (_, s), (_, t)] => do
      pure (FreeTopos.Internal.Term.roseRec (← decTy off C) (← lamBody (← s off)) (← t off))
    | .app (.const 50), [(A, _), (B, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.inl [← decTy off A, ← decTy off B] (← t off))
    | .app (.const 51), [(A, _), (B, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.inr [← decTy off A, ← decTy off B] (← t off))
    | .app (.const 52), [(A, _), (B, _), (C, _), (_, p)] => do
      pure (FreeTopos.Internal.Term.arr k.case [← decTy off A, ← decTy off B, ← decTy off C]
        (← p off))
    | .app (.const c), cs => decDefn k c cs off
    | .lam, [(_, d)] => FreeTopos.Internal.Term.lam FreeTopos.one <$> d (off + 1)
    | _, _ => none

/-- The decoding of a canonical LF term of the fragment as a term of the internal language, at the
offset of the variables of terms in scope. -/
def dec : Expr → ℕ → Option MTerm := RoseTree.para (decStep k)

/-- The computation rule of the decoding. -/
theorem dec_node (l : Label) (cs : List Expr) (off : ℕ) :
    dec k (RoseTree.node l cs) off = decStep k l (cs.map fun c ↦ (c, dec k c)) off :=
  congrFun (RoseTree.para_node _ l cs) off

/-- The step of the decoding at a constant past the signature is the decoding of a definition. -/
theorem decStep_defn {c : ℕ} (hc : sig.length ≤ c) (cs : List (Expr × (ℕ → Option MTerm)))
    (off : ℕ) : decStep k (.app (.const c)) cs off = decDefn k c cs off := by
  obtain ⟨i, rfl⟩ : ∃ i, c = i + 57 :=
    ⟨c - 57, by rw [show sig.length = 57 from rfl] at hc; omega⟩
  rfl

/-- The decodings of an application of a definition. -/
theorem decDefn_eq_some {c : ℕ} {cs : List (Expr × (ℕ → Option MTerm))} {off : ℕ}
    {s : MTerm} (h : decDefn k c cs off = some s) :
    ∃ kd m p θ args, sig.length ≤ c ∧ k.ext[c - sig.length]? = some (.defn kd m p) ∧
      cs.length = m + p ∧ (cs.take m).mapM (fun x ↦ decTy off x.1) = some θ ∧
      (cs.drop m).mapM (fun x ↦ x.2 off) = some args ∧
      s = FreeTopos.Internal.Term.defn kd θ.reverse args.reverse := by
  unfold decDefn at h
  by_cases hc : sig.length ≤ c
  · rw [ite_eq_left hc] at h
    rcases he : k.ext[c - sig.length]? with _ | ⟨_ | ⟨kd, m, p⟩ | _⟩ <;> rw [he] at h <;>
      dsimp only at h
    · exact nomatch h
    · exact nomatch h
    · by_cases hl : cs.length = m + p
      · rw [ite_eq_left hl] at h
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at h
        obtain ⟨θ, hθ, args, hargs, rfl⟩ := h
        exact ⟨kd, m, p, θ, args, hc, rfl, hl, hθ, hargs, rfl⟩
      · rw [ite_eq_right hl] at h
        exact nomatch h
    · exact nomatch h
  · rw [ite_eq_right hc] at h
    exact nomatch h

/-- The decoding of an application of a definition, from its parts. -/
theorem decDefn_of {c kd m p : ℕ} {cs : List (Expr × (ℕ → Option MTerm))} {off : ℕ}
    {θ : List PartialHorn.Tree} {args : List MTerm} (hc : sig.length ≤ c)
    (he : k.ext[c - sig.length]? = some (.defn kd m p)) (hl : cs.length = m + p)
    (hθ : (cs.take m).mapM (fun x ↦ decTy off x.1) = some θ)
    (hargs : (cs.drop m).mapM (fun x ↦ x.2 off) = some args) :
    decDefn k c cs off = some (FreeTopos.Internal.Term.defn kd θ.reverse args.reverse) := by
  unfold decDefn
  rw [ite_eq_left hc, he]
  simp only [ite_eq_left hl, hθ, hargs, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

end Decoding

/-- A partial function's values on a list carry over, element by element, to another's values on
the list's image. -/
theorem mapM_transfer {α β γ δ : Type} {f : α → Option β} {g : γ → Option δ} {h : α → γ}
    {r : β → δ} : ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → g (h x) = some (r y)) →
      (xs.map h).mapM g = some (ys.map r) := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List β}, xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → g (h x) = some (r y)) →
      (xs.map h).mapM g = some (ys.map r))
    (fun {ys} hm _ ↦ by obtain rfl := Option.some.inj hm.symm; rfl) (fun x xs ih {ys} hm hx ↦ ?_) xs
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨y, hy, ys', hys', rfl⟩ := hm
  rw [List.map_cons, List.mapM_cons, hx x List.mem_cons_self y hy,
    ih hys' fun x' hx' ↦ hx x' (List.mem_cons_of_mem _ hx')]
  rfl

/-- A list of the values of a partial function on a list is as long as the list. -/
theorem length_of_mapM {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  have := congrArg List.length ((PartialHorn.mapM_eq_some_iff xs ys).mp h)
  rw [List.length_map, List.length_map] at this
  exact this.symm

/-- A partial function's values on a list are undone by another, element by element, where the
other undoes it. -/
theorem mapM_inverse {α β : Type} {f : α → Option β} {g : β → Option α} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → g y = some x) → ys.mapM g = some xs := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List β}, xs.mapM f = some ys →
      (∀ x ∈ xs, ∀ y, f x = some y → g y = some x) → ys.mapM g = some xs)
    (fun {ys} hm _ ↦ by obtain rfl := Option.some.inj hm.symm; rfl) (fun x xs ih {ys} hm hx ↦ ?_) xs
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨y, hy, ys', hys', rfl⟩ := hm
  rw [List.mapM_cons, hx x List.mem_cons_self y hy,
    ih hys' fun x' hx' ↦ hx x' (List.mem_cons_of_mem _ hx')]
  rfl

/-- A partial function's values on a list carry over, position by position, to another's values on
a list as long. -/
theorem mapM_transfer_idx {α β γ δ : Type} {f : α → Option β} {g : γ → Option δ} {r : β → δ} :
    ∀ {xs : List α} {ys : List γ} {zs : List β}, xs.mapM f = some zs → ys.length = xs.length →
      (∀ (i : ℕ) (x : α) (y : γ) (z : β), xs[i]? = some x → ys[i]? = some y → f x = some z →
        g y = some (r z)) →
      ys.mapM g = some (zs.map r) := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List γ} {zs : List β}, xs.mapM f = some zs →
      ys.length = xs.length →
      (∀ (i : ℕ) (x : α) (y : γ) (z : β), xs[i]? = some x → ys[i]? = some y → f x = some z →
        g y = some (r z)) →
      ys.mapM g = some (zs.map r))
    (fun {ys zs} hm hl _ ↦ by
      obtain rfl := Option.some.inj hm.symm
      obtain rfl := List.length_eq_zero_iff.mp hl
      rfl) (fun x xs ih {ys zs} hm hl hx ↦ ?_) xs
  rcases ys with _ | ⟨y, ys⟩
  · exact Nat.noConfusion hl
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hm
  obtain ⟨z, hz, zs', hzs', rfl⟩ := hm
  rw [List.mapM_cons, hx 0 x y z rfl rfl hz,
    ih hzs' (Nat.succ.inj hl) fun i x' y' z' h₁ h₂ h₃ ↦ hx (i + 1) x' y' z' h₁ h₂ h₃]
  rfl

/-- The decoding of an application of a definition carries over to an application of the same
constant to arguments related position by position: the type arguments by a function of their
decodings, the term arguments by another. -/
theorem decDefn_transfer {c off off' : ℕ} {xs ys : List Expr} {s : MTerm}
    {fT : PartialHorn.Tree → PartialHorn.Tree} {fM : MTerm → MTerm}
    (h : decDefn k c (xs.map fun x ↦ (x, dec k x)) off = some s) (hlen : ys.length = xs.length)
    (hfin : ∀ kd m p, k.ext[c - sig.length]? = some (.defn kd m p) →
      (∀ i x y a, i < m → xs[i]? = some x → ys[i]? = some y → decTy off x = some a →
        decTy off' y = some (fT a)) ∧
      (∀ i x y u, m ≤ i → xs[i]? = some x → ys[i]? = some y → dec k x off = some u →
        dec k y off' = some (fM u))) :
    ∃ (kd : ℕ) (θ : List PartialHorn.Tree) (args : List MTerm),
      s = FreeTopos.Internal.Term.defn kd θ.reverse args.reverse ∧
      decDefn k c (ys.map fun y ↦ (y, dec k y)) off' =
        some (FreeTopos.Internal.Term.defn kd (θ.map fT).reverse (args.map fM).reverse) := by
  obtain ⟨kd, m, p, θ, args, hc, he, hl, hθ, hargs, rfl⟩ := decDefn_eq_some k h
  obtain ⟨hT, hM⟩ := hfin kd m p he
  rw [List.length_map] at hl
  refine ⟨kd, θ, args, rfl, decDefn_of k hc he (by rw [List.length_map, hlen, hl]) ?_ ?_⟩
  · rw [← List.map_take, List.mapM_map] at hθ ⊢
    refine mapM_transfer_idx hθ (by rw [List.length_take, List.length_take, hlen])
      fun i x y z h₁ h₂ h₃ ↦ ?_
    have hi : i < m := by
      have := (List.getElem?_eq_some_iff.mp h₁).1
      rw [List.length_take] at this
      omega
    rw [List.getElem?_take_of_lt hi] at h₁ h₂
    exact hT i x y z hi h₁ h₂ h₃
  · rw [← List.map_drop, List.mapM_map] at hargs ⊢
    refine mapM_transfer_idx hargs (by rw [List.length_drop, List.length_drop, hlen])
      fun i x y z h₁ h₂ h₃ ↦ ?_
    rw [List.getElem?_drop] at h₁ h₂
    exact hM (m + i) x y z (by omega) h₁ h₂ h₃

/-- The environment extended by a variable has one more variable. -/
@[simp] theorem length_extEnv (X a : PartialHorn.Tree) (e : MEnv) :
    (FreeTopos.Internal.extEnv X a e).length = e.length + 1 := by
  simp [FreeTopos.Internal.extEnv]

/-- Decoding inverts encoding. -/
theorem dec_enc {G : FreeTopos.Internal.Globals} {n : ℕ} {k : PrimIdx} :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (M : Expr), enc G n k s X e = some M →
      dec k M e.length = some s :=
  RoseTree.ind fun l cs ih X e M henc ↦ by
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨j, θ⟩ | _ | _ | c | ⟨j, θ⟩ | _
    · rcases cs with _ | ⟨d, cs⟩
      · simp only [encStep, List.map_nil, Option.some.injEq] at henc
        subst henc
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨d, cs⟩
      · simp only [encStep, List.map_nil, Option.some.injEq] at henc
        subst henc
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, a, -, -, b, -, A, -, B, -, Mt, hMt, Mu, hMu, rfl⟩ := henc
        rw [pair, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
          ih u (by simp) X e Mu hMu]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, p, -, a, b, -, A, -, B, -, Mt, hMt, rfl⟩ := henc
        rw [fst, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, p, -, a, b, -, A, -, B, -, Mt, hMt, rfl⟩ := henc
        rw [snd, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, b, -, A, hA, B, -, Mb, hMb, rfl⟩ := henc
        have hMb' := ih t (by simp) _ _ Mb hMb
        simp only [length_extEnv] at hMb'
        rw [lam, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
          hMb', decTy_encTy _ a A hA]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, p, -, a, b, -, A, -, B, -, Mt, hMt, Mu, hMu, rfl⟩ := henc
        rw [app, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
          ih u (by simp) X e Mu hMu]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · rcases θ with _ | ⟨θ₀, _ | ⟨θ₁, θ⟩⟩
        · by_cases hkz : j = k.zero
          · subst hkz
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.map_eq_map,
              Option.map_eq_some_iff] at henc
            obtain ⟨Mt, hMt, rfl⟩ := henc
            rw [zeroAt, Expr.const, Expr.app, dec_node]
            simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
            rfl
          · by_cases hks : j = k.succ
            · subst hks
              simp only [encStep, List.map_cons, List.map_nil, hkz, ↓reduceIte,
                Option.map_eq_map, Option.map_eq_some_iff] at henc
              obtain ⟨Mt, hMt, rfl⟩ := henc
              rw [succ, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
              rfl
            · by_cases hkd : j = k.node
              · subst hkd
                simp only [encStep, List.map_cons, List.map_nil, hkz, hks, ↓reduceIte,
                  Option.map_eq_map, Option.map_eq_some_iff] at henc
                obtain ⟨Mt, hMt, rfl⟩ := henc
                rw [node, Expr.const, Expr.app, dec_node]
                simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
                rfl
              · simp [encStep, hkz, hks, hkd] at henc
        · by_cases hkn : j = k.nil
          · subst hkn
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
            rw [nilAt, Expr.const, Expr.app, dec_node]
            simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
              decTy_encTy _ θ₀ A hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
            rfl
          · by_cases hkc : j = k.cons
            · subst hkc
              simp only [encStep, List.map_cons, List.map_nil, hkn, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
              rw [cons, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                decTy_encTy _ θ₀ A hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
              rfl
            · by_cases hkl : j = k.lnode
              · subst hkl
                simp only [encStep, List.map_cons, List.map_nil, hkn, hkc, ↓reduceIte,
                  Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                  Option.some.injEq] at henc
                obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
                rw [lnode, Expr.const, Expr.app, dec_node]
                simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                  decTy_encTy _ θ₀ A hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
                rfl
              · simp [encStep, hkn, hkc, hkl] at henc
        · rcases θ with _ | ⟨θ₂, _ | ⟨θ₃, θ⟩⟩
          · by_cases hkl : j = k.inl
            · subst hkl
              simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
                Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
              obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
              rw [inl, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                decTy_encTy _ θ₀ A hA, decTy_encTy _ θ₁ B hB, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def]
              rfl
            · by_cases hkr : j = k.inr
              · subst hkr
                simp only [encStep, List.map_cons, List.map_nil, hkl, ↓reduceIte,
                  Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                  Option.some.injEq] at henc
                obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
                rw [inr, Expr.const, Expr.app, dec_node]
                simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                  decTy_encTy _ θ₀ A hA, decTy_encTy _ θ₁ B hB, Option.bind_eq_bind,
                  Option.bind_some, Option.pure_def]
                rfl
              · simp [encStep, hkl, hkr] at henc
          · by_cases hkc : j = k.case
            · subst hkc
              simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
                Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
              obtain ⟨A, hA, B, hB, C, hC, Mt, hMt, rfl⟩ := henc
              rw [case, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                decTy_encTy _ θ₀ A hA, decTy_encTy _ θ₁ B hB, decTy_encTy _ θ₂ C hC,
                Option.bind_eq_bind, Option.bind_some, Option.pure_def]
              rfl
            · simp [encStep, hkc] at henc
          · simp [encStep] at henc
      · simp [encStep] at henc
    · rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, c, -, C, -, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hMs' := ih s (by simp) _ _ Ms hMs
        simp only [length_extEnv] at hMs'
        rw [natRec, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
          ih z (by simp) X e Mz hMz, hMs', ih m (by simp) X e Mm hMm]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, c, -, -, t, -, a, -, -, -, -, -, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hMs' := ih s (by simp) _ _ Ms hMs
        simp only [length_extEnv] at hMs'
        rw [listRec, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
          ih z (by simp) X e Mz hMz, hMs', ih m (by simp) X e Mm hMm,
          Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
          Option.pure_def]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Prod.exists] at henc
        obtain ⟨_, t, _, henc⟩ := henc
        split at henc
        · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
          have hMs' := ih s (by simp) _ _ Ms hMs
          simp only [length_extEnv] at hMs'
          rw [roseRec, Expr.const, Expr.app, dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
            decTy_encTy _ c C hC, hMs', ih m (by simp) X e Mm hMm,
            Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some,
            Option.map_eq_map, Option.pure_def]
          rfl
        · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨A, -, C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
          have hMs' := ih s (by simp) _ _ Ms hMs
          simp only [length_extEnv] at hMs'
          rw [lroseRec, Expr.const, Expr.app, dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
            decTy_encTy _ c C hC, hMs', ih m (by simp) X e Mm hMm,
            Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some,
            Option.map_eq_map, Option.pure_def]
          rfl
        · simp at henc
      · simp [encStep] at henc
    · simp only [encStep, Option.bind_eq_bind] at henc
      obtain ⟨d, -, henc⟩ := Option.bind_eq_some_iff.mp henc
      obtain ⟨c, hc, henc⟩ := Option.bind_eq_some_iff.mp henc
      by_cases hl : θ.length = d.arity ∧
          (cs.map fun c ↦ (c, enc G n k c)).length = d.params.length
      · rw [ite_eq_left hl] at henc
        obtain ⟨Ts, hTs, henc⟩ := Option.bind_eq_some_iff.mp henc
        obtain ⟨Ms, hMs, henc⟩ := Option.bind_eq_some_iff.mp henc
        obtain rfl := Option.some.inj henc
        obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hc
        have hext := ExtConst.find?_spec _ _ _ hi
        have hTl : Ts.length = d.arity := by
          rw [← hl.1, length_of_mapM hTs, List.length_reverse]
        rw [Expr.const, Expr.app, dec_node, decStep_defn _ (by omega)]
        rw [decDefn_of k (m := d.arity) (p := d.params.length) (θ := θ.reverse) (args := cs.reverse)
          (by omega) (by rw [Nat.add_sub_cancel_left]; exact hext)
          (by rw [List.length_map, List.length_append, hTl, ← hl.2, length_of_mapM hMs,
            List.length_reverse])
          (by
            rw [← List.map_take, List.take_left' hTl, List.mapM_map]
            exact mapM_inverse hTs fun a _ A hA ↦ decTy_encTy _ a A hA)
          (by
            rw [← List.map_drop, List.drop_left' hTl, List.mapM_map]
            rw [← List.map_reverse, List.mapM_map] at hMs
            exact mapM_inverse hMs fun x hx M hM ↦ ih x (List.mem_reverse.mp hx) X e M hM),
          List.reverse_reverse, List.reverse_reverse]
        rfl
      · rw [ite_eq_right hl] at henc
        exact nomatch henc
    · rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, a, -, A, -, Mt, hMt, Mu, hMu, rfl⟩ := henc
        rw [eq, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
          ih u (by simp) X e Mu hMu]
        rfl
      · simp [encStep] at henc

/-- Two nodes are equal exactly when their labels and children are. -/
theorem node_inj {l l' : Label} {cs cs' : List Expr} :
    (RoseTree.node l cs : Expr) = RoseTree.node l' cs' ↔ l = l' ∧ cs = cs' := by
  rw [RoseTree.node_eq_iff, RoseTree.label_node, RoseTree.children_node]

/-- The signature is formed. -/
theorem sig_ok : sig.ok = true := by decide +kernel

/-- The declarations whose types end in {lit}`tp` are the object types, of indices 1 to 5, of
index 30, of index 37, of index 42, and of indices 48 and 49. -/
theorem sig_head_tp₀ {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 0) :
    c ∈ [1, 2, 3, 4, 5, 30, 37, 42, 48, 49] := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 0) ||
      decide (p.2 ∈ [1, 2, 3, 4, 5, 30, 37, 42, 48, 49])) = true := by decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- The declarations whose types end in {lit}`tm` are the term constructors, of indices from 7
to 16, from 31 to 33, 38 and 39, 43 and 44, and from 50 to 52. -/
theorem sig_head_tm₀ {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 6) :
    c ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 31, 32, 33, 38, 39, 43, 44, 50, 51, 52] := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 6) ||
      decide (p.2 ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 31, 32, 33, 38, 39, 43, 44, 50, 51,
        52])) = true := by
    decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- The declarations of an extension of the signature whose types end in {lit}`tp` are the
signature's object types. -/
theorem sig_head_tp (hsg : SigExt G k sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
    (h : T.headDepth.1 = some 0) : c ∈ [1, 2, 3, 4, 5, 30, 37, 42, 48, 49] ∧ sig[c]? = some T := by
  by_cases hlt : c < sig.length
  · have hc' := hsg.of_lt hc hlt
    exact ⟨sig_head_tp₀ hc' h, hc'⟩
  · exact absurd h (hsg.noTp c T (Nat.le_of_not_lt hlt) hc)

/-- The declarations of an extension of the signature, within the signature, whose types end in
{lit}`tm` are the signature's term constructors. -/
theorem sig_head_tm (hsg : SigExt G k sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
    (h : T.headDepth.1 = some 6) (hlt : c < sig.length) :
    c ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 31, 32, 33, 38, 39, 43, 44, 50, 51, 52] ∧
      sig[c]? = some T := by
  have hc' := hsg.of_lt hc hlt
  exact ⟨sig_head_tm₀ hc' h, hc'⟩

/-- The signature extends itself, with indices declaring no further constants. -/
theorem sigExt_sig (hk : k.ext = []) : SigExt G k sig where
  ok := sig_ok
  pre := List.prefix_refl _
  len := by rw [hk, List.length_nil, Nat.add_zero]
  noTp _ _ hle hc := absurd (List.getElem?_eq_some_iff.mp hc).1 (Nat.not_lt_of_le hle)
  defs i _ _ _ h := by rw [hk] at h; exact absurd h (by simp)
  tmDefs i _ hc _ := absurd (List.getElem?_eq_some_iff.mp hc).1 (by omega)

/-- The inversion of the check of an application against an atomic type: the head's classifier
instantiates along the spine to it. -/
theorem judge_app_inv {Γ : Ctx} {h : Head} {ms : List Expr} {P : Expr}
    (hj : judge sg (Expr.app h ms) Γ (.check P) = true) :
    ∃ C, classOf sg Γ h = some C ∧ spine Γ C (ms.map fun m ↦ (m, judge sg m)) = some P := by
  rw [judge, Expr.app, judgeWith_node] at hj
  simp only [judgeStep, Bool.and_eq_true] at hj
  obtain ⟨-, hm⟩ := hj
  rcases hC : classOf sg Γ h with _ | C
  · rw [hC] at hm
    simp at hm
  · rw [hC, Option.bind_some] at hm
    rcases hS : spine Γ C (ms.map fun c ↦ (c, judgeWith (· == ·) sg c)) with _ | P'
    · rw [hS] at hm
      simp at hm
    · rw [hS] at hm
      simp only [beq_iff_eq] at hm
      subst hm
      exact ⟨C, rfl, hS⟩

/-- The checks against atomic types are of applications. -/
theorem judge_atomic_app {Γ : Ctx} {M P : Expr} (hP : IsApp P = true)
    (hj : judge sg M Γ (.check P) = true) : ∃ h ms, M = Expr.app h ms := by
  obtain ⟨l, cs, rfl⟩ := exists_node M
  rw [judge, judgeWith_node] at hj
  rcases l with _ | _ | _ | h
  · simp [judgeStep] at hj
  · simp [judgeStep] at hj
  · obtain ⟨pl, pcs, rfl⟩ := exists_node P
    rcases pl with _ | _ | _ | _ <;> simp [IsApp] at hP
    rcases cs with _ | ⟨m, _ | ⟨d, cs⟩⟩ <;> simp [judgeStep] at hj
  · exact ⟨h, cs, rfl⟩

/-- Every canonical term of {lit}`tp`, in a context whose variables of types ending in
{lit}`tp` are of {lit}`tp` itself, past an offset and fewer than {lit}`n` past it, is the
encoding at the offset of a type in {lit}`n` object variables. -/
theorem tyComplete {G' : FreeTopos.Internal.Globals} (hsg : SigExt G' k sg)
    (G : FreeTopos.Internal.Globals) {Γ : Ctx} {off n : ℕ}
    (hΓ : ∀ i t, varType Γ i = some t →
      t.TypeShape = true ∧ (t.headDepth.1 = some 0 → t = tp ∧ off ≤ i ∧ i < off + n)) :
    ∀ A : Expr, judge sg A Γ (.check tp) = true →
      ∃ a, encTy off a = some A ∧ FreeTopos.Internal.IsTy G n a = true :=
  RoseTree.ind fun l cs ih hj ↦ by
    obtain ⟨h, ms, hA⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hA
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    rcases h with i | c
    · obtain ⟨hCs, hCh⟩ := hΓ i C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C tp hCs hS
      obtain ⟨rfl, hi, hin⟩ := hCh (by rw [← h₁]; rfl)
      have hlen : cs.length = 0 := by
        rw [show tp.headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      obtain rfl := List.length_eq_zero_iff.mp hlen
      exact ⟨PartialHorn.var (i - off), by rw [encTy_var, Nat.add_sub_cancel' hi]; rfl,
        FreeTopos.Internal.isTy_var.mpr (by omega)⟩
    · have hCs := Sig.ok_typeShape hsg.ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C tp hCs hS
      obtain ⟨hc, hC⟩ := sig_head_tp hsg hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show tp.headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.one, rfl, FreeTopos.Internal.isTy_one⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl :
          some C = some (Expr.arrow tp (Expr.arrow tp tp)))
        obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha, hIa⟩ := ih x (by simp) hS.1
        obtain ⟨b, hb, hIb⟩ := ih y (by simp) hS.2
        exact ⟨FreeTopos.prod a b, by rw [encTy_prod, ha, hb]; rfl,
          by rw [FreeTopos.Internal.isTy_prod, hIa, hIb]; rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl :
          some C = some (Expr.arrow tp (Expr.arrow tp tp)))
        obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha, hIa⟩ := ih x (by simp) hS.1
        obtain ⟨b, hb, hIb⟩ := ih y (by simp) hS.2
        exact ⟨FreeTopos.exp a b, by rw [encTy_exp, ha, hb]; rfl,
          by rw [FreeTopos.Internal.isTy_exp, hIa, hIb]; rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.omega, rfl, FreeTopos.Internal.isTy_omega⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.nat, rfl, FreeTopos.Internal.isTy_nat⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.arrow tp tp))
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha, hIa⟩ := ih x (by simp) hS
        exact ⟨FreeTopos.list a, by rw [encTy_list, ha]; rfl,
          by rw [FreeTopos.Internal.isTy_list, hIa]⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.rose, rfl, FreeTopos.Internal.isTy_rose⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.arrow tp tp))
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha, hIa⟩ := ih x (by simp) hS
        exact ⟨FreeTopos.lrose a, by rw [encTy_lrose, ha]; rfl,
          by rw [FreeTopos.Internal.isTy_lrose, hIa]⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl :
          some C = some (Expr.arrow tp (Expr.arrow tp tp)))
        obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha, hIa⟩ := ih x (by simp) hS.1
        obtain ⟨b, hb, hIb⟩ := ih y (by simp) hS.2
        exact ⟨FreeTopos.coprod a b, by rw [encTy_coprod, ha, hb]; rfl,
          by rw [FreeTopos.Internal.isTy_coprod, hIa, hIb]; rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.zero, rfl, FreeTopos.Internal.isTy_zero⟩

/-- The first step of a spine whose classifier is a product: the first argument checks against
the domain, and the rest instantiates the substituted codomain. -/
theorem spine_cons_inv {Γ : Ctx} {a b m : Expr} {J : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi a b) ((m, J) :: ms) = some P) :
    J Γ (.check a) = true ∧ ∃ b', hsub (Expr.erase a) m b 0 = some b' ∧ spine Γ b' ms = some P := by
  simp only [spine, List.foldlM_cons] at h
  obtain ⟨b', hb', hr⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.pi, RoseTree.label_node, RoseTree.children_node] at hb'
  simp only at hb'
  split_ifs at hb' with hJ
  exact ⟨hJ, b', hb', hr⟩

/-- The leading arguments of a spine of a classifier that begins with two products over
{lit}`tp` check against {lit}`tp`. -/
theorem spine_tp₂ {Γ : Ctx} {X A B : Expr} {JA JB : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi tp (Expr.pi tp X)) ((A, JA) :: (B, JB) :: ms) = some P) :
    JA Γ (.check tp) = true ∧ JB Γ (.check tp) = true := by
  obtain ⟨hA, b', hb', h⟩ := spine_cons_inv h
  obtain ⟨tp', X', htp, -, rfl⟩ := hsub_pi _ _ _ _ _ _ hb'
  rw [hsub_eq, hsubWith_closed (show tp.FreeBelow 0 = true from rfl), Option.some.injEq] at htp
  subst htp
  exact ⟨hA, (spine_cons_inv h).1⟩

/-- The leading arguments of a spine of a classifier that begins with three products over
{lit}`tp` check against {lit}`tp`. -/
theorem spine_tp₃ {Γ : Ctx} {X A B C : Expr} {JA JB JC : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi tp (Expr.pi tp (Expr.pi tp X))) ((A, JA) :: (B, JB) :: (C, JC) :: ms) =
      some P) :
    JA Γ (.check tp) = true ∧ JB Γ (.check tp) = true ∧ JC Γ (.check tp) = true := by
  obtain ⟨hA, b', hb', h⟩ := spine_cons_inv h
  obtain ⟨tp', X', htp, hX, rfl⟩ := hsub_pi _ _ _ _ _ _ hb'
  rw [hsub_eq, hsubWith_closed (show tp.FreeBelow 0 = true from rfl), Option.some.injEq] at htp
  subst htp
  obtain ⟨tp'', X'', htp', -, rfl⟩ := hsub_pi _ _ _ _ _ _ hX
  rw [hsub_eq, hsubWith_closed (show tp.FreeBelow 0 = true from rfl), Option.some.injEq] at htp'
  subst htp'
  exact ⟨hA, spine_tp₂ h⟩

/-- The leading argument of a spine of a classifier that begins with a product over {lit}`tp`
checks against {lit}`tp`. -/
theorem spine_tp₁ {Γ : Ctx} {X A : Expr} {JA : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi tp X) ((A, JA) :: ms) = some P) : JA Γ (.check tp) = true :=
  (spine_cons_inv h).1

/-- A variable of an encoded environment's type has an arrow and that type. -/
theorem env_of_map_snd {e : MEnv} {i : ℕ} {a : PartialHorn.Tree}
    (h : (e.map Prod.snd)[i]? = some a) : ∃ f, e[i]? = some (f, a) := by
  rw [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨f, a'⟩, hf, rfl⟩ := h
  exact ⟨f, hf⟩

/-- The encoding of a context in {lit}`n` object variables has as many variables as the context
and {lit}`n` more. -/
theorem length_encCtx {n : ℕ} {Γ : List PartialHorn.Tree} {ΓLF : Ctx} (h : encCtx n Γ = some ΓLF) :
    ΓLF.length = Γ.length + n := by
  refine List.rec (motive := fun Γ ↦ ∀ (ΓLF : Ctx), encCtx n Γ = some ΓLF →
    ΓLF.length = Γ.length + n) (fun ΓLF h ↦ ?_) (fun b Γ ih ΓLF h ↦ ?_) Γ ΓLF h
  · obtain rfl := Option.some.inj h
    simp
  · obtain ⟨B, ΓLF', -, hΓ, rfl⟩ := encCtx_cons_inv h
    rw [List.length_cons, ih ΓLF' hΓ, List.length_cons]
    omega

/-- The types of the variables of an encoded context have the shape of types, and those ending in
{lit}`tp` are {lit}`tp` and past the variables of terms. -/
theorem encCtx_heads₀ {n : ℕ} {Γ : List PartialHorn.Tree} {ΓLF : Ctx}
    (h : encCtx n Γ = some ΓLF) :
    ∀ i t, varType ΓLF i = some t → t.TypeShape = true ∧
      (t.headDepth.1 = some 0 → t = tp ∧ Γ.length ≤ i ∧ i < Γ.length + n) := by
  intro i t ht
  rcases varType_encCtx_inv h ht with ⟨a, A, -, -, rfl⟩ | ⟨hi, hin, rfl⟩
  · exact ⟨rfl, fun h ↦ absurd (Option.some.inj (h.symm.trans rfl : some 0 = some 6)) (by decide)⟩
  · exact ⟨rfl, fun _ ↦ ⟨rfl, hi, hin⟩⟩

/-- The encoded types whose encodings at an offset mention no variable past the offset by
{lit}`n` or more are types of the internal language in {lit}`n` object variables, built from
operations of {name}`Geb.FreeTopos.Internal.tyOps`. -/
theorem isTy_of_encTy (G : FreeTopos.Internal.Globals) {n : ℕ} :
    ∀ (a : PartialHorn.Tree) (off : ℕ) (A : Expr), encTy off a = some A →
      A.FreeBelow (off + n) = true → FreeTopos.Internal.IsTy G n a = true :=
  RoseTree.ind fun l cs ih off A h hA ↦ by
    have hch : ∀ (idx : ℕ) (h : idx < A.children.length),
        Expr.FreeBelow A.children[idx] (off + n) = true := fun idx hidx ↦ by
      have := (freeBelow_node_iff.mp (by rw [RoseTree.node_label_children]; exact hA)).2 idx hidx
      rwa [show A.label.binders idx = 0 by
        rcases encTy_node_eq_some h with ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ |
          ⟨-, -, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ |
          ⟨-, -, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, rfl⟩ <;> rfl] at this
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩
    · have := (freeBelow_node_iff.mp hA).1 (off + i) rfl
      exact FreeTopos.Internal.isTy_var.mpr (by omega)
    · exact FreeTopos.Internal.isTy_one
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_eq_two hcs
      rw [show RoseTree.node 7 [c₁, c₂] = FreeTopos.prod c₁ c₂ from rfl,
        FreeTopos.Internal.isTy_prod, ih c₁ (by simp) off a h₁ (hch 0 Nat.zero_lt_two),
        ih c₂ (by simp) off b h₂ (hch 1 Nat.one_lt_two)]
      rfl
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_eq_two hcs
      rw [show RoseTree.node 23 [c₁, c₂] = FreeTopos.exp c₁ c₂ from rfl,
        FreeTopos.Internal.isTy_exp, ih c₁ (by simp) off a h₁ (hch 0 Nat.zero_lt_two),
        ih c₂ (by simp) off b h₂ (hch 1 Nat.one_lt_two)]
      rfl
    · exact FreeTopos.Internal.isTy_omega
    · exact FreeTopos.Internal.isTy_nat
    · obtain ⟨c₁, rfl, h₁⟩ := map_eq_one hcs
      rw [show RoseTree.node 34 [c₁] = FreeTopos.list c₁ from rfl, FreeTopos.Internal.isTy_list]
      exact ih c₁ (by simp) off a h₁ (hch 0 Nat.zero_lt_one)
    · exact FreeTopos.Internal.isTy_rose
    · obtain ⟨c₁, rfl, h₁⟩ := map_eq_one hcs
      rw [show RoseTree.node 41 [c₁] = FreeTopos.lrose c₁ from rfl, FreeTopos.Internal.isTy_lrose]
      exact ih c₁ (by simp) off a h₁ (hch 0 Nat.zero_lt_one)
    · exact FreeTopos.Internal.isTy_zero
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_eq_two hcs
      rw [show RoseTree.node 16 [c₁, c₂] = FreeTopos.coprod c₁ c₂ from rfl,
        FreeTopos.Internal.isTy_coprod, ih c₁ (by simp) off a h₁ (hch 0 Nat.zero_lt_two),
        ih c₂ (by simp) off b h₂ (hch 1 Nat.one_lt_two)]
      rfl

/-- An encoded type that checks against {lit}`tp` in the encoding of a context in {lit}`n`
object variables, at the offset of the context's variables of terms, is a type in {lit}`n`
object variables. -/
theorem isTy_of_judge (G : FreeTopos.Internal.Globals) {n : ℕ} {Γ : List PartialHorn.Tree}
    {ΓLF : Ctx} (hΓ : encCtx n Γ = some ΓLF) {a : PartialHorn.Tree} {A : Expr}
    (ha : encTy Γ.length a = some A) (hj : judge sg A ΓLF (.check tp) = true) :
    FreeTopos.Internal.IsTy G n a = true := by
  refine isTy_of_encTy G a _ A ha ?_
  rw [← length_encCtx hΓ]
  exact judgeWith_freeBelow A ΓLF _ hj

/-- The inversion of the judgment of the encoding of a pair of a term and an abstraction: the
term checks against the first factor, the abstraction's body against the product of families of
terms its types name, and the pair's type is the product of the two, the second the exponential
of the abstraction's types. -/
theorem judge_pair_lam_inv (hsg : SigExt G k sg) {Γ : Ctx} {A B Mz C B' Mf T : Expr}
    (h : judge sg (pair A B Mz (lam C B' Mf)) Γ (.check (tm T)) = true) :
    judge sg Mz Γ (.check (tm A)) = true ∧
      judge sg Mf Γ (.check (Expr.arrow (tm C) (tm B'))) = true ∧ T = prod A B ∧
        B = exp C B' := by
  obtain ⟨C₈, hC₈, hS⟩ := judge_app_inv h
  obtain rfl := Option.some.inj (hC₈.symm.trans (hsg.get rfl) :
    some C₈ = some (Expr.pi tp (Expr.pi tp
    (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (prod (v 1) (v 0))))))))
  simp only [List.map_cons, List.map_nil] at hS
  simp only [tm, tp, prod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, hz, hl, hT⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hT
  obtain ⟨C₁₁, hC₁₁, hS'⟩ := judge_app_inv hl
  obtain rfl := Option.some.inj (hC₁₁.symm.trans (hsg.get rfl) :
    some C₁₁ = some (Expr.pi tp (Expr.pi tp
    (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0))) (tm (exp (v 1) (v 0)))))))
  simp only [List.map_cons, List.map_nil] at hS'
  simp only [tm, tp, exp, Expr.const, Expr.app] at hS'
  lf_spine_at hS' [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, hf, hB⟩ := hS'
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hB
  exact ⟨hz, hf, hT.symm, hB.symm⟩

/-- The empty list's domain at an element type is the terminal object. -/
theorem subst_nilPrim_dom (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.nilPrim.dom = FreeTopos.one := by
  simp [FreeTopos.Internal.nilPrim, FreeTopos.one, FreeTopos.subst_op]

/-- The empty list's codomain at an element type is the list type. -/
theorem subst_nilPrim_cod (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.nilPrim.cod = FreeTopos.list a := by
  simp [FreeTopos.Internal.nilPrim, FreeTopos.subst_list, FreeTopos.subst_x]

/-- The construction's domain at an element type is the product of the element type and the list
type. -/
theorem subst_consPrim_dom (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.consPrim.dom =
      FreeTopos.prod a (FreeTopos.list a) := by
  simp [FreeTopos.Internal.consPrim, FreeTopos.subst_prod, FreeTopos.subst_list,
    FreeTopos.subst_x]

/-- The construction's codomain at an element type is the list type. -/
theorem subst_consPrim_cod (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.consPrim.cod = FreeTopos.list a := by
  simp [FreeTopos.Internal.consPrim, FreeTopos.subst_list, FreeTopos.subst_x]

/-- The domain of the left injection at two types. -/
theorem subst_inlPrim_dom (a b : PartialHorn.Tree) :
    PartialHorn.subst [a, b] FreeTopos.Internal.inlPrim.dom = a :=
  rfl

/-- The codomain of the left injection at two types. -/
theorem subst_inlPrim_cod (a b : PartialHorn.Tree) :
    PartialHorn.subst [a, b] FreeTopos.Internal.inlPrim.cod = FreeTopos.coprod a b :=
  rfl

/-- The domain of the right injection at two types. -/
theorem subst_inrPrim_dom (a b : PartialHorn.Tree) :
    PartialHorn.subst [a, b] FreeTopos.Internal.inrPrim.dom = b :=
  rfl

/-- The codomain of the right injection at two types. -/
theorem subst_inrPrim_cod (a b : PartialHorn.Tree) :
    PartialHorn.subst [a, b] FreeTopos.Internal.inrPrim.cod = FreeTopos.coprod a b :=
  rfl

/-- The domain of the case analysis at three types. -/
theorem subst_casePrim_dom (a b c : PartialHorn.Tree) :
    PartialHorn.subst [a, b, c] FreeTopos.Internal.casePrim.dom =
      FreeTopos.prod (FreeTopos.exp a c) (FreeTopos.exp b c) :=
  rfl

/-- The codomain of the case analysis at three types. -/
theorem subst_casePrim_cod (a b c : PartialHorn.Tree) :
    PartialHorn.subst [a, b, c] FreeTopos.Internal.casePrim.cod =
      FreeTopos.exp (FreeTopos.coprod a b) c :=
  rfl

/-- The domain of the construction of a rose tree of labels of a type at a type. -/
theorem subst_lnodePrim_dom (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.lnodePrim.dom =
      FreeTopos.prod a (FreeTopos.list (FreeTopos.lrose a)) := by
  simp [FreeTopos.Internal.lnodePrim, FreeTopos.subst_prod, FreeTopos.subst_list,
    FreeTopos.subst_lrose, FreeTopos.subst_x]

/-- The codomain of the construction of a rose tree of labels of a type at a type. -/
theorem subst_lnodePrim_cod (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.lnodePrim.cod = FreeTopos.lrose a := by
  simp [FreeTopos.Internal.lnodePrim, FreeTopos.subst_lrose, FreeTopos.subst_x]

/-- The rose-tree object of natural-number labels, as the datum of a fold. -/
theorem roseParts_rose :
    FreeTopos.Internal.roseParts FreeTopos.rose = some (FreeTopos.nat, FreeTopos.roseRec) := by
  unfold FreeTopos.Internal.roseParts
  exact ite_eq_left rfl

/-- The two rose-tree objects differ. -/
theorem lrose_ne_rose (a : PartialHorn.Tree) : FreeTopos.lrose a ≠ FreeTopos.rose := fun h ↦ by
  have h' := congrArg RoseTree.label h
  simp only [FreeTopos.lrose, FreeTopos.rose, PartialHorn.op, RoseTree.label_node] at h'
  exact absurd h' (by decide)

/-- The rose-tree object of labels of a type, as the datum of a fold. -/
theorem roseParts_lrose (a : PartialHorn.Tree) :
    FreeTopos.Internal.roseParts (FreeTopos.lrose a) = some (a, FreeTopos.lroseRec a) := by
  unfold FreeTopos.Internal.roseParts
  rw [ite_eq_right (lrose_ne_rose a)]
  exact ite_eq_left rfl

/-- The indices of the empty list and of the construction of valid indices differ. -/
theorem PrimIdx.Valid.cons_ne_nil {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.cons ≠ k.nil := fun h ↦ by
  have hd := congrArg FreeTopos.Internal.Prim.dom
    (Option.some.inj (hk.nil.symm.trans (h ▸ hk.cons)))
  exact absurd (congrArg RoseTree.label hd) (by decide)

/-- The index of the construction of a rose tree of valid indices is neither zero's nor the
successor's. -/
theorem PrimIdx.Valid.node_ne {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.node ≠ k.zero ∧ k.node ≠ k.succ :=
  ⟨fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.dom
      (Option.some.inj (hk.zero.symm.trans (h ▸ hk.node)))
    exact absurd (congrArg RoseTree.label hd) (by decide),
  fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.dom
      (Option.some.inj (hk.succ.symm.trans (h ▸ hk.node)))
    exact absurd (congrArg RoseTree.label hd) (by decide)⟩

/-- The index of the construction of a rose tree of labels of a type of valid indices is neither
the empty list's nor the construction of a list's. -/
theorem PrimIdx.Valid.lnode_ne {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.lnode ≠ k.nil ∧ k.lnode ≠ k.cons :=
  ⟨fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.cod
      (Option.some.inj (hk.nil.symm.trans (h ▸ hk.lnode)))
    exact absurd (congrArg RoseTree.label hd) (by decide),
  fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.cod
      (Option.some.inj (hk.cons.symm.trans (h ▸ hk.lnode)))
    exact absurd (congrArg RoseTree.label hd) (by decide)⟩

/-- The indices of the injections of valid indices differ. -/
theorem PrimIdx.Valid.inr_ne_inl {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.inr ≠ k.inl := fun h ↦ by
  have hd := congrArg FreeTopos.Internal.Prim.arrow
    (Option.some.inj (hk.inl.symm.trans (h ▸ hk.inr)))
  exact absurd (congrArg RoseTree.label hd) (by decide)


end Geb.LF.Topos

end
