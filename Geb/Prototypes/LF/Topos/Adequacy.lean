/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Internal.Substitution
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
functions, the folds of the natural numbers, of lists and of rose trees, and equality.

The encoding of terms ({lit}`enc`) is computed from the compilation, which supplies the types
that the constants of the signature take as arguments; decoding ({lit}`dec`) forgets them. The
fold of the signature is the fold of the language: its start a term of the fold's context and its
step an LF abstraction over the value, whose body is the language's step, a term of the context
extended by the value, so that both may mention the variables around the fold.

## Main definitions

* {lit}`encTy`, {lit}`decTy` — the encoding of the fragment's types, and its inverse.
* {lit}`enc`, {lit}`dec` — the encoding of the fragment's terms, and its inverse.

## Main statements

* {lit}`decTy_encTy` — decoding inverts the encoding of types.
* {lit}`encTy_rename` — renaming moves the encoding of a type from one offset to another.
* {lit}`encTy_checks` — encoded types are canonical terms of {lit}`tp` in contexts whose
  variables past the offset are of {lit}`tp`.
* {lit}`tyComplete` — every canonical term of {lit}`tp` is an encoded type.
* {lit}`enc_checks` — the encoding of a compiled term checks against the family of terms of its
  encoded type.
* {lit}`dec_enc` — decoding inverts the encoding of terms.
* {lit}`tmComplete` — every canonical term of a family of terms, in an encoded context, is the
  encoding of a compiled term of the type the family's index encodes.

## References

* {cite}`HarperLicata2007`, Section 3.2, for adequacy.

## Tags

logical framework, LF, adequacy, Mitchell–Bénabou language
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

/-- An extension of the signature: the signature is a prefix of it, it is formed, and its further
declarations are none of types or terms. -/
structure SigExt (sg : Sig) : Prop where
  /-- The extension is formed. -/
  ok : sg.ok = true
  /-- The signature is a prefix of it. -/
  pre : sig <+: sg
  /-- Its further declarations end in neither {lit}`tp` nor {lit}`tm`. -/
  inert : ∀ c T, sig.length ≤ c → sg[c]? = some T →
    T.headDepth.1 ≠ some 0 ∧ T.headDepth.1 ≠ some 6

/-- A declaration of the signature is one of its extension. -/
theorem SigExt.get (hsg : SigExt sg) {c : ℕ} {T : Expr} (hc : sig[c]? = some T) :
    sg[c]? = some T := by
  obtain ⟨t, rfl⟩ := hsg.pre
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hc).1, hc]

/-- A declaration of an extension below the signature's length is the signature's. -/
theorem SigExt.of_lt (hsg : SigExt sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
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
theorem encTy_checks (hsg : SigExt sg) (G : FreeTopos.Internal.Globals) {n : ℕ} :
    ∀ (a : PartialHorn.Tree) (off : ℕ) (A : Expr), encTy off a = some A →
      FreeTopos.Internal.IsTy G n a = true → ∀ Γ : Ctx,
        (∀ j < n, varType Γ (off + j) = some tp) → judge sg A Γ (.check tp) = true :=
  RoseTree.ind fun l cs ih off A h hty Γ hΓ ↦ by
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩
    · exact judge_var rfl (hΓ i (FreeTopos.Internal.isTy_var.mp hty))
    any_goals exact judge_const (T := tp) (hsg.get rfl) rfl rfl
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
         refine judge_const (T := Expr.arrow tp (Expr.arrow tp tp)) (hsg.get rfl) ?_ rfl
         simp only [tp, Expr.const, Expr.app] at ha hb ⊢
         lf_spine [ha, hb])
      | (obtain ⟨c₁, rfl, h₁⟩ := map_eq_one hcs
         first
           | rw [show RoseTree.node 34 [c₁] = FreeTopos.list c₁ from rfl,
               FreeTopos.Internal.isTy_list] at hty
           | rw [show RoseTree.node 41 [c₁] = FreeTopos.lrose c₁ from rfl,
               FreeTopos.Internal.isTy_lrose] at hty
         have ha := ih c₁ (by simp) off a h₁ hty Γ hΓ
         refine judge_const (T := Expr.arrow tp tp) (hsg.get rfl) ?_ rfl
         simp only [tp, Expr.const, Expr.app] at ha ⊢
         lf_spine [ha])

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
  /-- For each theorem the extension declares, the index of its entry, the number of its object
  variables and the number of its variables. -/
  thms : List (ℕ × ℕ × ℕ)

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
    | .lam, [(_, d)] => FreeTopos.Internal.Term.lam FreeTopos.one <$> d (off + 1)
    | _, _ => none

/-- The decoding of a canonical LF term of the fragment as a term of the internal language, at the
offset of the variables of terms in scope. -/
def dec : Expr → ℕ → Option MTerm := RoseTree.para (decStep k)

/-- The computation rule of the decoding. -/
theorem dec_node (l : Label) (cs : List Expr) (off : ℕ) :
    dec k (RoseTree.node l cs) off = decStep k l (cs.map fun c ↦ (c, dec k c)) off :=
  congrFun (RoseTree.para_node _ l cs) off

end Decoding

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
    · simp [encStep] at henc
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
theorem sig_head_tp (hsg : SigExt sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
    (h : T.headDepth.1 = some 0) : c ∈ [1, 2, 3, 4, 5, 30, 37, 42, 48, 49] ∧ sig[c]? = some T := by
  by_cases hlt : c < sig.length
  · have hc' := hsg.of_lt hc hlt
    exact ⟨sig_head_tp₀ hc' h, hc'⟩
  · exact absurd h (hsg.inert c T (Nat.le_of_not_lt hlt) hc).1

/-- The declarations of an extension of the signature whose types end in {lit}`tm` are the
signature's term constructors. -/
theorem sig_head_tm (hsg : SigExt sg) {c : ℕ} {T : Expr} (hc : sg[c]? = some T)
    (h : T.headDepth.1 = some 6) :
    c ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 31, 32, 33, 38, 39, 43, 44, 50, 51, 52] ∧
      sig[c]? = some T := by
  by_cases hlt : c < sig.length
  · have hc' := hsg.of_lt hc hlt
    exact ⟨sig_head_tm₀ hc' h, hc'⟩
  · exact absurd h (hsg.inert c T (Nat.le_of_not_lt hlt) hc).2

/-- The signature extends itself. -/
theorem sigExt_sig : SigExt sig where
  ok := sig_ok
  pre := List.prefix_refl _
  inert _ _ hle hc := absurd (List.getElem?_eq_some_iff.mp hc).1 (Nat.not_lt_of_le hle)

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
theorem tyComplete (hsg : SigExt sg) (G : FreeTopos.Internal.Globals) {Γ : Ctx} {off n : ℕ}
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
theorem judge_pair_lam_inv (hsg : SigExt sg) {Γ : Ctx} {A B Mz C B' Mf T : Expr}
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

section Soundness

variable {G : FreeTopos.Internal.Globals} {n : ℕ} {k : PrimIdx}

/-- The extension of an environment whose types are types by a variable of a type. -/
theorem extEnv_isTy {X a : PartialHorn.Tree} {e : MEnv} (ha : FreeTopos.Internal.IsTy G n a = true)
    (he : ∀ p ∈ e, FreeTopos.Internal.IsTy G n p.2 = true) :
    ∀ p ∈ FreeTopos.Internal.extEnv X a e, FreeTopos.Internal.IsTy G n p.2 = true := by
  intro p hp
  simp only [FreeTopos.Internal.extEnv, List.mem_cons, List.mem_map] at hp
  rcases hp with rfl | ⟨q, hq, rfl⟩
  · exact ha
  · exact he q hq

/-- Encoding is sound: the encoding of a term of the fragment in {lit}`n` object variables, in an
environment whose types are types in them and encoded, is a canonical LF term of the family of
terms of the encoding of its type, a type in them, at the offset of the environment's
variables. -/
theorem enc_checks (hsg : SigExt sg) (hk : k.Valid G) :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (M : Expr)
      (r : PartialHorn.Tree × PartialHorn.Tree), (∀ p ∈ e, FreeTopos.Internal.IsTy G n p.2 = true) →
      encCtx n (e.map Prod.snd) = some ΓLF → enc G n k s X e = some M →
      FreeTopos.Internal.compile G n s X e = some r →
      FreeTopos.Internal.IsTy G n r.2 = true ∧
        ∃ A, encTy e.length r.2 = some A ∧ judge sg M ΓLF (.check (tm A)) = true :=
  RoseTree.ind fun l cs ih X e ΓLF M r he hΓ henc hcomp ↦ by
    have htp : ∀ j < n, varType ΓLF (e.length + j) = some tp := fun j hj ↦ by
      simpa only [List.length_map] using varType_encCtx_tp hΓ hj
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨j, θ⟩ | _ | _ | c | ⟨j, θ⟩ | _
    · obtain ⟨rfl, hi⟩ := FreeTopos.Internal.compile_var_iff.mp hcomp
      simp only [encStep, List.map_nil, Option.some.injEq] at henc
      subst henc
      have hi' : (e.map Prod.snd)[i]? = some r.2 := by simp [hi]
      obtain ⟨A, hA, hv⟩ := varType_encCtx hΓ hi'
      rw [List.length_map] at hA
      exact ⟨he _ (List.mem_of_getElem? hi), A, hA, judge_var rfl hv⟩
    · obtain ⟨rfl, rfl⟩ := FreeTopos.Internal.compile_star_iff.mp hcomp
      simp only [encStep, List.map_nil, Option.some.injEq] at henc
      subst henc
      exact ⟨FreeTopos.Internal.isTy_one, one, rfl, judge_const (T := tm one) (hsg.get rfl) rfl rfl⟩
    · obtain ⟨t, u, f, a, g, b, rfl, hct, hcu, rfl⟩ :=
        FreeTopos.Internal.compile_pair_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, hcu, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨hIA', A', hA', hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      obtain ⟨hIB', B', hB', hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ he hΓ hMu hcu
      simp only [hA, Option.some.injEq] at hA'
      simp only [hB, Option.some.injEq] at hB'
      subst hA' hB'
      refine ⟨by rw [FreeTopos.Internal.isTy_prod, hIA', hIB']; rfl, prod A B,
        by simp [encTy_prod, hA, hB], judge_const
        (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0))
          (tm (prod (v 1) (v 0))))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIA' ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIB' ΓLF htp
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ hMuJ ⊢
      lf_spine [hAt, hBt, hMtJ, hMuJ]
    · obtain ⟨t, f, a, b, rfl, hct, rfl⟩ := FreeTopos.Internal.compile_fst_iff.mp hcomp
      have hp : FreeTopos.Internal.prodParts (FreeTopos.prod a b) = some (a, b) :=
        FreeTopos.Internal.prodParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
      obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      simp only [encTy_prod, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      subst hP
      rw [FreeTopos.Internal.isTy_prod, Bool.and_eq_true] at hIP
      obtain ⟨hIa, hIb⟩ := hIP
      refine ⟨hIa, A, hA, judge_const (T := Expr.pi tp (Expr.pi tp
        (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 1))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
      lf_spine [hAt, hBt, hMtJ]
    · obtain ⟨t, f, a, b, rfl, hct, rfl⟩ := FreeTopos.Internal.compile_snd_iff.mp hcomp
      have hp : FreeTopos.Internal.prodParts (FreeTopos.prod a b) = some (a, b) :=
        FreeTopos.Internal.prodParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
      obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      simp only [encTy_prod, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      subst hP
      rw [FreeTopos.Internal.isTy_prod, Bool.and_eq_true] at hIP
      obtain ⟨hIa, hIb⟩ := hIP
      refine ⟨hIb, B, hB, judge_const (T := Expr.pi tp (Expr.pi tp
        (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 0))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
      lf_spine [hAt, hBt, hMtJ]
    · obtain ⟨t, f, b, rfl, hIa, hct, rfl⟩ := FreeTopos.Internal.compile_lam_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mb, hMb, rfl⟩ := henc
      have hΓ' : encCtx n ((FreeTopos.Internal.extEnv X a e).map Prod.snd) =
          some (tm A :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons (by simpa only [List.length_map] using hA)
          (by simpa [Function.comp_def] using hΓ)
      obtain ⟨hIb, B', hB', hMbJ⟩ := ih t (by simp) _ _ _ Mb _ (extEnv_isTy hIa he) hΓ' hMb hct
      rw [length_extEnv, encTy_add hB, Option.some.injEq] at hB'
      subst hB'
      have hlam := judge_lam hMbJ
      refine ⟨by rw [FreeTopos.Internal.isTy_exp, hIa, hIb]; rfl, exp A B,
        by simp [encTy_exp, hA, hB], judge_const
        (T := Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0)))
          (tm (exp (v 1) (v 0)))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, exp, Expr.const, Expr.app, Expr.pi] at hAt hBt hlam ⊢
      lf_spine [hAt, hBt, hlam]
    · obtain ⟨t, u, rfl, f, a, b, hct, g, hcu, rfl⟩ := FreeTopos.Internal.compile_app_iff.mp hcomp
      have hp : FreeTopos.Internal.expParts (FreeTopos.exp a b) = some (a, b) :=
        FreeTopos.Internal.expParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      obtain ⟨hIA', A', hA', hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ he hΓ hMu hcu
      simp only [encTy_exp, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      simp only [hA, Option.some.injEq] at hA'
      subst hP hA'
      rw [FreeTopos.Internal.isTy_exp, Bool.and_eq_true] at hIP
      obtain ⟨hIa, hIb⟩ := hIP
      refine ⟨hIb, B, hB,
        judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (exp (v 1) (v 0)))
        (Expr.arrow (tm (v 1)) (tm (v 0)))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hBt := encTy_checks hsg G b _ B hB hIb ΓLF htp
      simp only [tm, tp, exp, Expr.const, Expr.app] at hAt hBt hMtJ hMuJ ⊢
      lf_spine [hAt, hBt, hMtJ, hMuJ]
    · obtain ⟨t, rfl, p, hp, g, hct, hl, hθ, rfl⟩ := FreeTopos.Internal.compile_arr_iff.mp hcomp
      rcases θ with _ | ⟨θ₀, _ | ⟨θ₁, θ⟩⟩
      · by_cases hkz : j = k.zero
        · subst hkz
          rw [hk.zero, Option.some.injEq] at hp
          subst hp
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.map_eq_map,
            Option.map_eq_some_iff] at henc
          obtain ⟨Mt, hMt, rfl⟩ := henc
          obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
          simp only [FreeTopos.Internal.zeroPrim, PartialHorn.subst_nil] at hP ⊢
          rw [show encTy e.length FreeTopos.one = some one from rfl, Option.some.injEq] at hP
          subst hP
          refine ⟨FreeTopos.Internal.isTy_nat, nat, rfl,
            judge_const (T := Expr.arrow (tm one) (tm nat)) (hsg.get rfl) ?_ rfl⟩
          simp only [tm, one, nat, Expr.const, Expr.app] at hMtJ ⊢
          lf_spine [hMtJ]
        · by_cases hks : j = k.succ
          · subst hks
            rw [hk.succ, Option.some.injEq] at hp
            subst hp
            simp only [encStep, List.map_cons, List.map_nil, hkz, ↓reduceIte, Option.map_eq_map,
              Option.map_eq_some_iff] at henc
            obtain ⟨Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            simp only [FreeTopos.Internal.succPrim, PartialHorn.subst_nil] at hP ⊢
            rw [show encTy e.length FreeTopos.nat = some nat from rfl, Option.some.injEq] at hP
            subst hP
            refine ⟨FreeTopos.Internal.isTy_nat, nat, rfl,
              judge_const (T := Expr.arrow (tm nat) (tm nat)) (hsg.get rfl) ?_ rfl⟩
            simp only [tm, nat, Expr.const, Expr.app] at hMtJ ⊢
            lf_spine [hMtJ]
          · by_cases hkd : j = k.node
            · subst hkd
              rw [hk.node, Option.some.injEq] at hp
              subst hp
              simp only [encStep, List.map_cons, List.map_nil, hkz, hks, ↓reduceIte,
                Option.map_eq_map, Option.map_eq_some_iff] at henc
              obtain ⟨Mt, hMt, rfl⟩ := henc
              obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
              simp only [FreeTopos.Internal.nodePrim, PartialHorn.subst_nil] at hP ⊢
              rw [show encTy e.length
                (FreeTopos.prod FreeTopos.nat (FreeTopos.list FreeTopos.rose)) =
                some (prod nat (list rose)) from rfl, Option.some.injEq] at hP
              subst hP
              refine ⟨FreeTopos.Internal.isTy_rose, rose, rfl,
                judge_const (T := Expr.arrow (tm (prod nat (list rose)))
                (tm rose)) (hsg.get rfl) ?_ rfl⟩
              simp only [tm, nat, rose, prod, list, Expr.const, Expr.app] at hMtJ ⊢
              lf_spine [hMtJ]
            · simp [encStep, hkz, hks, hkd] at henc
      · by_cases hkn : j = k.nil
        · subst hkn
          rw [hk.nil, Option.some.injEq] at hp
          subst hp
          have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
            Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
          obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
          rw [subst_nilPrim_dom, show encTy e.length FreeTopos.one = some one from rfl,
            Option.some.injEq] at hP
          subst hP
          refine ⟨by rw [subst_nilPrim_cod, FreeTopos.Internal.isTy_list]; exact hIθ₀, list A,
            by rw [subst_nilPrim_cod, encTy_list, hA]; rfl,
            judge_const (T := Expr.pi tp (Expr.arrow (tm one) (tm (list (v 0)))))
              (hsg.get rfl) ?_ rfl⟩
          have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
          simp only [tm, tp, one, list, Expr.const, Expr.app] at hAt hMtJ ⊢
          lf_spine [hAt, hMtJ]
        · by_cases hkc : j = k.cons
          · subst hkc
            rw [hk.cons, Option.some.injEq] at hp
            subst hp
            have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
            simp only [encStep, List.map_cons, List.map_nil, hkn, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            rw [subst_consPrim_dom, encTy_prod, encTy_list, hA] at hP
            simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
            subst hP
            refine ⟨by rw [subst_consPrim_cod, FreeTopos.Internal.isTy_list]; exact hIθ₀, list A,
              by rw [subst_consPrim_cod, encTy_list, hA]; rfl,
              judge_const (T := Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (v 0))))
                (tm (list (v 0))))) (hsg.get rfl) ?_ rfl⟩
            have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
            simp only [tm, tp, prod, list, Expr.const, Expr.app] at hAt hMtJ ⊢
            lf_spine [hAt, hMtJ]
          · by_cases hkl : j = k.lnode
            · subst hkl
              rw [hk.lnode, Option.some.injEq] at hp
              subst hp
              have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
              simp only [encStep, List.map_cons, List.map_nil, hkn, hkc, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
              obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
              rw [subst_lnodePrim_dom, encTy_prod, encTy_list, encTy_lrose, hA] at hP
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
              subst hP
              refine ⟨by rw [subst_lnodePrim_cod, FreeTopos.Internal.isTy_lrose]; exact hIθ₀,
                lrose A, by rw [subst_lnodePrim_cod, encTy_lrose, hA]; rfl,
                judge_const (T := Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (lrose (v 0)))))
                  (tm (lrose (v 0))))) (hsg.get rfl) ?_ rfl⟩
              have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
              simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hAt hMtJ ⊢
              lf_spine [hAt, hMtJ]
            · simp [encStep, hkn, hkc, hkl] at henc
      · rcases θ with _ | ⟨θ₂, _ | ⟨θ₃, θ⟩⟩
        · by_cases hkl : j = k.inl
          · subst hkl
            rw [hk.inl, Option.some.injEq] at hp
            subst hp
            have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
            have hIθ₁ := List.all_eq_true.mp hθ θ₁ (by simp)
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            rw [subst_inlPrim_dom, hA, Option.some.injEq] at hP
            subst hP
            refine ⟨by rw [subst_inlPrim_cod, FreeTopos.Internal.isTy_coprod, hIθ₀, hIθ₁]; rfl,
              coprod A B, by rw [subst_inlPrim_cod, encTy_coprod, hA, hB]; rfl,
              judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1))
                (tm (coprod (v 1) (v 0)))))) (hsg.get rfl) ?_ rfl⟩
            have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
            have hBt := encTy_checks hsg G θ₁ _ B hB hIθ₁ ΓLF htp
            simp only [tm, tp, coprod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
            lf_spine [hAt, hBt, hMtJ]
          · by_cases hkr : j = k.inr
            · subst hkr
              rw [hk.inr, Option.some.injEq] at hp
              subst hp
              have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
              have hIθ₁ := List.all_eq_true.mp hθ θ₁ (by simp)
              simp only [encStep, List.map_cons, List.map_nil, hkl, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
              obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
              rw [subst_inrPrim_dom, hB, Option.some.injEq] at hP
              subst hP
              refine ⟨by rw [subst_inrPrim_cod, FreeTopos.Internal.isTy_coprod, hIθ₀, hIθ₁]; rfl,
                coprod A B, by rw [subst_inrPrim_cod, encTy_coprod, hA, hB]; rfl,
                judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
                  (tm (coprod (v 1) (v 0)))))) (hsg.get rfl) ?_ rfl⟩
              have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
              have hBt := encTy_checks hsg G θ₁ _ B hB hIθ₁ ΓLF htp
              simp only [tm, tp, coprod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
              lf_spine [hAt, hBt, hMtJ]
            · simp [encStep, hkl, hkr] at henc
        · by_cases hkc : j = k.case
          · subst hkc
            rw [hk.case, Option.some.injEq] at hp
            subst hp
            have hIθ₀ := List.all_eq_true.mp hθ θ₀ (by simp)
            have hIθ₁ := List.all_eq_true.mp hθ θ₁ (by simp)
            have hIθ₂ := List.all_eq_true.mp hθ θ₂ (by simp)
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, B, hB, C, hC, Mt, hMt, rfl⟩ := henc
            obtain ⟨hIP, P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
            rw [subst_casePrim_dom, encTy_prod, encTy_exp, encTy_exp, hA, hB, hC] at hP
            simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
            subst hP
            refine ⟨by rw [subst_casePrim_cod, FreeTopos.Internal.isTy_exp,
                FreeTopos.Internal.isTy_coprod, hIθ₀, hIθ₁, hIθ₂]; rfl, exp (coprod A B) C, by
                rw [subst_casePrim_cod, encTy_exp, encTy_coprod, hA, hB, hC]; rfl,
              judge_const (T := Expr.pi tp (Expr.pi tp (Expr.pi tp
                (Expr.arrow (tm (prod (exp (v 2) (v 0)) (exp (v 1) (v 0))))
                  (tm (exp (coprod (v 2) (v 1)) (v 0))))))) (hsg.get rfl) ?_ rfl⟩
            have hAt := encTy_checks hsg G θ₀ _ A hA hIθ₀ ΓLF htp
            have hBt := encTy_checks hsg G θ₁ _ B hB hIθ₁ ΓLF htp
            have hCt := encTy_checks hsg G θ₂ _ C hC hIθ₂ ΓLF htp
            simp only [tm, tp, prod, exp, coprod, Expr.const, Expr.app] at hAt hBt hCt hMtJ ⊢
            lf_spine [hAt, hBt, hCt, hMtJ]
          · simp [encStep, hkc] at henc
        · simp [encStep] at henc
    · obtain ⟨z, s, m, rfl, -⟩ := FreeTopos.Internal.compile_natRec_iff.mp hcomp
      obtain ⟨⟨zf, hcz⟩, ⟨sf, hcs⟩, mf, hcm⟩ := FreeTopos.Internal.compile_natRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      have hΓ' : encCtx n ((FreeTopos.Internal.extEnv X r.2 e).map Prod.snd) =
          some (tm C :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons (by simpa only [List.length_map] using hC)
          (by simpa [Function.comp_def] using hΓ)
      obtain ⟨hIr2, A₁, hA₁, hMzJ⟩ := ih z (by simp) X e ΓLF Mz _ he hΓ hMz hcz
      obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ (extEnv_isTy hIr2 he) hΓ' hMs hcs
      obtain ⟨-, N, hN, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
      rw [hC, Option.some.injEq] at hA₁
      rw [length_extEnv, encTy_add hC, Option.some.injEq] at hA₂
      subst hA₁ hA₂
      rw [show encTy e.length FreeTopos.nat = some nat from rfl, Option.some.injEq] at hN
      subst hN
      have hfJ := judge_lam hMsJ
      refine ⟨hIr2, C, hC, judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0))) (Expr.arrow (tm nat) (tm (v 0))))))
        (hsg.get rfl) ?_ rfl⟩
      have hCt := encTy_checks hsg G r.2 _ C hC hIr2 ΓLF htp
      simp only [tm, tp, nat, Expr.const, Expr.app, Expr.pi] at hCt hMzJ hfJ hMmJ ⊢
      lf_spine [hCt, hMzJ, hfJ, hMmJ]
    · obtain ⟨z, s, m, rfl, -⟩ := FreeTopos.Internal.compile_listRec_iff.mp hcomp
      obtain ⟨mf, a, hcm, ⟨zf, hcz⟩, sf, hcs⟩ := FreeTopos.Internal.compile_listRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, hcm,
        FreeTopos.Internal.listPart_eq_some.mpr rfl, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      have hΓ' : encCtx n ((FreeTopos.Internal.extEnv (FreeTopos.prod X a) r.2
          (FreeTopos.Internal.extEnv X a e)).map Prod.snd) =
          some (tm (C.rename (· + 1)) :: tm A :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        refine encCtx_cons ?_ (encCtx_cons (by simpa only [List.length_map] using hA)
          (by simpa [Function.comp_def] using hΓ))
        simpa only [List.length_map, List.length_cons] using encTy_add (d := 1) hC
      obtain ⟨hIr2, A₁, hA₁, hMzJ⟩ := ih z (by simp) X e ΓLF Mz _ he hΓ hMz hcz
      obtain ⟨hIL, L, hL, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
      have hIa : FreeTopos.Internal.IsTy G n a = true := by
        rwa [FreeTopos.Internal.isTy_list] at hIL
      obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _
        (extEnv_isTy hIr2 (extEnv_isTy hIa he)) hΓ' hMs hcs
      rw [hC, Option.some.injEq] at hA₁
      rw [length_extEnv, length_extEnv, Nat.add_assoc, encTy_add hC, Option.some.injEq] at hA₂
      subst hA₁ hA₂
      rw [encTy_list, hA, Option.map_some, Option.some.injEq] at hL
      subst hL
      have hfJ := judge_lam (judge_lam hMsJ)
      refine ⟨hIr2, C, hC, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (v 0))))
          (Expr.arrow (tm (list (v 1))) (tm (v 0))))))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIa ΓLF htp
      have hCt := encTy_checks hsg G r.2 _ C hC hIr2 ΓLF htp
      simp only [tm, tp, list, Expr.const, Expr.app, Expr.pi] at hAt hCt hMzJ hfJ hMmJ ⊢
      lf_spine [hAt, hCt, hMzJ, hfJ, hMmJ]
    · obtain ⟨s, m, -, -, -, -, -, rfl, hIc, -⟩ := FreeTopos.Internal.compile_roseRec_iff.mp hcomp
      obtain ⟨hct, hrc, mf, t, a, F, hcm, ht, sf, hcs⟩ :=
        FreeTopos.Internal.compile_roseRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcm, Option.bind_eq_bind,
        Option.bind_some] at henc
      split at henc
      · next htl htc =>
        obtain rfl : t = FreeTopos.rose := by
          rw [← RoseTree.node_label_children t, htl, htc]
          rfl
        obtain ⟨rfl, rfl⟩ : a = FreeTopos.nat ∧ F = FreeTopos.roseRec := by
          simpa [FreeTopos.Internal.roseParts] using ht.symm
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
        obtain ⟨C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hpc : encTy e.length (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) =
            some (prod nat (list C)) := by rw [encTy_prod, encTy_list, hC]; rfl
        have hΓ' : encCtx n ((FreeTopos.Internal.extEnv X (FreeTopos.prod FreeTopos.nat
            (FreeTopos.list c)) e).map Prod.snd) = some (tm (prod nat (list C)) :: ΓLF) := by
          simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
          exact encCtx_cons (by simpa only [List.length_map] using hpc)
            (by simpa [Function.comp_def] using hΓ)
        have hIp : FreeTopos.Internal.IsTy G n
            (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) = true := by
          rw [FreeTopos.Internal.isTy_prod, FreeTopos.Internal.isTy_list, hIc]; rfl
        obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ (extEnv_isTy hIp he) hΓ' hMs hcs
        obtain ⟨-, T, hT, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
        rw [length_extEnv, ← hrc, encTy_add (hrc ▸ hC), Option.some.injEq] at hA₂
        subst hA₂
        rw [show encTy e.length FreeTopos.rose = some rose from rfl, Option.some.injEq] at hT
        subst hT
        have hfJ := judge_lam hMsJ
        refine ⟨by rw [hrc]; exact hIc, C, by rw [hrc]; exact hC,
          judge_const (T := Expr.pi tp (Expr.arrow
          (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0))) (Expr.arrow (tm rose) (tm (v 0)))))
          (hsg.get rfl) ?_ rfl⟩
        have hCt := encTy_checks hsg G c _ C hC hIc ΓLF htp
        simp only [tm, tp, nat, rose, prod, list, Expr.const, Expr.app, Expr.pi] at hCt hfJ hMmJ ⊢
        lf_spine [hCt, hfJ, hMmJ]
      · next a' htl htc =>
        obtain rfl : t = FreeTopos.lrose a' := by
          rw [← RoseTree.node_label_children t, htl, htc]
          rfl
        rw [roseParts_lrose, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
        obtain ⟨A, hA, C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hpc : encTy e.length (FreeTopos.prod a' (FreeTopos.list c)) =
            some (prod A (list C)) := by
          rw [encTy_prod, encTy_list, hA, hC]; rfl
        have hΓ' : encCtx n ((FreeTopos.Internal.extEnv X (FreeTopos.prod a'
            (FreeTopos.list c)) e).map Prod.snd) = some (tm (prod A (list C)) :: ΓLF) := by
          simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
          exact encCtx_cons (by simpa only [List.length_map] using hpc)
            (by simpa [Function.comp_def] using hΓ)
        obtain ⟨hIT, T, hT, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ he hΓ hMm hcm
        have hIa' : FreeTopos.Internal.IsTy G n a' = true := by
          rwa [FreeTopos.Internal.isTy_lrose] at hIT
        have hIp : FreeTopos.Internal.IsTy G n (FreeTopos.prod a' (FreeTopos.list c)) = true := by
          rw [FreeTopos.Internal.isTy_prod, FreeTopos.Internal.isTy_list, hIa', hIc]; rfl
        obtain ⟨-, A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ (extEnv_isTy hIp he) hΓ' hMs hcs
        rw [length_extEnv, ← hrc, encTy_add (hrc ▸ hC), Option.some.injEq] at hA₂
        subst hA₂
        rw [encTy_lrose, hA, Option.map_some, Option.some.injEq] at hT
        subst hT
        have hfJ := judge_lam hMsJ
        refine ⟨by rw [hrc]; exact hIc, C, by rw [hrc]; exact hC,
          judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow
          (Expr.arrow (tm (prod (v 1) (list (v 0)))) (tm (v 0)))
          (Expr.arrow (tm (lrose (v 1))) (tm (v 0)))))) (hsg.get rfl) ?_ rfl⟩
        have hAt := encTy_checks hsg G a' _ A hA hIa' ΓLF htp
        have hCt := encTy_checks hsg G c _ C hC hIc ΓLF htp
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app, Expr.pi] at hAt hCt hfJ hMmJ ⊢
        lf_spine [hAt, hCt, hfJ, hMmJ]
      · simp at henc
    · simp [encStep] at henc
    · obtain ⟨t, u, rfl, f, a, hct, g, hcu, rfl⟩ := FreeTopos.Internal.compile_eq_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨hIA₁, A₁, hA₁, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ he hΓ hMt hct
      obtain ⟨hIA₂, A₂, hA₂, hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ he hΓ hMu hcu
      simp only [hA, Option.some.injEq] at hA₁ hA₂
      subst hA₁ hA₂
      refine ⟨FreeTopos.Internal.isTy_omega, omega, rfl,
        judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (tm (v 0)) (tm omega)))) (hsg.get rfl) ?_ rfl⟩
      have hAt := encTy_checks hsg G a _ A hA hIA₁ ΓLF htp
      simp only [tm, tp, omega, Expr.const, Expr.app] at hAt hMtJ hMuJ ⊢
      lf_spine [hAt, hMtJ, hMuJ]

end Soundness

section Completeness

variable {G : FreeTopos.Internal.Globals} {n : ℕ} {k : PrimIdx}

/-- The conclusion of the completeness of the encoding in {lit}`n` object variables at a term, an
environment and a type: the term decodes, at the offset of the environment's variables, to a term
of the internal language that compiles in the environment to a type that the type encodes at that
offset, and whose encoding it is. -/
def TmConcl (G : FreeTopos.Internal.Globals) (n : ℕ) (k : PrimIdx) (M : Expr)
    (X : PartialHorn.Tree) (e : MEnv) (A : Expr) : Prop :=
  ∃ s r, dec k M e.length = some s ∧ FreeTopos.Internal.compile G n s X e = some r ∧
    encTy e.length r.2 = some A ∧ enc G n k s X e = some M

/-- The completeness of the encoding at a term, of the family of terms of a type, and, where the
term checks against a product of families of terms, or against a product of families of terms
into such a product, at the body of the abstraction it is, or of the abstraction that is its body,
in every environment of the extended types. -/
def TmComplete (sg : Sig) (G : FreeTopos.Internal.Globals) (n : ℕ) (k : PrimIdx) (M : Expr) :
    Prop :=
  (∀ (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (A : Expr),
    encCtx n (e.map Prod.snd) = some ΓLF →
    judge sg M ΓLF (.check (tm A)) = true → TmConcl G n k M X e A) ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a : PartialHorn.Tree) (A' B' : Expr),
    encCtx n Γ = some ΓLF → encTy Γ.length a = some A' →
    judge sg M ΓLF (.check (Expr.pi (tm A') (tm B'))) = true →
    ∃ body, M = Expr.lam body ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = a :: Γ →
        TmConcl G n k body X e B') ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a b : PartialHorn.Tree) (A' B' C' : Expr),
    encCtx n Γ = some ΓLF → encTy Γ.length a = some A' → encTy (Γ.length + 1) b = some B' →
    judge sg M ΓLF (.check (Expr.pi (tm A') (Expr.pi (tm B') (tm C')))) = true →
    ∃ body, M = Expr.lam (Expr.lam body) ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = b :: a :: Γ →
        TmConcl G n k body X e C')

/-- The completeness of the encoding at a left injection. -/
theorem tmComplete_inl (hsg : SigExt sg) (hk : k.Valid G) {X1 X2 X3 : Expr}
    (ih : TmComplete sg G n k X3)
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {A : Expr}
    (hΓ : encCtx n (e.map Prod.snd) = some ΓLF)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (tm (coprod (v 1) (v 0))))))
      ([X1, X2, X3].map fun m ↦ (m, judge sg m)) = some (tm A)) :
    TmConcl G n k (Expr.const 50 [X1, X2, X3]) X e A := by
  unfold TmConcl
  have hheads₀ := encCtx_heads₀ hΓ
  simp only [List.length_map] at hheads₀
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₂ hS
  obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
  obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2
  simp only [tm, tp, coprod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, ht, hA⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
  subst hA
  obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := ih.1 X e ΓLF X1 hΓ ht
  obtain rfl := encTy_inj ha hrt
  refine ⟨FreeTopos.Internal.Term.arr k.inl [a, b] st, _, ?_,
    FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.inl, g,
      by rw [subst_inlPrim_dom]; exact hct, rfl,
      by simp [hIa, hIb], rfl⟩,
    by rw [subst_inlPrim_cod, encTy_coprod, ha, hb]; rfl, ?_⟩
  · rw [Expr.const, Expr.app, dec_node]
    simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
      decTy_encTy _ b X2 hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · rw [FreeTopos.Internal.Term.arr, enc_node]
    simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, ha, hb, het,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- The completeness of the encoding at a right injection. -/
theorem tmComplete_inr (hsg : SigExt sg) (hk : k.Valid G) {X1 X2 X3 : Expr}
    (ih : TmComplete sg G n k X3)
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {A : Expr}
    (hΓ : encCtx n (e.map Prod.snd) = some ΓLF)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0)) (tm (coprod (v 1) (v 0))))))
      ([X1, X2, X3].map fun m ↦ (m, judge sg m)) = some (tm A)) :
    TmConcl G n k (Expr.const 51 [X1, X2, X3]) X e A := by
  unfold TmConcl
  have hheads₀ := encCtx_heads₀ hΓ
  simp only [List.length_map] at hheads₀
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₂ hS
  obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
  obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2
  simp only [tm, tp, coprod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, ht, hA⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
  subst hA
  obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := ih.1 X e ΓLF X2 hΓ ht
  obtain rfl := encTy_inj hb hrt
  refine ⟨FreeTopos.Internal.Term.arr k.inr [a, b] st, _, ?_,
    FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.inr, g,
      by rw [subst_inrPrim_dom]; exact hct, rfl,
      by simp [hIa, hIb], rfl⟩,
    by rw [subst_inrPrim_cod, encTy_coprod, ha, hb]; rfl, ?_⟩
  · rw [Expr.const, Expr.app, dec_node]
    simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
      decTy_encTy _ b X2 hb, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  · rw [FreeTopos.Internal.Term.arr, enc_node]
    simp only [encStep, List.map_cons, List.map_nil, hk.inr_ne_inl, ↓reduceIte, ha, hb, het,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- The completeness of the encoding at a case analysis. -/
theorem tmComplete_case (hsg : SigExt sg) (hk : k.Valid G) {X1 X2 X3 X4 : Expr}
    (ih : TmComplete sg G n k X4)
    {X : PartialHorn.Tree} {e : MEnv} {ΓLF : Ctx} {A : Expr}
    (hΓ : encCtx n (e.map Prod.snd) = some ΓLF)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (exp (v 2) (v 0))
      (exp (v 1) (v 0)))) (tm (exp (coprod (v 2) (v 1)) (v 0)))))))
      ([X1, X2, X3, X4].map fun m ↦ (m, judge sg m)) = some (tm A)) :
    TmConcl G n k (Expr.const 52 [X1, X2, X3, X4]) X e A := by
  unfold TmConcl
  have hheads₀ := encCtx_heads₀ hΓ
  simp only [List.length_map] at hheads₀
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₃ hS
  obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
  obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2.1
  obtain ⟨c, hc, hIc⟩ := tyComplete hsg G hheads₀ X3 hT.2.2
  simp only [tm, tp, prod, exp, coprod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
  obtain ⟨-, -, -, ht, hA⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
  subst hA
  have hdom : encTy e.length (FreeTopos.prod (FreeTopos.exp a c) (FreeTopos.exp b c)) =
      some (prod (exp X1 X3) (exp X2 X3)) := by
    rw [encTy_prod, encTy_exp, encTy_exp, ha, hb, hc]; rfl
  obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
    ih.1 X e ΓLF (prod (exp X1 X3) (exp X2 X3)) hΓ ht
  obtain rfl := encTy_inj hdom hrt
  refine ⟨FreeTopos.Internal.Term.arr k.case [a, b, c] st, _, ?_,
    FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.case, g,
      by rw [subst_casePrim_dom]; exact hct, rfl,
      by simp [hIa, hIb, hIc],
      rfl⟩,
    by rw [subst_casePrim_cod, encTy_exp, encTy_coprod, ha, hb, hc]; rfl, ?_⟩
  · rw [Expr.const, Expr.app, dec_node]
    simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
      decTy_encTy _ b X2 hb, decTy_encTy _ c X3 hc, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · rw [FreeTopos.Internal.Term.arr, enc_node]
    simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, ha, hb, hc, het,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl

/-- Encoding is onto the canonical LF terms: every canonical term of the family of terms of a type,
in an encoded context, decodes to a term of the internal language that compiles, in an
environment of the context's types, to a type the type encodes, and whose encoding it is. -/
theorem tmComplete (hsg : SigExt sg) (hk : k.Valid G) :
    ∀ M : Expr, TmComplete sg G n k M :=
  RoseTree.ind fun l cs ih ↦ by
    refine ⟨fun X e ΓLF A hΓ hj ↦ ?_, fun Γ ΓLF a A' B' hΓ ha hj ↦ ?_,
      fun Γ ΓLF a b A' B' C' hΓ ha hb hj ↦ ?_⟩
    rotate_left
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      refine ⟨body, rfl, fun X e he ↦ ?_⟩
      exact (ih body (by simp)).1 X e (tm A' :: ΓLF) B' (by rw [he]; exact encCtx_cons ha hΓ)
        hbJ
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      obtain ⟨body', rfl, hb'⟩ :=
        (ih body (by simp)).2.1 (a :: Γ) (tm A' :: ΓLF) b B' C' (encCtx_cons ha hΓ) hb hbJ
      exact ⟨body', rfl, hb'⟩
    unfold TmConcl
    obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hM
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    have hheads₀ := encCtx_heads₀ hΓ
    simp only [List.length_map] at hheads₀
    rcases h with i | c
    · rcases varType_encCtx_inv hΓ hC with ⟨a, A', ha, hA', rfl⟩ | ⟨-, -, rfl⟩
      swap
      · exact absurd (show some 6 = some 0 from (spine_headDepth _ _ _ rfl hS).1) (by decide)
      rw [List.length_map] at hA'
      have hlen := (spine_headDepth _ _ _ rfl hS).2
      rw [show (tm A).headDepth.2 = 0 from rfl, show (tm A').headDepth.2 = 0 from rfl,
        List.length_map] at hlen
      obtain rfl := List.length_eq_zero_iff.mp (by omega : cs.length = 0)
      simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq,
        tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] at hS
      subst hS
      obtain ⟨f, hf⟩ := env_of_map_snd ha
      refine ⟨FreeTopos.Internal.Term.var i, (f, a), rfl,
        FreeTopos.Internal.compile_var_iff.mpr ⟨rfl, hf⟩, hA', ?_⟩
      rw [FreeTopos.Internal.Term.var, enc_node]
      rfl
    · have hCs := Sig.ok_typeShape hsg.ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C _ hCs hS
      obtain ⟨hc, hC⟩ := sig_head_tm hsg hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (tm A).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (tm one))
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq,
          tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] at hS
        subst hS
        refine ⟨FreeTopos.Internal.Term.star, _,
          (by rw [dec_node]; rfl), FreeTopos.Internal.compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, ?_⟩
        rw [FreeTopos.Internal.Term.star, enc_node]
        rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.pi tp (Expr.pi tp
          (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (prod (v 1) (v 0))))))))
        obtain ⟨A', cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B', t, u, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ A' hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ B' hT.2
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a'⟩, hdt, hct, hrt, het⟩ :=
          (ih t (by simp)).1 X e ΓLF A' hΓ ht
        obtain ⟨su, ⟨g, b'⟩, hdu, hcu, hru, heu⟩ :=
          (ih u (by simp)).1 X e ΓLF B' hΓ hu
        obtain rfl := encTy_inj hrt ha
        obtain rfl := encTy_inj hru hb
        refine ⟨FreeTopos.Internal.Term.pair st su, (FreeTopos.pair f g, FreeTopos.prod a' b'),
          ?_, FreeTopos.Internal.compile_pair_iff.mpr ⟨st, su, f, a', g, b', rfl, hct, hcu, rfl⟩,
          by rw [encTy_prod, ha, hb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.pair, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, hcu, ha, hb, het, heu,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 1))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hp, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy e.length (FreeTopos.prod a b) = some (prod X1 X2) := by
          rw [encTy_prod, ha, hb]; rfl
        obtain ⟨sp, ⟨f, c'⟩, hdp, hcp, hrp, hep⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ hp
        obtain rfl := encTy_inj hrp hab
        refine ⟨FreeTopos.Internal.Term.fst sp, _, ?_,
          FreeTopos.Internal.compile_fst_iff.mpr ⟨sp, f, a, b, rfl, hcp, rfl⟩, ha, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdp]
          rfl
        · rw [FreeTopos.Internal.Term.fst, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcp, ha, hb, hep, Option.bind_eq_bind,
            Option.bind_some, FreeTopos.Internal.prodParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 0))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hp, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy e.length (FreeTopos.prod a b) = some (prod X1 X2) := by
          rw [encTy_prod, ha, hb]; rfl
        obtain ⟨sp, ⟨f, c'⟩, hdp, hcp, hrp, hep⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ hp
        obtain rfl := encTy_inj hrp hab
        refine ⟨FreeTopos.Internal.Term.snd sp, _, ?_,
          FreeTopos.Internal.compile_snd_iff.mpr ⟨sp, f, a, b, rfl, hcp, rfl⟩, hb, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdp]
          rfl
        · rw [FreeTopos.Internal.Term.snd, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcp, ha, hb, hep, Option.bind_eq_bind,
            Option.bind_some, FreeTopos.Internal.prodParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0)))
            (tm (exp (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hf, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨body, rfl, hbody⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF a X1 _ hΓ
          (by rwa [List.length_map])
          hf
        obtain ⟨sb, ⟨fb, b'⟩, hdb, hcb, hrb, heb⟩ :=
          hbody (FreeTopos.prod X a) (FreeTopos.Internal.extEnv X a e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hdb hrb
        obtain rfl := encTy_inj hrb (encTy_add hb)
        refine ⟨FreeTopos.Internal.Term.lam a sb, _, ?_,
          FreeTopos.Internal.compile_lam_iff.mpr ⟨sb, fb, b', rfl, hIa, hcb,
            rfl⟩, by rw [encTy_exp, ha, hb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam,
            dec_node, hdb, decTy_encTy _ a X1 ha]
          rfl
        · rw [FreeTopos.Internal.Term.lam, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcb, ha, hb, heb,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (exp (v 1) (v 0)))
            (Expr.arrow (tm (v 1)) (tm (v 0)))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
        obtain ⟨b, hb, hIb⟩ := tyComplete hsg G hheads₀ X2 hT.2
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy e.length (FreeTopos.exp a b) = some (exp X1 X2) := by
          rw [encTy_exp, ha, hb]; rfl
        obtain ⟨st, ⟨f, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (exp X1 X2) hΓ ht
        obtain ⟨su, ⟨g, a'⟩, hdu, hcu, hru, heu⟩ :=
          (ih X4 (by simp)).1 X e ΓLF X1 hΓ hu
        obtain rfl := encTy_inj hrt hab
        obtain rfl := encTy_inj ha hru
        refine ⟨FreeTopos.Internal.Term.app st su, _, ?_,
          FreeTopos.Internal.compile_app_iff.mpr ⟨st, su, rfl, f, a, b, hct, g, hcu, rfl⟩, hb, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.app, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, ha, hb, het, heu,
            Option.bind_eq_bind, Option.bind_some, FreeTopos.Internal.expParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm one) (tm nat)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, one, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF one hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy e.length FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr k.zero [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.zero, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm nat) (tm nat)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF nat hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy e.length FreeTopos.nat = some nat)
        have hne : k.succ ≠ k.zero := fun h ↦ by
          have hd := congrArg FreeTopos.Internal.Prim.dom
            (Option.some.inj (hk.zero.symm.trans (h ▸ hk.succ)))
          exact absurd (congrArg RoseTree.label hd) (by decide)
        refine ⟨FreeTopos.Internal.Term.arr k.succ [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.succ, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hne, ↓reduceIte, het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0)))
            (Expr.arrow (tm nat) (tm (v 0)))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg G hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ := (ih X2 (by simp)).1 X e ΓLF X1 hΓ hzJ
        obtain ⟨body, rfl, hbc⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF c X1 _ hΓ
          (by rwa [List.length_map]) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X c) (FreeTopos.Internal.extEnv X c e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X4 (by simp)).1 X e ΓLF nat hΓ hm
        obtain rfl := encTy_inj hc hrz
        obtain rfl := encTy_inj (encTy_add hc) hrs
        obtain rfl := encTy_inj hrm (rfl : encTy e.length FreeTopos.nat = some nat)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_natRec_of_parts hcz hcs hcm
        refine ⟨FreeTopos.Internal.Term.natRec sz ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.natRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (tm (v 0)) (tm omega)))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, omega, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a₁⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF X1 hΓ ht
        obtain ⟨su, ⟨g, a₂⟩, hdu, hcu, hru, heu⟩ :=
          (ih X3 (by simp)).1 X e ΓLF X1 hΓ hu
        obtain rfl := encTy_inj ha hrt
        obtain rfl := encTy_inj ha hru
        refine ⟨FreeTopos.Internal.Term.eq st su, _, ?_,
          FreeTopos.Internal.compile_eq_iff.mpr ⟨st, su, rfl, f, a, hct, g, hcu, rfl⟩, rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.eq, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, ha, het, heu,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm one) (tm (list (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, one, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := (ih X2 (by simp)).1 X e ΓLF one hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy e.length FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr k.nil [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.nil, g,
            by rw [subst_nilPrim_dom]; exact hct, rfl,
            by simp [hIa], rfl⟩,
          by rw [subst_nilPrim_cod, encTy_list, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, ha, het,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (v 0)))) (tm (list (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, prod, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpl : encTy e.length (FreeTopos.prod a (FreeTopos.list a)) =
            some (prod X1 (list X1)) := by
          rw [encTy_prod, encTy_list, ha]; rfl
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF (prod X1 (list X1)) hΓ ht
        obtain rfl := encTy_inj hrt hpl
        refine ⟨FreeTopos.Internal.Term.arr k.cons [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.cons, g,
            by rw [subst_consPrim_dom]; exact hct, rfl,
            by simp [hIa], rfl⟩,
          by rw [subst_consPrim_cod, encTy_list, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hk.cons_ne_nil, ↓reduceIte, ha, het,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
            (Expr.arrow (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (v 0))))
              (Expr.arrow (tm (list (v 1))) (tm (v 0))))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨X2, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        obtain ⟨X3, X4, X5, rfl⟩ := List.length_eq_three.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1)))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg G hheads₀ X2 hT.2
        simp only [tm, tp, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ := (ih X3 (by simp)).1 X e ΓLF X2 hΓ hzJ
        obtain ⟨body, rfl, hbc⟩ :=
          (ih X4 (by simp)).2.2 (e.map Prod.snd) ΓLF a c X1 _ _ hΓ (by rwa [List.length_map])
            (by rw [List.length_map]; exact encTy_add hc) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod (FreeTopos.prod X a) c)
            (FreeTopos.Internal.extEnv (FreeTopos.prod X a) c (FreeTopos.Internal.extEnv X a e))
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        have hla : encTy e.length (FreeTopos.list a) = some (list X1) := by rw [encTy_list, ha]; rfl
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X5 (by simp)).1 X e ΓLF (list X1) hΓ hm
        obtain rfl := encTy_inj hc hrz
        have hc₂ : encTy (e.length + 1 + 1) c = some (Expr.rename X2 (· + 2)) := by
          rw [Nat.add_assoc]
          exact encTy_add hc
        obtain rfl := encTy_inj hc₂ hrs
        obtain rfl := encTy_inj hrm hla
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_listRec_of_parts hcm hcz hcs
        refine ⟨FreeTopos.Internal.Term.listRec sz ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.listRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hcm,
            FreeTopos.Internal.listPart_eq_some.mpr rfl, ha, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm (prod nat (list rose))) (tm rose)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, nat, rose, prod, list, Expr.const,
          Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF (prod nat (list rose)) hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy e.length (FreeTopos.prod FreeTopos.nat
          (FreeTopos.list FreeTopos.rose)) = some (prod nat (list rose)))
        refine ⟨FreeTopos.Internal.Term.arr k.node [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.node, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hk.node_ne.1, hk.node_ne.2, ↓reduceIte,
            het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0)))
            (Expr.arrow (tm rose) (tm (v 0))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg G hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, nat, rose, prod, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpc : encTy e.length (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) =
            some (prod nat (list X1)) := by rw [encTy_prod, encTy_list, hc]; rfl
        obtain ⟨body, rfl, hbc⟩ := (ih X2 (by simp)).2.1 (e.map Prod.snd) ΓLF _ _ _ hΓ
          (by rw [List.length_map]; exact hpc) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)))
            (FreeTopos.Internal.extEnv X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X3 (by simp)).1 X e ΓLF rose hΓ hm
        obtain rfl := encTy_inj (encTy_add hc) hrs
        obtain rfl := encTy_inj hrm (rfl : encTy e.length FreeTopos.rose = some rose)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_roseRec_of_parts
          (hIc) hcm (show FreeTopos.Internal.roseParts FreeTopos.rose =
            some (FreeTopos.nat, FreeTopos.roseRec) by simp [FreeTopos.Internal.roseParts]) hcs
        refine ⟨FreeTopos.Internal.Term.roseRec c ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hds, hdm,
            decTy_encTy _ c X1 hc]
          rfl
        · rw [FreeTopos.Internal.Term.roseRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcm, hc, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (lrose (v 0))))) (tm (lrose (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 (spine_tp₁ hS)
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpl : encTy e.length (FreeTopos.prod a (FreeTopos.list (FreeTopos.lrose a))) =
            some (prod X1 (list (lrose X1))) := by
          rw [encTy_prod, encTy_list, encTy_lrose, ha]; rfl
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF (prod X1 (list (lrose X1))) hΓ ht
        obtain rfl := encTy_inj hrt hpl
        refine ⟨FreeTopos.Internal.Term.arr k.lnode [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.lnode, g,
            by rw [subst_lnodePrim_dom]; exact hct, rfl,
            by simp [hIa], rfl⟩,
          by rw [subst_lnodePrim_cod, encTy_lrose, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy _ a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hk.lnode_ne.1, hk.lnode_ne.2,
            ↓reduceIte, ha, het, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (prod (v 1) (list (v 0))))
            (tm (v 0))) (Expr.arrow (tm (lrose (v 1))) (tm (v 0)))))))
        obtain ⟨X1, X2, X3, X4, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha, hIa⟩ := tyComplete hsg G hheads₀ X1 hT.1
        obtain ⟨c, hc, hIc⟩ := tyComplete hsg G hheads₀ X2 hT.2
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨-, -, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpc : encTy e.length (FreeTopos.prod a (FreeTopos.list c)) =
            some (prod X1 (list X2)) := by
          rw [encTy_prod, encTy_list, ha, hc]; rfl
        obtain ⟨body, rfl, hbc⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF _ _ _ hΓ
          (by rw [List.length_map]; exact hpc) hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X (FreeTopos.prod a (FreeTopos.list c)))
            (FreeTopos.Internal.extEnv X (FreeTopos.prod a (FreeTopos.list c)) e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        simp only [length_extEnv] at hds hrs
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ :=
          (ih X4 (by simp)).1 X e ΓLF (lrose X1) hΓ hm
        obtain rfl := encTy_inj (encTy_add hc) hrs
        obtain rfl := encTy_inj hrm (show encTy e.length (FreeTopos.lrose a) = some (lrose X1) by
          rw [encTy_lrose, ha]; rfl)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_roseRec_of_parts
          (hIc) hcm (roseParts_lrose a) hcs
        refine ⟨FreeTopos.Internal.Term.roseRec c ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hds, hdm,
            decTy_encTy _ c X2 hc]
          rfl
        · rw [FreeTopos.Internal.Term.roseRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcm, FreeTopos.lrose, PartialHorn.op,
            RoseTree.label_node, RoseTree.children_node, Nat.reduceAdd, ha, hc, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (tm (coprod (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact tmComplete_inl hsg hk (ih X3 (by simp)) hΓ hS
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0)) (tm (coprod (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact tmComplete_inr hsg hk (ih X3 (by simp)) hΓ hS
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (exp (v 2) (v 0))
            (exp (v 1) (v 0)))) (tm (exp (coprod (v 2) (v 1)) (v 0))))))))
        obtain ⟨X1, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact tmComplete_case hsg hk (ih X4 (by simp)) hΓ hS

end Completeness

end Geb.LF.Topos

end
