/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PHOAS.Dual
public import Geb.Prototypes.PHOAS.Initial
public import Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.Types.End
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Whiskering

set_option doc.verso true in
/-!
# Categorical polynomial profunctors and their ends

The polynomial interpretation and its pointwise free monad are profunctors on types.
The compatible families of {name}`Geb.PHOAS.PProfunctor.End` are equivalent to mathlib's
explicit end, which has the limiting-wedge universal property.

## Main definitions

* {lit}`profunctor` and {lit}`freeProfunctor` package the two interpretations.
* {lit}`endEquiv` identifies compatible families with mathlib's explicit end.
* {lit}`algebraProfunctor` and {lit}`coalgebraProfunctor` package the derived profunctors.
* {lit}`contextExtensionFunctor` precomposes a context functor with adjoining bound variables.
* {lit}`bindingFunctor` is the binding-signature endofunctor on functors of contexts.
* {lit}`scopedAlgebra` equips the scoped family with its variable and binding constructors.

## Main statements

* {lit}`endIsLimit` supplies the universal property of the end.
* {lit}`scopedIsInitial` characterizes the whole scoped family as the initial binding algebra.
  Its morphism to a model is the natural fold, uniquely determined by the constructors.
* {lit}`endIsoInitial` identifies the closed end with the empty-context component of any
  initial binding algebra, independently of its implementation.
* {lit}`not_isInitial` and {lit}`not_isTerminal` rule out diagonal universal objects when
  the signature has distinct positions.
* {lit}`kmett_not_isInitial` and {lit}`kmett_not_isTerminal` exclude the corresponding
  universal objects for Kmett's derived algebra and coalgebra profunctors.

## Implementation notes

The value universe is raised before taking the end over a universe of types. This module
packages the constructive data in mathlib's category theory, whose proofs use choice.
The binding algebra uses {lit}`Type u` as its category of contexts and
{lit}`Type (max uA uB (u + 1))` as its value category, accommodating the end's universe.
Its initiality applies to functors on all contexts in that universe, with arbitrary arities.

## Tags

profunctor, end, polynomial functor, free monad
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PHOAS.PProfunctor

open CategoryTheory Opposite

universe uA uB uC u v

variable (P : PProfunctor.{uA, uB, uC})

/-- The polynomial interpretation as a categorical profunctor. -/
def profunctor : (Type u)ᵒᵖ ⥤ Type v ⥤ Type (max uA uB uC u v) where
  obj X := ofTypeFunctor (P.apply X.unop).Obj
  map f := { app := fun _ ↦ ↾(P.dimap f.unop.hom id), naturality := by intros; rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The pointwise free monads form a profunctor. The covariant functor and its laws come
from CSLib's lawful monad; input renaming supplies the outer action. -/
def freeProfunctor : (Type u)ᵒᵖ ⥤ Type v ⥤ Type (max uA uB uC u v) where
  obj X := ofTypeFunctor (P.Free X.unop)
  map f :=
    { app := fun _ ↦ ↾(Free.comap f.unop.hom)
      naturality := by
        intro Y Y' g
        ext t
        exact Free.comap_map f.unop.hom g.hom t }
  map_id X := by
    ext Y t
    exact Free.comap_id t
  map_comp f g := by
    ext Y t
    exact (Free.comap_comp f.unop.hom g.unop.hom t).symm

/-- Raise only the value universe so the end ranges over all types in {lit}`Type u`. -/
def liftedFreeProfunctor :
    (Type u)ᵒᵖ ⥤ Type u ⥤ Type (max uA uB uC (u + 1)) :=
  P.freeProfunctor ⋙ (CategoryTheory.Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1}

/-- Compatible families are mathlib's explicit end, with the value lift removed. -/
def endEquiv : P.End.{uA, uB, uC, u} ≃
    Limits.Types.end_.{max uA uB uC, u, u + 1} (liftedFreeProfunctor.{uA, uB, uC, u} P) where
  toFun e := ⟨fun X ↦ ULift.up (e.eval X), fun _ _ f ↦ congrArg ULift.up (e.wedge f.hom)⟩
  invFun e := ⟨fun X ↦ (e.val X).down, fun {_ _} f ↦ congrArg ULift.down (e.property (↾f))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Mathlib's explicit end has the limiting-wedge universal property. -/
def endIsLimit :
    Limits.IsLimit (Limits.Types.wedge.{max uA uB uC, u, u + 1}
      (liftedFreeProfunctor.{uA, uB, uC, u} P)) :=
  Limits.Types.wedgeIsLimit.{max uA uB uC, u, u + 1} (liftedFreeProfunctor.{uA, uB, uC, u} P)

/-- The category of one-object profunctor algebras from the nLab definition. -/
instance diagonalCategory : Category (P.Diagonal.{uA, uB, uC, u}) where
  Hom := Diagonal.Hom
  id _ := ⟨id, rfl⟩
  comp {s t r} f g := ⟨g.val ∘ f.val, by
    calc
      P.dimap id (g.val ∘ f.val) s.2 = P.dimap id g.val (P.dimap id f.val s.2) := rfl
      _ = P.dimap id g.val (P.dimap f.val id t.2) := congrArg (P.dimap id g.val) f.property
      _ = P.dimap f.val id (P.dimap id g.val t.2) := rfl
      _ = P.dimap f.val id (P.dimap g.val id r.2) := congrArg (P.dimap f.val id) g.property
      _ = P.dimap (g.val ∘ f.val) id r.2 := rfl⟩

/-- Distinct positions rule out every initial object in the diagonal-element category. -/
theorem not_isInitial (a b : P.A) (hab : a ≠ b) (s : P.Diagonal.{uA, uB, uC, u}) :
    ¬Nonempty (Limits.IsInitial s) := by
  rintro ⟨h⟩
  exact hab (Diagonal.positions_eq_of_weakly_initial s (fun t ↦ ⟨h.to t⟩) a b)

/-- Distinct positions also rule out every terminal object. -/
theorem not_isTerminal (a b : P.A) (hab : a ≠ b) (s : P.Diagonal.{uA, uB, uC, u}) :
    ¬Nonempty (Limits.IsTerminal s) := by
  rintro ⟨h⟩
  exact hab (Diagonal.positions_eq_of_weakly_terminal s (fun t ↦ ⟨h.from t⟩) a b)

/-- The derived algebra profunctor has diagonal elements {lit}`P(X, X) → X`. -/
def algebraProfunctor : (Type u)ᵒᵖ ⥤ Type v ⥤ Type (max uA uB uC u v) where
  obj X :=
    { obj := fun Y ↦ P.AlgebraObj X.unop Y
      map := fun g ↦ ↾(P.algebraDimap id g.hom) }
  map f := { app := fun _ ↦ ↾(P.algebraDimap f.unop.hom id), naturality := by intros; rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The derived coalgebra profunctor has diagonal elements {lit}`X → P(X, X)`. -/
def coalgebraProfunctor : (Type u)ᵒᵖ ⥤ Type v ⥤ Type (max uA uB uC u v) where
  obj X :=
    { obj := fun Y ↦ P.CoalgebraObj X.unop Y
      map := fun g ↦ ↾(P.coalgebraDimap id g.hom) }
  map f := { app := fun _ ↦ ↾(P.coalgebraDimap f.unop.hom id), naturality := by intros; rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The category of algebras of the derived algebra profunctor. -/
instance algebraCategory : Category (P.Algebra.{uA, uB, uC, u}) where
  Hom := Algebra.Hom
  id _ := ⟨id, rfl⟩
  comp {s t r} f g := ⟨g.val ∘ f.val, by
    calc
      P.algebraDimap id (g.val ∘ f.val) s.2 =
          P.algebraDimap id g.val (P.algebraDimap id f.val s.2) := rfl
      _ = P.algebraDimap id g.val (P.algebraDimap f.val id t.2) :=
        congrArg (P.algebraDimap id g.val) f.property
      _ = P.algebraDimap f.val id (P.algebraDimap id g.val t.2) := rfl
      _ = P.algebraDimap f.val id (P.algebraDimap g.val id r.2) :=
        congrArg (P.algebraDimap f.val id) g.property
      _ = P.algebraDimap (g.val ∘ f.val) id r.2 := rfl⟩

/-- The category of algebras of the derived coalgebra profunctor. -/
instance coalgebraCategory : Category (P.Coalgebra.{uA, uB, uC, u}) where
  Hom := Coalgebra.Hom
  id _ := ⟨id, rfl⟩
  comp := Coalgebra.Hom.comp

/-- Kmett's derived algebra profunctor has no initial object. -/
theorem kmett_not_isInitial (s : Kmett.signature.Algebra.{0, 0, 0, u}) :
    ¬Nonempty (Limits.IsInitial s) := by
  rintro ⟨h⟩
  apply Kmett.no_initial_algebra s
  intro t
  exact ⟨{ default := h.to t, uniq := fun f ↦ h.hom_ext f (h.to t) }⟩

/-- Kmett's derived coalgebra profunctor has no terminal object. -/
theorem kmett_not_isTerminal (t : Kmett.signature.Coalgebra.{0, 0, 0, u}) :
    ¬Nonempty (Limits.IsTerminal t) := by
  rintro ⟨h⟩
  apply Kmett.no_terminal_coalgebra t
  intro s
  exact ⟨{ default := h.from s, uniq := fun f ↦ h.hom_ext f (h.from s) }⟩

section Binding

variable (Q : PProfunctor.{uA, uB, u})

/-- Adjoin a fixed type of bound variables to each context. -/
def contextExtension (C : Type u) : Type u ⥤ Type u where
  obj Γ := Γ ⊕ C
  map f := ↾(Sum.map f.hom id)
  map_id Γ := by ext x; cases x <;> rfl
  map_comp f g := by ext x; cases x <;> rfl

/-- Context extension on the functor category, with object action {lit}`M(Γ ⊕ C)`.
Its underlying family is {name}`ContextExtension`; binding nodes take a sum of products
of these extended families. -/
def contextExtensionFunctor (C : Type u) : (Type u ⥤ Type v) ⥤ (Type u ⥤ Type v) :=
  (Functor.whiskeringLeft (Type u) (Type u) (Type v)).obj (contextExtension C)

/-- The binding-signature operator applied to a functor of contexts. -/
def bindingObj (M : Type u ⥤ Type v) : Type u ⥤ Type (max uA uB u v) where
  obj Γ := Q.BindingLayer M.obj Γ
  map f := ↾(Sum.map f.hom (fun n ↦
    ⟨n.1, fun b ↦ (((contextExtensionFunctor ((Q.B n.1).B b)).obj M).map f) (n.2 b)⟩))
  map_id Γ := by
    ext x
    rcases x with x | ⟨a, k⟩
    · rfl
    · change (Sum.inr ⟨a, fun b ↦
        (M.map ((contextExtension ((Q.B a).B b)).map (𝟙 Γ))) (k b)⟩ : Q.BindingLayer M.obj Γ) = _
      apply congrArg Sum.inr
      apply congrArg (Sigma.mk a)
      funext b
      rw [(contextExtension ((Q.B a).B b)).map_id, M.map_id]
      rfl
  map_comp f g := by
    ext x
    rcases x with x | ⟨a, k⟩
    · rfl
    · simp only [Functor.map_comp]
      rfl

/-- The binding-signature operator maps a natural transformation at each extended context. -/
def bindingMap {M N : Type u ⥤ Type v} (h : M ⟶ N) : bindingObj Q M ⟶ bindingObj Q N where
  app Γ := ↾(Sum.map id (fun n ↦
    ⟨n.1, fun b ↦ (((contextExtensionFunctor ((Q.B n.1).B b)).map h).app Γ) (n.2 b)⟩))
  naturality {Γ Δ} f := by
    ext x
    rcases x with x | ⟨a, k⟩
    · rfl
    · apply congrArg Sum.inr
      apply congrArg (Sigma.mk a)
      funext b
      exact congrArg (fun h ↦ h (k b)) (h.naturality ((contextExtension ((Q.B a).B b)).map f))

/-- The endofunctor {lit}`Id + H` on context functors, where {lit}`Id` is the variable
family and {lit}`H` takes the sum of products of the specified context extensions. -/
def bindingFunctor : (Type u ⥤ Type (max uA uB u v)) ⥤ (Type u ⥤ Type (max uA uB u v)) where
  obj := bindingObj Q
  map := bindingMap Q
  map_id _ := by ext Γ x; cases x <;> rfl
  map_comp _ _ := by ext Γ x; cases x <;> rfl

/-- Scoped terms form a functor of contexts by variable renaming. -/
def scopedFunctor : Type u ⥤ Type (max uA uB (u + 1)) where
  obj Γ := Q.Scoped.{uA, uB, u, u, u} Γ
  map f := ↾(Scoped.rename f.hom)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The variable and binding constructors give an algebra on the scoped family. -/
def scopedAlgebra : Endofunctor.Algebra (bindingFunctor.{uA, uB, u, u + 1} Q) where
  a := scopedFunctor Q
  str :=
    { app Γ := ↾Scoped.roll
      naturality {Γ Δ} f := by
        ext x
        rcases x with x | ⟨a, k⟩
        · rfl
        · exact (Scoped.rename_node f.hom a k).symm }

/-- The scoped fold is natural for every algebra of the binding-signature functor. -/
def scopedFold (M : Endofunctor.Algebra (bindingFunctor.{uA, uB, u, u + 1} Q)) :
    scopedFunctor Q ⟶ M.a where
  app Γ := ↾(Scoped.fold (fun Γ x ↦ M.str.app Γ (.inl x))
    (fun Γ a k ↦ M.str.app Γ (.inr ⟨a, k⟩)))
  naturality {Γ Δ} f := by
    ext t
    symm
    refine Scoped.fold_rename (P := Q) (fun Γ x ↦ M.str.app Γ (.inl x))
      (fun Γ a k ↦ M.str.app Γ (.inr ⟨a, k⟩)) (fun f ↦ (M.a.map (↾f)).hom) ?_ ?_ f.hom t
    · intro Γ Δ f x
      exact (congrArg (fun h ↦ h (.inl x)) (M.str.naturality (↾f))).symm
    · intro Γ Δ f a k
      exact (congrArg (fun h ↦ h (.inr ⟨a, k⟩)) (M.str.naturality (↾f))).symm

/-- The natural scoped fold preserves the algebra structure. -/
def scopedFoldHom (M : Endofunctor.Algebra (bindingFunctor.{uA, uB, u, u + 1} Q)) :
    scopedAlgebra Q ⟶ M where
  f := scopedFold Q M
  h := by
    ext Γ x
    rcases x with x | ⟨a, k⟩
    · rfl
    · exact (Scoped.fold_node (P := Q) (fun Γ x ↦ M.str.app Γ (.inl x))
        (fun Γ a k ↦ M.str.app Γ (.inr ⟨a, k⟩)) a k).symm

/-- Every algebra homomorphism from scoped syntax is its fold. -/
theorem scopedFold_unique (M : Endofunctor.Algebra (bindingFunctor.{uA, uB, u, u + 1} Q))
    (h : scopedAlgebra Q ⟶ M) : h = scopedFoldHom Q M := by
  have he := Scoped.fold_unique (fun Γ x ↦ M.str.app Γ (.inl x))
    (fun Γ a k ↦ M.str.app Γ (.inr ⟨a, k⟩)) (fun Γ t ↦ h.f.app Γ t)
    (fun Γ x ↦ (congrArg (fun α ↦ α.app Γ (.inl x)) h.h).symm)
    (fun Γ a k ↦ (congrArg (fun α ↦ α.app Γ (.inr ⟨a, k⟩)) h.h).symm)
  apply Endofunctor.Algebra.Hom.ext
  ext Γ t
  exact congrFun (congrFun he Γ) t

/-- The free-monad/end scoped family is the initial algebra of the binding-signature functor. -/
def scopedIsInitial : Limits.IsInitial (scopedAlgebra Q) :=
  Limits.IsInitial.ofUniqueHom (scopedFoldHom Q) (scopedFold_unique Q)

/-- The closed end is the empty-context component of any initial binding algebra. -/
def endIsoInitial (M : Endofunctor.Algebra (bindingFunctor.{uA, uB, u, u + 1} Q))
    (h : Limits.IsInitial M) : Q.End.{uA, uB, u, u} ≅ M.a.obj PEmpty.{u + 1} :=
  (Scoped.emptyEquivEnd (P := Q)).symm.toIso ≪≫
    ((Endofunctor.Algebra.forget _).mapIso ((scopedIsInitial Q).uniqueUpToIso h)).app PEmpty

end Binding

end Geb.PHOAS.PProfunctor
