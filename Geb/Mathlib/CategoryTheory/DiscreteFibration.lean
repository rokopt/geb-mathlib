/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Tactic.Attr.Core

/-!
# Discrete fibrations, presheaves, and categories of elements

The primary notion is `DiscreteFibration p`, a structure carrying, for
each `g : b ⟶ p.obj c`, a lift `hom g : src g ⟶ c` over `g` together with
the statement that it is the *only* lift (Loregian–Riehl, *Categorical
notions of fibration*, Def. 2.1.1).  Since lifts are unique, the structure
is a `Subsingleton`: carrying it as data costs nothing, and it lets the
fibre presheaf be *defined* without `Classical.choice`.

The pullback-square formulation (Loregian–Riehl Def. 2.1.3; nLab,
*discrete fibration*, internal formulation)

```
Arrow C ---right---> C
   |                 |
   | p               | p
   v                 v
Arrow B ---right---> B
```

is `IsDiscreteFibration p : Prop`, "`codPair p : Arrow C → Arrow B ×_B C`
is a bijection".  `DiscreteFibration p → IsDiscreteFibration p` is proved
without choice; the converse `IsDiscreteFibration.toDiscreteFibration`
needs choice and is isolated.

The nLab "discussion via category of elements", mechanised:

* `Functor.CoElements F`, the category of elements of `F : Bᵒᵖ ⥤ Type v`
  presented over `B` (mathlib's `Functor.Elements` presents it over
  `Bᵒᵖ`), with projection `Functor.CoElements.π F : F.CoElements ⥤ B` and
  `Functor.CoElements.discreteFibration F`.
* `DiscreteFibration.fibrePsh D : Bᵒᵖ ⥤ Type u`, the fibre presheaf
  `b ↦ p⁻¹(b)`, restriction along `g` being "domain of the unique lift".
* `DiscreteFibration.toElements` / `DiscreteFibration.ofElements`
  exhibiting `C` as isomorphic to `(fibrePsh D).CoElements` *over `B`*:
  both composites are identity functors and both functors commute with
  the projections.
* `Functor.CoElements.fibrePshIso F`:
  `(Functor.CoElements.discreteFibration F).fibrePsh ≅ F`.

Axiom budget (see the audit at the end of the file): every declaration
depends on at most `propext` and `Quot.sound`, except

* `IsDiscreteFibration.toDiscreteFibration` / `.nonempty`, which use
  `Classical.choice` on purpose, and
* the packaged statements mentioning `⋙` (`toElements_comp_π`,
  `ofElements_comp`, `toElements_comp_ofElements`,
  `ofElements_comp_toElements`) and `fibrePshIso` (built with
  `NatIso.ofComponents`), which inherit `Classical.choice` from
  mathlib's `Functor.comp` and `NatIso.ofComponents`, whose proof
  obligations mathlib discharges by classical automation.  Their
  elementwise counterparts (`π_toElements_obj`, `π_toElements_map`,
  `obj_ofElements_obj`, `map_ofElements_map`,
  `ofElements_obj_toElements_obj`, `ofElements_map_toElements_map`,
  `coElements_eq_toElements_obj`, `toElements_map_ofElements_map`,
  `fibrePshEquiv`, `fibrePshEquiv_restrict`) carry the same content within
  the `propext`/`Quot.sound` budget.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]

/-! ## 1. Discrete fibrations as lifting data -/

/-- Lifting data for `p`: for every `g : b ⟶ p.obj c` a lift
`hom g : src g ⟶ c` over `g`, unique among all lifts.  The base-side
`eqToHom` is forced by the *bundle* presentation (objects of `C` are only
propositionally over `b`); it vanishes in the *family* presentation
`Functor.CoElements` below. -/
structure DiscreteFibration (p : C ⥤ B) where
  /-- Domain of the lift of `g`. -/
  src : ∀ {b : B} {c : C}, (b ⟶ p.obj c) → C
  /-- The lift of `g`. -/
  hom : ∀ {b : B} {c : C} (g : b ⟶ p.obj c), src g ⟶ c
  obj_src : ∀ {b : B} {c : C} (g : b ⟶ p.obj c), p.obj (src g) = b
  map_hom : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
    p.map (hom g) = eqToHom (obj_src g) ≫ g
  /-- Uniqueness of lifts, as an equality in `Σ c', c' ⟶ c`. -/
  unique : ∀ {b : B} {c : C} (g : b ⟶ p.obj c) {c' : C} (h : c' ⟶ c)
    (e : p.obj c' = b), p.map h = eqToHom e ≫ g →
      (⟨c', h⟩ : Σ c', c' ⟶ c) = ⟨src g, hom g⟩

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- The uniqueness clause with the source fixed: `p` reflects equality of
parallel arrows, i.e. `p` is faithful. -/
theorem map_injective {c c' : C} {h₁ h₂ : c' ⟶ c}
    (H : p.map h₁ = p.map h₂) : h₁ = h₂ := by
  have h := (D.unique (p.map h₂) h₁ rfl (by simpa using H)).trans
    (D.unique (p.map h₂) h₂ rfl (by simp)).symm
  exact eq_of_heq (Sigma.mk.inj_iff.1 h).2

theorem faithful : p.Faithful := ⟨fun H => D.map_injective H⟩

/-- Uniqueness of the source of a lift. -/
theorem src_eq {b : B} {c c' : C} (g : b ⟶ p.obj c) (h : c' ⟶ c)
    (e : p.obj c' = b) (H : p.map h = eqToHom e ≫ g) : D.src g = c' :=
  (congrArg Sigma.fst (D.unique g h e H)).symm

theorem src_id (c : C) : D.src (𝟙 (p.obj c)) = c :=
  D.src_eq _ (𝟙 c) rfl (by simp)

/-- Lifting data is unique: `DiscreteFibration p` is a mere proposition. -/
instance : Subsingleton (DiscreteFibration p) := by
  constructor
  intro D₁ D₂
  have h : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
      (⟨D₁.src g, D₁.hom g⟩ : Σ c', c' ⟶ c) =
        ⟨D₂.src g, D₂.hom g⟩ :=
    fun g => D₂.unique g (D₁.hom g) (D₁.obj_src g) (D₁.map_hom g)
  obtain ⟨src₁, hom₁, _, _, _⟩ := D₁
  obtain ⟨src₂, hom₂, _, _, _⟩ := D₂
  have hs : @src₁ = @src₂ := by
    funext b c g
    exact congrArg Sigma.fst (h g)
  subst hs
  have hh : @hom₁ = @hom₂ := by
    funext b c g
    exact eq_of_heq (Sigma.mk.inj_iff.1 (h g)).2
  subst hh
  rfl

end DiscreteFibration

/-! ## 2. Mathlib's `IsHomLift` -/

/-- Mathlib's `IsHomLift` is the proposition
`Arrow.mk (p.map φ) = Arrow.mk f`. -/
theorem isHomLift_iff_arrow_mk_eq (p : C ⥤ B) {R S : B} {a b : C}
    (f : R ⟶ S) (φ : a ⟶ b) :
    p.IsHomLift f φ ↔ Arrow.mk (p.map φ) = Arrow.mk f := by
  constructor
  · intro h
    exact (Arrow.mk_eq_mk_iff _ _).2
      ⟨IsHomLift.domain_eq p f φ, IsHomLift.codomain_eq p f φ,
        IsHomLift.fac' p f φ⟩
  · intro h
    obtain ⟨hR, hS, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
    exact IsHomLift.of_fac' p f φ hR hS hf

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- The lift of `g` as an arrow of `C`. -/
def liftArrow {b : B} {c : C} (g : b ⟶ p.obj c) : Arrow C :=
  Arrow.mk (D.hom g)

theorem arrow_mk_map_hom {b : B} {c : C} (g : b ⟶ p.obj c) :
    Arrow.mk (p.map (D.hom g)) = Arrow.mk g :=
  (Arrow.mk_eq_mk_iff _ _).2 ⟨D.obj_src g, rfl, by simp [D.map_hom]⟩

theorem isHomLift_hom {b : B} {c : C} (g : b ⟶ p.obj c) :
    p.IsHomLift g (D.hom g) :=
  (isHomLift_iff_arrow_mk_eq p g (D.hom g)).2 (D.arrow_mk_map_hom g)

/-- Uniqueness of lifts, `Arrow`-style. -/
theorem eq_liftArrow {b : B} {c : C} (g : b ⟶ p.obj c) {c' : C}
    (h : c' ⟶ c) (hh : Arrow.mk (p.map h) = Arrow.mk g) :
    Arrow.mk h = D.liftArrow g := by
  obtain ⟨e, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 hh
  have hu := D.unique g h e (by simpa using hf)
  obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.1 hu
  simp only [liftArrow]
  subst h1
  rw [eq_of_heq h2]

end DiscreteFibration

/-! ## 3. The codomain square -/

/-- The set-theoretic pullback `Arrow B ×_B C` of `right : Arrow B → B`
along `p : C → B`: an arrow of `B` with an object of `C` over its
codomain. -/
abbrev CodPullback (p : C ⥤ B) : Type (max u₁ u₂ v₂) :=
  { q : Arrow B × C // q.1.right = p.obj q.2 }

/-- The comparison map `(p, right) : Arrow C → Arrow B ×_B C`. -/
def codPair (p : C ⥤ B) (a : Arrow C) : CodPullback p :=
  ⟨(Arrow.mk (p.map a.hom), a.right), rfl⟩

@[simp] theorem codPair_val (p : C ⥤ B) (a : Arrow C) :
    (codPair p a).1 = (Arrow.mk (p.map a.hom), a.right) := rfl

/-- The pullback-square formulation: `p` is a discrete fibration iff its
codomain square is a pullback of sets, i.e. iff `codPair p` is a
bijection. -/
def IsDiscreteFibration (p : C ⥤ B) : Prop := Function.Bijective (codPair p)

/-- Lifting data forces the codomain square to be a pullback.
No choice is used. -/
theorem DiscreteFibration.isDiscreteFibration {p : C ⥤ B}
    (D : DiscreteFibration p) : IsDiscreteFibration p := by
  constructor
  · rintro ⟨x₁, y₁, f₁⟩ ⟨x₂, y₂, f₂⟩ h
    have hy : y₁ = y₂ := congrArg (fun q : CodPullback p => q.1.2) h
    subst hy
    have hf : Arrow.mk (p.map f₁) = Arrow.mk (p.map f₂) :=
      congrArg (fun q : CodPullback p => q.1.1) h
    exact (D.eq_liftArrow (p.map f₂) f₁ hf).trans
      (D.eq_liftArrow (p.map f₂) f₂ rfl).symm
  · rintro ⟨⟨⟨X, Y, g⟩, c⟩, (hg : Y = p.obj c)⟩
    subst hg
    exact ⟨D.liftArrow g, Subtype.ext (Prod.ext (D.arrow_mk_map_hom g) rfl)⟩

/-- Auxiliary: an arrow equal to `Arrow.mk h` gives back `h` up to
transport of the codomain. -/
theorem sigma_eq_of_arrow_eq {c c' : C} (h : c' ⟶ c) (a : Arrow C)
    (ha' : a = Arrow.mk h) (ha : a.right = c) :
    (⟨c', h⟩ : Σ c', c' ⟶ c) = ⟨a.left, a.hom ≫ eqToHom ha⟩ := by
  subst ha'
  simp

/-- The bijection `Arrow C ≃ Arrow B ×_B C` of a discrete fibration in the
pullback-square sense.  Classical: `Equiv.ofBijective` uses choice. -/
noncomputable def IsDiscreteFibration.equiv {p : C ⥤ B}
    (H : IsDiscreteFibration p) : Arrow C ≃ CodPullback p :=
  Equiv.ofBijective _ H

theorem IsDiscreteFibration.equiv_apply {p : C ⥤ B}
    (H : IsDiscreteFibration p) (a : Arrow C) : H.equiv a = codPair p a := rfl

/-- Classical converse: a bijective `codPair p` yields lifting data.  Uses
`Classical.choice`; kept apart from the constructive development. -/
noncomputable def IsDiscreteFibration.toDiscreteFibration {p : C ⥤ B}
    (H : IsDiscreteFibration p) : DiscreteFibration p := by
  have hl : ∀ q, codPair p (H.equiv.symm q) = q := fun q =>
    (H.equiv_apply _).symm.trans (H.equiv.apply_symm_apply q)
  have hr : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
      (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).right = c :=
    fun g => congrArg (fun q : CodPullback p => q.1.2) (hl _)
  have hm : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
      Arrow.mk (p.map (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).hom) =
        Arrow.mk g :=
    fun g => congrArg (fun q : CodPullback p => q.1.1) (hl _)
  refine
    { src := fun {b c} g => (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).left
      hom := fun {b c} g =>
        (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).hom ≫ eqToHom (hr g)
      obj_src := fun {b c} g =>
        congrArg (fun q : CodPullback p => q.1.1.left) (hl _)
      map_hom := fun {b c} g => ?_
      unique := fun {b c} g {c'} h eh hh => ?_ }
  · obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (hm g)
    simp only [Functor.map_comp, eqToHom_map, hf]
    simp
  · refine sigma_eq_of_arrow_eq h _ ?_ (hr g)
    apply H.equiv.injective
    rw [H.equiv.apply_symm_apply, H.equiv_apply]
    exact Subtype.ext (Prod.ext
      ((Arrow.mk_eq_mk_iff _ _).2 ⟨eh, rfl, by simpa using hh⟩).symm rfl)

theorem IsDiscreteFibration.nonempty {p : C ⥤ B}
    (H : IsDiscreteFibration p) : Nonempty (DiscreteFibration p) :=
  ⟨H.toDiscreteFibration⟩

/-! ## 4. The category of elements of a presheaf -/

/-- The category of elements of a presheaf `F : Bᵒᵖ ⥤ Type v₃`, presented
over `B`: the opposite of mathlib's `Functor.Elements`, which presents it
over `Bᵒᵖ`.  An object is an object `b` of `B` with an element of `F b`,
and a morphism `⟨b, x⟩ ⟶ ⟨b', x'⟩` is a morphism `g : b ⟶ b'` of `B` with
`F g x' = x`.

The `Co` prefix marks the presentation whose morphisms are morphisms of
the base rather than of its opposite, as in `CoGrothendieck`. -/
@[implicit_reducible]
def Functor.CoElements (F : Bᵒᵖ ⥤ Type v₃) : Type (max u₂ v₃) := F.Elementsᵒᵖ

namespace Functor.CoElements

/-- The category structure on `F.CoElements`, inherited from the opposite
of `F.Elements`. -/
instance category (F : Bᵒᵖ ⥤ Type v₃) : Category.{v₂} F.CoElements :=
  inferInstanceAs (Category F.Elementsᵒᵖ)

variable {F : Bᵒᵖ ⥤ Type v₃}

/-- The object of `B` an element lies over. -/
def base (x : F.CoElements) : B := (Opposite.unop x).1.unop

/-- The element of `F` at `base x`. -/
def elt (x : F.CoElements) : F.obj (op x.base) := (Opposite.unop x).2

/-- An object of `F.CoElements` from an object of `B` and an element. -/
def mk (b : B) (x : F.obj (op b)) : F.CoElements := Opposite.op ⟨op b, x⟩

@[simp] theorem base_mk (b : B) (x : F.obj (op b)) : (mk b x).base = b := rfl

@[simp] theorem elt_mk (b : B) (x : F.obj (op b)) : (mk b x).elt = x := rfl

@[simp] theorem mk_base_elt (x : F.CoElements) : mk x.base x.elt = x := rfl

/-- The morphism of `B` underlying a morphism of `F.CoElements`. -/
def homBase {x y : F.CoElements} (f : x ⟶ y) : x.base ⟶ y.base :=
  (Quiver.Hom.unop f).1.unop

/-- The compatibility equation a morphism of `F.CoElements` satisfies. -/
theorem map_homBase_elt {x y : F.CoElements} (f : x ⟶ y) :
    F.map (homBase f).op y.elt = x.elt := (Quiver.Hom.unop f).2

/-- A morphism of `F.CoElements` from a morphism of `B` and the
compatibility equation. -/
def homMk {x y : F.CoElements} (g : x.base ⟶ y.base)
    (hg : F.map g.op y.elt = x.elt) : x ⟶ y :=
  Quiver.Hom.op (CategoryOfElements.homMk (Opposite.unop y) (Opposite.unop x) g.op hg)

@[simp] theorem homBase_homMk {x y : F.CoElements} (g : x.base ⟶ y.base)
    (hg : F.map g.op y.elt = x.elt) : homBase (homMk g hg) = g := rfl

@[ext] theorem hom_ext {x y : F.CoElements} {f g : x ⟶ y}
    (h : homBase f = homBase g) : f = g :=
  Quiver.Hom.unop_inj (Subtype.ext (Quiver.Hom.unop_inj h))

@[simp] theorem homBase_id (x : F.CoElements) : homBase (𝟙 x) = 𝟙 x.base := rfl

@[simp] theorem homBase_comp {x y z : F.CoElements} (f : x ⟶ y) (g : y ⟶ z) :
    homBase (f ≫ g) = homBase f ≫ homBase g := rfl

@[simp] theorem homBase_eqToHom {x y : F.CoElements} (h : x = y) :
    homBase (eqToHom h) = eqToHom (congrArg base h) := by
  subst h; rfl

/-- The projection `∫F ⥤ B`. -/
def π (F : Bᵒᵖ ⥤ Type v₃) : F.CoElements ⥤ B where
  obj x := x.base
  map f := homBase f

@[simp] theorem π_obj (x : F.CoElements) : (π F).obj x = x.base := rfl

@[simp] theorem π_map {x y : F.CoElements} (f : x ⟶ y) :
    (π F).map f = homBase f := rfl

/-- Every morphism of `F.CoElements` is the canonical lift of its image in
`B`: a morphism into `y` over `g : b ⟶ y.base` has source `mk b (F g y.elt)`
and equals `homMk g rfl`.  The compatibility equation is left loose so that
it can be substituted. -/
theorem sigma_eq (b : B) (e : F.obj (op b)) (y : F.CoElements)
    (g : b ⟶ y.base) (hg : F.map g.op y.elt = e) :
    (⟨mk b e, homMk g hg⟩ : Σ x, x ⟶ y) =
      ⟨mk b (F.map g.op y.elt), homMk g rfl⟩ := by
  subst hg
  rfl

/-- The lift of `g : b ⟶ b'` with codomain `⟨b', x'⟩` is
`g : ⟨b, F g x'⟩ ⟶ ⟨b', x'⟩`.  No `eqToHom` occurs: the source is
*computed*, not merely known to exist. -/
def discreteFibration (F : Bᵒᵖ ⥤ Type v₃) : DiscreteFibration (π F) where
  src {b y} g := mk b (F.map g.op y.elt)
  hom {_ _} g := homMk g rfl
  obj_src _ := rfl
  map_hom _ := (Category.id_comp _).symm
  unique {b y} g {x} f e hh := by
    obtain rfl : x.base = b := e
    have hg : homBase f = g := hh.trans (Category.id_comp g)
    subst hg
    exact sigma_eq x.base x.elt y (homBase f) (map_homBase_elt f)

theorem isDiscreteFibration_π (F : Bᵒᵖ ⥤ Type v₃) :
    IsDiscreteFibration (π F) :=
  (discreteFibration F).isDiscreteFibration

end Functor.CoElements

/-! ## 5. The fibre presheaf of a discrete fibration -/

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- Restriction along `g : b ⟶ b'` of a fibre element `c'` over `b'`: the
domain of the unique lift of `g` with codomain `c'`. -/
def restrict {b b' : B} (g : b ⟶ b') (c' : p.Fiber b') : p.Fiber b :=
  ⟨D.src (g ≫ eqToHom c'.2.symm), D.obj_src _⟩

@[simp] theorem restrict_val {b b' : B} (g : b ⟶ b') (c' : p.Fiber b') :
    (D.restrict g c').1 = D.src (g ≫ eqToHom c'.2.symm) := rfl

theorem restrict_id {b : B} (c : p.Fiber b) : D.restrict (𝟙 b) c = c :=
  Subtype.ext (D.src_eq _ (𝟙 c.1) c.2 (by simp))

theorem restrict_comp {b b' b'' : B} (g : b ⟶ b') (g' : b' ⟶ b'')
    (c : p.Fiber b'') :
    D.restrict (g ≫ g') c = D.restrict g (D.restrict g' c) := by
  apply Subtype.ext
  exact D.src_eq ((g ≫ g') ≫ eqToHom c.2.symm)
    (D.hom (g ≫ eqToHom (D.obj_src (g' ≫ eqToHom c.2.symm)).symm) ≫
      D.hom (g' ≫ eqToHom c.2.symm))
    (D.obj_src _) (by simp [D.map_hom])

/-- The fibre presheaf `b ↦ p⁻¹(b)` of a discrete fibration. -/
def fibrePsh : Bᵒᵖ ⥤ Type u₁ where
  obj b := p.Fiber b.unop
  map g := TypeCat.ofHom fun c => D.restrict g.unop c
  map_id _ := ConcreteCategory.hom_ext _ _ fun c => D.restrict_id c
  map_comp g g' :=
    ConcreteCategory.hom_ext _ _ fun c => D.restrict_comp g'.unop g.unop c

/-- The fibre presheaf's value on objects.  Not a `simp` lemma: it rewrites
the object arguments carried by the coercion in `fibrePsh_map`'s left-hand
side, which would take that lemma out of simp-normal form.  Mathlib omits
the corresponding `yoneda_obj_obj` for the same reason, supplying
`unif_hint`s instead. -/
theorem fibrePsh_obj (b : Bᵒᵖ) : D.fibrePsh.obj b = p.Fiber b.unop := rfl

@[simp] theorem fibrePsh_map {b b' : Bᵒᵖ} (g : b ⟶ b')
    (c : p.Fiber b.unop) : D.fibrePsh.map g c = D.restrict g.unop c := rfl

/-! ## 6. `C ≅ ∫(fibrePsh D)` over `B` -/

attribute [local simp] eqToHom_map

/-- An element of the fibre presheaf at `x` lies over `x.base`.  This
restates the fibre element's own property, whose type reads
`p.obj x.elt.1 = unop (op x.base)`: the `unop (op _)` blocks the `eqToHom`
composites below from matching. -/
theorem obj_elt (x : D.fibrePsh.CoElements) : p.obj x.elt.1 = x.base :=
  x.elt.2

/-- `c ↦ (p c, c)`. -/
def toElements : C ⥤ D.fibrePsh.CoElements where
  obj c := Functor.CoElements.mk (p.obj c) ⟨c, rfl⟩
  map {c c'} f :=
    Functor.CoElements.homMk (p.map f)
      (Subtype.ext (D.src_eq (p.map f ≫ eqToHom rfl) f rfl
        (by change p.map f = eqToHom rfl ≫ p.map f ≫ eqToHom rfl; simp)))
  map_id c := Functor.CoElements.hom_ext (p.map_id c)
  map_comp f g := Functor.CoElements.hom_ext (p.map_comp f g)

@[simp] theorem toElements_obj (c : C) :
    D.toElements.obj c =
      Functor.CoElements.mk (F := D.fibrePsh) (p.obj c) ⟨c, rfl⟩ := rfl

@[simp] theorem homBase_toElements_map {c c' : C} (f : c ⟶ c') :
    Functor.CoElements.homBase (D.toElements.map f) = p.map f := rfl

theorem obj_eq_src {x y : D.fibrePsh.CoElements} (f : x ⟶ y) :
    x.elt.1 = D.src (Functor.CoElements.homBase f ≫ eqToHom (D.obj_elt y).symm) :=
  (congrArg Subtype.val (Functor.CoElements.map_homBase_elt f)).symm

/-- The unique lift of `homBase f`, transported to a morphism between the
underlying objects of `C`. -/
def ofElementsMap {x y : D.fibrePsh.CoElements} (f : x ⟶ y) :
    x.elt.1 ⟶ y.elt.1 :=
  eqToHom (D.obj_eq_src f) ≫
    D.hom (Functor.CoElements.homBase f ≫ eqToHom (D.obj_elt y).symm)

theorem map_ofElementsMap {x y : D.fibrePsh.CoElements} (f : x ⟶ y) :
    p.map (D.ofElementsMap f) =
      eqToHom (D.obj_elt x) ≫ Functor.CoElements.homBase f ≫
        eqToHom (D.obj_elt y).symm := by
  rw [ofElementsMap, Functor.map_comp, eqToHom_map, D.map_hom]
  simp

/-- `(b, c) ↦ c`. -/
def ofElements : D.fibrePsh.CoElements ⥤ C where
  obj x := x.elt.1
  map f := D.ofElementsMap f
  map_id x :=
    D.map_injective (by rw [D.map_ofElementsMap, p.map_id]; simp)
  map_comp f g :=
    D.map_injective (by
      rw [D.map_ofElementsMap, p.map_comp, D.map_ofElementsMap,
        D.map_ofElementsMap]
      simp)

@[simp] theorem ofElements_obj (x : D.fibrePsh.CoElements) :
    D.ofElements.obj x = x.elt.1 := rfl

theorem map_ofElements_map {x y : D.fibrePsh.CoElements} (f : x ⟶ y) :
    p.map (D.ofElements.map f) =
      eqToHom (D.obj_elt x) ≫ Functor.CoElements.homBase f ≫
        eqToHom (D.obj_elt y).symm :=
  D.map_ofElementsMap f

/-! The "over `B`" statements come in two forms.  The elementwise ones
(`_obj`/`_map`) are the ones with the clean axiom budget.  The packaged
ones using `⋙` inherit `Classical.choice` from mathlib's `Functor.comp`
itself (whose functor laws are discharged by classical automation), not
from anything proved here. -/

theorem π_toElements_obj (c : C) :
    (Functor.CoElements.π D.fibrePsh).obj (D.toElements.obj c) = p.obj c := rfl

theorem π_toElements_map {c c' : C} (f : c ⟶ c') :
    (Functor.CoElements.π D.fibrePsh).map (D.toElements.map f) = p.map f := rfl

theorem obj_ofElements_obj (x : D.fibrePsh.CoElements) :
    p.obj (D.ofElements.obj x) = (Functor.CoElements.π D.fibrePsh).obj x :=
  D.obj_elt x

/-- `toElements` lies over `B`. -/
theorem toElements_comp_π :
    D.toElements ⋙ Functor.CoElements.π D.fibrePsh = p := rfl

/-- `ofElements` lies over `B`. -/
theorem ofElements_comp : D.ofElements ⋙ p = Functor.CoElements.π D.fibrePsh :=
  Functor.ext (fun x => D.obj_elt x) (fun x y f => by
    rw [Functor.comp_map, D.map_ofElements_map]
    rfl)

theorem ofElements_map_toElements_map {c c' : C} (f : c ⟶ c') :
    D.ofElements.map (D.toElements.map f) = f := by
  apply D.map_injective
  rw [D.map_ofElements_map]
  change 𝟙 _ ≫ p.map f ≫ 𝟙 _ = p.map f
  simp

theorem ofElements_obj_toElements_obj (c : C) :
    D.ofElements.obj (D.toElements.obj c) = c := rfl

theorem toElements_comp_ofElements : D.toElements ⋙ D.ofElements = 𝟭 C :=
  Functor.ext (fun c => rfl) (fun c c' f => by
    change D.ofElements.map (D.toElements.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
    rw [D.ofElements_map_toElements_map, Category.id_comp, Category.comp_id])

/-- An element of a fibre is `toElements` of its underlying object of
`C`. -/
theorem mk_eq_toElements_obj {b : B} (c : p.Fiber b) :
    Functor.CoElements.mk (F := D.fibrePsh) b c = D.toElements.obj c.1 := by
  obtain ⟨c, rfl⟩ := c
  rfl

/-- Every object of the category of elements of `fibrePsh D` is
`toElements` of its underlying object of `C`. -/
theorem coElements_eq_toElements_obj (x : D.fibrePsh.CoElements) :
    x = D.toElements.obj x.elt.1 :=
  (Functor.CoElements.mk_base_elt x).symm.trans (D.mk_eq_toElements_obj x.elt)

theorem toElements_map_ofElements_map {c c' : C}
    (f : D.toElements.obj c ⟶ D.toElements.obj c') :
    D.toElements.map (D.ofElements.map f) = f :=
  Functor.CoElements.hom_ext (by
    rw [homBase_toElements_map, D.map_ofElements_map]
    change 𝟙 _ ≫ Functor.CoElements.homBase f ≫ 𝟙 _ =
      Functor.CoElements.homBase f
    rw [Category.id_comp, Category.comp_id])

theorem ofElements_comp_toElements :
    D.ofElements ⋙ D.toElements = 𝟭 D.fibrePsh.CoElements :=
  Functor.ext (fun x => (D.coElements_eq_toElements_obj x).symm) (fun x y f => by
    obtain ⟨c, rfl⟩ : ∃ c, x = D.toElements.obj c :=
      ⟨_, D.coElements_eq_toElements_obj x⟩
    obtain ⟨c', rfl⟩ : ∃ c', y = D.toElements.obj c' :=
      ⟨_, D.coElements_eq_toElements_obj y⟩
    change D.toElements.map (D.ofElements.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
    rw [D.toElements_map_ofElements_map, Category.id_comp, Category.comp_id])

end DiscreteFibration

/-! ## 7. The other round trip: `fibrePsh (π F) ≅ F` -/

namespace Functor.CoElements

variable (F : Bᵒᵖ ⥤ Type v₃)

/-- Choice-free and universe-free form of `fibrePshIso` below: the fibre of
`π F` over `b` is in bijection with `F b`. -/
def fibrePshEquiv (b : B) : (π F).Fiber b ≃ F.obj (op b)
    where
  toFun x := F.map (eqToHom x.2.symm).op x.1.elt
  invFun y := ⟨mk b y, rfl⟩
  left_inv x := by
    obtain ⟨x, hb⟩ := x
    subst hb
    refine Subtype.ext ?_
    exact (congrArg (mk x.base)
      (ConcreteCategory.congr_hom (F.map_id (op x.base)) x.elt)).trans
      (mk_base_elt x)
  right_inv y :=
    show F.map (𝟙 (op b)) y = y from
      ConcreteCategory.congr_hom (F.map_id _) y

/-- Naturality of `fibrePshEquiv`: restriction in the fibre presheaf of
`π F` is restriction in `F`. -/
theorem fibrePshEquiv_restrict {b b' : B} (g : b ⟶ b')
    (x : (π F).Fiber b') :
    fibrePshEquiv F b ((discreteFibration F).restrict g x) =
      F.map g.op (fibrePshEquiv F b' x) := by
  obtain ⟨x, hb⟩ := x
  subst hb
  change F.map (𝟙 _) (F.map (g ≫ 𝟙 _).op x.elt) =
    F.map g.op (F.map (𝟙 _) x.elt)
  rw [Category.comp_id, F.map_id, F.map_id]
  rfl

/-- The fibre presheaf of `π F` is naturally isomorphic to `F` (up to the
universe lift forced by `F.CoElements : Type (max u₂ v₃)`): the fibre over
`b` is `{x : F.CoElements // x.base = b}`, and `x ↦ x.elt`, transported
along `x.base = b`, is a bijection onto `F b`. -/
def fibrePshIso :
    (discreteFibration F).fibrePsh ≅ F ⋙ uliftFunctor.{u₂, v₃} :=
  NatIso.ofComponents
    (fun b => ((fibrePshEquiv F b.unop).trans Equiv.ulift.symm).toIso)
    (fun {b b'} g => ConcreteCategory.hom_ext _ _ fun x => by
      have h := fibrePshEquiv_restrict F g.unop x
      rw [Quiver.Hom.op_unop] at h
      exact congrArg ULift.up h)

end Functor.CoElements

end CategoryTheory
