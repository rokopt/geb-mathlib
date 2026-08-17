/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
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

* `Elts F`, the category of elements of `F : Bᵒᵖ ⥤ Type v`, with
  projection `Elts.π F : Elts F ⥤ B` and `Elts.discreteFibration F`.
* `DiscreteFibration.fibrePsh D : Bᵒᵖ ⥤ Type u`, the fibre presheaf
  `b ↦ p⁻¹(b)`, restriction along `g` being "domain of the unique lift".
* `DiscreteFibration.toElts` / `DiscreteFibration.ofElts` exhibiting `C`
  as isomorphic to `Elts (fibrePsh D)` *over `B`*: both composites are
  identity functors and both functors commute with the projections.
* `Elts.fibrePshIso F : (Elts.discreteFibration F).fibrePsh ≅ F`.

Axiom budget (see the audit at the end of the file): every declaration
depends on at most `propext` and `Quot.sound`, except

* `IsDiscreteFibration.toDiscreteFibration` / `.nonempty`, which use
  `Classical.choice` on purpose, and
* the packaged statements mentioning `⋙` (`toElts_comp_π`, `ofElts_comp`,
  `toElts_comp_ofElts`, `ofElts_comp_toElts`) and `fibrePshIso` (built
  with `NatIso.ofComponents`), which inherit `Classical.choice` from
  mathlib's `Functor.comp` and `NatIso.ofComponents`, whose proof
  obligations mathlib discharges by classical automation.  Their
  elementwise counterparts (`π_toElts_obj`, `π_toElts_map`,
  `obj_ofElts_obj`, `map_ofElts_map`, `ofElts_obj_toElts_obj`,
  `ofElts_map_toElts_map`, `elts_eq_toElts_obj`, `toElts_map_ofElts_map`,
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
propositionally over `b`); it vanishes in the *family* presentation `Elts`
below. -/
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

/-! ## 2. Equality of arrows and mathlib's `IsHomLift` -/

/-- Two arrows are equal iff their endpoints are equal and the homs agree
up to the induced transports.  The only place `HEq` on homs is unpacked. -/
theorem arrow_mk_eq_iff {X Y X' Y' : B} (f : X ⟶ Y) (g : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk g ↔
      ∃ (hX : X = X') (hY : Y = Y'),
        f = eqToHom hX ≫ g ≫ eqToHom hY.symm := by
  constructor
  · intro h
    have hX : X = X' := congrArg Comma.left h
    have hY : Y = Y' := congrArg Comma.right h
    subst hX hY
    exact ⟨rfl, rfl, by simpa using (Arrow.mk_inj _ _).1 h⟩
  · rintro ⟨hX, hY, hfg⟩
    subst hX hY
    simpa using congrArg Arrow.mk hfg

/-- Mathlib's `IsHomLift` is the proposition
`Arrow.mk (p.map φ) = Arrow.mk f`. -/
theorem isHomLift_iff_arrow_mk_eq (p : C ⥤ B) {R S : B} {a b : C}
    (f : R ⟶ S) (φ : a ⟶ b) :
    p.IsHomLift f φ ↔ Arrow.mk (p.map φ) = Arrow.mk f := by
  constructor
  · intro h
    exact (arrow_mk_eq_iff _ _).2
      ⟨IsHomLift.domain_eq p f φ, IsHomLift.codomain_eq p f φ,
        IsHomLift.fac' p f φ⟩
  · intro h
    obtain ⟨hR, hS, hf⟩ := (arrow_mk_eq_iff _ _).1 h
    exact IsHomLift.of_fac' p f φ hR hS hf

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- The lift of `g` as an arrow of `C`. -/
def liftArrow {b : B} {c : C} (g : b ⟶ p.obj c) : Arrow C :=
  Arrow.mk (D.hom g)

theorem arrow_mk_map_hom {b : B} {c : C} (g : b ⟶ p.obj c) :
    Arrow.mk (p.map (D.hom g)) = Arrow.mk g :=
  (arrow_mk_eq_iff _ _).2 ⟨D.obj_src g, rfl, by simp [D.map_hom]⟩

theorem isHomLift_hom {b : B} {c : C} (g : b ⟶ p.obj c) :
    p.IsHomLift g (D.hom g) :=
  (isHomLift_iff_arrow_mk_eq p g (D.hom g)).2 (D.arrow_mk_map_hom g)

/-- Uniqueness of lifts, `Arrow`-style. -/
theorem eq_liftArrow {b : B} {c : C} (g : b ⟶ p.obj c) {c' : C}
    (h : c' ⟶ c) (hh : Arrow.mk (p.map h) = Arrow.mk g) :
    Arrow.mk h = D.liftArrow g := by
  obtain ⟨e, hY, hf⟩ := (arrow_mk_eq_iff _ _).1 hh
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
  · obtain ⟨hX, hY, hf⟩ := (arrow_mk_eq_iff _ _).1 (hm g)
    simp only [Functor.map_comp, eqToHom_map, hf]
    simp
  · refine sigma_eq_of_arrow_eq h _ ?_ (hr g)
    apply H.equiv.injective
    rw [H.equiv.apply_symm_apply, H.equiv_apply]
    exact Subtype.ext (Prod.ext
      ((arrow_mk_eq_iff _ _).2 ⟨eh, rfl, by simpa using hh⟩).symm rfl)

theorem IsDiscreteFibration.nonempty {p : C ⥤ B}
    (H : IsDiscreteFibration p) : Nonempty (DiscreteFibration p) :=
  ⟨H.toDiscreteFibration⟩

/-! ## 4. The category of elements of a presheaf -/

/-- Objects of the category of elements of `F : Bᵒᵖ ⥤ Type v`: pairs of an
object `b` and an element of `F b`. -/
structure Elts (F : Bᵒᵖ ⥤ Type v₃) : Type (max u₂ v₃) where
  /-- The object of `B` the element lies over. -/
  base : B
  /-- The element of `F` at `base`. -/
  elt : F.obj (op base)

namespace Elts

variable {F : Bᵒᵖ ⥤ Type v₃}

/-- Morphisms `⟨b, x⟩ ⟶ ⟨b', x'⟩` are morphisms `g : b ⟶ b'` of `B`
with `F g x' = x`: exactly the presheaf-compatible arrows, no more, no
less. -/
instance : Category.{v₂} (Elts F) where
  Hom x y := { g : x.base ⟶ y.base // F.map g.op y.elt = x.elt }
  id x := ⟨𝟙 _, by simp⟩
  comp {x y z} f g := ⟨f.1 ≫ g.1, by
    simp only [op_comp, Functor.map_comp, types_comp_apply, g.2, f.2]⟩

@[ext] theorem hom_ext {x y : Elts F} {f g : x ⟶ y} (h : f.1 = g.1) :
    f = g := Subtype.ext h

@[simp] theorem id_val (x : Elts F) : (𝟙 x : x ⟶ x).1 = 𝟙 x.base := rfl

@[simp] theorem comp_val {x y z : Elts F} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

@[simp] theorem eqToHom_val {x y : Elts F} (h : x = y) :
    (eqToHom h).1 = eqToHom (congrArg Elts.base h) := by
  subst h; rfl

/-- The projection `∫F → B`. -/
def π (F : Bᵒᵖ ⥤ Type v₃) : Elts F ⥤ B where
  obj x := x.base
  map f := f.1

@[simp] theorem π_obj (x : Elts F) : (π F).obj x = x.base := rfl
@[simp] theorem π_map {x y : Elts F} (f : x ⟶ y) : (π F).map f = f.1 := rfl

theorem sigma_eq_aux (b : B) (x : F.obj (op b)) (y : Elts F)
    (g : b ⟶ y.base) (hg : F.map g.op y.elt = x) :
    (⟨⟨b, x⟩, ⟨g, hg⟩⟩ : Σ x, x ⟶ y) =
      ⟨⟨b, F.map g.op y.elt⟩, ⟨g, rfl⟩⟩ := by
  subst hg
  rfl

/-- Every morphism of `Elts F` is the canonical lift of its image in `B`. -/
theorem sigma_eq {x y : Elts F} (h : x ⟶ y) :
    (⟨x, h⟩ : Σ x, x ⟶ y) =
      ⟨⟨x.base, F.map h.1.op y.elt⟩, ⟨h.1, rfl⟩⟩ :=
  sigma_eq_aux x.base x.elt y h.1 h.2

/-- The lift of `g : b ⟶ b'` with codomain `⟨b', x'⟩` is
`g : ⟨b, F g x'⟩ ⟶ ⟨b', x'⟩`.  No `eqToHom` occurs: the source is
*computed*, not merely known to exist. -/
def discreteFibration (F : Bᵒᵖ ⥤ Type v₃) :
    DiscreteFibration (π F) where
  src {b y} g := ⟨b, F.map g.op y.elt⟩
  hom {b y} g := ⟨g, rfl⟩
  obj_src _ := rfl
  map_hom _ := (Category.id_comp _).symm
  unique {b y} g {x} h e hh := by
    obtain rfl : x.base = b := e
    have hg : h.1 = g := hh.trans (Category.id_comp g)
    subst hg
    exact sigma_eq h

theorem isDiscreteFibration_π (F : Bᵒᵖ ⥤ Type v₃) :
    IsDiscreteFibration (π F) :=
  (discreteFibration F).isDiscreteFibration

end Elts

/-! ## 5. The fibre presheaf of a discrete fibration -/

namespace DiscreteFibration

/-- The fibre of `p` over `b`, as a type. -/
abbrev Fibre (p : C ⥤ B) (b : B) : Type u₁ := { c : C // p.obj c = b }

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- Restriction along `g : b ⟶ b'` of a fibre element `c'` over `b'`: the
domain of the unique lift of `g` with codomain `c'`. -/
def restrict {b b' : B} (g : b ⟶ b') (c' : Fibre p b') : Fibre p b :=
  ⟨D.src (g ≫ eqToHom c'.2.symm), D.obj_src _⟩

@[simp] theorem restrict_val {b b' : B} (g : b ⟶ b') (c' : Fibre p b') :
    (D.restrict g c').1 = D.src (g ≫ eqToHom c'.2.symm) := rfl

theorem restrict_id {b : B} (c : Fibre p b) : D.restrict (𝟙 b) c = c := by
  obtain ⟨c, hc⟩ := c
  subst hc
  exact Subtype.ext (by simpa using D.src_id c)

theorem restrict_comp {b b' b'' : B} (g : b ⟶ b') (g' : b' ⟶ b'')
    (c : Fibre p b'') :
    D.restrict (g ≫ g') c = D.restrict g (D.restrict g' c) := by
  apply Subtype.ext
  exact D.src_eq ((g ≫ g') ≫ eqToHom c.2.symm)
    (D.hom (g ≫ eqToHom (D.obj_src (g' ≫ eqToHom c.2.symm)).symm) ≫
      D.hom (g' ≫ eqToHom c.2.symm))
    (D.obj_src _) (by simp [D.map_hom])

/-- The fibre presheaf `b ↦ p⁻¹(b)` of a discrete fibration. -/
def fibrePsh : Bᵒᵖ ⥤ Type u₁ where
  obj b := Fibre p b.unop
  map g := TypeCat.ofHom fun c => D.restrict g.unop c
  map_id _ := ConcreteCategory.hom_ext _ _ fun c => D.restrict_id c
  map_comp g g' :=
    ConcreteCategory.hom_ext _ _ fun c => D.restrict_comp g'.unop g.unop c

/-- The fibre presheaf's value on objects.  Not a `simp` lemma: it rewrites
the object arguments carried by the coercion in `fibrePsh_map`'s left-hand
side, which would take that lemma out of simp-normal form.  Mathlib omits
the corresponding `yoneda_obj_obj` for the same reason, supplying
`unif_hint`s instead. -/
theorem fibrePsh_obj (b : Bᵒᵖ) : D.fibrePsh.obj b = Fibre p b.unop := rfl

@[simp] theorem fibrePsh_map {b b' : Bᵒᵖ} (g : b ⟶ b')
    (c : Fibre p b.unop) : D.fibrePsh.map g c = D.restrict g.unop c := rfl

/-! ## 6. `C ≅ ∫(fibrePsh D)` over `B` -/

attribute [local simp] eqToHom_map

/-- `c ↦ (p c, c)`. -/
def toElts : C ⥤ Elts D.fibrePsh where
  obj c := ⟨p.obj c, ⟨c, rfl⟩⟩
  map {c c'} f :=
    ⟨p.map f,
      Subtype.ext (D.src_eq (p.map f ≫ eqToHom rfl) f rfl (by simp))⟩
  map_id c := Elts.hom_ext (p.map_id c)
  map_comp f g := Elts.hom_ext (p.map_comp f g)

@[simp] theorem toElts_obj (c : C) :
    D.toElts.obj c = ⟨p.obj c, ⟨c, rfl⟩⟩ := rfl
@[simp] theorem toElts_map_val {c c' : C} (f : c ⟶ c') :
    (D.toElts.map f).1 = p.map f := rfl

theorem obj_eq_src {x y : Elts D.fibrePsh} (f : x ⟶ y) :
    x.elt.1 = D.src (f.1 ≫ eqToHom y.elt.2.symm) :=
  (congrArg Subtype.val f.2).symm

/-- `(b, c) ↦ c`. -/
def ofElts : Elts D.fibrePsh ⥤ C where
  obj x := x.elt.1
  map {x y} f :=
    eqToHom (D.obj_eq_src f) ≫ D.hom (f.1 ≫ eqToHom y.elt.2.symm)
  map_id x := by
    apply D.map_injective
    simp [D.map_hom]
  map_comp {x y z} f g := by
    apply D.map_injective
    simp [D.map_hom]

@[simp] theorem ofElts_obj (x : Elts D.fibrePsh) :
    D.ofElts.obj x = x.elt.1 := rfl

theorem map_ofElts_map {x y : Elts D.fibrePsh} (f : x ⟶ y) :
    p.map (D.ofElts.map f) =
      eqToHom x.elt.2 ≫ f.1 ≫ eqToHom y.elt.2.symm := by
  simp [ofElts, D.map_hom]

/-! The "over `B`" statements come in two forms.  The elementwise ones
(`_obj`/`_map`) are the ones with the clean axiom budget.  The packaged
ones using `⋙` inherit `Classical.choice` from mathlib's `Functor.comp`
itself (whose functor laws are discharged by classical automation), not
from anything proved here. -/

theorem π_toElts_obj (c : C) :
    (Elts.π D.fibrePsh).obj (D.toElts.obj c) = p.obj c := rfl

theorem π_toElts_map {c c' : C} (f : c ⟶ c') :
    (Elts.π D.fibrePsh).map (D.toElts.map f) = p.map f := rfl

theorem obj_ofElts_obj (x : Elts D.fibrePsh) :
    p.obj (D.ofElts.obj x) = (Elts.π D.fibrePsh).obj x := x.elt.2

/-- `toElts` lies over `B`. -/
theorem toElts_comp_π : D.toElts ⋙ Elts.π D.fibrePsh = p := rfl

/-- `ofElts` lies over `B`. -/
theorem ofElts_comp : D.ofElts ⋙ p = Elts.π D.fibrePsh :=
  Functor.ext (fun x => x.elt.2) (fun x y f => by
    rw [Functor.comp_map, D.map_ofElts_map]
    rfl)

theorem ofElts_map_toElts_map {c c' : C} (f : c ⟶ c') :
    D.ofElts.map (D.toElts.map f) = f := by
  apply D.map_injective
  rw [D.map_ofElts_map]
  change 𝟙 _ ≫ p.map f ≫ 𝟙 _ = p.map f
  simp

theorem ofElts_obj_toElts_obj (c : C) : D.ofElts.obj (D.toElts.obj c) = c :=
  rfl

theorem toElts_comp_ofElts : D.toElts ⋙ D.ofElts = 𝟭 C :=
  Functor.ext (fun c => rfl) (fun c c' f => by
    change D.ofElts.map (D.toElts.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
    rw [D.ofElts_map_toElts_map, Category.id_comp, Category.comp_id])

/-- Every object of `Elts (fibrePsh D)` is `toElts` of its underlying
object of `C`. -/
theorem elts_eq_toElts_obj (x : Elts D.fibrePsh) :
    x = D.toElts.obj x.elt.1 := by
  cases x with
  | mk b e =>
    cases e with
    | mk c hc =>
      have hc' : p.obj c = b := hc
      subst hc'
      rfl

theorem toElts_map_ofElts_map {c c' : C}
    (f : D.toElts.obj c ⟶ D.toElts.obj c') :
    D.toElts.map (D.ofElts.map f) = f :=
  Elts.hom_ext (by
    rw [toElts_map_val, D.map_ofElts_map]
    change 𝟙 _ ≫ f.1 ≫ 𝟙 _ = f.1
    rw [Category.id_comp, Category.comp_id])

theorem ofElts_comp_toElts : D.ofElts ⋙ D.toElts = 𝟭 (Elts D.fibrePsh) :=
  Functor.ext (fun x => (D.elts_eq_toElts_obj x).symm) (fun x y f => by
    obtain ⟨c, rfl⟩ : ∃ c, x = D.toElts.obj c :=
      ⟨_, D.elts_eq_toElts_obj x⟩
    obtain ⟨c', rfl⟩ : ∃ c', y = D.toElts.obj c' :=
      ⟨_, D.elts_eq_toElts_obj y⟩
    change D.toElts.map (D.ofElts.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
    rw [D.toElts_map_ofElts_map, Category.id_comp, Category.comp_id])

end DiscreteFibration

/-! ## 7. The other round trip: `fibrePsh (π F) ≅ F` -/

namespace Elts

variable (F : Bᵒᵖ ⥤ Type v₃)

/-- Choice-free and universe-free form of `fibrePshIso` below: the fibre of
`π F` over `b` is in bijection with `F b`. -/
def fibrePshEquiv (b : B) : DiscreteFibration.Fibre (π F) b ≃ F.obj (op b)
    where
  toFun x := F.map (eqToHom x.2.symm).op x.1.elt
  invFun y := ⟨⟨b, y⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨b₀, y⟩, hb⟩ := x
    have hb' : b₀ = b := hb
    subst hb'
    exact Subtype.ext (congrArg (Elts.mk _)
      (ConcreteCategory.congr_hom (F.map_id _) y))
  right_inv y :=
    show F.map (𝟙 (op b)) y = y from
      ConcreteCategory.congr_hom (F.map_id _) y

/-- Naturality of `fibrePshEquiv`: restriction in the fibre presheaf of
`π F` is restriction in `F`. -/
theorem fibrePshEquiv_restrict {b b' : B} (g : b ⟶ b')
    (x : DiscreteFibration.Fibre (π F) b') :
    fibrePshEquiv F b ((discreteFibration F).restrict g x) =
      F.map g.op (fibrePshEquiv F b' x) := by
  obtain ⟨⟨b₀, y⟩, hb⟩ := x
  have hb' : b₀ = b' := hb
  subst hb'
  change F.map (𝟙 _) (F.map (g ≫ 𝟙 _).op y) =
    F.map g.op (F.map (𝟙 _) y)
  rw [Category.comp_id, F.map_id, F.map_id]
  rfl

/-- The fibre presheaf of `π F` is naturally isomorphic to `F` (up to the
universe lift forced by `Elts F : Type (max u₂ v₃)`): the fibre over `b` is
`{x : Elts F // x.base = b}`, and `x ↦ x.elt`, transported along
`x.base = b`, is a bijection onto `F b`. -/
def fibrePshIso :
    (discreteFibration F).fibrePsh ≅ F ⋙ uliftFunctor.{u₂, v₃} :=
  NatIso.ofComponents
    (fun b =>
      { hom := TypeCat.ofHom fun x => ⟨F.map (eqToHom x.2.symm).op x.1.elt⟩
        inv := TypeCat.ofHom fun y => ⟨⟨b.unop, y.down⟩, rfl⟩
        hom_inv_id := ConcreteCategory.hom_ext _ _ (by
          intro x
          obtain ⟨⟨b₀, y⟩, hb⟩ := x
          have hb' : b₀ = b.unop := hb
          subst hb'
          exact Subtype.ext (congrArg (Elts.mk _)
            (ConcreteCategory.congr_hom (F.map_id _) y)))
        inv_hom_id := ConcreteCategory.hom_ext _ _ (by
          intro y
          obtain ⟨y⟩ := y
          exact congrArg ULift.up
            (ConcreteCategory.congr_hom (F.map_id _) y)) })
    (fun {b b'} g => ConcreteCategory.hom_ext _ _ (by
      intro x
      obtain ⟨⟨b₀, y⟩, hb⟩ := x
      have hb' : b₀ = b.unop := hb
      subst hb'
      change ULift.up (F.map (𝟙 _) (F.map (g.unop ≫ 𝟙 _).op y)) =
        ULift.up (F.map g (F.map (𝟙 _) y))
      rw [Category.comp_id, Quiver.Hom.op_unop, F.map_id, F.map_id]
      rfl))

end Elts

end CategoryTheory
