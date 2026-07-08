/-
Copyright (c) 2026 The geb-mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The geb-mathlib contributors
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Codes for positive inductive-recursive definitions

`IR D` is the type of codes for inductive-recursive definitions with
output type `D`, presented as the W-type of a polynomial functor
`IRpf D` whose shapes are the three code constructors — constant
(`iota`), dependent sum (`sigma`), and dependent product (`delta`) —
and whose directions are their subcode arities. A code is interpreted
as an endofunctor on the free coproduct completion of `D` treated as a
discrete category (the category of families of elements of `D`). This
file follows [GhaniNordvallForsbergMalatesta2015], Section 2
(Definitions 2.1–2.4), which presents the theory of
[DybjerSetzer1999].

## Main definitions

* `IRpf` — the polynomial functor whose W-type defines codes: shapes
  `IRshape`, directions `IRdir`.
* `IRdest`, `IRelim`, `IRelimInv` — the pattern-matched destructor for
  morphisms out of `IRobj` and its conversions to and from such
  morphisms.
* `IRdepDest`, `IRdepElim`, `IRdepElimInv` — the dependent
  counterparts.
* `IR`, `IRmk` — the type of codes and its constructor.
* `IRcata`, `IRrec` — the catamorphism and the dependent recursor.
* `FreeCoprodCompDisc`, `FreeCoprodCompDisc.Hom`,
  `freeCoprodCompDiscCopr`, `freeCoprodCompDiscCoprMor` — the free
  coproduct completion of `D` treated as a discrete category: objects,
  morphisms, indexed coproducts, and the coproducts' functorial
  action.
* `IRinterpObj`, `IRinterpMor` — the object-map and morphism-map
  components of the interpretation of a code as an endofunctor on
  `FreeCoprodCompDisc`.

## Main statements

* `IRelimIso` — `IRdest` is isomorphic to the morphisms out of
  `IRobj`.
* `IRdepElimIso` — `IRdepDest` is isomorphic to the dependent
  eliminators of `IRobj`.
* `IRmkExt`, `IRmkExtInv` — extensionality for codes.

## References

* [DybjerSetzer1999]
* [GhaniNordvallForsbergMalatesta2015]

## Tags

inductive-recursive, polynomial functor, W-type, universe, container
-/

@[expose]
public section

universe uA uD

namespace IndRec

variable (D : Type uD)

set_option linter.checkUnivs false in
/-- The shape type of the polynomial functor whose W-type
defines codes for positive inductive-recursive types. -/
def IRshape : Type (max (uA + 1) uD) :=
  D ⊕ Type uA ⊕ Type uA

/-- The direction type of the polynomial functor whose W-type
defines codes for positive inductive-recursive types. -/
def IRdir : IRshape D → Type (max uA uD)
  | Sum.inl _ => PEmpty
  | Sum.inr (Sum.inl (A : Type uA)) => ULift A
  | Sum.inr (Sum.inr (A : Type uA)) => A → D

/-- Simplification for constant (`iota`) case of `IRdir`. -/
@[simp]
lemma IRdirL (d : D) : IRdir.{uA, uD} D (Sum.inl d) = PEmpty := rfl

/-- Simplification for dependent sum (`sigma`) case of `IRdir`. -/
@[simp]
lemma IRdirRL (A : Type uA) : IRdir D (Sum.inr (Sum.inl A)) = ULift A := rfl

/-- Simplification for dependent product (`delta`) case of `IRdir`. -/
@[simp]
lemma IRdirRR (A : Type uA) : IRdir D (Sum.inr (Sum.inr A)) = (A → D) := rfl

/-- Rewrite the direction type given shape-type equality. -/
def IRdirRW {s s' : IRshape.{uA, uD} D} : s = s' → IRdir D s → IRdir D s'
  | rfl => id

/-- Elimination rule for `IRdir`. -/
def IRdirElim.{v} (V : Type v)
  (σ : (A : Type uA) → A → V)
  (δ : (A : Type uA) → (A → D) → V)
  (s : IRshape D) (ds : IRdir D s) : V :=
    match s with
      | Sum.inl _ => PEmpty.elim ds
      | Sum.inr (Sum.inl (A : Type uA)) => σ A (ULift.down ds)
      | Sum.inr (Sum.inr (A : Type uA)) => δ A ds

/-- The polynomial functor whose W-type defines codes for
positive inductive-recursive types. -/
def IRpf : PFunctor.{max (uA + 1) uD, max uA uD} :=
  ⟨IRshape D, IRdir D⟩

/-- The interpretation of `IRpf` into endofunctors on `Type`. -/
def IRobj.{v} (V : Type v) : Type (max (uA + 1) uD v) :=
  PFunctor.Obj.{v, max (uA + 1) uD, max uA uD} (IRpf D) V

/-- The first component of `IRobj`. -/
def IRobj1 : Type (max (uA + 1) uD) :=
  IRshape.{uA, uD} D

/-- The second component of `IRobj`. -/
def IRobj2.{v} (V : Type v) : IRobj1 D → Type (max uA uD v) :=
  fun s => IRdir.{uA, uD} D s → V

/-- Rewrite the second component of `IRobj` given shape-type equality. -/
def IRobj2RW.{v} (V : Type v) {s s' : IRobj1.{uA, uD} D} :
  s = s' → IRobj2 D V s → IRobj2 D V s'
    | rfl => id

/-- A destructor for `IRpf V` -- a pattern-matched form of elimination. -/
def IRdest.{v, w} (V : Type v) (W : Type w) : Type (max (uA + 1) uD v w) :=
  (D → W) × ((A : Type uA) → (A → V) → W) × ((A : Type uA) → ((A → D) → V) → W)

/-- Convert `IRdest` to a morphism out of `IRpf V` (an eliminator). -/
def IRelim.{v, w} (V : Type v) (W : Type w)
  (dest : IRdest.{uA, uD, v, w} D V W) :
    IRobj D V → W :=
      fun ⟨s, ds⟩ => match s with
        | Sum.inl d => dest.1 d
        | Sum.inr (Sum.inl (A : Type uA)) => dest.2.1 A (ds ∘ ULift.up)
        | Sum.inr (Sum.inr (A : Type uA)) => dest.2.2 A ds

/-- The inverse of `IRelim`. -/
def IRelimInv.{v, w} (V : Type v) (W : Type w)
  (m : IRobj D V → W) :
    IRdest.{uA, uD, v, w} D V W :=
      ⟨ fun d => m ⟨Sum.inl d, PEmpty.elim⟩,
        fun A f => m ⟨Sum.inr (Sum.inl A), f ∘ ULift.down⟩,
        fun A f => m ⟨Sum.inr (Sum.inr A), f⟩ ⟩

/-- `IRelimInv` is a left-inverse of `IRelim`. -/
lemma IRelimLeftInv.{v, w} (V : Type v) (W : Type w)
  (dest : IRdest.{uA, uD, v, w} D V W) :
    IRelimInv.{uA, uD, v, w} D V W (IRelim.{uA, uD, v, w} D V W dest) = dest :=
      match dest with | ⟨_, _, _⟩ => rfl

/-- `IRelimInv` is a right-inverse of `IRelim`. -/
lemma IRelimRightInv.{v, w} (V : Type v) (W : Type w)
  (m : IRobj D V → W) :
    IRelim.{uA, uD, v, w} D V W (IRelimInv.{uA, uD, v, w} D V W m) = m :=
      funext <| fun e => match e with | ⟨s, ds⟩ => match s with
        | Sum.inl _ =>
            Eq.rec rfl (funext (fun x => PEmpty.elim x) : PEmpty.elim = ds)
        | Sum.inr (Sum.inl _) =>
            rfl
        | Sum.inr (Sum.inr _) =>
            rfl

/-- `IRdest` is isomorphic to the set of morphisms out of `IRobj`. -/
def IRelimIso.{v, w} (V : Type v) (W : Type w) :
  IRdest.{uA, uD, v, w} D V W ≃ (IRobj D V → W) :=
  {
    toFun := IRelim D V W
    invFun := IRelimInv D V W
    left_inv := IRelimLeftInv D V W
    right_inv := IRelimRightInv D V W
  }

/-- A dependent destructor for `IRpf V` -- a pattern-matched form of
elimination. -/
def IRdepDest.{v, w} (V : Type v) (W : IRobj D V → Type w) :
  Type (max (uA + 1) uD v w) :=
    ((d : D) → W ⟨Sum.inl d, PEmpty.elim⟩) ×
    ((A : Type uA) → (f : A → V) → W ⟨Sum.inr (Sum.inl A), f ∘ ULift.down⟩) ×
    ((A : Type uA) → (f : (A → D) → V) → W ⟨Sum.inr (Sum.inr A), f⟩)

/-- Convert `IRdepDest` to a destructor into a sigma type. -/
def IRsigmaDest.{v, w} (V : Type v) (W : IRobj D V → Type w) :
  IRdepDest.{uA, uD, v, w} D V W →
  IRdest.{uA, uD, v, max (uA + 1) uD v w} D V (Σ e, W e) :=
    fun dest => ⟨
      fun d => ⟨⟨Sum.inl d, PEmpty.elim⟩, dest.1 d⟩,
      fun A f => ⟨⟨Sum.inr (Sum.inl A), f ∘ ULift.down⟩, dest.2.1 A f⟩,
      fun A f => ⟨⟨Sum.inr (Sum.inr A), f⟩, dest.2.2 A f⟩
    ⟩

/-- Convert `IRdepDest` to a morphism into a sigma type. -/
def IRsigmaElim.{v, w} (V : Type v) (W : IRobj D V → Type w) :
  IRdepDest.{uA, uD, v, w} D V W → IRobj D V → Σ e, W e :=
    IRelim.{uA, uD, v, max (uA + 1) uD v w} D V (Σ e, W e) ∘
    IRsigmaDest.{uA, uD, v, w} D V W

/-- `IRsigmaElim` is a section of the first projection. -/
lemma IRsigmaElimSect.{v, w} (V : Type v) (W : IRobj D V → Type w)
  (dest : IRdepDest.{uA, uD, v, w} D V W) (e : IRobj D V) :
    (IRsigmaElim D V W dest e).1 = e :=
      match e with
        | ⟨s, ds⟩ => match s with
          | Sum.inl _ =>
            Eq.rec rfl (funext (fun x => PEmpty.elim x) : PEmpty.elim = ds)
          | Sum.inr (Sum.inl _) => rfl
          | Sum.inr (Sum.inr _) => rfl

/-- Convert `IRdepDest` to a dependent eliminator for `IRobj V`. -/
def IRdepElim.{v, w} (V : Type v) (W : IRobj D V → Type w) :
  IRdepDest.{uA, uD, v, w} D V W → Π e, W e :=
    fun dest e =>
      Eq.ndrec (IRsigmaElim D V W dest e).2 (IRsigmaElimSect D V W dest e)

/-- The inverse of `IRdepElim`. -/
def IRdepElimInv.{v, w} (V : Type v) (W : IRobj D V → Type w) :
  (Π e, W e) → IRdepDest.{uA, uD, v, w} D V W :=
    fun m => ⟨
      fun d => m ⟨Sum.inl d, PEmpty.elim⟩,
      fun A f => m ⟨Sum.inr (Sum.inl A), f ∘ ULift.down⟩,
      fun A f => m ⟨Sum.inr (Sum.inr A), f⟩
    ⟩

/-- `IRdepElimInv` is a left-inverse of `IRdepElim`. -/
lemma IRdepElimLeftInv.{v, w} (V : Type v) (W : IRobj D V → Type w)
  (dest : IRdepDest.{uA, uD, v, w} D V W) :
    IRdepElimInv.{uA, uD, v, w} D V W (IRdepElim.{uA, uD, v, w} D V W dest) =
    dest :=
      match dest with | ⟨_, _, _⟩ => rfl

/-- `IRdepElimInv` is a right-inverse of `IRdepElim`. -/
lemma IRdepElimRightInv.{v, w} (V : Type v) (W : IRobj D V → Type w)
  (m : Π e, W e) :
    IRdepElim.{uA, uD, v, w} D V W (IRdepElimInv.{uA, uD, v, w} D V W m) = m :=
      funext <| fun e => match e with | ⟨s, ds⟩ => match s with
        | Sum.inl _ =>
            Eq.rec rfl (funext (fun x => PEmpty.elim x) : PEmpty.elim = ds)
        | Sum.inr (Sum.inl _) =>
            rfl
        | Sum.inr (Sum.inr _) =>
            rfl

/-- `IRdepDest` is isomorphic to the dependent eliminators of `IRobj`. -/
def IRdepElimIso.{v, w} (V : Type v) (W : IRobj D V → Type w) :
  IRdepDest.{uA, uD, v, w} D V W ≃ (Π e, W e) :=
  {
    toFun := IRdepElim D V W
    invFun := IRdepElimInv D V W
    left_inv := IRdepElimLeftInv D V W
    right_inv := IRdepElimRightInv D V W
  }

/-- A pattern-matched form of an algebra of `IRpf`. -/
def IRalg.{v} (V : Type v) : Type (max (uA + 1) uD v) :=
  IRdest.{uA, uD, v, v} D V V

/-- Convert `IRalg` to a category-theoretic algebra of `IRpf`. -/
def IRcatAlg.{v} (V : Type v) (alg : IRalg.{uA, uD, v} D V) :
  IRobj D V → V :=
    IRelim.{uA, uD, v, v} D V V alg

/-- The polynomial functor which defines codes for
positive inductive-recursive types. -/
def IR : Type (max (uA + 1) uD) :=
  PFunctor.W.{max (uA + 1) uD, max uA uD} (IRpf D)

/-- The constructor for `IR`. -/
def IRmk (s : IRshape D) (d : IRdir D s → IR D) : IR D :=
  WType.mk.{max (uA + 1) uD, max uA uD} s d

/-- Extensionality for `IRmk`s with the same shape. -/
lemma IRmkExtDir (s : IRshape D) {ds ds' : IRdir D s → IR D} :
  ds = ds' → IRmk.{uA, uD} D s ds = IRmk.{uA, uD} D s ds'
    | rfl => rfl

/-- The motive of the proof of extensionality for `IRmk`. -/
def IRmkExtStep
  (s : IRshape D) (d : IRdir D s → IR D) (s' : IRshape D) (eq1 : s = s') :
    Prop :=
      ∀ d' : (IRdir D s' → IR D),
        ((d = d' ∘ IRdirRW D eq1) → (IRmk D s d = IRmk D s' d'))

/-- Extensionality for `IRmk` (equality is determined by
equality of shape and pointwise equality of directions). -/
lemma IRmkExt {ir ir' : IR.{uA, uD} D} (eq1 : ir.1 = ir'.1)
  (eq2 : ir.2 = ir'.2 ∘ IRdirRW D eq1) :
  ir = ir' :=
    match ir, ir' with
      | ⟨s, d⟩, ⟨_, d'⟩ =>
          Eq.rec (motive := IRmkExtStep D s d)
            (fun _ => IRmkExtDir D s) eq1 d' eq2

/-- The converse of `IRmkExt`: an equality in `IR` determines a
pointwise equality of directions (transported along the shape
equality induced by the first projection). -/
lemma IRmkExtInv {ir ir' : IR.{uA, uD} D} :
  (eq : ir = ir') → ir.2 = ir'.2 ∘ IRdirRW D (congrArg (fun t => t.1) eq)
    | rfl => rfl

/-- The catamorphism (the unique algebra morphism out of the initial
object) for `IR`, using the category-theoretic form of an algebra. -/
def IRcataCat.{v} (V : Type v) (alg : IRobj.{uA, uD, v} D V → V) : IR D → V :=
  WType.elim.{max (uA + 1) uD, max uA uD, v} V alg

/-- The catamorphism (the unique algebra morphism out of the initial
object) for `IR`, using the convenience `IRalg` form of an algebra. -/
def IRcata.{v} (V : Type v) (alg : IRalg.{uA, uD, v} D V) : IR D → V :=
  IRcataCat D V (IRcatAlg D V alg)

/-- The induction principle -- the recursor into `Prop`
(`WType.rec` produces non-computable output, so we use it
only to generate propositions. -/
theorem IRind (motive : IR D → Prop) :
  ((a : IRshape D) → (f : IRdir D a → IR D) →
   ((d : IRdir D a) → motive (f d)) →
   motive (IRmk.{uA, uD} D a f)) →
  Π (t : IR D), motive t :=
    WType.rec.{0, max (uA + 1) uD, max uA uD}
      (α := IRshape D) (β := IRdir D)
      (motive := motive)

/-- The `IRpf` algebra over a sigma type generated by a dependent eliminator. -/
def IRsigmaCataAlg.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f)) :
  IRobj D (Σ e, motive e) → Σ e, motive e :=
    (fun ⟨s, f⟩ =>
      ⟨IRmk D s (Sigma.fst ∘ f),
       mk s (Sigma.fst ∘ f) (fun d => (f d).2)⟩)

/-- `IRsigmaCataAlg` preserves the first projection. -/
lemma IRsigmaCataAlg1.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f))
  (t : IRobj D (Σ e, motive e)) :
    (IRsigmaCataAlg D motive mk t).1.1 = t.1 :=
  rfl

/-- `IRsigmaCataAlg` preserves the second projection. -/
lemma IRsigmaCataAlg2.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f))
  (t : IRobj D (Σ e, motive e)) :
    (IRsigmaCataAlg D motive mk t).1.2 = Sigma.fst ∘ t.2 :=
  rfl

/-- `IR`'s catamorphism on a sigma type. -/
def IRsigmaCata.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f)) :
  IR D → Σ e, motive e :=
    IRcataCat D (Σ e, motive e) (IRsigmaCataAlg D motive mk)

/-- The inductive step of the proof that `IRsigmaCata`
is a section of the first projection. -/
lemma IRsigmaCataIndStep.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (ds : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (ds d)) →
    motive (IRmk.{uA, uD} D a ds)) :
  ∀ (s : IRshape D) (ds : IRdir D s → IR D),
    (∀ (d : IRdir D s), (IRsigmaCata D motive mk (ds d)).1 = ds d) →
      (IRsigmaCata D motive mk (IRmk D s ds)).1 = IRmk D s ds :=
  fun _ _ ih => IRmkExt D rfl (funext ih)

/-- `IRSigmaCata` is a section of the first projection. -/
lemma IRsigmaCataSect.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f)) :
  (t : IR D) → (IRsigmaCata D motive mk t).1 = t :=
    IRind D
      (motive := fun t => (IRsigmaCata D motive mk t).1 = t)
      (IRsigmaCataIndStep D motive mk)

/-- The first projection of `IRSigmaCata` is a section of the
first projection of the first projection. -/
lemma IRsigmaCataSect1.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f))
  (t : IR D) :
    (IRsigmaCata D motive mk t).1.1 = t.1 :=
  match t with
    | ⟨_, _⟩ => rfl

/-- The second projection of `IRSigmaCata` is a section of the
second projection of the first projection. -/
lemma IRsigmaCataSect2.{v} (motive : IR D → Type v)
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f))
  (t : IR D) :
    (IRsigmaCata D motive mk t).1.2 =
      t.2 ∘ IRdirRW D (IRsigmaCataSect1 D motive mk t) :=
  IRmkExtInv D (IRsigmaCataSect D motive mk t)

/-- The recursor -- the dependent catamorphism for `IR`. -/
def IRrec.{v} {motive : IR D → Type v}
  (mk :
    (a : IRshape D) → (f : IRdir D a → IR D) →
    ((d : IRdir D a) → motive (f d)) →
    motive (IRmk.{uA, uD} D a f)) :
  Π t, motive t :=
    fun t =>
      Eq.ndrec (IRsigmaCata D motive mk t).2 (IRsigmaCataSect D motive mk t)

end IndRec
