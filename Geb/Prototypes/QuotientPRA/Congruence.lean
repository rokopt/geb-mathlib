/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.QuotientPRA.FreeArity
public import Geb.Prototypes.QuotientPRA.Basic
public import Mathlib.Data.FinEnum

meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Reflexivity and congruence from congruence witnesses

A quotient presheaf polynomial functor with free arities
({lit}`GebProto.QuotientPRA.FreeArity`) over {lit}`I × WalkingParallelPair` has
congruences when every term constructor, applied to the endpoints of witnesses
between its arguments, gives the endpoints of one witness ({lit}`HasCongruences`).
This is the property a congruence constructor of each term constructor provides, as
{lit}`GebProto.QuotientPRA.Signature.qpra` adds one. It is stated for term
constructors whose arguments are all terms ({lit}`TermArguments`), and at every
object {lit}`c` of {lit}`I × WalkingParallelPair` lying over the terms, the two
endpoint morphisms into {lit}`(c.1, one)` being {lit}`endMor`.

For finitary arities the congruences give every term a reflexivity witness, by
induction on the term ({lit}`exists_refl`), although reflexivity is not a constructor
({lit}`GebProto.QuotientPRA.Obstruction`). With reflexivity witnesses for the other
arguments, a witness between one argument of a term constructor and another term
relates the applications before and after replacing the argument
({lit}`mk_linked_update`). Replacing the arguments one at a time along an enumeration,
the term constructors respect the equivalence relation the witnesses generate
({lit}`mk_eqvGen`): arguments with equal classes give terms with equal classes
({lit}`unit_mk_congr`).

## Main definitions

* {lit}`finEnumBool`, {lit}`finEnumPEmpty` — enumerations of the booleans and the empty
  type.
* {lit}`endMor` — the endpoint morphisms at an object over the terms.
* {lit}`TermArguments` — every argument of a term constructor is a term.
* {lit}`HasCongruences` — every term constructor has a congruence.
* {lit}`Linked` — two terms are the endpoints of a witness.

## Main statements

* {lit}`exists_forall_of_finEnum` — finitely many choices, constructively.
* {lit}`exists_refl` — every term has a reflexivity witness.
* {lit}`mk_linked_update`, {lit}`mk_eqvGen_update`, {lit}`mk_eqvGen` — the term
  constructors respect the witnesses, in one argument and in all.
* {lit}`unit_eq_iff` — two terms have the same class exactly when the witnesses relate
  them by a finite zig-zag.
* {lit}`unit_mk_congr` — the term constructors respect classes.

## Implementation notes

The finiteness of the arguments is an enumeration, {name}`FinEnum`, whose list the
choices recurse on. mathlib's {lit}`Quotient.finChoice` for a {name}`Fintype` depends
on {lit}`Classical.choice`, as do {name}`Function.update_idem` and
{name}`Function.update_eq_self`; the two lemmas on {name}`Function.update` are
reproved here as {lit}`update_update` and {lit}`update_apply_self`.

## References

* {cite}`FiorePittsSteenkamp2020`
* {cite}`AltenkirchCapriottiDijkstraKrausNordvallForsberg2018`

## Tags

quotient inductive-inductive type, congruence, reflexivity, W-type, free arity
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA

section Choice

universe u v

/-- Finitely many existence statements have a common witness function: the choice of
finitely many elements, constructive by recursion on an enumeration. -/
theorem exists_forall_of_finEnum {ι : Type u} [FinEnum ι] {α : ι → Sort v}
    {p : (i : ι) → α i → Prop} (h : ∀ i, ∃ x, p i x) : ∃ f : (i : ι) → α i, ∀ i, p i (f i) := by
  have key : ∀ l : List ι, ∃ f : (i : ι) → i ∈ l → α i, ∀ i (hi : i ∈ l), p i (f i hi) :=
    List.rec ⟨(fun _ hi ↦ nomatch hi), (fun _ hi ↦ nomatch hi)⟩ fun i₀ l ih ↦ by
      obtain ⟨x₀, hx₀⟩ := h i₀
      obtain ⟨f, hf⟩ := ih
      refine ⟨fun i hi ↦ if hii : i = i₀ then hii ▸ x₀ else f i (List.mem_of_ne_of_mem hii hi),
        fun i hi ↦ ?_⟩
      dsimp only
      split
      · rename_i hii
        subst hii
        exact hx₀
      · exact hf i _
  obtain ⟨f, hf⟩ := key (FinEnum.toList ι)
  exact ⟨fun i ↦ f i (FinEnum.mem_toList i), fun i ↦ hf i _⟩

/-- Updating a function twice at one point is updating it once with the second
value. -/
theorem update_update {ι : Type u} [DecidableEq ι] {α : ι → Sort v} (f : (i : ι) → α i)
    (i : ι) (x y : α i) : Function.update (Function.update f i x) i y = Function.update f i y := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj]

/-- Updating a function at a point with its own value there leaves it. -/
theorem update_apply_self {ι : Type u} [DecidableEq ι] {α : ι → Sort v} (f : (i : ι) → α i)
    (i : ι) : Function.update f i (f i) = f := by
  funext j
  by_cases hj : j = i
  · subst hj
    exact Function.update_self _ _ _
  · exact Function.update_of_ne hj _ _

/-- The booleans, enumerated without {lit}`Classical.choice`, on which mathlib's
enumerations of {name}`Fin` depend. -/
@[instance_reducible] def finEnumBool : FinEnum Bool where
  card := 2
  equiv :=
    { toFun b := cond b 1 0
      invFun i := Fin.cases false (fun _ ↦ true) i
      left_inv b := by cases b <;> rfl
      right_inv i := Fin.cases rfl (fun j ↦ Fin.cases rfl (fun k ↦ k.elim0) j) i }
  decEq := inferInstance

/-- The empty type, enumerated without {lit}`Classical.choice`. -/
@[instance_reducible] def finEnumPEmpty : FinEnum PEmpty.{u + 1} where
  card := 0
  equiv := ⟨(fun x ↦ nomatch x), Fin.elim0, (fun x ↦ nomatch x), (fun i ↦ i.elim0)⟩
  decEq x := nomatch x

end Choice

universe uI vI uA uB

variable {I : Type uI} [Category.{vI} I]

/-- The endpoint morphism at an object over the terms, into the witnesses over its sort:
the source for {lit}`false`, the target for {lit}`true`. -/
def endMor : (c : I × WalkingParallelPair) → c.2 = .zero → Bool → (c ⟶ eqObj c.1)
  | (k, .zero), _, o => (𝟙 k, endHom o)
  | (_, .one), h, _ => nomatch h

variable (S : FreeArity.{uI, vI, uA, uB} (I × WalkingParallelPair))

/-- Every argument of a term constructor is a term. -/
def TermArguments : Prop := ∀ a b, (S.q a).2 = .zero → (S.gobj a b).2 = .zero

variable {S} {restr_id : S.toData.ShapeRestrId} {restr_comp : S.toData.ShapeRestrComp}
  {reindex_id : S.toData.ReindexId restr_id} {reindex_comp : S.toData.ReindexComp restr_comp}

set_option hygiene false in
/-- The functor of the free-arity instance. -/
local notation "𝐅" => S.toPresheaf restr_id restr_comp reindex_id reindex_comp

/-- The arguments of a term constructor over an object over the terms are terms. -/
theorem TermArguments.gobj (ht : TermArguments S) {a : S.A} {c : I × WalkingParallelPair}
    (hq : S.q a = c) (hc : c.2 = .zero) (b : S.Gen a) : (S.gobj a b).2 = .zero :=
  ht a b ((congrArg Prod.snd hq).trans hc)

variable (restr_id restr_comp reindex_id reindex_comp) in
/-- Every term constructor has a congruence: applied to the endpoints of witnesses
between its arguments, it gives the endpoints of one witness. -/
def HasCongruences (ht : TermArguments S) : Prop :=
  ∀ (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c) (hc : c.2 = .zero)
    (es : (b : S.Gen a) → 𝐅.W.obj ⟨eqObj (S.gobj a b).1⟩),
    ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩, ∀ o : Bool,
      𝐅.W.map (endMor c hc o).op e = PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq
        fun b ↦ 𝐅.W.map (endMor _ (ht.gobj hq hc b) o).op (es b))

/-- Two terms at an object over the terms are linked when they are the endpoints of a
witness. -/
def Linked (c : I × WalkingParallelPair) (hc : c.2 = .zero) (u u' : 𝐅.W.obj ⟨c⟩) : Prop :=
  ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩,
    𝐅.W.map (endMor c hc false).op e = u ∧ 𝐅.W.map (endMor c hc true).op e = u'

/-- Two terms have the same class exactly when the witnesses relate them by the
equivalence relation they generate. -/
theorem unit_eq_iff {c : I × WalkingParallelPair} (hc : c.2 = .zero) (u u' : 𝐅.W.obj ⟨c⟩) :
    (coeqUnit 𝐅.W).app ⟨c⟩ u = (coeqUnit 𝐅.W).app ⟨c⟩ u' ↔
      Relation.EqvGen (Linked c hc) u u' := by
  obtain ⟨k, x⟩ := c
  obtain rfl : x = .zero := hc
  refine (coeqMk_eq_iff 𝐅.W u u').trans
    ⟨fun h ↦ Relation.EqvGen.mono ?_ _ _ h, fun h ↦ Relation.EqvGen.mono ?_ _ _ h⟩
  · rintro _ _ ⟨e⟩
    exact ⟨e, rfl, rfl⟩
  · rintro _ _ ⟨e, rfl, rfl⟩
    exact ⟨e⟩

variable [∀ a, FinEnum (S.Gen a)] {ht : TermArguments S}
  (hcong : HasCongruences restr_id restr_comp reindex_id reindex_comp ht)
include hcong

/-- Every term has a reflexivity witness: the congruence of its constructor at
reflexivity witnesses of its arguments. -/
theorem exists_refl {c : I × WalkingParallelPair} (hc : c.2 = .zero) (t : 𝐅.W.obj ⟨c⟩) :
    ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩, ∀ o : Bool, 𝐅.W.map (endMor c hc o).op e = t := by
  revert hc
  refine FreeArity.W_induction (S := S) (motive := fun c t ↦ ∀ hc : c.2 = .zero,
      ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩, ∀ o : Bool, 𝐅.W.map (endMor c hc o).op e = t)
    (fun a ts ih hc ↦ ?_) t
  obtain ⟨es, hes⟩ := exists_forall_of_finEnum fun b ↦ ih b (ht.gobj rfl hc b)
  obtain ⟨e, he⟩ := hcong a rfl hc es
  exact ⟨e, fun o ↦ (he o).trans (congrArg
    (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a rfl ts)) (funext fun b ↦ hes b o))⟩

/-- A witness between one argument of a term constructor and another term links the
constructor's applications before and after replacing that argument: the congruence at
that witness and at reflexivity witnesses of the other arguments. -/
theorem mk_linked_update (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) (ts : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩) (b₀ : S.Gen a)
    {y : 𝐅.W.obj ⟨S.gobj a b₀⟩} (h : Linked _ (ht.gobj hq hc b₀) (ts b₀) y) :
    Linked c hc (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (Function.update ts b₀ y))) := by
  obtain ⟨e, he₀, he₁⟩ := h
  obtain ⟨rs, hrs⟩ :=
    exists_forall_of_finEnum fun b ↦ exists_refl hcong (ht.gobj hq hc b) (ts b)
  obtain ⟨e', he'⟩ := hcong a hq hc (Function.update rs b₀ e)
  refine ⟨e', (he' false).trans (congrArg
      (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) (funext fun b ↦ ?_)),
    (he' true).trans (congrArg
      (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) (funext fun b ↦ ?_))⟩
  · by_cases hb : b = b₀
    · subst hb
      rw [Function.update_self]
      exact he₀
    · rw [Function.update_of_ne hb]
      exact hrs b false
  · by_cases hb : b = b₀
    · subst hb
      rw [Function.update_self, Function.update_self]
      exact he₁
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
      exact hrs b true

/-- The term constructors respect the generated equivalence relation in each
argument. -/
theorem mk_eqvGen_update (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) (ts : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩) (b₀ : S.Gen a)
    {x y : 𝐅.W.obj ⟨S.gobj a b₀⟩} (hxy : Relation.EqvGen (Linked _ (ht.gobj hq hc b₀)) x y) :
    Relation.EqvGen (Linked c hc)
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (Function.update ts b₀ x)))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (Function.update ts b₀ y))) := by
  refine Relation.EqvGen.rec (motive := fun x y _ ↦ Relation.EqvGen (Linked c hc)
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (Function.update ts b₀ x)))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (Function.update ts b₀ y))))
    (fun x y hr ↦ ?_) (fun _ ↦ .refl _) (fun _ _ _ ih ↦ .symm _ _ ih)
    (fun _ _ _ _ _ ih₁ ih₂ ↦ .trans _ _ _ ih₁ ih₂) hxy
  have h := mk_linked_update hcong a hq hc (Function.update ts b₀ x) b₀
    ((Function.update_self b₀ x ts).symm ▸ hr)
  rw [update_update] at h
  exact .rel _ _ h

/-- The term constructors respect the generated equivalence relation: arguments related
in every place give related applications, the arguments being replaced one at a time
along an enumeration. -/
theorem mk_eqvGen (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) {ts ts' : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩}
    (h : ∀ b, Relation.EqvGen (Linked _ (ht.gobj hq hc b)) (ts b) (ts' b)) :
    Relation.EqvGen (Linked c hc) (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts')) := by
  let g : List (S.Gen a) → (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩ :=
    List.foldr (fun b₀ g ↦ Function.update g b₀ (ts' b₀)) ts
  have hg : ∀ l b, g l b = ts b ∨ g l b = ts' b :=
    List.rec (fun _ ↦ .inl rfl) fun b₀ l ih b ↦ by
      change Function.update (g l) b₀ (ts' b₀) b = ts b ∨
        Function.update (g l) b₀ (ts' b₀) b = ts' b
      by_cases hb : b = b₀
      · subst hb
        rw [Function.update_self]
        exact .inr rfl
      · rw [Function.update_of_ne hb]
        exact ih b
  have hmem : ∀ l b, b ∈ l → g l b = ts' b :=
    List.rec (fun _ hb ↦ nomatch hb) fun b₀ l ih b hb ↦ by
      change Function.update (g l) b₀ (ts' b₀) b = ts' b
      by_cases hbb : b = b₀
      · subst hbb
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hbb]
        exact ih b (List.mem_of_ne_of_mem hbb hb)
  have hstep : ∀ l, Relation.EqvGen (Linked c hc)
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (g l))) :=
    List.rec (.refl _) fun b₀ l ih ↦ by
      refine .trans _ _ _ ih ?_
      have hb₀ : Relation.EqvGen (Linked _ (ht.gobj hq hc b₀)) (g l b₀) (ts' b₀) :=
        (hg l b₀).elim (fun he ↦ he ▸ h b₀) (fun he ↦ he ▸ .refl _)
      have := mk_eqvGen_update hcong a hq hc (g l) b₀ hb₀
      rwa [update_apply_self] at this
  have hfin : g (FinEnum.toList (S.Gen a)) = ts' :=
    funext fun b ↦ hmem _ b (FinEnum.mem_toList b)
  exact hfin ▸ hstep _

/-- The term constructors respect classes: arguments with equal classes give terms with
equal classes. -/
theorem unit_mk_congr (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) {ts ts' : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩}
    (h : ∀ b, (coeqUnit 𝐅.W).app ⟨S.gobj a b⟩ (ts b) = (coeqUnit 𝐅.W).app ⟨S.gobj a b⟩ (ts' b)) :
    (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) =
      (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts')) :=
  (unit_eq_iff hc _ _).mpr
    (mk_eqvGen hcong a hq hc fun b ↦ (unit_eq_iff (ht.gobj hq hc b) _ _).mp (h b))

end GebProto.QuotientPRA
