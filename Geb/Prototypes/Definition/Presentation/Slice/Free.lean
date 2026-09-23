/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Definition.Presentation.Free
public import Geb.Prototypes.Definition.Presentation.Slice.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The free model of a finitary presentation over a slice

For a presentation over a slice polynomial endofunctor ({name}`Geb.Definition.Slice.Presentation`)
whose operations and equations have finitely many arguments and variables, the classes of all
sorts, over variables {lit}`Γ` sorted by {lit}`γ`, form an algebra over {lit}`I`
({lit}`Slice.Presentation.clsAlg`) that satisfies the equations
({lit}`Slice.Presentation.satisfies_clsAlg`). It is the free one on {lit}`Γ`: for every algebra
over {lit}`I` satisfying the equations and every assignment of {lit}`Γ` lying over the sorts of
the variables, the value of classes ({lit}`Slice.Presentation.liftAll`) is a morphism of algebras
over {lit}`I` extending the assignment ({lit}`Slice.Presentation.liftAll_g`), and the only one
({lit}`Slice.Presentation.eq_liftAll`).

An operation applies to classes of the input sorts of its arguments through representatives
chosen by {name}`Quotient.listChoice` ({lit}`Slice.Presentation.op`). It respects classes because
the congruence of the operation at a well-sorted witness
({name}`Geb.Definition.Presentation.congWit`) is well sorted when the other arguments are
({lit}`Slice.Presentation.linked_opTm_update`). The algebra of classes lies over {lit}`I` through
the sort of a class, and applies the operation to its arguments re-sorted along the equations of
sorts their compatibility states ({lit}`Slice.Presentation.resort`).

## Main definitions

* {lit}`Slice.opTm` — an operation applied to well-sorted terms of its input sorts.
* {lit}`Slice.Presentation.op` — an operation applied to classes.
* {lit}`Slice.Presentation.resort` — a class lying over a sort, as a class of that sort.
* {lit}`Slice.Presentation.clsAlg` — the algebra of classes over {lit}`I`.
* {lit}`Slice.Presentation.liftAll` — the value of a class of any sort.

## Main statements

* {lit}`Slice.Presentation.cls_opTm_congr` — the operations respect classes.
* {lit}`Slice.Presentation.op_cls` — an operation applied to the classes of terms.
* {lit}`Slice.Presentation.evalS_clsAlg` — the value of a term in the classes is the class of
  the term substituted.
* {lit}`Slice.Presentation.satisfies_clsAlg` — the classes satisfy the equations.
* {lit}`Slice.Presentation.liftAll_g`, {lit}`Slice.Presentation.eq_liftAll` — the value of classes
  is the unique morphism of algebras over {lit}`I` extending the assignment.

## References

* {cite}`KellyPower1993`, for presentations of finitary monads by operations and equations.

## Tags

equational presentation, many-sorted algebra, free algebra, finite choice, slice
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Definition.Slice

open PFunctor GebProto

universe uA uE uI u v

variable {I : Type uI} {F : SlicePFunctor.{uA, u, uI, uI} I I} {Γ Δ : Type u} (γ : Γ → I)

/-- An operation applied to well-sorted terms of the input sorts of its arguments. -/
def opTm (a : F.A) (ts : (b : F.B a) → Tm F γ (F.r ⟨a, b⟩)) : Tm F γ (F.q a) :=
  ⟨.liftBind a fun b ↦ (ts b).1, fun b ↦ ⟨(ts b).2.2, (ts b).2.1⟩, rfl⟩

/-- The terms of an updated family of well-sorted terms. -/
theorem val_update (a : F.A) [DecidableEq (F.B a)] (ts : (b : F.B a) → Tm F γ (F.r ⟨a, b⟩))
    (b : F.B a) (y : Tm F γ (F.r ⟨a, b⟩)) :
    (fun b' ↦ (Function.update ts b y b').1) = Function.update (fun b' ↦ (ts b').1) b y.1 := by
  funext b'
  by_cases hb : b' = b
  · subst hb
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hb, Function.update_of_ne hb]

namespace Presentation

variable (p : Presentation.{uA, uE, uI, u} F)

/-- An operation applied to reflexivities and one well-sorted witness is a well-sorted witness:
replacing one argument of an operation by a linked term links the applications. -/
theorem linked_opTm_update (a : F.A) [DecidableEq (F.B a)]
    (ts : (b : F.B a) → Tm F γ (F.r ⟨a, b⟩)) (b : F.B a) {y : Tm F γ (F.r ⟨a, b⟩)}
    (h : p.Linked γ (ts b) y) :
    p.Linked γ (opTm γ a ts) (opTm γ a (Function.update ts b y)) := by
  obtain ⟨w, hs, ht⟩ := h
  have hws : ∀ b' : F.B a,
      sort (F := sum F p.E) γ
          (Function.update (fun b ↦ p.toPresentation.refl (ts b).1) b w.1 b') = F.r ⟨a, b'⟩ ∧
        WellSorted (F := sum F p.E) γ
          (Function.update (fun b ↦ p.toPresentation.refl (ts b).1) b w.1 b') := by
    refine update_apply_of (fun b' t ↦ sort (F := sum F p.E) γ t = F.r ⟨a, b'⟩ ∧
      WellSorted (F := sum F p.E) γ t) _ b w.1 ⟨w.2.2, w.2.1⟩ fun b' _ ↦ ?_
    exact ⟨(p.wellSorted_refl γ (ts b').2.1).2.trans (ts b').2.2,
      (p.wellSorted_refl γ (ts b').2.1).1⟩
  have hs' : p.toPresentation.src w.1 = (ts b).1 := congrArg Subtype.val hs
  have ht' : p.toPresentation.tgt w.1 = y.1 := congrArg Subtype.val ht
  refine ⟨⟨p.toPresentation.congWit a (fun b ↦ (ts b).1) b w.1, hws, rfl⟩, ?_, ?_⟩
  · refine Subtype.ext ((p.toPresentation.src_congWit a _ b w.1).trans ?_)
    rw [hs']
    exact congrArg (FreeM.liftBind a) (update_apply_self (fun b ↦ (ts b).1) b)
  · refine Subtype.ext ((p.toPresentation.tgt_congWit a _ b w.1).trans ?_)
    rw [ht']
    exact congrArg (FreeM.liftBind a) (val_update γ a ts b y).symm

/-- The operations respect classes: arguments with equal classes give applications with equal
classes. -/
theorem cls_opTm_congr (a : F.A) [FinEnum (F.B a)] {ts ts' : (b : F.B a) → Tm F γ (F.r ⟨a, b⟩)}
    (h : ∀ b, p.cls γ (ts b) = p.cls γ (ts' b)) :
    p.cls γ (opTm γ a ts) = p.cls γ (opTm γ a ts') :=
  (p.cls_eq_iff γ _ _).mpr (eqvGen_of_update (r := fun b ↦ p.Linked γ (i := F.r ⟨a, b⟩))
    (R := p.Linked γ) (opTm γ a) (fun ts b _ hy ↦ p.linked_opTm_update γ a ts b hy)
    fun b ↦ (p.cls_eq_iff γ _ _).mp (h b))

/-- The kernel of the class map at a sort: two terms with one class. -/
abbrev kerSetoid (i : I) : Setoid (Tm F γ i) where
  r s t := p.cls γ s = p.cls γ t
  iseqv := ⟨fun _ ↦ rfl, Eq.symm, Eq.trans⟩

/-- A class as a class of the kernel of the class map. -/
def toKer {i : I} : p.Cls γ i → Quotient (p.kerSetoid γ i) :=
  Quot.lift (Quotient.mk _) fun _ _ r ↦ Quotient.sound (Quot.sound r)

/-- An operation applied to classes of the input sorts of its arguments: the class of its
application to representatives, chosen through {name}`Quotient.listChoice` along an enumeration
of its arguments. -/
def op (a : F.A) [FinEnum (F.B a)] (f : (b : F.B a) → p.Cls γ (F.r ⟨a, b⟩)) :
    p.Cls γ (F.q a) :=
  letI : ∀ i, Setoid (Tm F γ i) := p.kerSetoid γ
  Quotient.lift (s := piSetoid)
    (fun g : (b : F.B a) → b ∈ FinEnum.toList (F.B a) → Tm F γ (F.r ⟨a, b⟩) ↦
      p.cls γ (opTm γ a fun b ↦ g b (FinEnum.mem_toList b)))
    (fun g g' hgg ↦ p.cls_opTm_congr γ a fun b ↦
      (show ∀ hb : b ∈ FinEnum.toList (F.B a), p.cls γ (g b hb) = p.cls γ (g' b hb) from hgg b)
        (FinEnum.mem_toList b))
    (Quotient.listChoice fun b _ ↦ p.toKer γ (f b))

/-- An operation applied to the classes of terms is the class of its application to the
terms. -/
theorem op_cls (a : F.A) [FinEnum (F.B a)] (ts : (b : F.B a) → Tm F γ (F.r ⟨a, b⟩)) :
    p.op γ a (fun b ↦ p.cls γ (ts b)) = p.cls γ (opTm γ a ts) :=
  letI : ∀ i, Setoid (Tm F γ i) := p.kerSetoid γ
  congrArg (Quotient.lift (s := piSetoid) _ _) (Quotient.listChoice_mk fun b _ ↦ ts b)

/-- A class lying over {lit}`j`, as a class of sort {lit}`j`. -/
def resort {j : I} : (y : Σ i, p.Cls γ i) → y.1 = j → p.Cls γ j
  | ⟨_, c⟩, h => h ▸ c

/-- Re-sorting equal classes gives equal classes. -/
theorem resort_congr {y y' : Σ i, p.Cls γ i} (hy : y = y') {j : I} (h : y.1 = j)
    (h' : y'.1 = j) : p.resort γ y h = p.resort γ y' h' := by
  subst hy
  rfl

/-- A class re-sorted to its own sort is itself, as an element of the classes of all sorts. -/
theorem sigma_resort {j : I} (y : Σ i, p.Cls γ i) (h : y.1 = j) : y = ⟨j, p.resort γ y h⟩ := by
  obtain ⟨i, c⟩ := y
  subst h
  rfl

/-- The class of a term, as an element of the classes of all sorts, is the class of the term at
any equal sort. -/
theorem sigma_cls {i j : I} (t : Tm F γ i) (h : i = j) :
    (⟨i, p.cls γ t⟩ : Σ i, p.Cls γ i) = ⟨j, p.cls γ ⟨t.1, t.2.1, t.2.2.trans h⟩⟩ := by
  subst h
  rfl

/-- Every finite family of classes is the family of classes of a family of terms. -/
theorem exists_cls {ι : Type u} [FinEnum ι] {s : ι → I} (f : (x : ι) → p.Cls γ (s x)) :
    ∃ ts : (x : ι) → Tm F γ (s x), ∀ x, p.cls γ (ts x) = f x :=
  exists_forall_of_finEnum fun x ↦ Function.Coequalizer.mk_surjective _ _ (f x)

/-- Re-sorting the class of a term is the class of the term at the new sort. -/
theorem resort_cls {i j : I} (t : Tm F γ i) (h : i = j) :
    p.resort γ ⟨i, p.cls γ t⟩ h = p.cls γ ⟨t.1, t.2.1, t.2.2.trans h⟩ := by
  subst h
  rfl

variable [∀ a, FinEnum (F.B a)]

/-- The algebra of classes over {lit}`I`: the classes of all sorts, each over its sort, and an
operation applied to classes of the input sorts of its arguments. -/
def clsAlg : Alg.{uA, uI, u, max uI uA u} F where
  carrier := Σ i, p.Cls γ i
  p := Sigma.fst
  g x := ⟨F.q x.1.1, p.op γ x.1.1 fun b ↦ p.resort γ (x.1.2 b) (congrFun x.2 b)⟩
  hg := rfl

/-- The value of a term in the classes, its variables assigned the classes of well-sorted terms of
their sorts, is the class of the term with those terms substituted. -/
theorem evalS_clsAlg {δ : Δ → I} {σ : Δ → F.toPFunctor.FreeM Γ} (hσ : IsSorted δ γ σ)
    (t : F.toPFunctor.FreeM Δ) (ht : WellSorted δ t) :
    evalS (p.clsAlg γ) δ (fun x ↦ ⟨δ x, p.cls γ ⟨σ x, hσ x⟩⟩) rfl t ht =
      ⟨sort δ t, p.cls γ ⟨t.bind σ, (wellSorted_bind hσ t ht).1, (wellSorted_bind hσ t ht).2⟩⟩ := by
  refine FreeM.rec (motive := fun t ↦ ∀ ht : WellSorted δ t,
    evalS (p.clsAlg γ) δ (fun x ↦ ⟨δ x, p.cls γ ⟨σ x, hσ x⟩⟩) rfl t ht =
      ⟨sort δ t, p.cls γ ⟨t.bind σ, (wellSorted_bind hσ t ht).1, (wellSorted_bind hσ t ht).2⟩⟩)
    (fun _ _ ↦ rfl) ?_ t ht
  intro a k ih h
  refine Sigma.ext rfl (heq_of_eq ?_)
  refine (congrArg (p.op γ a) (funext fun b ↦ ?_)).trans (p.op_cls γ a fun b ↦
    ⟨(k b).bind σ, (wellSorted_bind hσ (k b) (h b).2).1,
      (wellSorted_bind hσ (k b) (h b).2).2.trans (h b).1⟩)
  exact (p.resort_congr γ (ih b (h b).2) _ (h b).1).trans (p.resort_cls γ _ (h b).1)

/-- The classes satisfy the equations: an equation's instance at representatives of the
variables relates its two sides. -/
theorem satisfies_clsAlg [∀ e, FinEnum (p.E.B e)] : p.Satisfies (p.clsAlg γ) := by
  intro e σ hσ
  obtain ⟨ts, hts⟩ := p.exists_cls γ fun v ↦ p.resort γ (σ v) (congrFun hσ v)
  obtain rfl : σ = fun v ↦ ⟨p.E.r ⟨e, v⟩, p.cls γ (ts v)⟩ :=
    funext fun v ↦ (p.sigma_resort γ (σ v) (congrFun hσ v)).trans (by rw [hts v])
  have hs : IsSorted (fun v ↦ p.E.r ⟨e, v⟩) γ fun v ↦ (ts v).1 := fun v ↦ (ts v).2
  refine (p.evalS_clsAlg γ hs (p.lhs e) (p.lhs_sorted e).1).trans ?_
  refine Eq.trans ?_ (p.evalS_clsAlg γ hs (p.rhs e) (p.rhs_sorted e).1).symm
  exact (p.sigma_cls γ ⟨_, (wellSorted_bind hs _ (p.lhs_sorted e).1).1,
      (wellSorted_bind hs _ (p.lhs_sorted e).1).2⟩ (p.lhs_sorted e).2).trans
    ((congrArg (Sigma.mk _) (p.cls_bind_lhs γ e _ hs)).trans
      (p.sigma_cls γ ⟨_, (wellSorted_bind hs _ (p.rhs_sorted e).1).1,
        (wellSorted_bind hs _ (p.rhs_sorted e).1).2⟩ (p.rhs_sorted e).2).symm)

variable {A : Alg.{uA, uI, u, v} F} {γ} (h : p.Satisfies A) (env : Γ → A.carrier)
  (henv : A.p ∘ env = γ)

omit [∀ a, FinEnum (F.B a)] in
/-- The value of a class of any sort. -/
def liftAll : (Σ i, p.Cls γ i) → A.carrier := fun y ↦ p.lift h env henv y.1 y.2

omit [∀ a, FinEnum (F.B a)] in
/-- The value of a class lies over its sort. -/
theorem p_liftAll : A.p ∘ p.liftAll h env henv = Sigma.fst :=
  funext fun y ↦ p.p_lift h env henv y.2

omit [∀ a, FinEnum (F.B a)] in
/-- The value of a class is the value of its re-sorting. -/
theorem liftAll_resort {j : I} (y : Σ i, p.Cls γ i) (hy : y.1 = j) :
    p.liftAll h env henv y = p.lift h env henv j (p.resort γ y hy) := by
  obtain ⟨i, c⟩ := y
  subst hy
  rfl

/-- The value of classes is a morphism of algebras over {lit}`I`. -/
theorem liftAll_g (x : F.toSliceDomPFunctor.Obj (p.clsAlg γ).p) :
    p.liftAll h env henv ((p.clsAlg γ).g x) =
      A.g (F.toSliceDomPFunctor.map (p.liftAll h env henv) (p.p_liftAll h env henv) x) := by
  obtain ⟨⟨a, v⟩, hv⟩ := x
  obtain ⟨ts, hts⟩ := p.exists_cls γ fun b ↦ p.resort γ (v b) (congrFun hv b)
  have hf : (fun b ↦ p.resort γ (v b) (congrFun hv b)) = fun b ↦ p.cls γ (ts b) :=
    (funext hts).symm
  refine (congrArg (fun f ↦ p.lift h env henv (F.q a) (p.op γ a f)) hf).trans
    ((congrArg (p.lift h env henv (F.q a)) (p.op_cls γ a ts)).trans ((p.lift_cls h env henv _).trans
      ((evalS_liftBind γ env henv a _ _).trans
        (congrArg A.g (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦ ?_))))))))
  exact ((p.liftAll_resort h env henv (v b) (congrFun hv b)).trans
    (congrArg (p.lift h env henv _) (hts b).symm)).symm

/-- The value of classes is the only morphism of algebras over {lit}`I` extending the
assignment: a morphism of algebras agrees with it on the class of every term, by induction on
the term. -/
theorem eq_liftAll (g : (Σ i, p.Cls γ i) → A.carrier) (hgp : A.p ∘ g = Sigma.fst)
    (hg : ∀ x, g ((p.clsAlg γ).g x) = A.g (F.toSliceDomPFunctor.map g hgp x))
    (hgenv : ∀ x, g ⟨γ x, p.cls γ ⟨.pure x, trivial, rfl⟩⟩ = env x) (y : Σ i, p.Cls γ i) :
    g y = p.liftAll h env henv y := by
  obtain ⟨i, c⟩ := y
  refine Quot.ind (β := fun c ↦ g ⟨i, c⟩ = p.liftAll h env henv ⟨i, c⟩) (fun t ↦ ?_) c
  obtain ⟨t, ht⟩ := t
  refine FreeM.rec (motive := fun t ↦ ∀ i (ht : WellSorted γ t ∧ sort γ t = i),
    g ⟨i, p.cls γ ⟨t, ht⟩⟩ = evalS A γ env henv t ht.1) ?_ ?_ t i ht
  · intro x i ht
    obtain ⟨_, rfl⟩ := ht
    exact hgenv x
  · intro a k ih i ht
    obtain ⟨hw, rfl⟩ := ht
    let ts : (b : F.B a) → Tm F γ (F.r ⟨a, b⟩) := fun b ↦ ⟨k b, (hw b).2, (hw b).1⟩
    have hx : (⟨F.q a, p.cls γ ⟨.liftBind a k, hw, rfl⟩⟩ : Σ i, p.Cls γ i) =
        (p.clsAlg γ).g ⟨⟨a, fun b ↦ ⟨F.r ⟨a, b⟩, p.cls γ (ts b)⟩⟩, rfl⟩ :=
      Sigma.ext rfl (heq_of_eq (p.op_cls γ a ts).symm)
    exact (congrArg g hx).trans ((hg _).trans (congrArg A.g (Subtype.ext (Sigma.ext rfl
      (heq_of_eq (funext fun b ↦ ih b _ ⟨(hw b).2, (hw b).1⟩))))))

end Presentation

end Geb.Definition.Slice

end
