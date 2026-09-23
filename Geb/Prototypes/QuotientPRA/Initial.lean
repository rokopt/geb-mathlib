/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.QuotientPRA.Congruence
public import Geb.Prototypes.QuotientPRA.Signature
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Fintype.Quotient

meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The quotient W-type of a finitary signature is the initial model

For a signature whose operations have finitely many arguments and a system of one-step
equations whose equations have finitely many variables, the quotient W-type of
{lit}`GebProto.QuotientPRA.Signature.qpra` is an algebra of the signature
({lit}`opQ`) that satisfies the equations ({lit}`satisfies_opQ`), and the eliminator
{lit}`GebProto.QuotientPRA.Signature.lift` into any algebra satisfying the equations is
the unique morphism of algebras out of it ({lit}`lift_opQ`, {lit}`eq_lift`). It is
therefore the initial algebra satisfying the equations: the quotient inductive type of
the signature and equations.

The algebra structure applies an operation to classes by choosing representatives.
Finitely many choices are constructive, through {name}`Quotient.listChoice` over an
enumeration of the arguments. The result is independent of the representatives because
the witnesses generate a congruence: the congruence of an operation relates the
applications of the operation to arguments related by witnesses, and changing one
argument at a time, the other arguments are related to themselves by the reflexivity
witnesses the congruences build ({lit}`exists_refl`).

## Main definitions

* {lit}`Term`, {lit}`Wit`, {lit}`Cls` — the terms, the witnesses, and the classes of
  terms.
* {lit}`op`, {lit}`congW` — the term an operation builds, and the witness its
  congruence builds.
* {lit}`WRel`, {lit}`wSetoid` — the relation of being the endpoints of a witness, and
  the equivalence relation it generates.
* {lit}`opQ` — the operations on classes.

## Main statements

* {lit}`term_induction` — induction on terms.
* {lit}`exists_refl` — every term has a reflexivity witness.
* {lit}`op_rel_update`, {lit}`op_eqvGen_update`, {lit}`op_eqvGen` — the operations
  respect the equivalence relation the witnesses generate, in one argument and in all.
* {lit}`opQ_mk` — the operations on classes of terms.
* {lit}`satisfies_opQ` — the classes satisfy the equations.
* {lit}`lift_opQ`, {lit}`eq_lift` — the eliminator is the unique morphism of algebras
  out of the classes.

## Implementation notes

The finiteness of the arguments is an enumeration, {name}`FinEnum`, whose list the
choices recurse on, as in {lit}`GebProto.QuotientPRA.Congruence`. mathlib's
{name}`Quotient.finChoice` for a {name}`Fintype` depends on {lit}`Classical.choice`;
{name}`Quotient.listChoice` does not.

## References

* {cite}`FiorePittsSteenkamp2020`
* {cite}`AltenkirchCapriottiDijkstraKrausNordvallForsberg2018`

## Tags

quotient inductive type, initial algebra, W-type, congruence, equational theory
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA.Signature

universe uA uB

variable {P : PFunctor.{uA, uB}} {eqns : Equations P}

variable (P eqns) in
/-- The terms of the W-type. -/
abbrev Term : Type (max uA uB) := (qpra P eqns).W.obj ⟨objOf .zero⟩

variable (P eqns) in
/-- The witnesses of the W-type. -/
abbrev Wit : Type (max uA uB) := (qpra P eqns).W.obj ⟨objOf .one⟩

/-- The term an operation builds from terms. -/
def op (a : P.A) (ts : P.B a → Term P eqns) : Term P eqns :=
  PresheafPFunctor.W.mk (freeNode _ (.inl a) ts)

/-- The congruence witness of an operation at witnesses between its arguments. -/
def congW (a : P.A) (es : P.B a → Wit P eqns) : Wit P eqns :=
  PresheafPFunctor.W.mk (freeNode _ (.inr (.inl a)) es)

/-- The source of a congruence witness is the operation on the sources. -/
theorem src_congW (a : P.A) (es : P.B a → Wit P eqns) :
    src (qpra P eqns).W ⟨⟨⟩⟩ (congW a es) = op a fun b ↦ src (qpra P eqns).W ⟨⟨⟩⟩ (es b) :=
  endpoint_mk_freeNode_cong false a es

/-- The target of a congruence witness is the operation on the targets. -/
theorem tgt_congW (a : P.A) (es : P.B a → Wit P eqns) :
    tgt (qpra P eqns).W ⟨⟨⟩⟩ (congW a es) = op a fun b ↦ tgt (qpra P eqns).W ⟨⟨⟩⟩ (es b) :=
  endpoint_mk_freeNode_cong true a es

/-- Induction on terms: a property of every term follows from its preservation by the
operations. -/
theorem term_induction {motive : Term P eqns → Prop}
    (step : ∀ (a : P.A) (ts : P.B a → Term P eqns), (∀ b, motive (ts b)) → motive (op a ts))
    (t : Term P eqns) : motive t :=
  FreeArity.W_induction (S := freeArity P eqns)
    (motive := fun c ↦ match c with
      | (_, .zero) => motive
      | (_, .one) => fun _ ↦ True)
    (fun s ts ih ↦ by
      rcases s with a | a | ⟨e, o⟩
      · exact step a ts ih
      · trivial
      · trivial)
    t

section Finitary

variable [∀ a, FinEnum (P.B a)]

/-- Every term has a reflexivity witness: the congruence of its operation at reflexivity
witnesses of its arguments. -/
theorem exists_refl (t : Term P eqns) :
    ∃ e : Wit P eqns, src (qpra P eqns).W ⟨⟨⟩⟩ e = t ∧ tgt (qpra P eqns).W ⟨⟨⟩⟩ e = t :=
  term_induction (motive := fun t ↦
      ∃ e : Wit P eqns, src (qpra P eqns).W ⟨⟨⟩⟩ e = t ∧ tgt (qpra P eqns).W ⟨⟨⟩⟩ e = t)
    (fun a ts ih ↦ by
      obtain ⟨es, hes⟩ := exists_forall_of_finEnum ih
      exact ⟨congW a es,
        (src_congW a es).trans (congrArg (op a) (funext fun b ↦ (hes b).1)),
        (tgt_congW a es).trans (congrArg (op a) (funext fun b ↦ (hes b).2))⟩) t

variable (P eqns) in
/-- The relation on terms of being the endpoints of a witness. -/
abbrev WRel : Term P eqns → Term P eqns → Prop :=
  Function.Coequalizer.Rel (src (qpra P eqns).W ⟨⟨⟩⟩) (tgt (qpra P eqns).W ⟨⟨⟩⟩)

/-- A witness between one argument of an operation and another term relates the
operation's applications before and after replacing that argument: the congruence of the
operation at that witness and at reflexivity witnesses of the other arguments. -/
theorem op_rel_update (a : P.A) (ts : P.B a → Term P eqns) (b₀ : P.B a) (e : Wit P eqns)
    (he : src (qpra P eqns).W ⟨⟨⟩⟩ e = ts b₀) :
    WRel P eqns (op a ts) (op a (Function.update ts b₀ (tgt (qpra P eqns).W ⟨⟨⟩⟩ e))) := by
  obtain ⟨rs, hrs⟩ := exists_forall_of_finEnum fun b ↦ exists_refl (ts b)
  have hsrc : src (qpra P eqns).W ⟨⟨⟩⟩ (congW a (Function.update rs b₀ e)) = op a ts := by
    refine (src_congW a _).trans (congrArg (op a) (funext fun b ↦ ?_))
    by_cases hb : b = b₀
    · subst hb
      rw [Function.update_self]
      exact he
    · rw [Function.update_of_ne hb]
      exact (hrs b).1
  have htgt : tgt (qpra P eqns).W ⟨⟨⟩⟩ (congW a (Function.update rs b₀ e)) =
      op a (Function.update ts b₀ (tgt (qpra P eqns).W ⟨⟨⟩⟩ e)) := by
    refine (tgt_congW a _).trans (congrArg (op a) (funext fun b ↦ ?_))
    by_cases hb : b = b₀
    · subst hb
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
      exact (hrs b).2
  rw [← hsrc, ← htgt]
  exact Function.Coequalizer.Rel.intro _

/-- The operations respect the generated equivalence relation in each argument. -/
theorem op_eqvGen_update (a : P.A) (ts : P.B a → Term P eqns) (b₀ : P.B a)
    {x y : Term P eqns} (hxy : Relation.EqvGen (WRel P eqns) x y) :
    Relation.EqvGen (WRel P eqns) (op a (Function.update ts b₀ x))
      (op a (Function.update ts b₀ y)) := by
  refine Relation.EqvGen.rec (motive := fun x y _ ↦ Relation.EqvGen (WRel P eqns)
      (op a (Function.update ts b₀ x)) (op a (Function.update ts b₀ y)))
    (fun x y hr ↦ ?_) (fun _ ↦ .refl _) (fun _ _ _ ih ↦ .symm _ _ ih)
    (fun _ _ _ _ _ ih₁ ih₂ ↦ .trans _ _ _ ih₁ ih₂) hxy
  obtain ⟨e⟩ := hr
  have h := op_rel_update a (Function.update ts b₀ (src (qpra P eqns).W ⟨⟨⟩⟩ e)) b₀ e
    (Function.update_self b₀ _ ts).symm
  rw [update_update] at h
  exact .rel _ _ h

/-- The operations respect the generated equivalence relation: arguments related in
every place give related applications, the arguments being replaced one at a time
along an enumeration. -/
theorem op_eqvGen (a : P.A) {ts ts' : P.B a → Term P eqns}
    (h : ∀ b, Relation.EqvGen (WRel P eqns) (ts b) (ts' b)) :
    Relation.EqvGen (WRel P eqns) (op a ts) (op a ts') := by
  let g : List (P.B a) → P.B a → Term P eqns :=
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
  have hstep : ∀ l, Relation.EqvGen (WRel P eqns) (op a ts) (op a (g l)) :=
    List.rec (.refl _) fun b₀ l ih ↦ by
      refine .trans _ _ _ ih ?_
      have hb₀ : Relation.EqvGen (WRel P eqns) (g l b₀) (ts' b₀) :=
        (hg l b₀).elim (fun he ↦ he ▸ h b₀) (fun he ↦ he ▸ .refl _)
      have := op_eqvGen_update a (g l) b₀ hb₀
      rwa [update_apply_self] at this
  have hfin : g (FinEnum.toList (P.B a)) = ts' :=
    funext fun b ↦ hmem _ b (FinEnum.mem_toList b)
  exact hfin ▸ hstep _

variable (P eqns) in
/-- The classes of terms: the quotient W-type's value at the one object. -/
abbrev Cls : Type (max uA uB) := (quotient (qpra P eqns)).obj ⟨⟨⟨⟩⟩⟩

variable (P eqns) in
/-- The equivalence relation the witnesses generate, as a setoid. -/
abbrev wSetoid : Setoid (Term P eqns) := Relation.EqvGen.setoid (WRel P eqns)

attribute [local instance] wSetoid

/-- The class of a term, in the quotient by the equivalence relation the witnesses
generate. -/
def toSetoid : Cls P eqns → Quotient (wSetoid P eqns) :=
  Quot.map id fun _ _ h ↦ .rel _ _ h

/-- The operation {lit}`a` on classes: apply it to representatives, chosen through
{name}`Quotient.listChoice` over an enumeration of its arguments. -/
def opQ (a : P.A) (f : P.B a → Cls P eqns) : Cls P eqns :=
  Quotient.lift (s := piSetoid)
    (fun g : (b : P.B a) → b ∈ FinEnum.toList (P.B a) → Term P eqns ↦
      quotientMk (qpra P eqns) (op a fun b ↦ g b (FinEnum.mem_toList b)))
    (fun _ _ hgg ↦ Quot.eqvGen_sound (op_eqvGen a fun b ↦
      (show ∀ _ : b ∈ FinEnum.toList (P.B a), Relation.EqvGen (WRel P eqns) _ _ from hgg b)
        (FinEnum.mem_toList b)))
    (Quotient.listChoice fun b _ ↦ toSetoid (f b))

/-- The operation on the classes of terms is the class of the operation on the terms. -/
theorem opQ_mk (a : P.A) (ts : P.B a → Term P eqns) :
    opQ a (fun b ↦ quotientMk (qpra P eqns) (ts b)) = quotientMk (qpra P eqns) (op a ts) :=
  congrArg (Quotient.lift (s := piSetoid) _ _) (Quotient.listChoice_mk fun b _ ↦ ts b)

omit [∀ a, FinEnum (P.B a)] in
/-- Every finite family of classes is the family of classes of a family of terms. -/
theorem exists_mk {ι : Type uB} [FinEnum ι] (f : ι → Cls P eqns) :
    ∃ ts : ι → Term P eqns, ∀ i, quotientMk (qpra P eqns) (ts i) = f i :=
  exists_forall_of_finEnum fun i ↦ Quot.exists_rep (f i)

variable {Y : Type (max uA uB)} {S : P.Obj Y → Y}

/-- The eliminator is a morphism of algebras out of the classes. -/
theorem lift_opQ (sat : Satisfies (eqns := eqns) S) (a : P.A) (f : P.B a → Cls P eqns) :
    (lift S sat).app ⟨⟨⟨⟩⟩⟩ (opQ a f) = S ⟨a, fun b ↦ (lift S sat).app ⟨⟨⟨⟩⟩⟩ (f b)⟩ := by
  obtain ⟨ts, hts⟩ := exists_mk f
  obtain rfl : f = fun b ↦ quotientMk (qpra P eqns) (ts b) := (funext hts).symm
  rw [opQ_mk]
  exact lift_intro S sat a ts

/-- The eliminator is the only morphism of algebras out of the classes: a morphism of
algebras agrees with it on the class of every term, by induction on the term. -/
theorem eq_lift (sat : Satisfies (eqns := eqns) S) (h : Cls P eqns → Y)
    (hh : ∀ a f, h (opQ a f) = S ⟨a, fun b ↦ h (f b)⟩) (q : Cls P eqns) :
    h q = (lift S sat).app ⟨⟨⟨⟩⟩⟩ q :=
  Quot.ind (β := fun q ↦ h q = (lift S sat).app ⟨⟨⟨⟩⟩⟩ q)
    (term_induction fun a ts ih ↦ by
      change h (quotientMk (qpra P eqns) (op a ts)) =
        (lift S sat).app ⟨⟨⟨⟩⟩⟩ (quotientMk (qpra P eqns) (op a ts))
      rw [← opQ_mk, hh, lift_opQ sat]
      exact congrArg S (Sigma.ext rfl (heq_of_eq (funext ih)))) q

variable [∀ e, FinEnum (eqns.V e)]

/-- The classes satisfy the equations: an equation's witness at representatives of the
variables relates its two sides. -/
theorem satisfies_opQ : Satisfies (eqns := eqns) fun x : P.Obj (Cls P eqns) ↦ opQ x.1 x.2 := by
  intro e ρ
  obtain ⟨ts, hts⟩ := exists_mk ρ
  obtain rfl : ρ = fun v ↦ quotientMk (qpra P eqns) (ts v) := (funext hts).symm
  change opQ (eqns.lhs e).1 (fun b ↦ quotientMk (qpra P eqns) (ts ((eqns.lhs e).2 b))) =
    opQ (eqns.rhs e).1 (fun b ↦ quotientMk (qpra P eqns) (ts ((eqns.rhs e).2 b)))
  rw [opQ_mk, opQ_mk]
  exact (congrArg (quotientMk (qpra P eqns)) (src_mk_freeNode_eqn e false ts)).symm.trans
    ((quotientMk_src (qpra P eqns) _).trans
      (congrArg (quotientMk (qpra P eqns)) (tgt_mk_freeNode_eqn e false ts)))

end Finitary

end GebProto.QuotientPRA.Signature
