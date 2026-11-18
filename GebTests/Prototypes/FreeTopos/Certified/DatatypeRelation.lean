/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The relation at a type of the datatype language, in Lean

The datatype language's soundness relates a value to a type by a relation defined in the
internal language as a fold of the type's tree
({name}`GebTests.Prototypes.FreeTopos.Datatypes.relDefn`): the fold's value at a node pairs the
node rebuilt with a predicate of a context, the program's definitions and the
markers of its datatypes, and a value. At the trees a value is a tree's quotation, at the unit
type the unit value, at a product a pair of related values, at a function type a value whose
application to each related argument converges to a related value, at a list type a list of
related values, at a datatype the quotation of a member, by the typing's membership in the
markers' datatypes, and at an opaque sort a tree's quotation. The same fold over Lean's trees,
with the values of the globals the kernel loads in place of the references to the compilers'
definitions, is a relation of Lean ({lit}`DRel`), and the definition's arrow represents it.

## Main definitions

* {lit}`DRel` — the relation at a type, in a context, of a value.

## Main statements

* {lit}`represents_rel` — the relation's arrow represents {lit}`DRel`.

## References

* {citeKey}`Tait1967`, for the logical relation.

## Tags

internal language, logical relation, datatypes, rose tree, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open GebTests.Prototypes.FreeTopos.Weakening (Prog)
open GebTests.Prototypes.FreeTopos.Normalization (Defs pc)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeAccepted (statementDefs fnsK)
open GebTests.Prototypes.FreeTopos.Certified.DatatypeTranslated
open GebTests.Prototypes.FreeTopos.Certified.DatatypeStatements
open Internal (Term RepC repC_lam repC_app repC_pair repC_fst repC_snd repC_eq repC_listRec
  repC_roseRec repC_nil repC_cons repC_lnode repC_star objVal_nat objVal_one objVal_exp
  objVal_prod objVal_list objVal_omega isTy_nat isTy_exp isTy_omega isTy_list isTy_prod)
open Kernel (tT tList tProd tArrow)
open Sorts

/-- The relation's contexts: the program's definitions and the markers of its datatypes. -/
abbrev Ctx : Type := List Kernel.Tree × List Kernel.Tree

/-- The values of the relation's fold: a type's tree rebuilt, and the relation at it. -/
abbrev RelV : Type := Kernel.Tree × (Ctx → Kernel.Tree → Prop)

/-- The choice between two propositions by a label's being a given one, as the fold's test of
the type's label computes it. -/
def labelIs (l k : ℕ) (P Q : Prop) : Prop := if (if l = k then 1 else 0) ≠ 0 then P else Q

/-- The fold's value where a type has no child: the leaf of label zero, related to nothing. -/
def relNone : RelV := (Kernel.leaf 0, fun _ _ ↦ False)

/-- The values of a type's first two children, {name}`relNone` for one it has not. -/
def firstTwo (cs : List RelV) : RelV × RelV := cs.foldr (fun x r ↦ (x, r.1)) (relNone, relNone)

/-- The relation at a type's node, from its label and its children's values, in a context, of
a value: by the label, at the trees a tree's quotation, at the unit type the unit value, at a
product a pair of values related at the children, at a function type a value whose application
to each value related at the first child converges to one related at the second, at a list
type a list of values related at the child, at a datatype the quotation of a member of the
datatype the first child's atom names among the context's markers, at an opaque sort a tree's
quotation, and at no other label a value. -/
def relBody (f : EvalFns) (l : ℕ) (cs : List RelV) (R : Ctx) (w : Kernel.Tree) : Prop :=
  labelIs l Kernel.Label.tyTree (∃ t, w = f.valQuote t)
  (labelIs l Kernel.Label.tyUnit (w = f.valUnit)
  (labelIs l Kernel.Label.tyProd
    (∃ a, ∃ b, w = f.valPair a b ∧ (firstTwo cs).1.2 R a ∧ (firstTwo cs).2.2 R b)
  (labelIs l Kernel.Label.tyArrow
    (∀ x, (firstTwo cs).1.2 R x →
      Conv f.just (fun k ↦ (Level f R.1 k).2 w x) fun y ↦ (firstTwo cs).2.2 R y)
  (labelIs l Kernel.Label.tyList
    ((f.isSome (f.listOf w)).label ≠ 0 ∧
      ∀ x ∈ (f.get (f.listOf w)).children, (firstTwo cs).1.2 R x)
  (labelIs l 5
    (∃ t, w = f.valQuote t ∧
      (f.memberOf R.2 (RoseTree.node 1 (firstTwo cs).1.1.children) t).label ≠ 0)
  (labelIs l 6 (∃ t, w = f.valQuote t) False))))))

/-- The fold's step: the node rebuilt from the label and the children's rebuilt trees, with the
relation at the node ({name}`relBody`). -/
def relStep (f : EvalFns) (p : ℕ × List RelV) : RelV :=
  (RoseTree.node p.1 (p.2.foldr (fun x r ↦ x.1 :: r) []), fun R w ↦ relBody f p.1 p.2 R w)

/-- The relation at a type of the datatype language, in a context, of a value: the fold of the
type's tree by {name}`relStep`. -/
def DRel (f : EvalFns) (A : Kernel.Tree) (R : Ctx) (w : Kernel.Tree) : Prop :=
  (RoseTree.elim (fun l cs ↦ relStep f (l, cs)) A).2 R w

/-- The type of the relation's fold's values: a tree and a predicate of a context and a
value. -/
def relC : PartialHorn.Tree := prod treeTy (exp Defs3.ctxTy (exp treeTy omega))

/-- The trees of bitstrings, the values of the type of trees. -/
abbrev BT : Type := RoseTree (List Bit)

/-- The values of the type of the relation's contexts. -/
abbrev BCtx : Type := List BT × List BT

/-- The values of the type of the fold's values. -/
abbrev BRel : Type := BT × FunRel BCtx (FunRel BT Prop)

/-- The representation of the kernel's trees. -/
abbrev RT : Kernel.Tree → BT → Prop := Rep.rose RN

/-- The representation of the relation's contexts. -/
abbrev RCtx : Ctx → BCtx → Prop := Rep.prod (Rep.list RT) (Rep.list RT)

/-- The representation of the predicates of a value. -/
abbrev RPred : (Kernel.Tree → Prop) → FunRel BT Prop → Prop := Rep.exp RT Rep.prop

/-- The representation of the fold's values. -/
abbrev RRel : RelV → BRel → Prop := Rep.prod RT (Rep.exp RCtx RPred)

/-- The fold's value where a type has no child, as a term. -/
def noneT (o : ℕ) : Term :=
  Term.pair (leafT bnilT) (Term.lam Defs3.ctxTy (Term.lam treeTy (Internal.Logic.ff o)))

/-- The values of a type's first two children, as a term of the fold's argument. -/
def firstTwoT (o : ℕ) (t : Term) : Term :=
  Term.listRec (Term.pair (noneT o) (noneT o)) (Term.pair (v 1) (Term.fst (v 0))) (Term.snd t)

/-- The type of trees is a type, over every constants. -/
theorem isTy_tree (G : Internal.Globals) : Internal.IsTy G 0 treeTy = true :=
  (ty_spec (G := G) (n := 0) (ρ := []) (ds := []) tT rfl).1

/-- The type of bitstrings is a type, over every constants. -/
theorem isTy_bits (G : Internal.Globals) : Internal.IsTy G 0 bitsTy = true := by
  simp [bitsTy, bitTy, isTy_list, Internal.isTy_coprod, Internal.isTy_one]

/-- The type of the relation's contexts is a type, over every constants. -/
theorem isTy_ctx (G : Internal.Globals) : Internal.IsTy G 0 Defs3.ctxTy = true := by
  simp [Defs3.ctxTy, isTy_prod, isTy_list, isTy_tree]

/-- The type of the fold's values is a type, over every constants. -/
theorem isTy_relC (G : Internal.Globals) : Internal.IsTy G 0 relC = true := by
  simp [relC, isTy_prod, isTy_exp, isTy_tree, isTy_ctx, isTy_omega]

/-- The type of pairs of the fold's values is a type, over every constants. -/
theorem isTy_relC₂ (G : Internal.Globals) : Internal.IsTy G 0 (prod relC relC) = true := by
  simp [isTy_prod, isTy_relC]

/-- The type of the fold's arguments is a type, over every constants. -/
theorem isTy_arg (G : Internal.Globals) :
    Internal.IsTy G 0 (prod bitsTy (list relC)) = true := by
  simp [isTy_prod, isTy_list, isTy_relC, isTy_bits]

section Values

variable {ds : List PartialHorn.Defn}

/-- The value of the type of trees, unfolded. -/
theorem objVal_tree : ObjVal [] (unfoldTerm sig ds treeTy) BT := objVal_ty' (T := tT) rfl

/-- The value of the type of bitstrings, unfolded. -/
theorem objVal_bits : ObjVal [] (unfoldTerm sig ds bitsTy) (List Bit) := by obj_val

/-- The value of the type of the relation's contexts, unfolded. -/
theorem objVal_ctx : ObjVal [] (unfoldTerm sig ds Defs3.ctxTy) BCtx :=
  objVal_prod (objVal_list objVal_tree) (objVal_list objVal_tree)

/-- The value of the type of predicates of a value, unfolded. -/
theorem objVal_pred : ObjVal [] (unfoldTerm sig ds (exp treeTy omega)) (FunRel BT Prop) :=
  objVal_exp objVal_tree objVal_omega

/-- The value of the type of the fold's values, unfolded. -/
theorem objVal_relC : ObjVal [] (unfoldTerm sig ds relC) BRel :=
  objVal_prod objVal_tree (objVal_exp objVal_ctx objVal_pred)

end Values

section Children

variable {G : Internal.Globals} {ds : List PartialHorn.Defn} {X : PartialHorn.Tree}
  {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}

/-- The relation of the first of two children's values, applied to a context and a value,
represents the relation's holding of them. -/
theorem repC_first {Ht Rt xt : Term} {Hf : S → RelV × RelV} {Rf : S → Ctx}
    {Xf : S → Kernel.Tree}
    (hH : RepC G 0 ds [] Ht X e (prod relC relC) R (Rep.prod RRel RRel) Hf)
    (hR : RepC G 0 ds [] Rt X e Defs3.ctxTy R RCtx Rf)
    (hx : RepC G 0 ds [] xt X e treeTy R RT Xf) :
    RepC G 0 ds [] (Term.app (Term.app (Term.snd (Term.fst Ht)) Rt) xt) X e omega R Rep.prop
      fun s ↦ (Hf s).1.2 (Rf s) (Xf s) :=
  repC_app (repC_app (repC_snd (repC_fst hH objVal_relC objVal_relC) objVal_tree
    (objVal_exp objVal_ctx objVal_pred)) hR objVal_ctx objVal_pred) hx objVal_tree objVal_omega

/-- The relation of the second of two children's values, applied to a context and a value,
represents the relation's holding of them. -/
theorem repC_second {Ht Rt xt : Term} {Hf : S → RelV × RelV} {Rf : S → Ctx}
    {Xf : S → Kernel.Tree}
    (hH : RepC G 0 ds [] Ht X e (prod relC relC) R (Rep.prod RRel RRel) Hf)
    (hR : RepC G 0 ds [] Rt X e Defs3.ctxTy R RCtx Rf)
    (hx : RepC G 0 ds [] xt X e treeTy R RT Xf) :
    RepC G 0 ds [] (Term.app (Term.app (Term.snd (Term.snd Ht)) Rt) xt) X e omega R Rep.prop
      fun s ↦ (Hf s).2.2 (Rf s) (Xf s) :=
  repC_app (repC_app (repC_snd (repC_snd hH objVal_relC objVal_relC) objVal_tree
    (objVal_exp objVal_ctx objVal_pred)) hR objVal_ctx objVal_pred) hx objVal_tree objVal_omega

end Children

variable {PST : Prog × Defs × Defs3} (h : extended3 = some PST) (L : Translated PST)

include h

/-- The term of the first two children's values, at a term of the fold's argument, represents
them ({name}`firstTwo`). -/
theorem repC_firstTwo {X : PartialHorn.Tree} {e : List (PartialHorn.Tree × PartialHorn.Tree)}
    {S A : Type} {R : S → A → Prop} {t : Term} {Arg : S → ℕ × List RelV}
    (ht : RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] t X e (prod bitsTy (list relC)) R
      (Rep.prod RN (Rep.list RRel)) Arg) :
    RepC PST.1.G 0 (L.cds₀ ++ L.ext) [] (firstTwoT PST.1.o t) X e (prod relC relC) R
      (Rep.prod RRel RRel) fun s ↦ firstTwo (Arg s).2 := by
  have hC := connectives h L
  -- the value at no child, in no variables
  have cn := RepCtx.nil L.ctx
  have cn₁ := cn.extend L.ctx objVal_ctx (isTy_ctx _) RCtx
  have cn₂ := cn₁.extend L.ctx objVal_tree (isTy_tree _) RT
  have hnone := repC_pair (cn.quote L.ctx (Kernel.leaf 0))
    (repC_lam (G := PST.1.G) (n := 0) (isTy_ctx _) cn.val objVal_ctx
      (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cn₁.val objVal_tree
        (hC.ff (e := Internal.extEnv (prod one Defs3.ctxTy) treeTy
          (Internal.extEnv one Defs3.ctxTy [])) cn₂.val (Rep.prod (Rep.prod Rep.unit RCtx) RT))))
  -- the step, in a child's value and the rest's pair: the value, before the rest's first
  have ch := (RepCtx.single L.ctx objVal_relC (isTy_relC _) RRel).extend L.ctx
    (objVal_prod objVal_relC objVal_relC) (isTy_relC₂ _) (Rep.prod RRel RRel)
  exact repC_listRec (repC_snd ht objVal_bits (objVal_list objVal_relC)) (repC_pair hnone hnone)
    (repC_pair (ch.var (i := 1) rfl) (repC_fst (ch.var (i := 0) rfl) objVal_relC objVal_relC))
    objVal_relC

/-- The relation's arrow represents the relation at a type of the datatype language, in a
context, of a value ({name}`DRel`), by the values of the loaded globals. -/
theorem represents_rel {f : EvalFns} (hf : f.Loaded L.Gk PST.1.idx) {fk : PartialHorn.Tree}
    (hdk : (L.cds₀ ++ L.ext)[PST.2.2.q]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig (L.cds₀ ++ L.ext) fk) (Rep.prod RCtx RT) RPred
      fun p : Ctx × Kernel.Tree ↦ DRel f p.2 p.1 := by
  have hC := connectives h L
  have hlog := DatatypeAccepted.hasLogic h
  have hk : PST.1.G.defs[PST.2.2.q]? = some (.language (relDefn PST.1 PST.2.1)) :=
    DatatypeAccepted.defined h (List.mem_of_getElem? (i := 4) rfl)
  have hT := objVal_tree (ds := L.cds₀ ++ L.ext)
  have hR := objVal_ctx (ds := L.cds₀ ++ L.ext)
  have hc := objVal_relC (ds := L.cds₀ ++ L.ext)
  have hB := objVal_bits (ds := L.cds₀ ++ L.ext)
  have hLc := objVal_list hc
  have hL := objVal_list hT
  have hN := objVal_nat (ds := L.cds₀ ++ L.ext) (ρ := [])
  have hTT := objVal_exp hT hT
  have hRP := objVal_exp hR (objVal_pred (ds := L.cds₀ ++ L.ext))
  have hops := (ty_spec (G := PST.1.G) (n := 0) (ρ := []) (ds := L.cds₀ ++ L.ext) tT rfl).2.1
  have hvT : ObjVal [] treeTy BT := objVal_ty (T := tT) rfl
  obtain ⟨htot, hsur, hl, hr⟩ := (order_props tT).1 rfl
  have hkNil : PST.1.G.prims[0]? = some Internal.nilPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have hkCons : PST.1.G.prims[1]? = some Internal.consPrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  have hkNode : PST.1.G.prims[2]? = some Internal.lnodePrim :=
    Internal.getElem?_of_prefix L.ctx.le.1 rfl
  -- the contexts: the fold's argument, the relation's context, the value, and bound variables
  have cs₀ := RepCtx.single L.ctx (objVal_prod hB hLc) (isTy_arg _) (Rep.prod RN (Rep.list RRel))
  have cs₁ := cs₀.extend L.ctx hR (isTy_ctx _) RCtx
  have cs₂ := cs₁.extend L.ctx hT (isTy_tree _) RT
  have c₃ := cs₂.extend L.ctx hT (isTy_tree _) RT
  have c₄ := c₃.extend L.ctx hT (isTy_tree _) RT
  have c₃n := c₃.extend L.ctx hN isTy_nat Rep.nat
  -- the test of the type's label
  have lab := fun k : ℕ ↦ repC_eqB L.ctx (repC_fst (cs₂.var (i := 2) rfl) hB hLc)
    (cs₂.numeral L.ctx k)
  -- a tree's quotation
  have hq := hC.ex htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cs₂.val hT
      (repC_eq (c₃.var (i := 1) rfl) (repC_pc₁ L hf.valQuote rfl rfl c₃.val (c₃.var (i := 0) rfl))
        hT hl hr))
  -- the unit value
  have hunit := repC_eq (cs₂.var (i := 0) rfl)
    (repC_pc₀ L hf.valUnit rfl cs₂.val (Rep.prod (Rep.prod (Rep.prod RN (Rep.list RRel)) RCtx) RT))
    hT hl hr
  -- a pair of related values
  have hprod := hC.ex htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cs₂.val hT
      (hC.ex htot hsur (isTy_tree _) hops hvT
        (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c₃.val hT
          (hC.conj
            (repC_eq (c₄.var (i := 2) rfl)
              (repC_pc₂ L hf.valPair rfl rfl rfl c₄.val (c₄.var (i := 1) rfl)
                (c₄.var (i := 0) rfl)) hT hl hr)
            (hC.conj
              (repC_first (repC_firstTwo h L (c₄.var (i := 4) rfl)) (c₄.var (i := 3) rfl)
                (c₄.var (i := 1) rfl))
              (repC_second (repC_firstTwo h L (c₄.var (i := 4) rfl)) (c₄.var (i := 3) rfl)
                (c₄.var (i := 0) rfl)))))))
  -- a function: at each related argument, its application converges to a related value
  have harrow := hC.all htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cs₂.val hT
      (hC.imp
        (repC_first (repC_firstTwo h L (c₃.var (i := 3) rfl)) (c₃.var (i := 2) rfl)
          (c₃.var (i := 0) rfl))
        (repC_conv h L hf
          (repC_lam (G := PST.1.G) (n := 0) isTy_nat c₃.val hN
            (repC_app (repC_app
              (repC_snd (repC_level h L hf (repC_fst (c₃n.var (i := 3) rfl) hL hL)
                (c₃n.var (i := 0) rfl)) (objVal_exp hL hTT) (objVal_exp hT hTT))
              (c₃n.var (i := 2) rfl) hT hTT) (c₃n.var (i := 1) rfl) hT hT))
          (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) c₃.val hT
            (repC_second (repC_firstTwo h L (c₄.var (i := 4) rfl)) (c₄.var (i := 3) rfl)
              (c₄.var (i := 0) rfl))))))
  -- a list of related values
  have hlist := hC.conj
    (repC_truth L.ctx hlog cs₂.val (repC_pc₁ L hf.isSome rfl rfl cs₂.val
      (repC_pc₁ L hf.listOf rfl rfl cs₂.val (cs₂.var (i := 0) rfl))))
    (repC_allL h L
      (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cs₂.val hT
        (repC_first (repC_firstTwo h L (c₃.var (i := 3) rfl)) (c₃.var (i := 2) rfl)
          (c₃.var (i := 0) rfl)))
      (repC_children L.ctx (repC_pc₁ L hf.get rfl rfl cs₂.val
        (repC_pc₁ L hf.listOf rfl rfl cs₂.val (cs₂.var (i := 0) rfl)))))
  -- the quotation of a member of a datatype
  have hdata := hC.ex htot hsur (isTy_tree _) hops hvT
    (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cs₂.val hT
      (hC.conj
        (repC_eq (c₃.var (i := 1) rfl)
          (repC_pc₁ L hf.valQuote rfl rfl c₃.val (c₃.var (i := 0) rfl)) hT hl hr)
        (repC_truth L.ctx hlog c₃.val
          (repC_pc₃ L hf.memberOf rfl rfl rfl rfl c₃.val (repC_snd (c₃.var (i := 2) rfl) hL hL)
            (repC_lnode hkNode (isTy_bits _)
              (repC_pair (c₃.numeral L.ctx 1)
                (repC_children L.ctx
                  (repC_fst (repC_fst (repC_firstTwo h L (c₃.var (i := 3) rfl)) hc hc) hT hRP)))
              hB)
            (c₃.var (i := 0) rfl)))))
  -- the relation at the node, by the label
  have hbody :=
    repC_condB L.ctx isTy_omega rfl eval_omega (lab Kernel.Label.tyTree) hq
    (repC_condB L.ctx isTy_omega rfl eval_omega (lab Kernel.Label.tyUnit) hunit
    (repC_condB L.ctx isTy_omega rfl eval_omega (lab Kernel.Label.tyProd) hprod
    (repC_condB L.ctx isTy_omega rfl eval_omega (lab Kernel.Label.tyArrow) harrow
    (repC_condB L.ctx isTy_omega rfl eval_omega (lab Kernel.Label.tyList) hlist
    (repC_condB L.ctx isTy_omega rfl eval_omega (lab 5) hdata
    (repC_condB L.ctx isTy_omega rfl eval_omega (lab 6) hq
      (hC.ff cs₂.val (Rep.prod (Rep.prod (Rep.prod RN (Rep.list RRel)) RCtx) RT))))))))
  -- the node rebuilt from the label and the children's rebuilt trees
  have cr := (RepCtx.single L.ctx hc (isTy_relC _) RRel).extend L.ctx hL
    (by simp [isTy_list, isTy_tree]) (Rep.list RT)
  have hreb := repC_lnode hkNode (isTy_bits _)
    (repC_pair (repC_fst (cs₀.var (i := 0) rfl) hB hLc)
      (repC_listRec (repC_snd (cs₀.var (i := 0) rfl) hB hLc)
        (repC_nil hkNil (isTy_tree _) (repC_star (X := one) (e := []) objVal_one Rep.unit) hT RT)
        (repC_cons hkCons (isTy_tree _)
          (repC_pair (repC_fst (cr.var (i := 1) rfl) hT hRP) (cr.var (i := 0) rfl)) hT)
        hc))
    hB
  have hstep := repC_pair hreb
    (repC_lam (G := PST.1.G) (n := 0) (isTy_ctx _) cs₀.val hR
      (repC_lam (G := PST.1.G) (n := 0) (isTy_tree _) cs₁.val hT hbody))
  -- the fold of the type's tree, at the context
  have c₀ := (RepCtx.single L.ctx hR (isTy_ctx _) RCtx).extend L.ctx hT (isTy_tree _) RT
  exact Internal.rep_def_full (τ' := []) L.ctx.compiles hk
    (repC_app (repC_snd (repC_roseRec (isTy_relC _) (c₀.var (i := 0) rfl) hstep hB) hT hRP)
      (c₀.var (i := 1) rfl) hR objVal_pred) (fun _ ↦ rfl) hdk

end GebTests.Prototypes.FreeTopos.Certified.DatatypeRelation

end
