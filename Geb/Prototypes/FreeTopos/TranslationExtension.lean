/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.RepresentEq
public import Geb.Prototypes.FreeTopos.Internal.RepresentLift
public import Geb.Prototypes.FreeTopos.Internal.RepresentLogic
public import Geb.Prototypes.FreeTopos.TranslationSound

set_option doc.verso true in
/-!
# Terms over an extension of a kernel program's translation

A program of the internal language that extends the translation of a kernel program, by the
connectives' definitions and further ones, has terms that no kernel term translates to: a test
by the conditional between truth and falsity, an equation, a call of a library definition. Where
such a term is built from references to the translated globals by application, pairing, the
projections and the list of a tree's children, it represents the function built the same way
from the values of the globals the kernel loads: each step's representation is stated over the
translation's constants ({name}`Geb.FreeTopos.Translation.GlobRep`, the library's and the
primitives' representations) and holds over constants that extend them
({name}`Geb.FreeTopos.Internal.repC_le`, {name}`Geb.FreeTopos.Internal.unfoldTerm_append_defn`).
A test then represents the proposition that a kernel tree's label is not zero, and an equation
at a type of first order the equality of two kernel values.

## Main definitions

* {lit}`ExtCtx` — constants that extend a kernel program's translation, with a context of types.
* {lit}`RepK` — a term in the context represents a function into a kernel type's denotation.

## Main statements

* {lit}`repK_global` — a reference to a translated global represents the loaded global's value.
* {lit}`repK_app`, {lit}`repK_pair`, {lit}`repK_fst`, {lit}`repK_snd`, {lit}`repK_children`,
  {lit}`repK_prim`, {lit}`repK_quote` — the term formers represent the kernel's.
* {lit}`repC_test` — the truth of a test represents that its tree's label is not zero.
* {lit}`repC_eqK` — an equation at a type of first order represents the equality of the values.

## Tags

translation, kernel, logical relation, representation, connectives, definitional extension
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Translation

open PartialHorn (Tree)
open Internal (Term Defn Globals RepC compileDefs HasLogic)
open Sorts
open scoped Internal

/-- Constants that extend the translation of a kernel program and compile to the translation's
definitions before further ones, with a context of types of the translation and its value. -/
structure ExtCtx (defs : List Defn) (ds ext : List PartialHorn.Defn) (G' : Globals)
    (Γ : List Tree) (A : Type) : Prop where
  /-- The constants extend the translation's. -/
  le : (globals defs).Le G'
  /-- The check accepts the translation's constants. -/
  ok : (globals defs).ok (ExtEnv.ofDefs ds) = true
  /-- The translation's constants compile. -/
  compiles₀ : compileDefs (globals defs) = some ds
  /-- The constants compile to the translation's definitions before further ones. -/
  compiles : compileDefs G' = some (ds ++ ext)
  /-- The compiled definitions are well formed. -/
  wf : PartialHorn.DefnsWF sig (ds ++ ext)
  /-- The context is one of types of the translation. -/
  isTy : Γ.all (Internal.IsTy (globals defs) 0) = true
  /-- The value of the context over the translation's definitions. -/
  val₀ : ObjVal [] (unfoldTerm sig ds (Internal.ctxObj Γ)) A
  /-- The value of the context over all the definitions. -/
  val : ObjVal [] (unfoldTerm sig (ds ++ ext) (Internal.ctxObj Γ)) A

/-- A term in the standard environment of a context of types represents a function into the
denotation of a kernel type, at the type's translation and its representation. -/
def RepK (G : Globals) (cds : List PartialHorn.Defn) (Γ : List Tree) {S A : Type}
    (R : S → A → Prop) (u : Term) (T : Kernel.Tree) (F : S → Kernel.Ty.den T) : Prop :=
  ∃ a, ty T = some a ∧
    RepC G 0 cds [] u (Internal.ctxObj Γ) (Internal.stdEnv Γ) a R (KRel T) F

/-- The variable of a context of one kernel type's translation represents the identity. -/
theorem repK_var₀ {G : Globals} {cds : List PartialHorn.Defn} {C : Kernel.Tree} {c : Tree}
    (hC : ty C = some c) : RepK G cds [c] (KRel C) (v 0) C id :=
  ⟨c, hC, Internal.repC_var (Internal.envRep_std₁ (objVal_ty' hC) (KRel C)) rfl⟩

section Extended

variable {defs : List Defn} {ds ext : List PartialHorn.Defn} {G' : Globals} {Γ : List Tree}
  {S A : Type} {R : S → A → Prop} (hE : ExtCtx defs ds ext G' Γ A)
include hE

/-- The constants' base is the theory's signature. -/
theorem ExtCtx.base : G'.base = sig.length := hE.le.2.1.symm

/-- The translation's compiled definitions are well formed. -/
theorem ExtCtx.wf₀ : PartialHorn.DefnsWF sig ds := PartialHorn.defnsWF_of_append ext ds sig hE.wf

/-- A representation over the translation's constants is one over the constants that extend
them. -/
theorem repK_of_le {u : Term} {T : Kernel.Tree} {F : S → Kernel.Ty.den T}
    (h : RepK (globals defs) ds Γ R u T F) : RepK G' (ds ++ ext) Γ R u T F :=
  let ⟨a, ha, hr⟩ := h
  ⟨a, ha, Internal.repC_le (G := globals defs) hE.le
    (show (globals defs).base = sig.length from rfl) hE.ok hE.compiles₀ hE.isTy hr⟩

/-- A reference to a translated global represents the value of the global the kernel loads. -/
theorem repK_global {Gk : List Kernel.Glob} (hG : GlobRep defs ds Gk) {n : ℕ} {g : Kernel.Glob}
    (hg : Gk[n]? = some g) :
    RepK G' (ds ++ ext) Γ R (call (lib.length + n) [] []) g.1 fun _ ↦ g.2 := by
  obtain ⟨a, d, fk, hty, hk, har, hpar, hsub, hdk, hrep⟩ := hG n g hg
  refine ⟨a, hty, Internal.repC_call₀ (n := 0) (e := Internal.stdEnv Γ) (Fk := fun _ ↦ g.2)
    hE.base (Internal.getElem?_of_prefix hE.le.2.2 hk) hE.wf
    (Internal.getElem?_of_prefix (List.prefix_append ds ext) hdk) har hpar hsub hE.val ?_⟩
  rw [show unfoldTerm sig (ds ++ ext) fk = unfoldTerm sig ds fk from
    Internal.unfoldTerm_append_defn hE.wf₀ hdk]
  exact hrep

/-- A primitive's translation represents the primitive. -/
theorem repK_prim {k : ℕ} {g : Kernel.Glob} {u : Term} (hg : Kernel.prims[k]? = some g)
    (hu : primT k = some u) : RepK G' (ds ++ ext) Γ R u g.1 fun _ ↦ g.2 :=
  repK_of_le hE (repC_primT hE.compiles₀ hE.wf₀ hE.val₀ hg hu)

/-- A quoted tree's translation represents the tree. -/
theorem repK_quote (t : Kernel.Tree) :
    RepK G' (ds ++ ext) Γ R (quoteT t) Kernel.tT fun _ ↦ t :=
  repK_of_le hE ⟨treeTy, ty_tT, repC_quote hE.compiles₀ hE.wf₀ hE.val₀ t⟩

omit hE in
/-- An application represents the application of the functions its parts represent. -/
theorem repK_app {t u : Term} {B C : Kernel.Tree} {cds : List PartialHorn.Defn} {G : Globals}
    {F : S → Kernel.Ty.den B → Kernel.Ty.den C} {F' : S → Kernel.Ty.den B}
    (ht : RepK G cds Γ R t (Kernel.tArrow B C) F) (hu : RepK G cds Γ R u B F') :
    RepK G cds Γ R (Term.app t u) C fun s ↦ F s (F' s) := by
  obtain ⟨a, ha, hr⟩ := ht
  obtain ⟨b, hb, hru⟩ := hu
  rw [ty_tArrow] at ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨b', hb', c, hc, rfl⟩ := ha
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  exact ⟨c, hc, Internal.repC_app hr hru (objVal_ty' hb) (objVal_ty' hc)⟩

omit hE in
/-- A pair represents the pairing of the functions its parts represent. -/
theorem repK_pair {t u : Term} {B C : Kernel.Tree} {cds : List PartialHorn.Defn} {G : Globals}
    {F : S → Kernel.Ty.den B} {F' : S → Kernel.Ty.den C} (ht : RepK G cds Γ R t B F)
    (hu : RepK G cds Γ R u C F') :
    RepK G cds Γ R (Term.pair t u) (Kernel.tProd B C) fun s ↦ (F s, F' s) := by
  obtain ⟨b, hb, hr⟩ := ht
  obtain ⟨c, hc, hru⟩ := hu
  exact ⟨prod b c, by simp [hb, hc], Internal.repC_pair hr hru⟩

omit hE in
/-- A first projection represents the first component of the function its pair represents. -/
theorem repK_fst {t : Term} {B C : Kernel.Tree} {cds : List PartialHorn.Defn} {G : Globals}
    {F : S → Kernel.Ty.den B × Kernel.Ty.den C} (ht : RepK G cds Γ R t (Kernel.tProd B C) F) :
    RepK G cds Γ R (Term.fst t) B fun s ↦ (F s).1 := by
  obtain ⟨a, ha, hr⟩ := ht
  rw [ty_tProd] at ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨b, hb, c, hc, rfl⟩ := ha
  exact ⟨b, hb, Internal.repC_fst hr (objVal_ty' hb) (objVal_ty' hc)⟩

omit hE in
/-- A second projection represents the second component of the function its pair represents. -/
theorem repK_snd {t : Term} {B C : Kernel.Tree} {cds : List PartialHorn.Defn} {G : Globals}
    {F : S → Kernel.Ty.den B × Kernel.Ty.den C} (ht : RepK G cds Γ R t (Kernel.tProd B C) F) :
    RepK G cds Γ R (Term.snd t) C fun s ↦ (F s).2 := by
  obtain ⟨a, ha, hr⟩ := ht
  rw [ty_tProd] at ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at ha
  obtain ⟨b, hb, c, hc, rfl⟩ := ha
  exact ⟨c, hc, Internal.repC_snd hr (objVal_ty' hb) (objVal_ty' hc)⟩

/-- The library's list of a tree's children represents the list of a kernel tree's children. -/
theorem repK_children {t : Term} {F : S → Kernel.Tree}
    (ht : RepK G' (ds ++ ext) Γ R t Kernel.tT F) :
    RepK G' (ds ++ ext) Γ R (call D.children [] [t]) (Kernel.tList Kernel.tT)
      fun s ↦ (F s).children := by
  obtain ⟨a, ha, hr⟩ := ht
  obtain rfl : a = treeTy := Option.some.inj (ha.symm.trans ty_tT)
  obtain ⟨fc, hfc⟩ :=
    Internal.compiled_language hE.compiles₀ (k := D.children) (d := lib[D.children]) rfl
  have hch : Represents [] (unfoldTerm sig (ds ++ ext) fc) (Rep.rose RN)
      (Rep.list (Rep.rose RN)) RoseTree.children := by
    rw [show unfoldTerm sig (ds ++ ext) fc = unfoldTerm sig ds fc from
      Internal.unfoldTerm_append_defn hE.wf₀ hfc]
    exact represents_children (rep_children hE.compiles₀ hE.wf₀ hfc)
  have hk : G'.defs[D.children]? = some (.language lib[D.children]) :=
    Internal.getElem?_of_prefix hE.le.2.2 rfl
  exact ⟨list treeTy, rfl, Internal.repC_call₁ (τ' := []) (a := list treeTy) hE.base hk hE.wf
    (Internal.getElem?_of_prefix (List.prefix_append ds ext) hfc) rfl (by simp) (by simp) .nil
    rfl rfl hch hr⟩

/-- The truth of a test, the conditional on the label of a tree between truth and falsity,
represents the proposition that the label of the kernel tree the tree's term represents is not
zero, over constants with the connectives' definitions. -/
theorem repC_test {o : ℕ} (hlog : HasLogic G' o) {u : Term} {B : S → Kernel.Tree}
    (hu : RepK G' (ds ++ ext) Γ R u Kernel.tT B) :
    RepC G' 0 (ds ++ ext) [] (condT omega (call D.lab [] [u]) (Internal.Logic.tt o)
      (Internal.Logic.ff o)) (Internal.ctxObj Γ) (Internal.stdEnv Γ) omega R Rep.prop
      fun s ↦ (B s).label ≠ 0 := by
  obtain ⟨a, ha, hu⟩ := hu
  obtain rfl : a = treeTy := Option.some.inj (ha.symm.trans ty_tT)
  have hF₀ := hE.compiles₀
  have hF := hE.compiles
  have hwf := hE.wf
  have hwf₀ := hE.wf₀
  have hbase := hE.base
  have hX := hE.val
  obtain ⟨fc, hfc⟩ := Internal.compiled_language hF₀ (k := D.cond) (d := lib[D.cond]) rfl
  obtain ⟨fl, hfl⟩ := Internal.compiled_language hF₀ (k := D.lab) (d := lib[D.lab]) rfl
  -- the library's conditional and label, over the extended constants
  have hcond : Represents (Internal.objs [Prop]) (unfoldTerm sig (ds ++ ext) fc)
      (Rep.prod (Rep.prod RN Rep.prop) Rep.prop) Rep.prop
      fun p ↦ if p.1.1 ≠ 0 then p.1.2 else p.2 := by
    rw [show unfoldTerm sig (ds ++ ext) fc = unfoldTerm sig ds fc from
      Internal.unfoldTerm_append_defn hwf₀ hfc]
    exact represents_cond (rep_cond hF₀ hfc Rep.prop)
  have hlab : Represents [] (unfoldTerm sig (ds ++ ext) fl) (Rep.rose RN) RN RoseTree.label := by
    rw [show unfoldTerm sig (ds ++ ext) fl = unfoldTerm sig ds fl from
      Internal.unfoldTerm_append_defn hwf₀ hfl]
    exact represents_lab (rep_lab hF₀ hfl)
  have hkc : G'.defs[D.cond]? = some (.language lib[D.cond]) :=
    Internal.getElem?_of_prefix hE.le.2.2 rfl
  have hkl : G'.defs[D.lab]? = some (.language lib[D.lab]) :=
    Internal.getElem?_of_prefix hE.le.2.2 rfl
  have hdc := Internal.getElem?_of_prefix (List.prefix_append ds ext) hfc
  have hdl := Internal.getElem?_of_prefix (List.prefix_append ds ext) hfl
  -- truth and falsity
  have hk₀ : G'.defs[o]? = some (.language ⟨0, [], omega, Term.eq Term.star Term.star⟩) :=
    hlog 0 _ rfl
  have hk₃ : G'.defs[o + 3]? = some (.language ⟨1, [exp (x 0) omega], omega,
      Term.eq (Term.var 0) (Term.lam (x 0) (Internal.Logic.tt o))⟩) :=
    hlog 3 _ rfl
  have hk₄ : G'.defs[o + 4]? = some (.language ⟨0, [], omega,
      Internal.Logic.all o omega (Term.lam omega (Term.var 0))⟩) :=
    hlog 4 _ rfl
  obtain ⟨ft, hdt⟩ := Internal.compiled_language hF hk₀
  obtain ⟨fa, hda⟩ := Internal.compiled_language hF hk₃
  obtain ⟨ff', hdf⟩ := Internal.compiled_language hF hk₄
  have htt := Internal.repC_tt (n := 0) (ρ := []) (e := Internal.stdEnv Γ) hbase hk₀ hwf hdt
    (Internal.represents_tt hF hlog hdt) hX R
  have hff := Internal.repC_ff (n := 0) (ρ := []) (e := Internal.stdEnv Γ) hbase hk₄ hwf hdf
    (Internal.represents_ff hbase hF hwf hlog hdt hda hdf) hX R
  have hl := Internal.repC_call₁ (τ' := []) (a := bitsTy) hbase hkl hwf hdl rfl (by simp)
    (by simp) .nil rfl rfl hlab hu
  exact repC_congr (Internal.repC_call₃ (τ' := [Prop]) (a := omega) hbase hkc hwf hdc rfl rfl
    (by simp [show PartialHorn.OpsBelow sig.length omega = true from rfl]) (.cons eval_omega .nil)
    rfl rfl hcond hl htt hff) fun s ↦ by simp

omit hE in
/-- An equation at a kernel type of first order represents the equality of the functions its
sides represent. -/
theorem repC_eqK {t u : Term} {T : Kernel.Tree} {cds : List PartialHorn.Defn} {G : Globals}
    (hT : (order T).2 = true) {F F' : S → Kernel.Ty.den T} (ht : RepK G cds Γ R t T F)
    (hu : RepK G cds Γ R u T F') :
    RepC G 0 cds [] (Term.eq t u) (Internal.ctxObj Γ) (Internal.stdEnv Γ) omega R Rep.prop
      fun s ↦ F s = F' s := by
  obtain ⟨a, ha, hr⟩ := ht
  obtain ⟨a', ha', hru⟩ := hu
  obtain rfl : a' = a := Option.some.inj (ha'.symm.trans ha)
  obtain ⟨-, hl, hr'⟩ := (order_props T).2 hT
  exact Internal.repC_eq hr hru (objVal_ty' ha) hl hr'

end Extended

end Geb.FreeTopos.Translation

end
