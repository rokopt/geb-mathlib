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
* {lit}`RepCtx` — an environment with its object's value, its entries' representation and its
  sortedness, as the readings under binders extend it.

## Main statements

* {lit}`repC_global`, {lit}`repK_global` — a reference to a translated global represents the
  loaded global's value.
* {lit}`repK_app`, {lit}`repK_pair`, {lit}`repK_fst`, {lit}`repK_snd`, {lit}`repK_children`,
  {lit}`repK_prim`, {lit}`repK_quote` — the term formers represent the kernel's.
* {lit}`repC_truth`, {lit}`repC_test` — the truth of a test represents that its tree's label
  is not zero.
* {lit}`repC_eqK` — an equation at a type of first order represents the equality of the values.
* {lit}`repC_condB`, {lit}`repC_eqB` — the library's conditional and test of equality of
  bitstrings represent the kernel's on labels.
* {lit}`RepCtx.lift`, {lit}`RepCtx.prim`, {lit}`RepCtx.numeral`, {lit}`RepCtx.quote` — the
  translation's constants in a represented context.

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

/-- A reference to a translated global, in any environment over an object with a value,
represents the value of the global the kernel loads, at the translation of the global's
type. -/
theorem repC_global {Gk : List Kernel.Glob} (hG : GlobRep defs ds Gk) {n : ℕ} {g : Kernel.Glob}
    (hg : Gk[n]? = some g) {X : Tree} {e : List (Tree × Tree)} {S' A' : Type}
    (hX : ObjVal [] (unfoldTerm sig (ds ++ ext) X) A') (R' : S' → A' → Prop) :
    ∃ a, ty g.1 = some a ∧
      RepC G' 0 (ds ++ ext) [] (call (lib.length + n) [] []) X e a R' (KRel g.1) fun _ ↦ g.2 := by
  obtain ⟨a, d, fk, hty, hk, har, hpar, hsub, hdk, hrep⟩ := hG n g hg
  refine ⟨a, hty, Internal.repC_call₀ (n := 0) (e := e) (Fk := fun _ ↦ g.2)
    hE.base (Internal.getElem?_of_prefix hE.le.2.2 hk) hE.wf
    (Internal.getElem?_of_prefix (List.prefix_append ds ext) hdk) har hpar hsub hX ?_⟩
  rw [show unfoldTerm sig (ds ++ ext) fk = unfoldTerm sig ds fk from
    Internal.unfoldTerm_append_defn hE.wf₀ hdk]
  exact hrep

/-- A reference to a translated global represents the value of the global the kernel loads. -/
theorem repK_global {Gk : List Kernel.Glob} (hG : GlobRep defs ds Gk) {n : ℕ} {g : Kernel.Glob}
    (hg : Gk[n]? = some g) :
    RepK G' (ds ++ ext) Γ R (call (lib.length + n) [] []) g.1 fun _ ↦ g.2 :=
  repC_global hE hG hg hE.val R

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

/-- The library's list of a tree's children, in any environment, represents the list of a
kernel tree's children. -/
theorem repC_children {t : Term} {X : Tree} {e : List (Tree × Tree)} {S' A' : Type}
    {R' : S' → A' → Prop} {F : S' → Kernel.Tree}
    (hr : RepC G' 0 (ds ++ ext) [] t X e treeTy R' (Rep.rose RN) F) :
    RepC G' 0 (ds ++ ext) [] (call D.children [] [t]) X e (list treeTy) R'
      (Rep.list (Rep.rose RN)) fun s ↦ (F s).children := by
  obtain ⟨fc, hfc⟩ :=
    Internal.compiled_language hE.compiles₀ (k := D.children) (d := lib[D.children]) rfl
  have hch : Represents [] (unfoldTerm sig (ds ++ ext) fc) (Rep.rose RN)
      (Rep.list (Rep.rose RN)) RoseTree.children := by
    rw [show unfoldTerm sig (ds ++ ext) fc = unfoldTerm sig ds fc from
      Internal.unfoldTerm_append_defn hE.wf₀ hfc]
    exact represents_children (rep_children hE.compiles₀ hE.wf₀ hfc)
  have hk : G'.defs[D.children]? = some (.language lib[D.children]) :=
    Internal.getElem?_of_prefix hE.le.2.2 rfl
  exact Internal.repC_call₁ (τ' := []) (a := list treeTy) hE.base hk hE.wf
    (Internal.getElem?_of_prefix (List.prefix_append ds ext) hfc) rfl (by simp) (by simp) .nil
    rfl rfl hch hr

/-- The library's list of a tree's children represents the list of a kernel tree's children. -/
theorem repK_children {t : Term} {F : S → Kernel.Tree}
    (ht : RepK G' (ds ++ ext) Γ R t Kernel.tT F) :
    RepK G' (ds ++ ext) Γ R (call D.children [] [t]) (Kernel.tList Kernel.tT)
      fun s ↦ (F s).children := by
  obtain ⟨a, ha, hr⟩ := ht
  obtain rfl : a = treeTy := Option.some.inj (ha.symm.trans ty_tT)
  exact ⟨list treeTy, rfl, repC_children hE hr⟩

/-- The truth of a test in any environment over an object with a value, the conditional on the
label of a tree between truth and falsity, represents the proposition that the label of the
kernel tree the tree's term represents is not zero, over constants with the connectives'
definitions. -/
theorem repC_truth {o : ℕ} (hlog : HasLogic G' o) {u : Term} {X : Tree}
    {e : List (Tree × Tree)} {S' A' : Type} {R : S' → A' → Prop}
    (hX : ObjVal [] (unfoldTerm sig (ds ++ ext) X) A') {B : S' → Kernel.Tree}
    (hu : RepC G' 0 (ds ++ ext) [] u X e treeTy R (Rep.rose RN) B) :
    RepC G' 0 (ds ++ ext) [] (condT omega (call D.lab [] [u]) (Internal.Logic.tt o)
      (Internal.Logic.ff o)) X e omega R Rep.prop fun s ↦ (B s).label ≠ 0 := by
  have hF₀ := hE.compiles₀
  have hF := hE.compiles
  have hwf := hE.wf
  have hwf₀ := hE.wf₀
  have hbase := hE.base
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
  have htt := Internal.repC_tt (n := 0) (ρ := []) (e := e) hbase hk₀ hwf hdt
    (Internal.represents_tt hF hlog hdt) hX R
  have hff := Internal.repC_ff (n := 0) (ρ := []) (e := e) hbase hk₄ hwf hdf
    (Internal.represents_ff hbase hF hwf hlog hdt hda hdf) hX R
  have hl := Internal.repC_call₁ (τ' := []) (a := bitsTy) hbase hkl hwf hdl rfl (by simp)
    (by simp) .nil rfl rfl hlab hu
  exact repC_congr (Internal.repC_call₃ (τ' := [Prop]) (a := omega) hbase hkc hwf hdc rfl rfl
    (by simp [show PartialHorn.OpsBelow sig.length omega = true from rfl]) (.cons eval_omega .nil)
    rfl rfl hcond hl htt hff) fun s ↦ by simp

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
  exact repC_truth hE hlog hE.val hu

/-- The conditional on a bitstring, in any environment, represents the choice of the first
branch at a label other than zero and of the second at zero, at any representation of the
branches' type, a type of the theory's signature. -/
theorem repC_condB {a : Tree} {X : Tree} {e : List (Tree × Tree)} {S' A' T B : Type}
    {R' : S' → A' → Prop} {Ra : T → B → Prop} (hta : Internal.IsTy G' 0 a = true)
    (hops : PartialHorn.OpsBelow sig.length a = true) (hva : ObjVal [] a B) {c t u : Term}
    {C : S' → ℕ} {Ft Fu : S' → T} (hc : RepC G' 0 (ds ++ ext) [] c X e bitsTy R' RN C)
    (ht : RepC G' 0 (ds ++ ext) [] t X e a R' Ra Ft)
    (hu : RepC G' 0 (ds ++ ext) [] u X e a R' Ra Fu) :
    RepC G' 0 (ds ++ ext) [] (condT a c t u) X e a R' Ra
      fun s ↦ if C s ≠ 0 then Ft s else Fu s := by
  obtain ⟨fc, hfc⟩ :=
    Internal.compiled_language hE.compiles₀ (k := D.cond) (d := lib[D.cond]) rfl
  have hcond : Represents (Internal.objs [B]) (unfoldTerm sig (ds ++ ext) fc)
      (Rep.prod (Rep.prod RN Ra) Ra) Ra fun p ↦ if p.1.1 ≠ 0 then p.1.2 else p.2 := by
    rw [show unfoldTerm sig (ds ++ ext) fc = unfoldTerm sig ds fc from
      Internal.unfoldTerm_append_defn hE.wf₀ hfc]
    exact represents_cond (rep_cond hE.compiles₀ hfc Ra)
  have hkc : G'.defs[D.cond]? = some (.language lib[D.cond]) :=
    Internal.getElem?_of_prefix hE.le.2.2 rfl
  exact Internal.repC_call₃ (τ' := [B]) (a := a) hE.base hkc hE.wf
    (Internal.getElem?_of_prefix (List.prefix_append ds ext) hfc) rfl (by simp [hta])
    (by simp [hops]) (.cons hva .nil) rfl rfl hcond hc ht hu

/-- The library's test of the equality of two bitstrings, in any environment, represents the
test of the equality of two labels. -/
theorem repC_eqB {X : Tree} {e : List (Tree × Tree)} {S' A' : Type} {R' : S' → A' → Prop}
    {m k : Term} {M K : S' → ℕ} (hm : RepC G' 0 (ds ++ ext) [] m X e bitsTy R' RN M)
    (hk : RepC G' 0 (ds ++ ext) [] k X e bitsTy R' RN K) :
    RepC G' 0 (ds ++ ext) [] (call D.eqB [] [m, k]) X e bitsTy R' RN
      fun s ↦ if M s = K s then 1 else 0 := by
  obtain ⟨fq, hfq⟩ := Internal.compiled_language hE.compiles₀ (k := D.eqB) (d := lib[D.eqB]) rfl
  have hq : Represents [] (unfoldTerm sig (ds ++ ext) fq) (Rep.prod RN RN) RN
      fun p : ℕ × ℕ ↦ if p.1 = p.2 then 1 else 0 := by
    rw [show unfoldTerm sig (ds ++ ext) fq = unfoldTerm sig ds fq from
      Internal.unfoldTerm_append_defn hE.wf₀ hfq]
    exact represents_bin (op := fun m n ↦ if m = n then 1 else 0)
      (rep_eqB hE.compiles₀ hE.wf₀ hfq)
  have hkq : G'.defs[D.eqB]? = some (.language lib[D.eqB]) :=
    Internal.getElem?_of_prefix hE.le.2.2 rfl
  exact Internal.repC_call₂ (τ' := []) (a := bitsTy) hE.base hkq hE.wf
    (Internal.getElem?_of_prefix (List.prefix_append ds ext) hfq) rfl (by simp) (by simp) .nil
    rfl rfl hq hm hk

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

/-- A represented context over an extension of a translation: an object and an environment
over it, with the object's value, the representation of the environment's entries, and the
environment's sortedness over the translation's constants. -/
structure RepCtx (defs : List Defn) (ds ext : List PartialHorn.Defn) (X : Tree)
    (e : List (Tree × Tree)) {S A : Type} (R : S → A → Prop)
    (ents : List (Internal.RepEntry S)) : Prop where
  /-- The object's value. -/
  val : ObjVal [] (unfoldTerm sig (ds ++ ext) X) A
  /-- The environment's entries represent functions of the context's values. -/
  rep : Internal.EnvRep (ds ++ ext) [] e R ents
  /-- The environment is sorted over the translation's constants. -/
  sorted : Internal.EnvSorted (globals defs) ds 0 X e

namespace RepCtx

variable {defs : List Defn} {ds ext : List PartialHorn.Defn} {G' : Globals} {Γ : List Tree}
  {A₀ : Type} (hE : ExtCtx defs ds ext G' Γ A₀) {X : Tree} {e : List (Tree × Tree)}
  {S A : Type} {R : S → A → Prop} {ents : List (Internal.RepEntry S)}

include hE in
/-- The empty context is represented at the terminal object. -/
theorem nil : RepCtx defs ds ext one [] Rep.unit [] :=
  ⟨Internal.objVal_one, .nil,
    Internal.EnvSorted.std (Γ := []) (show (globals defs).base = sig.length from rfl)
      hE.compiles₀ rfl⟩

include hE in
/-- The context of one variable of a type is represented at the type. -/
theorem single {p : Tree} (hp : ObjVal [] (unfoldTerm sig (ds ++ ext) p) A)
    (htp : Internal.IsTy (globals defs) 0 p = true) (R : S → A → Prop) :
    RepCtx defs ds ext p (Internal.stdEnv [p]) R [⟨p, S, A, R, id⟩] :=
  ⟨hp, Internal.envRep_std₁ hp R,
    Internal.EnvSorted.std (Γ := [p]) (show (globals defs).base = sig.length from rfl)
      hE.compiles₀ (by simp [htp])⟩

include hE in
/-- A context extended by a variable of a type is represented at the product with the type. -/
theorem extend (c : RepCtx defs ds ext X e R ents) {a : Tree} {S' A' : Type}
    (ha : ObjVal [] (unfoldTerm sig (ds ++ ext) a) A')
    (hta : Internal.IsTy (globals defs) 0 a = true) (Ra : S' → A' → Prop) :
    RepCtx defs ds ext (prod X a) (Internal.extEnv X a e) (Rep.prod R Ra)
      (⟨a, S', A', Ra, Prod.snd⟩ ::
        ents.map fun x ↦ ⟨x.ty, x.T, x.B, x.rel, x.get ∘ Prod.fst⟩) :=
  ⟨Internal.objVal_prod c.val ha, Internal.envRep_ext c.val ha c.rep Ra,
    c.sorted.extend (show (globals defs).base = sig.length from rfl) hE.compiles₀ hta⟩

/-- The value of a represented context's object over the translation's definitions. -/
theorem val₀ (c : RepCtx defs ds ext X e R ents) : ObjVal [] (unfoldTerm sig ds X) A :=
  c.sorted.unfold (ext := ext) ▸ c.val

/-- A variable of a represented context represents its entry's function. -/
theorem var (c : RepCtx defs ds ext X e R ents) {G : Globals} {i : ℕ} {a : Tree} {T B : Type}
    {R' : T → B → Prop} {F : S → T} (hx : ents[i]? = some ⟨a, T, B, R', F⟩) :
    RepC G 0 (ds ++ ext) [] (Term.var i) X e a R R' F :=
  Internal.repC_var c.rep hx

include hE in
/-- A representation over the translation's constants, in a represented context, is one over
the constants that extend them. -/
theorem lift (c : RepCtx defs ds ext X e R ents) {t : Term} {a : Tree} {T B : Type}
    {R' : T → B → Prop} {F : S → T} (h : RepC (globals defs) 0 ds [] t X e a R R' F) :
    RepC G' 0 (ds ++ ext) [] t X e a R R' F :=
  Internal.repC_lift (show (globals defs).base = sig.length from rfl) hE.compiles₀ hE.le hE.ok
    c.sorted h

include hE in
/-- A primitive's translation, in a represented context, represents the primitive, at its
type's translation. -/
theorem prim (c : RepCtx defs ds ext X e R ents) {k : ℕ} {g : Kernel.Glob} {u : Term}
    (hg : Kernel.prims[k]? = some g) (hu : primT k = some u) :
    ∃ a, ty g.1 = some a ∧
      RepC G' 0 (ds ++ ext) [] u X e a R (KRel g.1) fun _ ↦ g.2 :=
  let ⟨a, ha, hr⟩ := repC_primT hE.compiles₀ hE.wf₀ c.val₀ (R := R) (e := e) hg hu
  ⟨a, ha, c.lift hE hr⟩

include hE in
/-- The numeral of a natural number, in a represented context, represents it. -/
theorem numeral (c : RepCtx defs ds ext X e R ents) (n : ℕ) :
    RepC G' 0 (ds ++ ext) [] (numeral n) X e bitsTy R RN fun _ ↦ n :=
  c.lift hE (repC_numeral hE.compiles₀ hE.wf₀ c.val₀ n)

include hE in
/-- A quoted tree's translation, in a represented context, represents the tree. -/
theorem quote (c : RepCtx defs ds ext X e R ents) (t : Kernel.Tree) :
    RepC G' 0 (ds ++ ext) [] (quoteT t) X e treeTy R (Rep.rose RN) fun _ ↦ t :=
  c.lift hE (repC_quote hE.compiles₀ hE.wf₀ c.val₀ t)

end RepCtx

end Geb.FreeTopos.Translation

end
