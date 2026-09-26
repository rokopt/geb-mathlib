/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Proofs
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of the internal language's developments

A development's declarations are checked in order, each with the constants and the entries before
it ({name}`Geb.FreeTopos.Internal.checkDev`), so that the constants grow along it: a definition of
the language or a primitive arrow joins them once it is confirmed. The soundness of the check is an
invariant of it ({lit}`DevInv`), relative to the constants it ends with and a model of the theory
extended by their compilations: the constants so far are among the final ones and well formed,
their definitions compile, their primitive arrows are arrows of the signature, and every entry is
valid; and, at every assignment of objects to their object parameters, their primitive arrows are
arrows between their types ({lit}`Prim.Val`), their definitions of the language arrows of their
types with their compiled bodies' values and their object definitions objects ({lit}`DefsVal`,
{lit}`DefnsVal`). Stated at assignments of objects rather than at types, these persist as the
constants, and with them the types, grow; at types they follow by substitution
({lit}`primsHom_of_val`, {lit}`defsHom_of_val`, {lit}`defnsOk_of_val`).

A theorem valid with fewer constants is valid with more ({lit}`Thm.Valid.mono`), since its formulas
compile to the same arrows ({name}`Geb.FreeTopos.Internal.compile_mono`), so every entry stays
valid as the constants grow. The definitions so far compile to an initial segment of the final
definitions ({name}`Geb.FreeTopos.Internal.compileDefs_prefix`), so that a certificate checked in
the theory they extend, and a primitive arrow the inference confirms there, are sound in every
model of the final extension ({name}`Geb.PartialHorn.check_sound`,
{name}`Geb.FreeTopos.infers_sound`). A primitive arrow whose sequent a certificate proves is an
arrow between its types ({lit}`Prim.val_of_seq`), since the composite of an arrow with identities
is defined only where their objects are its domain and codomain; its certificate may cite the
theorems before it, whose validity uses only the primitive arrows before them.

In every model of the theory extended by the combinators' definitions and those the language's
definitions compile to, every entry of a development that checks is valid
({lit}`valid_of_checkDev`). With every definition unfolded, the equation of a theorem without
hypotheses holds in every model of the theory itself ({lit}`valid_unfoldAll_of_checkDev`), as does
the truth of its formula ({lit}`valid_unfoldAll_holds_of_checkDev`).

## Main definitions

* {lit}`Prim.Val`, {lit}`DefsVal`, {lit}`DefnsVal` — the constants' arrows and objects at every
  assignment of objects.
* {lit}`DevInv` — the invariant of a development's check.

## Main statements

* {lit}`Thm.Valid.mono` — a valid theorem stays valid with more constants.
* {lit}`Prim.val_of_seq` — a primitive arrow whose sequent is valid is an arrow between its types.
* {lit}`DevInv.step` — each declaration's check keeps the invariant.
* {lit}`valid_of_checkDev`, {lit}`valid_unfoldAll_of_checkDev`,
  {lit}`valid_unfoldAll_holds_of_checkDev` — the entries of a development that checks are valid,
  in the extension and in the theory.

## Tags

internal language, development, soundness, definitional extension, certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

section Lift

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}
  (hM : IsModel (ext defs) M)
include hM

/-- A theorem valid with fewer constants is valid with more, when their primitive arrows and
definitions are arrows: its formulas compile to the same arrows. -/
theorem Thm.Valid.mono {G G' : Globals} (hG : G.WF) (hle : G.Le G') {a : Thm}
    (hps : ∀ ρ : List M.Val, ρ.map Sigma.fst = List.replicate a.arity obj →
      PrimsHom M ρ G' a.arity)
    (hds : ∀ ρ : List M.Val, ρ.map Sigma.fst = List.replicate a.arity obj →
      DefsHom M ρ G' a.arity)
    (ha : a.Valid M G) : a.Valid M G' := by
  obtain ⟨hctx, hhyps, hconcl, hv⟩ := ha
  have htype : ∀ {φ : Term}, typeIn G a.arity a.ctx φ = some omega →
      typeIn G' a.arity a.ctx φ = some omega := fun h ↦ by
    obtain ⟨r, hr, hro⟩ := Option.map_eq_some_iff.mp h
    exact Option.map_eq_some_iff.mpr ⟨r, compile_mono hle _ _ _ _ hr, hro⟩
  refine ⟨all_isTy_mono hle hctx, fun h hh ↦ htype (hhyps h hh), htype hconcl,
    fun ρ hρ ↦ ⟨hps ρ hρ, hds ρ hρ, ?_⟩⟩
  obtain ⟨hpsG, hdsG, hfm⟩ := hv ρ hρ
  -- an environment of the context's types is one with fewer constants
  have henv : ∀ (X : Tree) (e : List (Tree × Tree)), EnvHom M ρ G' a.arity X e →
      e.map Prod.snd = a.ctx → EnvHom M ρ G a.arity X e := fun X e he hΓ ↦
    ⟨he.1, fun p hp ↦ ⟨(he.2 p hp).1,
      List.all_eq_true.mp hctx _ (hΓ ▸ List.mem_map_of_mem hp)⟩⟩
  -- a formula of the context compiles with fewer constants to its arrow with more
  have hcomp : ∀ {φ : Term}, typeIn G a.arity a.ctx φ = some omega →
      ∀ (X : Tree) (e : List (Tree × Tree)), EnvHom M ρ G a.arity X e →
        e.map Prod.snd = a.ctx → ∀ r, compile G' a.arity φ X e = some r →
          compile G a.arity φ X e = some r := fun h X e he hΓ r hr ↦ by
    obtain ⟨r₀, hr₀, -⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨r', hr', -⟩ := compile_of_stdEnv hM hG hρ hpsG hdsG hr₀ he hΓ
    rw [hr', Option.some_inj.mp ((compile_mono hle _ _ _ _ hr').symm.trans hr)]
  intro X e he hΓ hH r hr
  have he' := henv X e he hΓ
  refine hfm X e he' hΓ (fun ψ hψ ↦ ?_) r (hcomp hconcl X e he' hΓ r hr)
  obtain ⟨r', hr', hh⟩ := hH ψ hψ
  exact ⟨r', hcomp (hhyps ψ hψ) X e he' hΓ r' hr', hh⟩

/-- An entry valid with fewer constants is valid with more, when their primitive arrows and
definitions are arrows. -/
theorem Entry.Valid.mono {G G' : Globals} (hG : G.WF) (hle : G.Le G')
    (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
      PrimsHom M ρ G' m)
    (hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
      DefsHom M ρ G' m)
    {e : Entry} (he : e.Valid M G) : e.Valid M G' := by
  cases e with
  | language a => exact Thm.Valid.mono hM hG hle (hps _) (hds _) he
  | combinators s => exact he

omit hM in
/-- An arrow between objects at the values of terms, carried to them: a term of the arrow's value
at the terms' values is an arrow between the substitution instances. -/
theorem Hom.subst_of_vals {ρ ws : List M.Val} {θ : List Tree}
    (hθ : θ.map (eval M ρ) = ws.map Part.some) {f f' X Y : Tree}
    (hX : PartialHorn.Scoped θ.length X = true) (hY : PartialHorn.Scoped θ.length Y = true)
    (hf : eval M ρ f' = eval M ws f) (h : Hom M ws f X Y) :
    Hom M ρ f' (PartialHorn.subst θ X) (PartialHorn.subst θ Y) := by
  obtain ⟨w, hw, hs, ⟨x, hx, hxs⟩, ⟨y, hy, hys⟩, hd, hc⟩ := h
  have hX' := (PartialHorn.eval_subst hθ X hX).trans hx
  have hY' := (PartialHorn.eval_subst hθ Y hY).trans hy
  exact ⟨w, hf.trans hw, hs, ⟨x, hX', hxs⟩, ⟨y, hY', hys⟩,
    (eval_op₁_of_eq hf).trans (hd.trans (hx.trans hX'.symm)),
    (eval_op₁_of_eq hf).trans (hc.trans (hy.trans hY'.symm))⟩

omit hM in
/-- The variables of an assignment's length have its values. -/
theorem map_eval_vars (ws : List M.Val) :
    ((List.range ws.length).map PartialHorn.var).map (eval M ws) = ws.map Part.some :=
  (PartialHorn.mapM_part_eq_some_iff _ _).mp (PartialHorn.mapM_vars ws)

omit hM in
/-- The variables of a number of object parameters are types in them. -/
theorem all_isTy_vars (G : Globals) (m : ℕ) :
    ((List.range m).map PartialHorn.var).all (IsTy G m) = true := by
  rw [List.all_map, List.all_eq_true]
  intro i hi
  simp [PartialHorn.var, isTy_var_node, List.mem_range.mp hi]

variable (M) in
/-- A primitive arrow is an arrow between its types at every assignment of objects to its object
parameters. -/
def Prim.Val (p : Prim) : Prop :=
  ∀ ws : List M.Val, ws.map Sigma.fst = List.replicate p.arity obj → Hom M ws p.arrow p.dom p.cod

variable (M) in
/-- Each definition of the language's operation is, at every assignment of objects to its object
parameters, an arrow from the product of its parameters' types to its value's type, and each
object definition's operation takes objects to an object. -/
def DefsVal (G : Globals) : Prop :=
  (∀ (k : ℕ) (d : Defn), G.defs[k]? = some (.language d) →
    ∀ ws : List M.Val, ws.map Sigma.fst = List.replicate d.arity obj →
      Hom M ws (PartialHorn.opVars (G.base + k) d.arity) (ctxObj d.params) d.type) ∧
  ObjsHom M G

variable (M) in
/-- Each definition of the language's body compiles in its parameters' environment to its
value's type and an arrow with, at every assignment of objects to its object parameters, the
value of the definition's operation. -/
def DefnsVal (G : Globals) : Prop :=
  ∀ (k : ℕ) (d : Defn), G.defs[k]? = some (.language d) →
    ∃ F, compile G d.arity d.body (ctxObj d.params) (stdEnv d.params) = some (F, d.type) ∧
      ∀ ws : List M.Val, ws.map Sigma.fst = List.replicate d.arity obj →
        eval M ws (PartialHorn.opVars (G.base + k) d.arity) = eval M ws F

/-- A primitive arrow that is an arrow at every assignment of objects is an arrow at types. -/
theorem Prim.hom_of_val {G : Globals} (hO : ObjsHom M G) {p : Prim} (hv : p.Val M)
    (har : PartialHorn.Scoped p.arity p.arrow = true) (hdt : IsTy G p.arity p.dom = true)
    (hct : IsTy G p.arity p.cod = true) {m : ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = List.replicate m obj) {θ : List Tree} (hl : θ.length = p.arity)
    (hθ : θ.all (IsTy G m) = true) :
    Hom M ρ (PartialHorn.subst θ p.arrow) (PartialHorn.subst θ p.dom)
      (PartialHorn.subst θ p.cod) := by
  obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hO hρ θ hθ
  rw [hl] at hws
  exact Hom.subst_of_vals hθw (hl ▸ scoped_of_isTy _ hdt) (hl ▸ scoped_of_isTy _ hct)
    (PartialHorn.eval_subst hθw _ (hl ▸ har)) (hv ws hws)

/-- The primitive arrows of well-formed constants, each an arrow at every assignment of objects,
are arrows at types. -/
theorem primsHom_of_val {G : Globals} (hG : G.WF) (hO : ObjsHom M G)
    (hv : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p → p.Val M) {m : ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = List.replicate m obj) : PrimsHom M ρ G m := fun k p hp _ hl hθ ↦
  have hwf := hG.prims k p hp
  Prim.hom_of_val hM hO (hv k p hp) hwf.1 hwf.2.1 hwf.2.2 hρ hl hθ

/-- The definitions of well-formed constants, each of the language an arrow at every assignment
of objects, are arrows at types. -/
theorem defsHom_of_val {G : Globals} (hG : G.WF) (hv : DefsVal M G) {m : ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = List.replicate m obj) : DefsHom M ρ G m := by
  refine ⟨fun k d hd θ hl hθ ↦ ?_, hv.2⟩
  obtain ⟨hpt, htt⟩ := hG.defs k d hd
  obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hv.2 hρ θ hθ
  rw [hl] at hws
  have hlen : ws.length = d.arity := by simpa using congrArg List.length hws
  rw [← subst_ctxObj]
  refine Hom.subst_of_vals hθw (hl ▸ scoped_of_isTy _ (isTy_ctxObj _ hpt))
    (hl ▸ scoped_of_isTy _ htt) ?_ (hv.1 k d hd ws hws)
  rw [eval_op_of_values hθw, ← hlen, eval_opVars]

/-- The definitions of well-formed constants, each of the language with its body's value at
every assignment of objects, have their bodies' values at types. -/
theorem defnsOk_of_val {G : Globals} (hdv : DefsVal M G) (hv : DefnsVal M G) :
    DefnsOk M G := by
  intro k d hd
  obtain ⟨F, hF, hFv⟩ := hv k d hd
  refine ⟨F, hF, fun m ρ θ hρ hl hθ ↦ ?_⟩
  obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hdv.2 hρ θ hθ
  rw [hl] at hws
  have hlen : ws.length = d.arity := by simpa using congrArg List.length hws
  obtain ⟨v, hv', -⟩ := hdv.1 k d hd ws hws
  have hFw : eval M ws F = Part.some v := (hFv ws hws).symm.trans hv'
  have hsc : PartialHorn.Scoped θ.length F = true := by
    have := scoped_of_eval F hFw
    rwa [hlen, ← hl] at this
  rw [PartialHorn.eval_subst hθw F hsc, ← hFv ws hws, eval_op_of_values hθw, ← hlen,
    eval_opVars]

omit hM in
/-- The definitions of the language of constants whose definitions are arrows at types are
arrows at every assignment of objects. -/
theorem defsVal_of_defsHom {G : Globals} (hG : G.WF)
    (hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
      DefsHom M ρ G m) : DefsVal M G := by
  refine ⟨fun k d hd ws hws ↦ ?_, (hds 0 [] rfl).2⟩
  obtain ⟨hpt, htt⟩ := hG.defs k d hd
  have hlen : ws.length = d.arity := by simpa using congrArg List.length hws
  have hvars := map_eval_vars ws
  rw [hlen] at hvars
  have h := (hds d.arity ws hws).1 k d hd _ (by simp) (all_isTy_vars G d.arity)
  rw [← subst_ctxObj] at h
  exact h.congr rfl
    (PartialHorn.eval_subst hvars _ (by simpa using scoped_of_isTy _ (isTy_ctxObj _ hpt))).symm
    (PartialHorn.eval_subst hvars _ (by simpa using scoped_of_isTy _ htt)).symm

omit hM in
/-- A primitive arrow whose sequent is valid, between types in its object parameters, is an
arrow between its types at every assignment of objects: its composite with the identities of its
domain and of its codomain is defined only where they are its domain and codomain. -/
theorem Prim.val_of_seq (hM : IsModel (ext defs) M) {G : Globals} (hO : ObjsHom M G) {p : Prim}
    (hs : p.seq.Valid M) (hdt : IsTy G p.arity p.dom = true)
    (hct : IsTy G p.arity p.cod = true) : p.Val M := by
  intro ws hws
  obtain ⟨d, hd, hds⟩ := isObj_of_isTy hM hO hws _ hdt
  obtain ⟨c, hc, hcs⟩ := isObj_of_isTy hM hO hws _ hct
  -- the sequent at the objects
  obtain ⟨w, h₁, h₂⟩ := hs ws hws fun _ h ↦ by simp [Prim.seq] at h
  simp only [Prim.seq] at h₁ h₂
  have hw : w.1 = arr := sort_of_eval_op rfl h₁
  obtain ⟨vi, hvi⟩ := exists_eval_of_eval_op h₁ (idt p.cod) (by simp)
  obtain ⟨vg, hvg⟩ := exists_eval_of_eval_op h₁ (comp p.arrow (idt p.dom)) (by simp)
  obtain ⟨vd, hvd⟩ := exists_eval_of_eval_op hvg (idt p.dom) (by simp)
  have hts₁ : [idt p.cod, comp p.arrow (idt p.dom)].map (eval M ws) = [vi, vg].map Part.some := by
    simp [hvi, hvg]
  have hs₁ : [vi, vg].map Sigma.fst = [arr, arr] := by
    simp [sort_of_eval_op rfl hvi, sort_of_eval_op rfl hvg]
  have hts₂ : [p.arrow, idt p.dom].map (eval M ws) = [w, vd].map Part.some := by simp [h₂, hvd]
  have hs₂ : [w, vd].map Sigma.fst = [arr, arr] := by simp [hw, sort_of_eval_op rfl hvd]
  have hD : [p.dom].map (eval M ws) = [d].map Part.some := by simp [hd]
  have hC : [p.cod].map (eval M ws) = [c].map Part.some := by simp [hc]
  -- the codomain of the composite with the domain's identity is the codomain's identity's domain
  have hcg := eval_eq_of_holds (ax_holds hM 3 rfl (by decide) hts₁ hs₁
    (hs' := [⟨comp (idt p.cod) (comp p.arrow (idt p.dom)),
      comp (idt p.cod) (comp p.arrow (idt p.dom))⟩]) rfl ⟨w, h₁, h₁⟩
    (q := ⟨FreeTopos.cod (comp p.arrow (idt p.dom)), FreeTopos.dom (idt p.cod)⟩) rfl)
  have hcf := eval_eq_of_holds (ax_holds hM 6 rfl (by decide) hts₂ hs₂
    (hs' := [⟨comp p.arrow (idt p.dom), comp p.arrow (idt p.dom)⟩]) rfl ⟨vg, hvg, hvg⟩
    (q := ⟨FreeTopos.cod (comp p.arrow (idt p.dom)), FreeTopos.cod p.arrow⟩) rfl)
  have hdf := eval_eq_of_holds (ax_holds hM 3 rfl (by decide) hts₂ hs₂
    (hs' := [⟨comp p.arrow (idt p.dom), comp p.arrow (idt p.dom)⟩]) rfl ⟨vg, hvg, hvg⟩
    (q := ⟨FreeTopos.cod (idt p.dom), FreeTopos.dom p.arrow⟩) rfl)
  have hdi := eval_eq_of_holds (ax_holds hM 8 rfl (by decide) hC (by simp [hcs]) rfl trivial
    (q := ⟨FreeTopos.dom (idt p.cod), p.cod⟩) rfl)
  have hci := eval_eq_of_holds (ax_holds hM 9 rfl (by decide) hD (by simp [hds]) rfl trivial
    (q := ⟨FreeTopos.cod (idt p.dom), p.dom⟩) rfl)
  exact ⟨w, h₂, hw, ⟨d, hd, hds⟩, ⟨c, hc, hcs⟩, hdf.symm.trans (hci.trans rfl),
    hcf.symm.trans (hcg.trans hdi)⟩

omit hM in
/-- A primitive arrow the check accepts, with definitions of the combinators that begin those of
the model's theory, is an arrow between its types at every assignment of objects. -/
theorem Prim.val_of_ok (hM : IsModel (ext defs) M) {G : Globals} (hO : ObjsHom M G)
    {cds' : List PartialHorn.Defn} (hpre : cds' <+: defs) {p : Prim}
    (hpo : p.ok G (ExtEnv.ofDefs cds') = true) : p.Val M := by
  intro ws hws
  unfold Prim.ok at hpo
  simp only [Prim.wf, Bool.and_eq_true] at hpo
  obtain ⟨⟨⟨⟨-, hdt⟩, hct⟩, -⟩, hinf⟩ := hpo
  split at hinf
  · rename_i a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hinf
    obtain ⟨⟨hs, hlo⟩, hhi⟩ := hinf
    obtain ⟨w, hw, hwsrt, -, harr⟩ := (infers_sound ((ExtEnv.wf_ofDefs cds').sound hpre hM) hws
      (H := []) (by simp) inferFuel).2 _ a ha
    obtain ⟨⟨d, hd, hdl⟩, ⟨c, hc, hch⟩⟩ := harr hs
    refine ⟨w, hw, hwsrt.trans hs, isObj_of_isTy hM hO hws _ hdt,
      isObj_of_isTy hM hO hws _ hct, ?_, ?_⟩
    · rw [hd, ← hlo, hdl]
    · rw [hc, ← hhi, hch]
  · simp at hinf

end Lift

section Theorems

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}
  (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF)
  (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
  (hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m)
  (hδ : DefnsOk M G)
  (hcert : ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: defs)
include hM hG hps hds hδ hcert

/-- A theorem a derivation proves with valid earlier entries is valid. -/
theorem Thm.valid_of_checks {E : Array Entry}
    (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {a : Thm} {d : Deriv}
    (h : a.checks G E d = true) : a.Valid M G := by
  simp only [Thm.checks, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hctx, hhyps⟩, hconcl⟩, hd⟩ := h
  exact ⟨hctx, fun h hh ↦ of_decide_eq_true (List.all_eq_true.mp hhyps h hh), hconcl,
    fun ρ hρ ↦ ⟨hps _ ρ hρ, hds _ ρ hρ,
      (check_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE hcert d).2 _ _ _ hd⟩⟩

end Theorems

/-- The definitions of the language of constants the check accepts, of none but definitions of
the language, have their bodies' values at every assignment of objects. -/
theorem defnsVal_of_ok {pre cds defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}
    (hM : IsModel (ext defs) M) {G : Globals} (hbase : G.base = sig.length + pre.length)
    (hG : G.WF) (hno : ∀ (k m : ℕ) (b : Tree), G.defs[k]? ≠ some (.object m b))
    (hc : compileDefs G = some cds) (hpre : pre ++ cds <+: defs)
    (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
      PrimsHom M ρ G m) : DefnsVal M G := by
  intro k d hd
  obtain ⟨cd, hcd, hdc⟩ := compileDefs_getElem? hc hd
  obtain ⟨cb, hcb, rfl⟩ := Defn.compile_eq_some hdc
  have hk : k < G.defs.length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨hds, -⟩ := defsInv hM hbase hG hno hc hpre hps k hk.le
  have hle : Globals.Le { G with defs := G.defs.take k } G :=
    ⟨List.prefix_refl _, rfl, List.take_prefix k G.defs⟩
  obtain ⟨hpt, -⟩ := hG.defs k d hd
  have hptk : d.params.all (IsTy { G with defs := G.defs.take k } d.arity) = true := by
    rw [isTy_take_of_noObj hno]; exact hpt
  refine ⟨cb, compile_mono hle _ _ _ _ hcb, fun ws hws ↦ ?_⟩
  obtain ⟨v, hv, -⟩ := (compile_hom hM (hG.take hno k) hws (primsHom_take hno (hps _ ws hws) k)
    (hds _ ws hws) _ _ _ _ hcb (stdEnv_hom hM (hds _ ws hws).2 hws _ hptk)).1
  have hlen : ws.length = d.arity := by simpa using congrArg List.length hws
  have hvars := map_eval_vars ws
  rw [hlen] at hvars
  rw [hv, PartialHorn.opVars, hbase, Nat.add_assoc]
  exact eval_op_defn hM (i := pre.length + k) (d := ⟨List.replicate d.arity obj, arr, cb⟩)
    (getElem?_of_prefix hpre (by simp [List.getElem?_append_right, hcd])) hvars hws hv

/-- The environment with a valid entry pushed has valid entries. -/
theorem valid_push {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {G : Globals}
    {E : Array Entry} (hE : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G) {e : Entry}
    (he : e.Valid M G) : ∀ (j : ℕ) (e' : Entry), (E.push e)[j]? = some e' → e'.Valid M G := by
  intro j e' hj
  rcases Nat.lt_trichotomy j E.size with hlt | rfl | hgt
  · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at hj
    exact hE j e' hj
  · rw [Array.getElem?_push_size] at hj
    exact Option.some_inj.mp hj ▸ he
  · rw [Array.getElem?_eq_none (by rw [Array.size_push]; omega)] at hj
    cases hj

/-- A declaration's check extends the constants. -/
theorem Decl.le_of_step {d : Decl} {G G' : Globals} {E E' : Array Entry}
    (h : d.step G E = some (G', E')) : G.Le G' := by
  cases d <;> simp only [Decl.step] at h <;> split_ifs at h <;>
    simp only [Option.some.injEq, Prod.mk.injEq] at h <;> obtain ⟨rfl, -⟩ := h
  · exact Globals.Le.refl G
  · exact Globals.Le.refl G
  · exact ⟨List.prefix_refl _, rfl, List.prefix_append _ _⟩
  · exact ⟨List.prefix_append _ _, rfl, List.prefix_refl _⟩

/-- The check of a development of one more declaration first checks it. -/
theorem checkDev_cons (G : Globals) (E : Array Entry) (d : Decl) (ds : List Decl) :
    checkDev G E (d :: ds) = (d.step G E).bind fun st ↦ checkDev st.1 st.2 ds := by
  simp only [checkDev, List.foldlM_cons]
  rfl

/-- A development's check extends the constants. -/
theorem le_of_checkDev (ds : List Decl) :
    ∀ {G Gf : Globals} {E Ef : Array Entry}, checkDev G E ds = some (Gf, Ef) → G.Le Gf :=
  ds.rec (motive := fun ds ↦ ∀ {G Gf : Globals} {E Ef : Array Entry},
      checkDev G E ds = some (Gf, Ef) → G.Le Gf)
    (fun h ↦ by
      simp only [checkDev, List.foldlM_nil, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      exact h.1 ▸ Globals.Le.refl _)
    fun d ds ih G Gf E Ef h ↦ by
      rw [checkDev_cons] at h
      obtain ⟨⟨G', E'⟩, hs, hr⟩ := Option.bind_eq_some_iff.mp h
      exact (Decl.le_of_step hs).trans (ih hr)

/-- The definitions of constants among the final ones compile to an initial segment of the final
definitions, after the combinators' own. -/
theorem prefix_of_le {pre F : List PartialHorn.Defn} {G Gf : Globals}
    (hF : compileDefs Gf = some F) (hle : G.Le Gf) {cds : List PartialHorn.Defn}
    (hc : compileDefs G = some cds) : pre ++ cds <+: pre ++ F :=
  (List.prefix_append_right_inj pre).mpr (compileDefs_prefix hle hc hF)

variable (M) in
/-- The invariant of a development's check, relative to the constants {lit}`Gf` it ends with: the
constants so far are among those and well formed, their definitions compile, their primitive
arrows are arrows of the model's signature, and, at every assignment of objects, arrows between
their types, their definitions of the language arrows of their types with their bodies' values
and their object definitions objects, and the entries are valid. -/
structure DevInv {defs : List PartialHorn.Defn} (M : Model.{v} (ext defs).sig) (Gf G : Globals)
    (E : Array Entry) : Prop where
  /-- The constants are among the final ones. -/
  le : G.Le Gf
  /-- The constants are well formed. -/
  wf : G.WF
  /-- The definitions compile. -/
  compiles : ∃ cds, compileDefs G = some cds
  /-- The primitive arrows are arrows of the model's signature. -/
  sorts : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
    PartialHorn.sortOf (ext defs).sig (List.replicate p.arity obj) p.arrow = some arr
  /-- The primitive arrows are arrows between their types. -/
  prims : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p → p.Val M
  /-- The definitions are arrows and objects. -/
  defs : DefsVal M G
  /-- The definitions of the language have their bodies' values. -/
  defns : DefnsVal M G
  /-- The entries are valid. -/
  entries : ∀ (j : ℕ) (e : Entry), E[j]? = some e → e.Valid M G

section Development

variable {pre F : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ F)).sig}
  (hM : IsModel (ext (pre ++ F)) M) {Gf : Globals} (hF : compileDefs Gf = some F)
  (hbase : Gf.base = sig.length + pre.length)

include hM hF hbase

omit hF hbase in
/-- The primitive arrows of the invariant's constants are arrows at types. -/
theorem DevInv.primsHom {G : Globals} {E : Array Entry} (h : DevInv M Gf G E) :
    ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m :=
  fun _ _ hρ ↦ primsHom_of_val hM h.wf h.defs.2 h.prims hρ

omit hF hbase in
/-- The definitions of the invariant's constants are arrows and objects at types. -/
theorem DevInv.defsHom {G : Globals} {E : Array Entry} (h : DevInv M Gf G E) :
    ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m :=
  fun _ _ hρ ↦ defsHom_of_val hM h.wf h.defs hρ

omit hM in
/-- A certificate is checked with the constants among the final ones only in a theory whose
definitions begin the model's. -/
theorem cert_of_le {G : Globals} (hle : G.Le Gf) :
    ∀ cds, compileDefs G = some cds → G.base = sig.length → cds <+: pre ++ F := fun cds hc hb ↦ by
  have hpre : pre.length = 0 :=
    Nat.add_left_cancel (((hle.2.1.trans hbase).symm.trans hb).trans (Nat.add_zero _).symm)
  obtain rfl := List.length_eq_zero_iff.mp hpre
  exact compileDefs_prefix hle hc hF

/-- A definition of the language compiled with the constants of the invariant, added to them
among the final ones, is at every assignment of objects an arrow of its types with its compiled
body's value. -/
theorem defn_val_snoc {G : Globals} (hG : G.WF)
    (hpv : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p → p.Val M) (hdv : DefsVal M G)
    {cds : List PartialHorn.Defn} (hc : compileDefs G = some cds) {d : Defn} {cb : Tree}
    (hcb : compile G d.arity d.body (ctxObj d.params) (stdEnv d.params) = some (cb, d.type))
    (hcd : d.compile G = some ⟨List.replicate d.arity obj, arr, cb⟩)
    (hle : ({ G with defs := G.defs ++ [.language d] } : Globals).Le Gf) {ws : List M.Val}
    (hws : ws.map Sigma.fst = List.replicate d.arity obj) :
    Hom M ws (PartialHorn.opVars (G.base + G.defs.length) d.arity) (ctxObj d.params) d.type ∧
      eval M ws (PartialHorn.opVars (G.base + G.defs.length) d.arity) = eval M ws cb := by
  have hpt := Defn.params_of_compile hcd
  have hc' := compileDefs_snoc hc (d := .language d) hcd
  have hpre := prefix_of_le (pre := pre) hF hle hc'
  have hlen := length_compileDefs hc
  have hbody := (compile_hom hM hG hws (primsHom_of_val hM hG hdv.2 hpv hws)
    (defsHom_of_val hM hG hdv hws) _ _ _ _ hcb (stdEnv_hom hM hdv.2 hws _ hpt)).1
  obtain ⟨v, hv, -⟩ := hbody.exists_eval
  have hwl : ws.length = d.arity := by simpa using congrArg List.length hws
  have hvars := map_eval_vars ws
  rw [hwl] at hvars
  have hop : eval M ws (PartialHorn.opVars (G.base + G.defs.length) d.arity) = eval M ws cb := by
    rw [hv, PartialHorn.opVars, show G.base = sig.length + pre.length from hle.2.1.trans hbase,
      Nat.add_assoc]
    exact eval_op_defn hM (i := pre.length + G.defs.length)
      (d := ⟨List.replicate d.arity obj, arr, cb⟩)
      (getElem?_of_prefix hpre (by simp [hlen])) hvars hws hv
  exact ⟨hbody.congr hop rfl rfl, hop⟩

/-- Each declaration's check keeps the invariant, when the constants it ends with are among the
final ones. -/
theorem DevInv.step {G G' : Globals} {E E' : Array Entry} (h : DevInv M Gf G E) {d : Decl}
    (hs : d.step G E = some (G', E')) (hle : G'.Le Gf) : DevInv M Gf G' E' := by
  obtain ⟨cds, hc⟩ := h.compiles
  have hcert := cert_of_le hF hbase h.le
  cases d with
  | language a der =>
    simp only [Decl.step] at hs
    split_ifs at hs with hck
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact { h with
      entries := valid_push h.entries (Thm.valid_of_checks hM h.wf (h.primsHom hM)
        (h.defsHom hM) (defnsOk_of_val hM h.defs h.defns) hcert h.entries hck) }
  | combinators s c =>
    simp only [Decl.step] at hs
    split_ifs at hs with hck
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact { h with
      entries := valid_push h.entries (certifies_valid hM h.wf h.entries hcert hck) }
  | definition d =>
    simp only [Decl.step] at hs
    split_ifs at hs with hck
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    simp only [Defn.checks, Bool.and_eq_true, Option.isSome_iff_exists] at hck
    obtain ⟨⟨cd, hcd⟩, hty⟩ := hck
    obtain ⟨cb, hcb, rfl⟩ := Defn.compile_eq_some hcd
    have hc' := compileDefs_snoc hc (d := .language d) hcd
    have hpt := Defn.params_of_compile hcd
    have hle' : G.Le { G with defs := G.defs ++ [.language d] } :=
      ⟨List.prefix_refl _, rfl, List.prefix_append _ _⟩
    have hG' : ({ G with defs := G.defs ++ [.language d] } : Globals).WF := by
      refine ⟨fun k p hp ↦ ?_, fun k d' hd' ↦ ?_⟩
      · obtain ⟨ha, hd, hc⟩ := h.wf.prims k p hp
        exact ⟨ha, isTy_mono hle' _ hd, isTy_mono hle' _ hc⟩
      · rw [List.getElem?_append] at hd'
        split_ifs at hd' with hlt
        · obtain ⟨hp, ht⟩ := h.wf.defs k d' hd'
          exact ⟨all_isTy_mono hle' hp, isTy_mono hle' _ ht⟩
        · rw [List.getElem?_singleton] at hd'
          split_ifs at hd'
          obtain rfl := Definition.language.inj (Option.some_inj.mp hd')
          exact ⟨all_isTy_mono hle' hpt, isTy_mono hle' _ hty⟩
    have hval := fun {ws : List M.Val} (hws : ws.map Sigma.fst = List.replicate d.arity obj) ↦
      defn_val_snoc hM hF hbase h.wf h.prims h.defs hc hcb hcd hle hws
    have hdv' : DefsVal M { G with defs := G.defs ++ [.language d] } := by
      refine ⟨fun j d' hd' ws hws ↦ ?_, fun j m b hj ↦ ?_⟩
      · rw [List.getElem?_append] at hd'
        split_ifs at hd' with hlt
        · exact h.defs.1 j d' hd' ws hws
        · rw [List.getElem?_singleton] at hd'
          split_ifs at hd' with hj0
          obtain rfl := Definition.language.inj (Option.some_inj.mp hd')
          obtain rfl : j = G.defs.length := by omega
          exact (hval hws).1
      · rw [List.getElem?_append] at hj
        split_ifs at hj with hlt
        · exact h.defs.2 j m b hj
        · rw [List.getElem?_singleton] at hj
          split_ifs at hj
          simp at hj
    have hdn' : DefnsVal M { G with defs := G.defs ++ [.language d] } := by
      intro j d' hd'
      rw [List.getElem?_append] at hd'
      split_ifs at hd' with hlt
      · obtain ⟨F', hF', hFv⟩ := h.defns j d' hd'
        exact ⟨F', compile_mono hle' _ _ _ _ hF', hFv⟩
      · rw [List.getElem?_singleton] at hd'
        split_ifs at hd' with hj0
        obtain rfl := Definition.language.inj (Option.some_inj.mp hd')
        obtain rfl : j = G.defs.length := by omega
        exact ⟨cb, compile_mono hle' _ _ _ _ hcb, fun ws hws ↦ (hval hws).2⟩
    exact ⟨hle, hG', ⟨_, hc'⟩, h.sorts, h.prims, hdv', hdn', fun j e he ↦
      Entry.Valid.mono hM h.wf hle' (fun _ _ hρ ↦ primsHom_of_val hM hG' hdv'.2 h.prims hρ)
        (fun _ _ hρ ↦ defsHom_of_val hM hG' hdv' hρ) (h.entries j e he)⟩
  | constant p c =>
    simp only [Decl.step] at hs
    split_ifs at hs with hck
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    -- the primitive arrow is well formed, an arrow of the signature and between its types
    obtain ⟨har, hdt, hct, hsort, hval⟩ :
        PartialHorn.Scoped p.arity p.arrow = true ∧ IsTy G p.arity p.dom = true ∧
          IsTy G p.arity p.cod = true ∧
          PartialHorn.sortOf (ext (pre ++ F)).sig (List.replicate p.arity obj) p.arrow =
            some arr ∧ p.Val M := by
      cases c with
      | none =>
        simp only [Prim.confirms, hc, Option.any_some, Bool.and_eq_true,
          decide_eq_true_eq] at hck
        obtain ⟨hb, hok⟩ := hck
        have hpre := hcert cds hc hb
        have hwf := hok
        simp only [Prim.ok, Prim.wf, Bool.and_eq_true, beq_iff_eq] at hwf
        obtain ⟨⟨⟨⟨har, hdt⟩, hct⟩, hsrt⟩, -⟩ := hwf
        exact ⟨har, hdt, hct, PartialHorn.sortOf_of_prefix (ext_prefix hpre).1
          (by simpa [ExtEnv.ofDefs] using hsrt), Prim.val_of_ok hM h.defs.2 hpre hok⟩
      | some c =>
        simp only [Prim.confirms, hc, Option.any_some, Bool.and_eq_true] at hck
        obtain ⟨hwf, hcf⟩ := hck
        have hb : G.base = sig.length := by
          simp only [certifies, hc, Option.any_some, Bool.and_eq_true,
            decide_eq_true_eq] at hcf
          exact hcf.1
        have hpre := hcert cds hc hb
        simp only [Prim.wf, Bool.and_eq_true, beq_iff_eq] at hwf
        obtain ⟨⟨⟨har, hdt⟩, hct⟩, hsrt⟩ := hwf
        have hsv := certifies_valid hM h.wf h.entries hcert hcf
        exact ⟨har, hdt, hct, PartialHorn.sortOf_of_prefix (ext_prefix hpre).1 hsrt,
          Prim.val_of_seq hM h.defs.2 hsv hdt hct⟩
    have hG' : ({ G with prims := G.prims ++ [p] } : Globals).WF := by
      refine ⟨fun k p' hp' ↦ ?_, h.wf.defs⟩
      rw [List.getElem?_append] at hp'
      split_ifs at hp' with hlt
      · exact h.wf.prims k p' hp'
      · rw [List.getElem?_singleton] at hp'
        split_ifs at hp'
        obtain rfl := Option.some_inj.mp hp'
        exact ⟨har, hdt, hct⟩
    have hle' : G.Le { G with prims := G.prims ++ [p] } :=
      ⟨List.prefix_append _ _, rfl, List.prefix_refl _⟩
    have hpv' : ∀ (k : ℕ) (p' : Prim), ({ G with prims := G.prims ++ [p] } : Globals).prims[k]? =
        some p' → p'.Val M := fun k p' hp' ↦ by
      rw [List.getElem?_append] at hp'
      split_ifs at hp' with hlt
      · exact h.prims k p' hp'
      · rw [List.getElem?_singleton] at hp'
        split_ifs at hp'
        obtain rfl := Option.some_inj.mp hp'
        exact hval
    have hc' := compileDefs_of_prims hle' rfl hc
    have hdn' : DefnsVal M { G with prims := G.prims ++ [p] } := fun j d' hd' ↦ by
      obtain ⟨F', hF', hFv⟩ := h.defns j d' hd'
      exact ⟨F', compile_mono hle' _ _ _ _ hF', hFv⟩
    refine ⟨hle, hG', ⟨_, hc'⟩, fun k p' hp' ↦ ?_, hpv', h.defs, hdn', fun j e he ↦
      Entry.Valid.mono hM h.wf hle' (fun _ _ hρ ↦ primsHom_of_val hM hG' h.defs.2 hpv' hρ)
        (fun _ _ hρ ↦ defsHom_of_val hM hG' h.defs hρ) (h.entries j e he)⟩
    rw [List.getElem?_append] at hp'
    split_ifs at hp' with hlt
    · exact h.sorts k p' hp'
    · rw [List.getElem?_singleton] at hp'
      split_ifs at hp'
      obtain rfl := Option.some_inj.mp hp'
      exact hsort

/-- The invariant holds at the end of a development's check that begins with it. -/
theorem devInv_checkDev {Ef : Array Entry} (ds : List Decl) :
    ∀ {G : Globals} {E : Array Entry}, checkDev G E ds = some (Gf, Ef) → DevInv M Gf G E →
      DevInv M Gf Gf Ef :=
  ds.rec (motive := fun ds ↦ ∀ {G : Globals} {E : Array Entry},
      checkDev G E ds = some (Gf, Ef) → DevInv M Gf G E → DevInv M Gf Gf Ef)
    (fun h hinv ↦ by
      simp only [checkDev, List.foldlM_nil, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hinv)
    fun d ds ih G E h hinv ↦ by
      rw [checkDev_cons] at h
      obtain ⟨⟨G', E'⟩, hs, hr⟩ := Option.bind_eq_some_iff.mp h
      exact ih hr (hinv.step hM hF hbase hs (le_of_checkDev ds hr))

end Development

/-- The invariant at the end of a development that checks, from constants the check accepts. -/
theorem devInv_of_checkDev {pre F : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ F)).sig}
    (hM : IsModel (ext (pre ++ F)) M) {G Gf : Globals} {cds : List PartialHorn.Defn}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) {ds : List Decl} {Ef : Array Entry}
    (h : checkDev G #[] ds = some (Gf, Ef)) (hF : compileDefs Gf = some F) :
    DevInv M Gf Gf Ef := by
  have hle := le_of_checkDev ds h
  have hpre := prefix_of_le (pre := pre) hF hle hc
  have hG := Globals.wf_of_ok hok
  have hno := Globals.noObj_of_ok hok
  have hps := fun (m : ℕ) (ρ : List M.Val) (hρ : ρ.map Sigma.fst = List.replicate m obj) ↦
    primsHom_of_ok hM hpre hok hρ
  have hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
      DefsHom M ρ G m := fun m ρ hρ ↦ by
    have := (defsInv hM hbase hG hno hc hpre hps G.defs.length le_rfl).1 m ρ hρ
    simpa only [List.take_length] using this
  have hok' := hok
  simp only [Globals.ok, Bool.and_eq_true, List.all_eq_true] at hok'
  exact devInv_checkDev hM hF (hle.2.1.symm.trans hbase) ds h
    ⟨hle, hG, ⟨cds, hc⟩,
      fun k p hp ↦ PartialHorn.sortOf_of_prefix (ext_prefix hpre).1 (sortOf_prims_of_ok hok hp),
      fun k p hp ↦ Prim.val_of_ok hM (objsHom_of_noObj hno) hpre
        (hok'.1 p (List.mem_of_getElem? hp)),
      defsVal_of_defsHom hG hds, defnsVal_of_ok hM hbase hG hno hc hpre hps,
      fun _ _ hj ↦ by simp at hj⟩

/-- The soundness of the internal language's developments: in every model of the theory extended
by the combinators' definitions and those the language's definitions compile to, every entry of a
development that checks is valid, when the check accepts the constants it begins with. -/
theorem valid_of_checkDev {pre F : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ F)).sig}
    (hM : IsModel (ext (pre ++ F)) M) {G Gf : Globals} {cds : List PartialHorn.Defn}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) {ds : List Decl} {Ef : Array Entry}
    (h : checkDev G #[] ds = some (Gf, Ef)) (hF : compileDefs Gf = some F) :
    ∀ (j : ℕ) (e : Entry), Ef[j]? = some e → e.Valid M Gf :=
  (devInv_of_checkDev hM hbase hok hc h hF).entries

/-- The one-point model is a model of every well-formed extension of the theory. -/
theorem isModel_point_ext {pre cds : List PartialHorn.Defn}
    (hwf : PartialHorn.DefnsWF sig (pre ++ cds)) :
    IsModel (ext (pre ++ cds)) (PartialHorn.pointModel (ext (pre ++ cds)).sig) :=
  PartialHorn.isModel_point
    (PartialHorn.sidesSorted_extendAll (pre ++ cds) theory theory_sidesSorted hwf)

/-- The soundness of the internal language's developments for the theory itself, for
equations: each equation proved without hypotheses in a development that checks has sides that
compile in its context to arrows of one type, whose equation, with every definition unfolded,
holds in every model of the theory, when the check accepts the constants it begins with and the
definitions are well formed. -/
theorem valid_unfoldAll_of_checkDev {pre cds F : List PartialHorn.Defn} {G Gf : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) {ds : List Decl} {Ef : Array Entry}
    (h : checkDev G #[] ds = some (Gf, Ef)) (hF : compileDefs Gf = some F)
    (hwf : PartialHorn.DefnsWF sig (pre ++ F)) {j : ℕ} {a : Thm}
    (hp : Ef[j]? = some (.language a)) (hnil : a.hyps = []) {l r : Term}
    (hlr : eqParts a.concl = some (l, r)) :
    ∃ f g A, compile Gf a.arity l (ctxObj a.ctx) (stdEnv a.ctx) = some (f, A) ∧
      compile Gf a.arity r (ctxObj a.ctx) (stdEnv a.ctx) = some (g, A) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ F)
          ⟨List.replicate a.arity obj, [], ⟨f, g⟩⟩).Valid M := by
  have hinv := devInv_of_checkDev (isModel_point_ext hwf) hbase hok hc h hF
  obtain ⟨hctx, -, hcon, -⟩ : a.Valid _ Gf := hinv.entries j _ hp
  obtain ⟨⟨C, C'⟩, hC, -⟩ := Option.map_eq_some_iff.mp hcon
  rw [eqParts_eq_some hlr] at hC
  obtain ⟨l', r', hlr', f, A, hf, g, hg, -⟩ := compile_eq_iff.mp hC
  simp only [List.cons.injEq, and_true] at hlr'
  obtain ⟨rfl, rfl⟩ := hlr'
  refine ⟨f, g, A, hf, hg, fun M hM ↦ ?_⟩
  have hbF : Gf.base = sig.length + pre.length := (le_of_checkDev ds h).2.1.symm.trans hbase
  have hdefs := fun k d (hd : Gf.defs[k]? = some d) ↦ getElem?_sig_compileDefs hbF hF hd
  have hsrt := fun {s : Term} {r : Tree × Tree}
      (hs : compile Gf a.arity s (ctxObj a.ctx) (stdEnv a.ctx) = some r) ↦
    compile_sortOf (defs := pre ++ F) hinv.wf hinv.sorts hdefs s _ _ r hs
      (sortOf_ctxObj hdefs _ hctx) (sortOf_stdEnv hdefs _ hctx)
  refine PartialHorn.valid_unfoldAll (pre ++ F) theory M hM theory_ofSig hwf _ ?_ ?_
  · intro q hq
    obtain rfl : q = ⟨f, g⟩ := by simpa using hq
    exact ⟨⟨arr, (hsrt hf).1⟩, ⟨arr, (hsrt hg).1⟩⟩
  · intro N hN ρ hρ _
    have hinvN := devInv_of_checkDev hN hbase hok hc h hF
    obtain ⟨-, -, -, hv⟩ : a.Valid N Gf := hinvN.entries j _ hp
    obtain ⟨hpsN, hdsN, hfN⟩ := hv ρ hρ
    have hstd := stdEnv_hom hN hinvN.defs.2 hρ _ hctx
    have hH := hfN _ _ hstd (map_snd_stdEnv _) (by rw [hnil]; exact fun _ h ↦ by simp at h) _
      (by rw [eqParts_eq_some hlr]; exact compile_eq_iff.mpr ⟨_, _, rfl, f, A, hf, g, hg, rfl⟩)
    have heq := (holds_eq_iff hN hinvN.wf hρ hpsN hdsN hstd hf hg).mp hH
    obtain ⟨w, hw, -⟩ := (compile_hom hN hinvN.wf hρ hpsN hdsN _ _ _ _ hf hstd).1.exists_eval
    exact ⟨w, hw, heq.symm.trans hw⟩

/-- The soundness of the internal language's developments for the theory itself, for formulas:
each formula proved without hypotheses in a development that checks compiles in its context to
an arrow that, with every definition unfolded, is true in every model of the theory, when the
check accepts the constants it begins with and the definitions are well formed. -/
theorem valid_unfoldAll_holds_of_checkDev {pre cds F : List PartialHorn.Defn} {G Gf : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) {ds : List Decl} {Ef : Array Entry}
    (h : checkDev G #[] ds = some (Gf, Ef)) (hF : compileDefs Gf = some F)
    (hwf : PartialHorn.DefnsWF sig (pre ++ F)) {j : ℕ} {a : Thm}
    (hp : Ef[j]? = some (.language a)) (hnil : a.hyps = []) :
    ∃ C, compile Gf a.arity a.concl (ctxObj a.ctx) (stdEnv a.ctx) = some (C, omega) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ F)
          ⟨List.replicate a.arity obj, [], ⟨C, comp tru (bang (ctxObj a.ctx))⟩⟩).Valid M := by
  have hinv := devInv_of_checkDev (isModel_point_ext hwf) hbase hok hc h hF
  obtain ⟨hctx, -, hcon, -⟩ : a.Valid _ Gf := hinv.entries j _ hp
  obtain ⟨⟨C, C'⟩, hC, hC'⟩ := Option.map_eq_some_iff.mp hcon
  obtain rfl : C' = omega := hC'
  refine ⟨C, hC, fun M hM ↦ ?_⟩
  have hbF : Gf.base = sig.length + pre.length := (le_of_checkDev ds h).2.1.symm.trans hbase
  have hdefs := fun k d (hd : Gf.defs[k]? = some d) ↦ getElem?_sig_compileDefs hbF hF hd
  have hsC := (compile_sortOf (defs := pre ++ F) hinv.wf hinv.sorts hdefs _ _ _ _ hC
    (sortOf_ctxObj hdefs _ hctx) (sortOf_stdEnv hdefs _ hctx)).1
  refine PartialHorn.valid_unfoldAll (pre ++ F) theory M hM theory_ofSig hwf _ ?_ ?_
  · intro q hq
    obtain rfl : q = ⟨C, comp tru (bang (ctxObj a.ctx))⟩ := by simpa using hq
    exact ⟨⟨arr, hsC⟩, ⟨arr, sortOf_comp (sortOf_op rfl rfl)
      (sortOf_bang (sortOf_ctxObj hdefs _ hctx))⟩⟩
  · intro N hN ρ hρ _
    have hinvN := devInv_of_checkDev hN hbase hok hc h hF
    obtain ⟨-, -, -, hv⟩ : a.Valid N Gf := hinvN.entries j _ hp
    obtain ⟨-, -, hfN⟩ := hv ρ hρ
    have hstd := stdEnv_hom hN hinvN.defs.2 hρ _ hctx
    have hH := hfN _ _ hstd (map_snd_stdEnv _) (by rw [hnil]; exact fun _ h ↦ by simp at h) _ hC
    obtain ⟨w, hw, -⟩ := (truth_hom hN hstd.1).exists_eval
    exact ⟨w, hH.2.trans hw, hw⟩

end Geb.FreeTopos.Internal

end
