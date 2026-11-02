/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Conversion
public import Geb.Prototypes.FreeTopos.Internal.Development
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Developments with certificates of the conversion checker

A development whose theorems are proved by derivations of the base checker
({name}`Geb.FreeTopos.Internal.Thm.checks`) or by certificates of the conversion checker
({name}`Geb.FreeTopos.Internal.Thm.convChecks`), checked in order as
{name}`Geb.FreeTopos.Internal.checkDev` checks a development: a theorem of either kind joins the
entries once its certificate proves it with the constants and the entries before it. A third
kind of declaration records an index at which the evaluation at literals is ready
({name}`Geb.FreeTopos.Literals.ready`), tested at that declaration alone: the test reads the
constants and the entries, which the declarations after it extend, and neither a step's term nor
its context, and it holds with more constants and entries
({name}`Geb.FreeTopos.Literals.ready_mono`), so every later step of evaluation at that index
reads the record in place of the test. Its soundness is the base development's invariant
({name}`Geb.FreeTopos.Internal.DevInv`) with the readiness of the indices recorded, kept by a
theorem of the conversion checker as by one of the base checker, by the relative soundness of the
conversion checker ({name}`Geb.FreeTopos.Internal.Thm.valid_of_convChecks`); the base
development's check is the check of its declarations, each of the first kind.

## Main definitions

* {lit}`ConvDecl` — a declaration of a development: a declaration of the base checker, a theorem
  with a certificate of the conversion checker, or the record of an index at which the evaluation
  at literals is ready.
* {lit}`checkConvDev` — the check of a development.

## Main statements

* {lit}`valid_of_checkConvDev` — in every model of the theory extended by the combinators'
  definitions and those the language's definitions compile to, every entry of a development that
  checks is valid.

## References

* {cite}`Davis2009`, Chapter 1, for checkers admitted by relative soundness.

## Tags

internal language, development, conversion, relative soundness, certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree Model IsModel)
open Sorts

universe v

/-- A declaration of a development: a declaration of the base checker, a theorem of the language
with a certificate of the conversion checker, or the record that the evaluation at literals is
ready at an index. -/
inductive ConvDecl where
  /-- A declaration of the base checker. -/
  | base (d : Decl)
  /-- A theorem of the language, with a certificate of the conversion checker. -/
  | conv (a : Thm) (c : ConvDeriv)
  /-- The record that the evaluation at literals is ready at the index {lit}`j`
  ({name}`Geb.FreeTopos.Literals.ready`), its equations the theorems from {lit}`j` on. -/
  | ready (j : ℕ)

/-- The state of a development's check: the constants, the entries, and the indices at which the
evaluation at literals is ready. -/
abbrev ConvState : Type := Globals × Array Entry × List ℕ

/-- The check of a declaration with the constants of {lit}`G`, the entries of {lit}`E` and the
indices of {lit}`R` at which the evaluation at literals is ready: a declaration of the base
checker's; a theorem whose certificate the conversion checker accepts given those indices, added
to the entries; and the record of an index, added to the indices where the evaluation is ready
there. -/
def ConvDecl.step (G : Globals) (E : Array Entry) (R : List ℕ) : ConvDecl → Option ConvState
  | .base d => (d.step G E).map fun (G', E') ↦ (G', E', R)
  | .conv a c => if a.convChecks G E R c then some (G, E.push (.language a), R) else none
  | .ready j => if Literals.ready G E j then some (G, E, j :: R) else none

/-- The check of a development's declarations in order, each with the state the declarations
before it leave, from no index at which the evaluation at literals is ready. -/
def checkConvDev (G : Globals) (E : Array Entry) (ds : List ConvDecl) : Option ConvState :=
  ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) (G, E, [])

/-- A declaration's check of the base checker extends the entries. -/
theorem Decl.prefix_of_step {d : Decl} {G G' : Globals} {E E' : Array Entry}
    (h : d.step G E = some (G', E')) : E.toList <+: E'.toList := by
  have push (e : Entry) : E.toList <+: (E.push e).toList := ⟨_, (Array.toList_push ..).symm⟩
  -- the conditions of the step read by their lemma rather than split, which would select a
  -- choice-dependent instance of their decidability here
  cases d with
  | quotient n A R =>
    dsimp only [Decl.step] at h
    split at h
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (Option.ite_none_right_eq_some.mp h).2)
      exact push _
    · cases h
  | descent kq C h' jr =>
    dsimp only [Decl.step] at h
    split at h
    · split at h
      · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (Option.ite_none_right_eq_some.mp h).2)
        exact push _
      · cases h
    · cases h
  | _ =>
    dsimp only [Decl.step] at h
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj (Option.ite_none_right_eq_some.mp h).2)
    first
      | exact List.prefix_refl _
      | exact push _

/-- A declaration's check extends the constants and the entries. -/
theorem ConvDecl.le_of_step {d : ConvDecl} {G G' : Globals} {E E' : Array Entry}
    {R R' : List ℕ} (h : d.step G E R = some (G', E', R')) :
    G.Le G' ∧ E.toList <+: E'.toList := by
  cases d with
  | base d =>
    simp only [ConvDecl.step, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨_, _, hs, rfl, rfl, -⟩ := h
    exact ⟨Decl.le_of_step hs, Decl.prefix_of_step hs⟩
  | conv a c =>
    dsimp only [ConvDecl.step] at h
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨Globals.Le.refl G, Array.toList_push .. ▸ List.prefix_append _ _⟩
  | ready j =>
    dsimp only [ConvDecl.step] at h
    obtain ⟨-, h⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨Globals.Le.refl G, List.prefix_refl _⟩

/-- A check of declarations in order extends the constants. -/
theorem ConvDecl.le_of_foldlM (ds : List ConvDecl) :
    ∀ {G Gf : Globals} {E Ef : Array Entry} {R Rf : List ℕ},
      ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) (G, E, R) = some (Gf, Ef, Rf) →
        G.Le Gf :=
  ds.rec (motive := fun ds ↦ ∀ {G Gf : Globals} {E Ef : Array Entry} {R Rf : List ℕ},
      ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) (G, E, R) = some (Gf, Ef, Rf) →
        G.Le Gf)
    (fun h ↦ by
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      exact h.1 ▸ Globals.Le.refl _)
    fun d ds ih G Gf E Ef R Rf h ↦ by
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨G', E', R'⟩, hs, hr⟩ := h
      exact (ConvDecl.le_of_step hs).1.trans (ih hr)

section Development

variable {pre F : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ F)).sig}
  (hM : IsModel (ext (pre ++ F)) M) {Gf : Globals} (hF : compileDefs Gf = some F)
  (hbase : Gf.base = sig.length + pre.length)

/-- The invariant of a development's check: the base development's
({name}`Geb.FreeTopos.Internal.DevInv`), and the evaluation at literals ready at the indices
recorded. -/
def ConvInv (M : Model.{v} (ext (pre ++ F)).sig) (Gf : Globals) (st : ConvState) : Prop :=
  DevInv M Gf st.1 st.2.1 ∧ ∀ j ∈ st.2.2, Literals.ready st.1 st.2.1 j = true

include hM hF hbase

/-- Each declaration's check keeps the invariant, when the constants it ends with are among the
final ones. -/
theorem ConvInv.step {G G' : Globals} {E E' : Array Entry} {R R' : List ℕ}
    (h : ConvInv M Gf (G, E, R)) {d : ConvDecl} (hs : d.step G E R = some (G', E', R'))
    (hle : G'.Le Gf) : ConvInv M Gf (G', E', R') := by
  obtain ⟨hinv, hR⟩ := h
  have hmono := ConvDecl.le_of_step hs
  have hR' : ∀ j ∈ R, Literals.ready G' E' j = true := fun j hj ↦
    Literals.ready_mono hmono.1 hmono.2 (hR j hj)
  cases d with
  | base d =>
    simp only [ConvDecl.step, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at hs
    obtain ⟨_, _, hs, rfl, rfl, rfl⟩ := hs
    exact ⟨hinv.step hM hF hbase hs hle, hR'⟩
  | conv a c =>
    dsimp only [ConvDecl.step] at hs
    obtain ⟨hck, hs⟩ := Option.ite_none_right_eq_some.mp hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨{ hinv with
      entries := valid_push hinv.entries (Thm.valid_of_convChecks hM hinv.wf (hinv.primsHom hM)
        (hinv.defsHom hM) (defnsOk_of_val hM hinv.defs hinv.defns) (cert_of_le hF hbase hinv.le)
        hinv.entries hR hck) }, hR'⟩
  | ready j =>
    dsimp only [ConvDecl.step] at hs
    obtain ⟨hj, hs⟩ := Option.ite_none_right_eq_some.mp hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    exact ⟨hinv, fun i hi ↦ (List.mem_cons.mp hi).elim (· ▸ hj) (hR i)⟩

/-- The invariant holds at the end of a check of declarations in order that begins with it. -/
theorem ConvInv.foldlM {Ef : Array Entry} {Rf : List ℕ} (ds : List ConvDecl) :
    ∀ {G : Globals} {E : Array Entry} {R : List ℕ},
      ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) (G, E, R) = some (Gf, Ef, Rf) →
        ConvInv M Gf (G, E, R) → ConvInv M Gf (Gf, Ef, Rf) :=
  ds.rec (motive := fun ds ↦ ∀ {G : Globals} {E : Array Entry} {R : List ℕ},
      ds.foldlM (fun st d ↦ d.step st.1 st.2.1 st.2.2) (G, E, R) = some (Gf, Ef, Rf) →
        ConvInv M Gf (G, E, R) → ConvInv M Gf (Gf, Ef, Rf))
    (fun h hinv ↦ by
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact hinv)
    fun d ds ih G E R h hinv ↦ by
      simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨G', E', R'⟩, hs, hr⟩ := h
      exact ih hr (hinv.step hM hF hbase hs (ConvDecl.le_of_foldlM ds hr))

end Development

/-- The soundness of developments with certificates of the conversion checker: in every model of
the theory extended by the combinators' definitions and those the language's definitions compile
to, every entry of a development that checks is valid, when the check accepts the constants it
begins with. -/
theorem valid_of_checkConvDev {pre F : List PartialHorn.Defn}
    {M : Model.{v} (ext (pre ++ F)).sig} (hM : IsModel (ext (pre ++ F)) M) {G Gf : Globals}
    {cds : List PartialHorn.Defn} (hbase : G.base = sig.length + pre.length)
    (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true) (hc : compileDefs G = some cds)
    {ds : List ConvDecl} {Ef : Array Entry} {Rf : List ℕ}
    (h : checkConvDev G #[] ds = some (Gf, Ef, Rf)) (hF : compileDefs Gf = some F) :
    ∀ (j : ℕ) (e : Entry), Ef[j]? = some e → e.Valid M Gf :=
  have hf := ConvDecl.le_of_foldlM ds h
  (ConvInv.foldlM hM hF (hf.2.1.symm.trans hbase) ds h
    ⟨devInv_init hM hbase hok hc hf hF, fun _ h ↦ nomatch h⟩).1.entries

end Geb.FreeTopos.Internal

end
