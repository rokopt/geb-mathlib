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
entries once its certificate proves it with the constants and the entries before it. Its
soundness is the base development's invariant ({name}`Geb.FreeTopos.Internal.DevInv`), kept by a
theorem of the conversion checker as by one of the base checker, by the relative soundness of the
conversion checker ({name}`Geb.FreeTopos.Internal.Thm.valid_of_convChecks`); the base
development's check is the check of its declarations, each of the first kind.

## Main definitions

* {lit}`ConvDecl` — a declaration of a development: a declaration of the base checker, or a
  theorem with a certificate of the conversion checker.
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

/-- A declaration of a development: a declaration of the base checker, or a theorem of the
language with a certificate of the conversion checker. -/
inductive ConvDecl where
  /-- A declaration of the base checker. -/
  | base (d : Decl)
  /-- A theorem of the language, with a certificate of the conversion checker. -/
  | conv (a : Thm) (c : ConvDeriv)

/-- The check of a declaration with the constants of {lit}`G` and the entries of {lit}`E`: a
declaration of the base checker's, and a theorem whose certificate the conversion checker
accepts added to the entries. -/
def ConvDecl.step (G : Globals) (E : Array Entry) : ConvDecl → Option (Globals × Array Entry)
  | .base d => d.step G E
  | .conv a c => if a.convChecks G E c then some (G, E.push (.language a)) else none

/-- The check of a development's declarations in order, each with the constants and the entries
the declarations before it leave. -/
def checkConvDev (G : Globals) (E : Array Entry) (ds : List ConvDecl) :
    Option (Globals × Array Entry) :=
  ds.foldlM (fun st d ↦ d.step st.1 st.2) (G, E)

/-- A declaration's check extends the constants. -/
theorem ConvDecl.le_of_step {d : ConvDecl} {G G' : Globals} {E E' : Array Entry}
    (h : d.step G E = some (G', E')) : G.Le G' := by
  cases d with
  | base d => exact Decl.le_of_step h
  | conv a c =>
    simp only [ConvDecl.step] at h
    split_ifs at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1 ▸ Globals.Le.refl G

section Development

variable {pre F : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ F)).sig}
  (hM : IsModel (ext (pre ++ F)) M) {Gf : Globals} (hF : compileDefs Gf = some F)
  (hbase : Gf.base = sig.length + pre.length)

include hM hF hbase

/-- Each declaration's check keeps the invariant, when the constants it ends with are among the
final ones. -/
theorem DevInv.convStep {G G' : Globals} {E E' : Array Entry} (h : DevInv M Gf G E)
    {d : ConvDecl} (hs : d.step G E = some (G', E')) (hle : G'.Le Gf) : DevInv M Gf G' E' := by
  cases d with
  | base d => exact h.step hM hF hbase hs hle
  | conv a c =>
    simp only [ConvDecl.step] at hs
    split_ifs at hs with hck
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact { h with
      entries := valid_push h.entries (Thm.valid_of_convChecks hM h.wf (h.primsHom hM)
        (h.defsHom hM) (defnsOk_of_val hM h.defs h.defns) (cert_of_le hF hbase h.le) h.entries
        hck) }

end Development

/-- The soundness of developments with certificates of the conversion checker: in every model of
the theory extended by the combinators' definitions and those the language's definitions compile
to, every entry of a development that checks is valid, when the check accepts the constants it
begins with. -/
theorem valid_of_checkConvDev {pre F : List PartialHorn.Defn}
    {M : Model.{v} (ext (pre ++ F)).sig} (hM : IsModel (ext (pre ++ F)) M) {G Gf : Globals}
    {cds : List PartialHorn.Defn} (hbase : G.base = sig.length + pre.length)
    (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true) (hc : compileDefs G = some cds)
    {ds : List ConvDecl} {Ef : Array Entry} (h : checkConvDev G #[] ds = some (Gf, Ef))
    (hF : compileDefs Gf = some F) :
    ∀ (j : ℕ) (e : Entry), Ef[j]? = some e → e.Valid M Gf :=
  have hf := le_of_foldlM (fun (d : ConvDecl) G E ↦ d.step G E) ConvDecl.le_of_step ds h
  (devInv_foldlM (fun (d : ConvDecl) G E ↦ d.step G E) ConvDecl.le_of_step
    (fun hinv hs hle ↦ hinv.convStep hM hF (hf.2.1.symm.trans hbase) hs hle) ds h
    (devInv_init hM hbase hok hc hf hF)).entries

end Geb.FreeTopos.Internal

end
