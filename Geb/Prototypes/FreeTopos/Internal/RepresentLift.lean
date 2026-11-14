/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Represent
public import Geb.Prototypes.FreeTopos.Internal.Square

set_option doc.verso true in
/-!
# A representation over constants is one over constants that extend them

Constants extend others when the first's primitive arrows and definitions are the others'
before further ones ({name}`Geb.FreeTopos.Internal.Globals.Le`), and then the definitions the
first compile to are those the others compile to, before further ones. A term over the first
compiles over the others to the same arrow ({name}`Geb.FreeTopos.Internal.compile_mono`), and
the unfolding of the further definitions leaves the arrow, whose operations are the first's
({name}`Geb.FreeTopos.unfoldTerm_append`): so a term's representation over the first
({name}`Geb.FreeTopos.Internal.RepC`) is one over the others, and the arrow of a definition of
the first represents over the others what it represents over the first. The representations of
a translated program's definitions and of the library are stated over the translation's
constants; a program that extends the translation by further definitions reads them so.

## Main statements

* {lit}`unfoldTerm_append_defn` — the unfolding of further definitions leaves a definition's
  arrow.
* {lit}`repC_le` — a term's representation over constants is one over constants that extend
  them.

## Tags

internal language, logical relation, representation, definitional extension
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts

variable {ds ext : List PartialHorn.Defn}

/-- The unfolding of a list of well-formed definitions with further ones after them leaves the
body of one of them as their own unfolding does: its operations are those before it. -/
theorem unfoldTerm_append_defn (hwf : PartialHorn.DefnsWF sig ds) {k : ℕ} {d : PartialHorn.Defn}
    (hk : ds[k]? = some d) : unfoldTerm sig (ds ++ ext) d.body = unfoldTerm sig ds d.body := by
  have hs := (defnsWF_getElem ds sig hwf hk).sort
  have hops := PartialHorn.opsBelow_of_sortOf d.body hs
  refine unfoldTerm_append ext ds sig d.body (PartialHorn.opsBelow_mono ?_ d.body hops)
  rw [extendAll_eq, extendAll_eq, List.length_append, List.length_append, List.length_map,
    List.length_map, List.length_take]
  omega

/-- A term's representation in the standard environment of a context of types, over constants
the check accepts, is one over constants that extend them and compile to their definitions
before further ones. -/
theorem repC_le {G G' : Globals} (hle : G.Le G') (hbase : G.base = sig.length)
    (hok : G.ok (ExtEnv.ofDefs ds) = true) (hc : compileDefs G = some ds) {n : ℕ}
    {Γ : List Tree} (hΓ : Γ.all (IsTy G n) = true) {ρ : List relTopos.model.Val} {t : Term}
    {a : Tree} {S T A B : Type} {R : S → A → Prop} {R' : T → B → Prop} {F : S → T}
    (h : RepC G n ds ρ t (ctxObj Γ) (stdEnv Γ) a R R' F) :
    RepC G' n (ds ++ ext) ρ t (ctxObj Γ) (stdEnv Γ) a R R' F := by
  obtain ⟨f, hf, hR⟩ := h
  have hdefs := fun k d (hd : G.defs[k]? = some d) ↦
    getElem?_sig_compileDefs (pre := []) (by simpa using hbase) hc hd
  have hs := (compile_sortOf (defs := [] ++ ds) (Globals.wf_of_ok hok)
    (fun k p hp ↦ sortOf_prims_of_ok (by simpa using hok) hp) hdefs _ _ _ _ hf
    (sortOf_ctxObj hdefs Γ hΓ) (sortOf_stdEnv hdefs Γ hΓ)).1
  have hops := PartialHorn.opsBelow_of_sortOf _ hs
  rw [List.nil_append, PartialHorn.Theory.extendAll_sig] at hops
  exact ⟨f, compile_mono hle _ _ _ _ hf, by rw [unfoldTerm_append ext ds sig f hops]; exact hR⟩

end Geb.FreeTopos.Internal

end
