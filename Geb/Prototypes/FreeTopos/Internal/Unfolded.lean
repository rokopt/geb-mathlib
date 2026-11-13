/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Development
public import Geb.Prototypes.PartialHorn.WellFormed

set_option doc.verso true in
/-!
# A valid formula, unfolded, is true in the models of the theory

A formula of the internal language that is valid, without hypotheses, in every model of the
constants' extension in which their invariant holds compiles in its context to an arrow that,
with every definition unfolded, is true in every model of the theory of a topos itself. The
statement is that of a formula proved in a development checked from no entries
({name}`Geb.FreeTopos.Internal.valid_unfoldAll_holds_of_checkDev`), with the validity given in
place of the check: so it reads a theorem whose validity is composed from developments checked
after one another's statements ({lit}`Geb.FreeTopos.Internal.valid_of_checkAfter`), which no
one development proves from no entries. The models of the theory have no operation for a
constant, so a formula's meaning in one of them, such as the topos of types and functional
relations, is its unfolded arrow's value.

## Main definitions

* {lit}`Globals.accepted` — the decision that the constants compile, are accepted by the check,
  and compile to well-formed definitions.

## Main statements

* {lit}`valid_unfoldAll_holds_of_valid` — a valid formula's unfolded arrow is true in every
  model of the theory.
* {lit}`Globals.of_accepted` — what the decision of the constants accepts.

## Tags

internal language, development, soundness, definitional extension
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree Model IsModel)
open Sorts

universe v

/-- A formula in a context of types, valid without hypotheses in every model of the constants'
extension in which their invariant holds, compiles in its context to an arrow that, with every
definition unfolded, is true in every model of the theory, when the check accepts the constants
and their definitions are well formed. -/
theorem valid_unfoldAll_holds_of_valid {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds)) {a : Thm}
    (hctx : a.ctx.all (IsTy G a.arity) = true)
    (hcon : typeIn G a.arity a.ctx a.concl = some omega) (hnil : a.hyps = [])
    (hall : ∀ N : Model.{v} (ext (pre ++ cds)).sig, IsModel (ext (pre ++ cds)) N →
      DevInv N G G #[] → a.Valid N G) :
    ∃ C, compile G a.arity a.concl (ctxObj a.ctx) (stdEnv a.ctx) = some (C, omega) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ cds)
          ⟨List.replicate a.arity obj, [], ⟨C, comp tru (bang (ctxObj a.ctx))⟩⟩).Valid M := by
  obtain ⟨⟨C, C'⟩, hC, hC'⟩ := Option.map_eq_some_iff.mp (typeIn_eq_some.mp hcon)
  obtain rfl : C' = omega := hC'
  refine ⟨C, hC, fun M hM ↦ ?_⟩
  have hinv := devInv_init (isModel_point_ext hwf) hbase hok hc (Globals.Le.refl G) hc
  have hdefs := fun k d (hd : G.defs[k]? = some d) ↦ getElem?_sig_compileDefs hbase hc hd
  have hsC := (compile_sortOf (defs := pre ++ cds) hinv.wf hinv.sorts hdefs _ _ _ _ hC
    (sortOf_ctxObj hdefs _ hctx) (sortOf_stdEnv hdefs _ hctx)).1
  refine PartialHorn.valid_unfoldAll (pre ++ cds) theory M hM theory_ofSig hwf _ ?_ ?_
  · intro q hq
    obtain rfl : q = ⟨C, comp tru (bang (ctxObj a.ctx))⟩ := by simpa using hq
    exact ⟨⟨arr, hsC⟩, ⟨arr, sortOf_comp (sortOf_op rfl rfl)
      (sortOf_bang (sortOf_ctxObj hdefs _ hctx))⟩⟩
  · intro N hN ρ hρ _
    have hinvN := devInv_init hN hbase hok hc (Globals.Le.refl G) hc
    obtain ⟨-, -, -, hv⟩ : a.Valid N G := hall N hN hinvN
    obtain ⟨-, -, hfN⟩ := hv ρ hρ
    have hstd := stdEnv_hom hN hinvN.defs.2 hρ _ hctx
    have hH := hfN _ _ hstd (map_snd_stdEnv _) (by rw [hnil]; exact fun _ h ↦ by simp at h) _ hC
    obtain ⟨w, hw, -⟩ := (truth_hom hN hstd.1).exists_eval
    exact ⟨w, hH.2.trans hw, hw⟩

/-- Whether the constants are ones whose developments the models of the theory read: their
definitions compile and come after no other definitions of the combinators, the check accepts
them, and the definitions they compile to are well formed. -/
def Globals.accepted (G : Globals) : Bool :=
  match compileDefs G with
  | some cds => decide (G.base = sig.length) && G.ok (ExtEnv.ofDefs cds) &&
      PartialHorn.defnsWFb cds sig
  | none => false

/-- What the decision of the constants accepts: definitions they compile to, after no others,
which the check accepts and which are well formed. -/
theorem Globals.of_accepted {G : Globals} (h : G.accepted = true) :
    ∃ cds, compileDefs G = some cds ∧ G.base = sig.length ∧
      G.ok (ExtEnv.ofDefs cds) = true ∧ PartialHorn.DefnsWF sig cds := by
  unfold Globals.accepted at h
  split at h
  · next cds hc =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨cds, hc, h.1.1, h.1.2, PartialHorn.defnsWF_of_defnsWFb cds sig h.2⟩
  · exact (Bool.false_ne_true h).elim

end Geb.FreeTopos.Internal

end
