/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.RepresentLogic
public import Geb.Prototypes.FreeTopos.TranslationKernel
public import GebTests.Prototypes.FreeTopos.DatatypeProgramRuns

set_option doc.verso true in
/-!
# The prelude's fold and the passes' runs represent Lean's folds

The statements about the compilers' passes are written with two term formers: the prelude's
right fold of a list by a function and a value
({name}`GebTests.Prototypes.FreeTopos.Datatypes.foldrT`), and a run, the state a step function
leaves after the elements of a list in order
({name}`GebTests.Prototypes.FreeTopos.Datatypes.runT`), itself a right fold of the elements'
continuations. Where their parts represent functions of Lean, the fold represents the right
fold of lists and the run the left fold of the step.

## Main statements

* {lit}`repC_foldrT` — the prelude's right fold represents the right fold of lists.
* {lit}`repC_runT` — a run represents the left fold of its step.

## Tags

internal language, logical relation, representation, list, fold, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Certified.DatatypeFolds

open Geb Geb.FreeTopos Geb.FreeTopos.Translation GebTests.Prototypes.FreeTopos.Datatypes
open Internal (Term RepC repC_var repC_lam repC_app repC_pair repC_fst repC_snd repC_listRec
  envRep_std₂ envRep_ext objVal_one objVal_exp objVal_prod isTy_exp isTy_prod)
open Sorts

/-- The fold that defines the prelude's right fold, at the pair of a function and a value, is
the right fold by them. -/
theorem foldr_pair {α β : Type} (f : α → β → β) (z : β) :
    ∀ xs : List α, List.foldr (fun x (r : (α → β → β) × β → β) p ↦ p.1 x (r p)) (fun p ↦ p.2)
      xs (f, z) = xs.foldr f z :=
  List.rec rfl fun x _ ih ↦ congrArg (f x) ih

/-- The right fold of continuations that defines a run is the left fold of the step. -/
theorem foldr_run {α σ : Type} (step : σ → α → σ) :
    ∀ (xs : List α) (s : σ), List.foldr (fun x (k : σ → σ) s ↦ k (step s x)) (fun s ↦ s) xs s =
      xs.foldl step s :=
  List.rec (fun _ ↦ rfl) fun x _ ih s ↦ ih (step s x)

variable {G : Internal.Globals} {ds : List PartialHorn.Defn} {X : PartialHorn.Tree}
  {e : List (PartialHorn.Tree × PartialHorn.Tree)} {S A : Type} {R : S → A → Prop}

/-- The prelude's right fold of a list by a function and a value represents the right fold of
the list they represent. -/
theorem repC_foldrT {a b : PartialHorn.Tree} {SA VA SB VB : Type} {RA : SA → VA → Prop}
    {RB : SB → VB → Prop} (hta : Internal.IsTy G 0 a = true) (htb : Internal.IsTy G 0 b = true)
    (ha : ObjVal [] (unfoldTerm sig ds a) VA) (hb : ObjVal [] (unfoldTerm sig ds b) VB)
    {f z xs : Term} {Ff : S → SA → SB → SB} {Fz : S → SB} {Fxs : S → List SA}
    (hf : RepC G 0 ds [] f X e (exp a (exp b b)) R (Rep.exp RA (Rep.exp RB RB)) Ff)
    (hz : RepC G 0 ds [] z X e b R RB Fz)
    (hxs : RepC G 0 ds [] xs X e (list a) R (Rep.list RA) Fxs) :
    RepC G 0 ds [] (foldrT a b f z xs) X e b R RB fun s ↦ (Fxs s).foldr (Ff s) (Fz s) := by
  have hF := objVal_exp ha (objVal_exp hb hb)
  have hP := objVal_prod hF hb
  have hc := objVal_exp hP hb
  have htP : Internal.IsTy G 0 (prod (exp a (exp b b)) b) = true := by
    simp [isTy_prod, isTy_exp, hta, htb]
  -- the start, the pair's value, under the pair
  have hz' := repC_lam (G := G) (n := 0) htP objVal_one hP
    (repC_snd (repC_var (i := 0)
      (envRep_ext (R := Rep.unit) objVal_one hP .nil
        (Rep.prod (Rep.exp RA (Rep.exp RB RB)) RB)) rfl) hF hb)
  -- the step, in an element and the rest's function, under the pair
  have hes := envRep_ext (objVal_prod ha hc) hP
    (envRep_std₂ (ds := ds) (ρ := []) ha hc RA
      (Rep.exp (Rep.prod (Rep.exp RA (Rep.exp RB RB)) RB) RB))
    (Rep.prod (Rep.exp RA (Rep.exp RB RB)) RB)
  have hs' := repC_lam (G := G) (n := 0) htP (objVal_prod ha hc) hP
    (repC_app
      (repC_app (repC_fst (repC_var (i := 0) hes rfl) hF hb) (repC_var (i := 2) hes rfl) ha
        (objVal_exp hb hb))
      (repC_app (repC_var (i := 1) hes rfl) (repC_var (i := 0) hes rfl) hP hb) hb hb)
  exact repC_congr (repC_app (repC_listRec hxs hz' hs' ha) (repC_pair hf hz) hP hb)
    fun s ↦ foldr_pair (Ff s) (Fz s) (Fxs s)

/-- A run over a list from a state represents the left fold, over the list its list represents
and from the state its state represents, of the function its step represents in the
environment extended by an element, a continuation and a state. -/
theorem repC_runT {a st : PartialHorn.Tree} {SA VA SSt VSt : Type} {RA : SA → VA → Prop}
    {RSt : SSt → VSt → Prop} (hta : Internal.IsTy G 0 a = true)
    (hts : Internal.IsTy G 0 st = true) (ha : ObjVal [] (unfoldTerm sig ds a) VA)
    (hst : ObjVal [] (unfoldTerm sig ds st) VSt) {ents : List (Internal.RepEntry S)}
    (he : Internal.EnvRep ds [] e R ents) (hX : ObjVal [] (unfoldTerm sig ds X) A)
    {step : Term → Term → Term} {xs s : Term} {StepF : S → SSt → SA → SSt}
    {Fxs : S → List SA} {Fs : S → SSt}
    (hstep : RepC G 0 ds [] (step (v 0) (v 2)) (prod (prod (prod X a) (exp st st)) st)
      (Internal.extEnv (prod (prod X a) (exp st st)) st
        (Internal.extEnv (prod X a) (exp st st) (Internal.extEnv X a e))) st
      (Rep.prod (Rep.prod (Rep.prod R RA) (Rep.exp RSt RSt)) RSt) RSt
      fun q ↦ StepF q.1.1.1 q.2 q.1.1.2)
    (hxs : RepC G 0 ds [] xs X e (list a) R (Rep.list RA) Fxs)
    (hs : RepC G 0 ds [] s X e st R RSt Fs) :
    RepC G 0 ds [] (runT a st step xs s) X e st R RSt
      fun σ ↦ (Fxs σ).foldl (StepF σ) (Fs σ) := by
  have hC := objVal_exp hst hst
  have htC : Internal.IsTy G 0 (exp st st) = true := by simp [isTy_exp, hts]
  have hX₁ := objVal_prod hX ha
  have hX₂ := objVal_prod hX₁ hC
  have he₃ := envRep_ext hX₂ hst (envRep_ext hX₁ hC (envRep_ext hX ha he RA) (Rep.exp RSt RSt))
    RSt
  -- the element's continuation: the rest's, after the step
  have hf := repC_lam (G := G) (n := 0) hta hX ha
    (repC_lam (G := G) (n := 0) htC hX₁ hC
      (repC_lam (G := G) (n := 0) hts hX₂ hst
        (repC_app (repC_var (i := 1) he₃ rfl) hstep hst hst)))
  have hz := repC_lam (G := G) (n := 0) hts hX hst
    (repC_var (i := 0) (envRep_ext hX hst he RSt) rfl)
  exact repC_congr (repC_app (repC_foldrT hta htC ha hC hf hz hxs) hs hst hst)
    fun σ ↦ foldr_run (StepF σ) (Fxs σ) (Fs σ)

end GebTests.Prototypes.FreeTopos.Certified.DatatypeFolds

end
