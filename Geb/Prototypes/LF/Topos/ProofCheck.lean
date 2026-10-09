/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Soundness
public import Geb.Prototypes.FreeTopos.Internal.SyntaxLaws
public import Geb.Prototypes.LF.Topos.Compose
public import Geb.Prototypes.LF.Topos.Proofs
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The checking of the derivations decoded from proofs

The results of the internal language's checker ({name}`Geb.FreeTopos.Internal.check`) at the
derivations the decoding of proofs builds ({name}`Geb.LF.Topos.decPf`): at each rule they use, the
rewriting it performs and the conditions under which it proves a formula, and at the composite
derivations the decoding builds, the rewriting or the proof they perform.

## Main statements

* {lit}`check_join`, {lit}`check_cut`, {lit}`check_conv`, {lit}`check_convFrom`,
  {lit}`check_propExt`, {lit}`check_funExt`, {lit}`check_natIndHyp`, {lit}`check_listIndHyp` —
  the proof rules.
* {lit}`check_natZero`, {lit}`check_natSucc`, {lit}`check_listNil`, {lit}`check_listCons` — the
  computations of the folds.
* {lit}`check_leibD`, {lit}`check_indD`, {lit}`check_natIndD`, {lit}`check_listIndD` — the
  substitution of equals and the induction.

## Tags

internal language, derivation, proof checker, rewriting
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Deriv Globals Entry check checkStep rootStep typeIn instVar weaken1
  check_node ctxObj stdEnv extEnv)

variable {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List PartialHorn.Tree} {Φ : List Term}

/-- The identity rewriting rewrites a term to itself. -/
@[simp] theorem check_refl (t : Term) : (check G E n reflD).1 Γ Φ t = some t := by
  rw [check_node]
  rfl

/-- A rule of the language's equations, other than the identity, the sequence and the
congruence, rewrites at the root. -/
theorem check_rule (r : FreeTopos.Internal.Rule)
    (hr : r ≠ .refl ∧ r ≠ .trans ∧ r ≠ .cong) (t : Term) :
    (check G E n (ruleD r)).1 Γ Φ t = rootStep G E n Γ Φ r t := by
  rw [check_node]
  obtain ⟨h₁, h₂, h₃⟩ := hr
  cases r <;> first | exact absurd rfl h₁ | exact absurd rfl h₂ | exact absurd rfl h₃ | rfl

/-- A proof of an equation by two rewritings to one term. -/
theorem check_join {d₁ d₂ : Deriv} {t u v : Term} (h₁ : (check G E n d₁).1 Γ Φ t = some v)
    (h₂ : (check G E n d₂).1 Γ Φ u = some v) :
    (check G E n (joinD d₁ d₂)).2 Γ Φ (Term.eq t u) = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil, checkStep, FreeTopos.Internal.eqParts, Term.eq,
    RoseTree.label_node, RoseTree.children_node, h₁, h₂, decide_true]

/-- A hypothesis proves itself. -/
theorem check_hyp {h : ℕ} {φ : Term} (hφ : Φ[h]? = some φ) :
    (check G E n (ruleD (.hyp h))).2 Γ Φ φ = true := by
  rw [check_node]
  simp only [List.map_nil, checkStep, hφ, decide_true]

/-- A cut through a formula: the formula proved, and the goal proved under it. -/
theorem check_cut {ψ φ : Term} {p q : Deriv} (hψ : typeIn G n Γ ψ = some FreeTopos.omega)
    (hp : (check G E n p).2 Γ Φ ψ = true) (hq : (check G E n q).2 Γ (Φ ++ [ψ]) φ = true) :
    (check G E n (nd (.cut ψ) [p, q])).2 Γ Φ φ = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil, checkStep, hψ, decide_true, hp, hq, Bool.and_self]

/-- A goal rewritten, and the result proved. -/
theorem check_conv {φ φ' : Term} {d p : Deriv} (hd : (check G E n d).1 Γ Φ φ = some φ')
    (hp : (check G E n p).2 Γ Φ φ' = true) :
    (check G E n (nd .conv [d, p])).2 Γ Φ φ = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil, checkStep, hd, hp]

/-- A formula proved and rewritten to the goal. -/
theorem check_convFrom {ψ φ : Term} {d p : Deriv} (hψ : typeIn G n Γ ψ = some FreeTopos.omega)
    (hd : (check G E n d).1 Γ Φ ψ = some φ) (hp : (check G E n p).2 Γ Φ ψ = true) :
    (check G E n (nd (.convFrom ψ) [d, p])).2 Γ Φ φ = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil, checkStep, hψ, hd, and_self, decide_true, hp,
    Bool.and_self]

/-- Propositional extensionality: two formulas, each proved under the other, are equal. -/
theorem check_propExt {α β : Term} {p q : Deriv} (hα : typeIn G n Γ α = some FreeTopos.omega)
    (hβ : typeIn G n Γ β = some FreeTopos.omega) (hp : (check G E n p).2 Γ (Φ ++ [α]) β = true)
    (hq : (check G E n q).2 Γ (Φ ++ [β]) α = true) :
    (check G E n (nd .propExt [p, q])).2 Γ Φ (Term.eq α β) = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil, checkStep, FreeTopos.Internal.eqParts, Term.eq,
    RoseTree.label_node, RoseTree.children_node, hα, hβ, and_self, decide_true, hp, hq,
    Bool.and_self]

/-- Function extensionality: two functions whose applications to a new variable are proved equal
are equal. -/
theorem check_funExt {f g : Term} {a b : PartialHorn.Tree} {p : Deriv}
    (hf : typeIn G n Γ f = some (FreeTopos.exp a b))
    (hp : (check G E n p).2 (a :: Γ) (Φ.map weaken1)
      (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0))) = true) :
    (check G E n (nd .funExt [p])).2 Γ Φ (Term.eq f g) = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil, checkStep, FreeTopos.Internal.eqParts, Term.eq,
    RoseTree.label_node, RoseTree.children_node, hf, Option.bind_some,
    FreeTopos.Internal.expParts_eq_some.mpr rfl]
  exact hp

/-- The congruence at a node whose children are each in the node's context, or rewritten by the
identity: each child rewritten by its derivation in the node's context. -/
theorem check_cong_same {l : FreeTopos.Internal.Label} {ds : List Deriv} {ts ts' : List Term}
    (hsame : ∀ (k : ℕ) (hk : k < ds.length),
      FreeTopos.Internal.sameCtx l k = true ∨ ds[k].label.isRefl = true)
    (hlen : ds.length = ts.length) (hlen' : ts'.length = ts.length)
    (hk : ∀ (k : ℕ) (h₁ : k < ds.length) (h₂ : k < ts.length) (h₃ : k < ts'.length),
      (check G E n ds[k]).1 Γ Φ ts[k] = some ts'[k]) :
    (check G E n (nd .cong ds)).1 Γ Φ (RoseTree.node l ts) = some (RoseTree.node l ts') := by
  rw [check_node]
  have hall : ((ds.map fun c ↦ (c, check G E n c)).map Prod.fst).zipIdx.all
      (fun (d, i) ↦ FreeTopos.Internal.sameCtx l i || d.label.isRefl) = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨k, hk', rfl⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_zipIdx, List.length_map] at hk'
    simp only [List.getElem_zipIdx, List.getElem_map, zero_add, Bool.or_eq_true]
    exact hsame k hk'
  simp only [checkStep, RoseTree.label_node, RoseTree.children_node,
    FreeTopos.Internal.congCtxs, hall, ↓reduceIte, Option.bind_eq_bind, Option.bind_some,
    List.length_map, hlen, true_and, Option.pure_def]
  rw [show ((List.map (fun c ↦ (c, check G E n c)) ds).zip
      ((List.map (fun _ ↦ (Γ, Φ)) ts).zip ts)).mapM
      (fun x ↦ x.1.2.1 x.2.1.1 x.2.1.2 x.2.2) = some ts' from
    (PartialHorn.mapM_eq_some_iff _ _).mpr (List.ext_getElem (by simp [hlen, hlen']) fun k h₁ h₂ ↦
      by
        simp only [List.length_map, List.length_zip, List.length_map, hlen, Nat.min_self] at h₁
        simpa using hk k (by omega) h₁ (by simpa using h₂))]
  rfl

/-- β at an application of an abstraction. -/
theorem check_beta (a : PartialHorn.Tree) (b u : Term) :
    (check G E n (ruleD .beta)).1 Γ Φ (Term.app (Term.lam a b) u) =
      some (Term.subst b (instVar u)) := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  rfl

/-- The first component of a pair. -/
theorem check_fstPair (t u : Term) :
    (check G E n (ruleD .fstPair)).1 Γ Φ (Term.fst (Term.pair t u)) = some t := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  rfl

/-- The second component of a pair. -/
theorem check_sndPair (t u : Term) :
    (check G E n (ruleD .sndPair)).1 Γ Φ (Term.snd (Term.pair t u)) = some u := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  rfl

/-- The pair of a term's components. -/
theorem check_pairEta (t : Term) :
    (check G E n (ruleD .pairEta)).1 Γ Φ (Term.pair (Term.fst t) (Term.snd t)) = some t := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp [rootStep, Term.pair, Term.fst, Term.snd]

/-- A term of the terminal type is its element. -/
theorem check_unitEta {t : Term} (ht : typeIn G n Γ t = some FreeTopos.one) :
    (check G E n (ruleD .unitEta)).1 Γ Φ t = some Term.star := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp [rootStep, ht]

/-- A hypothesis equation rewrites its left side to its right, or its right to its left. -/
theorem check_rwHyp {i : ℕ} {flip : Bool} {t u : Term} (h : Φ[i]? = some (Term.eq t u)) :
    (check G E n (ruleD (.rwHyp i flip))).1 Γ Φ (if flip then u else t) =
      some (if flip then t else u) := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp only [rootStep, h, Option.bind_some, FreeTopos.Internal.eqParts, Term.eq,
    RoseTree.label_node, RoseTree.children_node, Option.bind_eq_bind]
  cases flip <;> simp

/-- The congruence at a node of two children in its context. -/
theorem check_cong₂ {l : FreeTopos.Internal.Label} (h₀ : FreeTopos.Internal.sameCtx l 0 = true)
    (h₁ : FreeTopos.Internal.sameCtx l 1 = true) {d₁ d₂ : Deriv} {t₁ t₂ t₁' t₂' : Term}
    (hd₁ : (check G E n d₁).1 Γ Φ t₁ = some t₁') (hd₂ : (check G E n d₂).1 Γ Φ t₂ = some t₂') :
    (check G E n (nd .cong [d₁, d₂])).1 Γ Φ (RoseTree.node l [t₁, t₂]) =
      some (RoseTree.node l [t₁', t₂']) :=
  check_cong_same (fun k hk ↦ match k, hk with
      | 0, _ => .inl h₀
      | 1, _ => .inl h₁) rfl rfl fun k hk _ _ ↦ match k, hk with
    | 0, _ => hd₁
    | 1, _ => hd₂

variable {kz ks kn kc : ℕ}

/-- The computation of the fold at zero: the start. -/
theorem check_natZero (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim) (z s : Term) :
    (check G E n (ruleD (.natZero kz))).1 Γ Φ (Term.natRec z s (Term.arr kz [] Term.star)) =
      some z := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp [FreeTopos.Internal.rootStep, Term.natRec, Term.arr, hz, Term.star]

/-- The computation of the fold at a successor: the step at the fold of the predecessor. -/
theorem check_natSucc (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim) (z s m : Term) :
    (check G E n (ruleD (.natSucc ks))).1 Γ Φ (Term.natRec z s (Term.arr ks [] m)) =
      some (Term.subst s (instVar (Term.natRec z s m))) := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp [FreeTopos.Internal.rootStep, Term.natRec, Term.arr, hs]

/-- The computation of the fold of a list at the empty list: the start. -/
theorem check_listNil (hn : G.prims[kn]? = some FreeTopos.Internal.nilPrim) (a : PartialHorn.Tree)
    (z s : Term) :
    (check G E n (ruleD (.listNil kn))).1 Γ Φ (Term.listRec z s (Term.arr kn [a] Term.star)) =
      some z := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp [FreeTopos.Internal.rootStep, Term.listRec, Term.arr, hn, Term.star]

/-- The computation of the fold of a list at a construction: the step at the element and the fold
of the rest. -/
theorem check_listCons (hc : G.prims[kc]? = some FreeTopos.Internal.consPrim)
    (a : PartialHorn.Tree) (z s h t : Term) :
    (check G E n (ruleD (.listCons kc))).1 Γ Φ
      (Term.listRec z s (Term.arr kc [a] (Term.pair h t))) =
      some (Term.subst s (FreeTopos.Internal.instVar2 (Term.listRec z s t) h)) := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp [FreeTopos.Internal.rootStep, Term.listRec, Term.arr, Term.pair, hc]

section Typing

variable {m : ℕ}

/-- An equation of two terms of one type is a formula. -/
theorem typeIn_eq {t u : Term} {a : PartialHorn.Tree} (ht : typeIn G m Γ t = some a)
    (hu : typeIn G m Γ u = some a) : typeIn G m Γ (Term.eq t u) = some FreeTopos.omega := by
  obtain ⟨⟨f, a₁⟩, hf, ha₁⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨⟨g, a₂⟩, hg, ha₂⟩ := Option.map_eq_some_iff.mp hu
  dsimp only at ha₁ ha₂
  subst ha₁ ha₂
  rw [typeIn, Term.eq, FreeTopos.Internal.compile_eq_iff.mpr ⟨t, u, rfl, f, _, hf, g, hg, rfl⟩]
  rfl

/-- An application of a function to an argument of its domain is of its codomain. -/
theorem typeIn_app {f u : Term} {a b : PartialHorn.Tree}
    (hf : typeIn G m Γ f = some (FreeTopos.exp a b)) (hu : typeIn G m Γ u = some a) :
    typeIn G m Γ (Term.app f u) = some b := by
  obtain ⟨⟨p, c⟩, hp, hc⟩ := Option.map_eq_some_iff.mp hf
  obtain ⟨⟨g, a₁⟩, hg, ha₁⟩ := Option.map_eq_some_iff.mp hu
  dsimp only at hc ha₁
  subst hc ha₁
  rw [typeIn, Term.app,
    FreeTopos.Internal.compile_app_iff.mpr ⟨f, u, rfl, p, _, b, hp, g, hg, rfl⟩]
  rfl

/-- An abstraction over a type of a term of a type in the extended context is of the
exponential. -/
theorem typeIn_lam {a c : PartialHorn.Tree} {b : Term} (ha : FreeTopos.Internal.IsTy G m a = true)
    (hb : typeIn G m (a :: Γ) b = some c) :
    typeIn G m Γ (Term.lam a b) = some (FreeTopos.exp a c) := by
  obtain ⟨r, hr, hc⟩ := Option.map_eq_some_iff.mp hb
  subst hc
  obtain ⟨f, hf⟩ := FreeTopos.Internal.compile_retype b _ _ r hr
    (FreeTopos.prod (ctxObj Γ) a) (extEnv (ctxObj Γ) a (stdEnv Γ))
    (by simp [extEnv, List.map_map, Function.comp_def, FreeTopos.Internal.map_snd_stdEnv])
  rw [typeIn, Term.lam, FreeTopos.Internal.compile_lam_iff.mpr ⟨b, f, r.2, rfl, ha, hf, rfl⟩]
  rfl

/-- The element of the terminal object is of it. -/
theorem typeIn_star : typeIn G m Γ Term.star = some FreeTopos.one := by
  rw [typeIn, Term.star, FreeTopos.Internal.compile_star_iff.mpr ⟨rfl, rfl⟩]
  rfl

/-- The formula true is a formula. -/
theorem typeIn_truth : typeIn G m Γ truth = some FreeTopos.omega :=
  typeIn_eq typeIn_star typeIn_star

/-- A term of a type has variables that are leaves. -/
theorem varLeaves_of_typeIn {t : Term} {a : PartialHorn.Tree} (h : typeIn G m Γ t = some a) :
    Term.VarLeaves t = true := by
  obtain ⟨r, hr, -⟩ := Option.map_eq_some_iff.mp h
  exact Term.varLeaves_of_compile t _ _ r hr

/-- Formulas weakened by a variable lower to themselves. -/
theorem lowerHyps_map_weaken1 {Φ : List Term}
    (h : ∀ φ ∈ Φ, typeIn G m Γ φ = some FreeTopos.omega) :
    FreeTopos.Internal.lowerHyps G m Γ (Φ.map weaken1) = some Φ := by
  rw [FreeTopos.Internal.lowerHyps, PartialHorn.mapM_eq_some_iff, List.map_map]
  refine List.map_congr_left fun φ hφ ↦ ?_
  have hl : Term.rename (weaken1 φ) (· - 1) = φ := by
    rw [weaken1, Term.rename_rename φ _ _ id fun i ↦ Nat.add_sub_cancel i 1,
      Term.rename_id φ (varLeaves_of_typeIn (h φ hφ)) id fun _ ↦ rfl]
  simp only [Function.comp_apply, hl, h φ hφ, and_self, ↓reduceIte]

end Typing

/-- A decision of a proposition that holds, by whichever instance. -/
theorem decide_eq_true_of {p : Prop} {inst : Decidable p} (h : p) : @decide p inst = true :=
  match inst with
    | isTrue _ => rfl
    | isFalse hn => absurd h hn

/-- Induction on the natural numbers at the innermost variable: the formula at zero under the
hypotheses lowered, and at the successor under the formula. -/
theorem check_natIndHyp {Γ₀ : List PartialHorn.Tree} {Φ' : List Term} {φ : Term} {p₀ p₁ : Deriv}
    (hlow : FreeTopos.Internal.lowerHyps G n Γ₀ Φ = some Φ')
    (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim)
    (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim)
    (hφ : typeIn G n (FreeTopos.nat :: Γ₀) φ = some FreeTopos.omega)
    (hp₀ : (check G E n p₀).2 Γ₀ Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))) = true)
    (hp₁ : (check G E n p₁).2 (FreeTopos.nat :: Γ₀) (Φ ++ [φ])
      (FreeTopos.Internal.natSuccAt ks φ) = true) :
    (check G E n (nd (.natIndHyp kz ks) [p₀, p₁])).2 (FreeTopos.nat :: Γ₀) Φ φ = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil]
  dsimp only [checkStep]
  rw [hlow]
  dsimp only
  rw [decide_eq_true_of ⟨rfl, hz, hs, hφ⟩, hp₀, hp₁]
  rfl

/-- Induction on a list at the innermost variable: the formula at the empty list under the
hypotheses lowered, and at the construction of an element and the variable under those
hypotheses weakened past the element and the formula. -/
theorem check_listIndHyp {Γ₀ : List PartialHorn.Tree} {a : PartialHorn.Tree} {Φ' : List Term}
    {φ : Term} {p₀ p₁ : Deriv} (hlow : FreeTopos.Internal.lowerHyps G n Γ₀ Φ = some Φ')
    (hn : G.prims[kn]? = some FreeTopos.Internal.nilPrim)
    (hc : G.prims[kc]? = some FreeTopos.Internal.consPrim)
    (hφ : typeIn G n (FreeTopos.list a :: Γ₀) φ = some FreeTopos.omega)
    (hp₀ : (check G E n p₀).2 Γ₀ Φ' (Term.subst φ (instVar (Term.arr kn [a] Term.star))) = true)
    (hp₁ : (check G E n p₁).2 (FreeTopos.list a :: a :: Γ₀)
      (Φ'.map FreeTopos.Internal.weaken2 ++ [FreeTopos.Internal.weakenElem φ])
      (FreeTopos.Internal.listConsAt kc a φ) = true) :
    (check G E n (nd (.listIndHyp kn kc) [p₀, p₁])).2 (FreeTopos.list a :: Γ₀) Φ φ = true := by
  rw [check_node]
  simp only [List.map_cons, List.map_nil]
  dsimp only [checkStep]
  rw [FreeTopos.Internal.listPart_eq_some.mpr rfl, hlow]
  dsimp only
  rw [decide_eq_true_of ⟨hn, hc, hφ⟩, hp₀, hp₁]
  rfl

/-- The substitution at the innermost variable is the instantiation. -/
theorem substAt_zero (u : Term) : substAt 0 u = instVar u := by
  funext i
  rcases i with _ | i
  · rfl
  · simp [substAt, instVar]

/-- The substitution of equals: the motive at {lit}`u`, from the equation {lit}`t = u` and the
motive at {lit}`t`. -/
theorem check_leibD {a : PartialHorn.Tree} {pb t u : Term} {Dh Dp : Deriv}
    (ha : FreeTopos.Internal.IsTy G n a = true)
    (hpb : typeIn G n (a :: Γ) pb = some FreeTopos.omega) (ht : typeIn G n Γ t = some a)
    (hu : typeIn G n Γ u = some a) (hh : (check G E n Dh).2 Γ Φ (Term.eq t u) = true)
    (hp : (check G E n Dp).2 Γ (Φ ++ [Term.eq t u]) (Term.subst pb (instVar t)) = true) :
    (check G E n (leibD a pb t u Φ.length Dh Dp)).2 Γ Φ (Term.subst pb (instVar u)) = true := by
  have hL := typeIn_lam ha hpb
  refine check_cut (typeIn_eq ht hu) hh
    (check_convFrom (typeIn_app hL hu) (check_beta _ _ _) ?_)
  refine check_conv (φ' := Term.app (Term.lam a pb) t) (check_cong₂ rfl rfl (check_refl _)
    (check_rwHyp (flip := true)
      (by rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl))) ?_
  exact check_conv (check_beta _ _ _) hp

/-- The β-reduct of a term's weakening under a binder, abstracted and applied to the bound
variable, is the term. -/
theorem subst_rename_liftR_var0 {pb : Term} (h : Term.VarLeaves pb = true) :
    Term.subst (Term.rename pb (Term.liftR (· + 1))) (instVar (Term.var 0)) = pb := by
  rw [Term.subst_rename pb _ _ Term.var fun i ↦ by rcases i with _ | i <;> rfl,
    Term.subst_id pb h _ fun _ ↦ rfl]

/-- An induction at a term: the motive at {lit}`n'`, from the induction rule's proof of the
motive in the context extended by a variable of its type, under the hypotheses weakened past it
and the hypothesis true, which the derivation's cut and propositional extensionality add. -/
theorem check_indD {c : PartialHorn.Tree} {r : FreeTopos.Internal.Rule} {pb n' : Term}
    {D₀ Ds : Deriv} (hc : FreeTopos.Internal.IsTy G 0 c = true)
    (hpb : typeIn G 0 (c :: Γ) pb = some FreeTopos.omega) (hn : typeIn G 0 Γ n' = some c)
    (hind : (check G E 0 (nd r [D₀, Ds])).2 (c :: Γ) (Φ.map weaken1 ++ [truth]) pb = true) :
    (check G E 0 (indD c r pb n' Φ.length D₀ Ds)).2 Γ Φ (Term.subst pb (instVar n')) =
      true := by
  have hL := typeIn_lam (Γ := Γ) hc hpb
  have hR := typeIn_lam (Γ := Γ) hc (typeIn_truth (G := G) (Γ := c :: Γ))
  refine check_cut (typeIn_eq hL hR) (check_funExt hL ?_) ?_
  · refine check_conv (φ' := Term.eq pb truth) (check_cong₂ rfl rfl ?_ ?_) ?_
    · rw [show weaken1 (Term.lam c pb) = Term.lam c (Term.rename pb (Term.liftR (· + 1))) from rfl,
        check_beta, subst_rename_liftR_var0 (varLeaves_of_typeIn hpb)]
    · exact check_beta _ _ _
    · exact check_propExt hpb typeIn_truth (check_join (check_refl _) (check_refl _)) hind
  · refine check_convFrom (typeIn_app hL hn) (check_beta _ _ _) ?_
    refine check_conv (φ' := Term.app (Term.lam c truth) n')
      (check_cong₂ rfl rfl (check_rwHyp (flip := false)
        (by rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl)) (check_refl _)) ?_
    exact check_conv (check_beta _ _ _) (check_join (check_refl _) (check_refl _))

/-- The hypotheses weakened past a variable, with the hypothesis true, lower to the hypotheses
with it. -/
theorem lowerHyps_truth
    (hΦ : ∀ φ ∈ Φ, typeIn G 0 Γ φ = some FreeTopos.omega) :
    FreeTopos.Internal.lowerHyps G 0 Γ (Φ.map weaken1 ++ [truth]) = some (Φ ++ [truth]) := by
  rw [show Φ.map weaken1 ++ [truth] = (Φ ++ [truth]).map weaken1 by rw [List.map_append]; rfl]
  refine lowerHyps_map_weaken1 fun φ hφ ↦ ?_
  rcases List.mem_append.mp hφ with hφ | hφ
  · exact hΦ φ hφ
  · obtain rfl := List.mem_singleton.mp hφ
    exact typeIn_truth

/-- The induction on the natural numbers at a term: the motive at {lit}`n'`, from its base at
zero and its step, each under the hypothesis true, which the derivation's cut adds. -/
theorem check_natIndD {k : PrimIdx} (hz : G.prims[k.zero]? = some FreeTopos.Internal.zeroPrim)
    (hs : G.prims[k.succ]? = some FreeTopos.Internal.succPrim) {pb n' : Term} {D₀ Ds : Deriv}
    (hpb : typeIn G 0 (FreeTopos.nat :: Γ) pb = some FreeTopos.omega)
    (hn : typeIn G 0 Γ n' = some FreeTopos.nat)
    (hΦ : ∀ φ ∈ Φ, typeIn G 0 Γ φ = some FreeTopos.omega)
    (hD₀ : (check G E 0 D₀).2 Γ (Φ ++ [truth])
      (Term.subst pb (instVar (Term.arr k.zero [] Term.star))) = true)
    (hDs : (check G E 0 Ds).2 (FreeTopos.nat :: Γ) (Φ.map weaken1 ++ [truth] ++ [pb])
      (FreeTopos.Internal.natSuccAt k.succ pb) = true) :
    (check G E 0 (indD FreeTopos.nat (.natIndHyp k.zero k.succ) pb n' Φ.length D₀ Ds)).2 Γ Φ
      (Term.subst pb (instVar n')) = true :=
  check_indD (isTy_of_encTy G FreeTopos.nat nat rfl) hpb hn
    (check_natIndHyp (lowerHyps_truth hΦ) hz hs hpb hD₀ hDs)

/-- The induction on a list at a term: the motive at {lit}`n'`, from its base at the empty list
and its step at a construction, each under the hypothesis true, which the derivation's cut
adds. -/
theorem check_listIndD {k : PrimIdx} (hn : G.prims[k.nil]? = some FreeTopos.Internal.nilPrim)
    (hc : G.prims[k.cons]? = some FreeTopos.Internal.consPrim) {a : PartialHorn.Tree}
    (ha : FreeTopos.Internal.IsTy G 0 (FreeTopos.list a) = true) {pb n' : Term} {D₀ Ds : Deriv}
    (hpb : typeIn G 0 (FreeTopos.list a :: Γ) pb = some FreeTopos.omega)
    (hn' : typeIn G 0 Γ n' = some (FreeTopos.list a))
    (hΦ : ∀ φ ∈ Φ, typeIn G 0 Γ φ = some FreeTopos.omega)
    (hD₀ : (check G E 0 D₀).2 Γ (Φ ++ [truth])
      (Term.subst pb (instVar (Term.arr k.nil [a] Term.star))) = true)
    (hDs : (check G E 0 Ds).2 (FreeTopos.list a :: a :: Γ)
      ((Φ ++ [truth]).map FreeTopos.Internal.weaken2 ++ [FreeTopos.Internal.weakenElem pb])
      (FreeTopos.Internal.listConsAt k.cons a pb) = true) :
    (check G E 0 (indD (FreeTopos.list a) (.listIndHyp k.nil k.cons) pb n' Φ.length D₀ Ds)).2
      Γ Φ (Term.subst pb (instVar n')) = true :=
  check_indD ha hpb hn' (check_listIndHyp (lowerHyps_truth hΦ) hn hc hpb
    hD₀ hDs)

end Geb.LF.Topos

end
