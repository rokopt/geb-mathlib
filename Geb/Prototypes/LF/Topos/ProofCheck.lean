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
  {lit}`check_propExt`, {lit}`check_funExt`, {lit}`check_natIndHyp` — the proof rules.
* {lit}`check_congAlong` — the rewriting by a derivation along a variable of a simple term.
* {lit}`check_natZeroLhs`, {lit}`check_natSuccLhs` — the computations of the fold with
  parameters.
* {lit}`check_leibD`, {lit}`check_natIndD` — the substitution of equals and the induction.

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

/-- One rewriting after another rewrites by the first, then by the second. -/
theorem check_trans (d₁ d₂ : Deriv) (t : Term) :
    (check G E n (transD d₁ d₂)).1 Γ Φ t =
      ((check G E n d₁).1 Γ Φ t).bind ((check G E n d₂).1 Γ Φ) := by
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

/-- The congruence at an abstraction: its body rewritten in the context extended by the bound
variable, the hypotheses weakened, or by the identity in any. -/
theorem check_cong_lam {a : PartialHorn.Tree} {d : Deriv} {b b' : Term}
    (h : (check G E n d).1 (a :: Γ) (Φ.map weaken1) b = some b')
    (hrefl : d.label.isRefl = true → b' = b) :
    (check G E n (nd .cong [d])).1 Γ Φ (Term.lam a b) = some (Term.lam a b') := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, d = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children d).symm⟩
  by_cases hd : (RoseTree.node l cs : Deriv).label.isRefl = true
  · obtain rfl := hrefl hd
    refine check_cong_same (fun _ _ ↦ by simpa using Or.inr hd) rfl rfl fun k h₁ _ _ ↦ ?_
    obtain rfl : k = 0 := by simpa using h₁
    cases l <;> simp only [RoseTree.label_node, FreeTopos.Internal.Rule.isRefl,
      reduceCtorEq] at hd
    rcases cs with _ | ⟨c, cs⟩
    · exact check_refl _
    · rw [check_node] at h
      simp [checkStep] at h
  · rw [check_node]
    have hd' : l.isRefl = false := by simpa using hd
    have hcc : FreeTopos.Internal.congCtxs G n (.lam a) [b] Γ Φ [RoseTree.node l cs] =
        some [(a :: Γ, Φ.map weaken1)] := by
      simp [FreeTopos.Internal.congCtxs, FreeTopos.Internal.sameCtx, hd',
        FreeTopos.Internal.childCtxs]
    simp only [checkStep, Term.lam, RoseTree.label_node, RoseTree.children_node, List.map_cons,
      List.map_nil]
    rw [hcc]
    simp [h]

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

/-- One step of whether a term is built without folds and with unary abstractions: the terms the
decoding produces. -/
def simpleStep (l : FreeTopos.Internal.Label) (cs : List Bool) : Bool :=
  match l with
    | .natRec | .listRec | .roseRec _ => false
    | .lam _ => cs.length == 1 && cs.all id
    | _ => cs.all id

/-- Whether a term is built without folds and with unary abstractions. -/
def Term.Simple : Term → Bool := RoseTree.elim simpleStep

/-- The computation rule of {name}`Geb.LF.Topos.Term.Simple`. -/
theorem simple_node (l : FreeTopos.Internal.Label) (cs : List Term) :
    Term.Simple (RoseTree.node l cs) = simpleStep l (cs.map Term.Simple) :=
  RoseTree.elim_node _ l cs

/-- The children of a simple term are simple. -/
theorem simple_child {l : FreeTopos.Internal.Label} {cs : List Term}
    (h : Term.Simple (RoseTree.node l cs) = true) {c : Term} (hc : c ∈ cs) :
    Term.Simple c = true := by
  rw [simple_node] at h
  have hall : (cs.map Term.Simple).all id = true := by
    unfold simpleStep at h
    split at h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · exact (Bool.and_eq_true _ _ ▸ h).2
    · exact h
  rw [List.all_eq_true] at hall
  exact hall _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- The computation rule of {name}`Geb.LF.Topos.congAlong`. -/
theorem congAlong_node (d : Deriv) (l : FreeTopos.Internal.Label) (cs : List Term) :
    congAlong d (RoseTree.node l cs) = congAlongStep d l (cs.map fun c ↦ (c, congAlong d c)) :=
  RoseTree.para_node _ l cs

/-- The rewriting by a derivation along a variable: in a simple term, at depth {lit}`j`, where the
derivation rewrites the term {lit}`u`, weakened past the variables bound so far, to {lit}`u'`,
weakened alike, under the hypotheses weakened alike, it rewrites the term with {lit}`u`
substituted for the variable to the term with {lit}`u'` substituted. -/
theorem check_congAlong {d : Deriv} {u u' : Term} {Φ₀ : List Term}
    (hd : ∀ (k : ℕ) (Δ : List PartialHorn.Tree),
      (check G E n d).1 Δ ((List.map weaken1)^[k] Φ₀) (weaken1^[k] u) = some (weaken1^[k] u')) :
    ∀ (t : Term), Term.Simple t = true → ∀ (j : ℕ) (Δ : List PartialHorn.Tree),
      (check G E n (congAlong d t j)).1 Δ ((List.map weaken1)^[j] Φ₀)
        (Term.subst t (substAt j (weaken1^[j] u))) =
          some (Term.subst t (substAt j (weaken1^[j] u'))) :=
  RoseTree.ind fun l cs ih hs j Δ ↦ by
    rw [congAlong_node]
    rcases Term.shape l cs with ⟨i, rfl⟩ | ⟨a, b, rfl, rfl⟩ | ⟨z, sₛ, m, hl, rfl⟩ |
      ⟨c, sₛ, m, rfl, rfl⟩ | hp
    · simp only [congAlongStep, Term.subst_node, Term.substStep]
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, substAt, lt_irrefl]
        exact hd i Δ
      · simp only [hij, ↓reduceIte, check_refl, substAt]
    · simp only [congAlongStep, List.map_cons, List.map_nil, Term.subst_node, Term.substStep]
      have hb := ih b (by simp) (simple_child hs (by simp)) (j + 1) (a :: Δ)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        Function.iterate_succ_apply'] at hb
      rw [liftS_substAt, liftS_substAt]
      exact check_cong_lam hb fun hr ↦ FreeTopos.Internal.check_isRefl hr hb
    · rcases hl with rfl | rfl <;> simp [simple_node, simpleStep] at hs
    · simp [simple_node, simpleStep] at hs
    · have plain : (∀ i, FreeTopos.Internal.sameCtx l i = true) →
          congAlongStep d l (cs.map fun c ↦ (c, congAlong d c)) j =
            nd .cong (cs.map fun c ↦ congAlong d c j) →
          (check G E n (congAlongStep d l (cs.map fun c ↦ (c, congAlong d c)) j)).1 Δ
              ((List.map weaken1)^[j] Φ₀)
              (Term.subst (RoseTree.node l cs) (substAt j (weaken1^[j] u))) =
            some (Term.subst (RoseTree.node l cs) (substAt j (weaken1^[j] u'))) := by
        intro hsame hstep
        rw [hstep, Term.subst_plain hp rfl, Term.subst_plain hp rfl]
        refine check_cong_same (fun k _ ↦ .inl (hsame k)) (by simp) (by simp)
          fun k h₁ h₂ h₃ ↦ ?_
        simp only [List.getElem_map]
        exact ih _ (List.getElem_mem (by simpa using h₁)) (simple_child hs (List.getElem_mem _)) j
          Δ
      have hplain : congAlongStep d l (cs.map fun c ↦ (c, congAlong d c)) j =
          nd .cong (cs.map fun c ↦ congAlong d c j) →
          (∀ i, FreeTopos.Internal.sameCtx l i = true) → _ := fun h₁ h₂ ↦ plain h₂ h₁
      rcases l with i | _ | _ | _ | _ | a | _ | ⟨k, θ⟩ | _ | _ | c | ⟨k, θ⟩ | _
      · have := congrArg RoseTree.label ((hp cs rfl).1 (fun c _ ↦ c) Nat.succ)
        simp only [Term.renameStep, Term.var, RoseTree.label_node,
          FreeTopos.Internal.Label.var.injEq] at this
        exact absurd this (Nat.succ_ne_self i)
      all_goals first
        | exact hplain (by simp [congAlongStep, List.map_map, Function.comp_def]) fun _ ↦ rfl
        | exact absurd ((simple_node _ _).symm.trans hs) Bool.false_ne_true
        | skip
      rw [simple_node] at hs
      simp only [simpleStep, Bool.and_eq_true, beq_iff_eq, List.length_map] at hs
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hs.1
      have := congrArg (fun t ↦ t.children)
        ((hp [b] rfl).1 (fun _ f ↦ Term.var (f 0)) Nat.succ)
      simp only [Term.renameStep, Term.var, Term.liftR, List.map_cons, List.map_nil,
        RoseTree.children_node, List.cons.injEq, and_true] at this
      have h' := congrArg RoseTree.label this
      simp only [RoseTree.label_node, FreeTopos.Internal.Label.var.injEq] at h'
      exact absurd h' (by decide)

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

/-- The start of the fold in the body of {name}`Geb.FreeTopos.Internal.iterDefn` at the type
{lit}`c`: the first component of the pair. -/
def iterStart (c : PartialHorn.Tree) : Term :=
  Term.lam (FreeTopos.prod c (FreeTopos.exp c c)) (Term.fst (Term.var 0))

/-- The step of the fold in the body of {name}`Geb.FreeTopos.Internal.iterDefn` at the type
{lit}`c`: the pair's second component applied to the previous function's value at the pair. -/
def iterStep (c : PartialHorn.Tree) : Term :=
  Term.lam (FreeTopos.prod c (FreeTopos.exp c c))
    (Term.app (Term.snd (Term.var 0)) (Term.app (Term.var 1) (Term.var 0)))

variable {ki kz ks : ℕ}

/-- The unfolding of the fold with parameters. -/
theorem check_delta_iter (hi : G.defs[ki]? = some (.language FreeTopos.Internal.iterDefn))
    (c : PartialHorn.Tree) (m p : Term) :
    (check G E n (ruleD .delta)).1 Γ Φ (Term.defn ki [c] [m, p]) =
      some (Term.app (Term.natRec (iterStart c) (iterStep c) m) p) := by
  rw [check_rule _ ⟨by simp, by simp, by simp⟩]
  simp only [rootStep, Term.defn, RoseTree.label_node, RoseTree.children_node, hi,
    Option.bind_some]
  rfl

/-- The computation of the fold with parameters at zero: the start. -/
theorem check_natZeroLhs (hi : G.defs[ki]? = some (.language FreeTopos.Internal.iterDefn))
    (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim) (c : PartialHorn.Tree) (z s : Term) :
    (check G E n (natZeroLhsD kz)).1 Γ Φ
      (Term.defn ki [c] [Term.arr kz [] Term.star, Term.pair z (Term.lam c s)]) = some z := by
  simp only [natZeroLhsD, check_trans, check_delta_iter hi, Option.bind_some]
  rw [show Term.app (Term.natRec (iterStart c) (iterStep c) (Term.arr kz [] Term.star))
      (Term.pair z (Term.lam c s)) = RoseTree.node .app [_, _] from rfl,
    check_cong₂ rfl rfl (d₁ := ruleD (.natZero kz)) (t₁' := iterStart c) ?_ (check_refl _)]
  · simp only [Option.bind_some]
    rw [show RoseTree.node FreeTopos.Internal.Label.app [iterStart c, Term.pair z (Term.lam c s)] =
      Term.app (Term.lam _ (Term.fst (Term.var 0))) (Term.pair z (Term.lam c s)) from rfl,
      check_beta, Option.bind_some]
    exact check_fstPair _ _
  · rw [check_rule _ ⟨by simp, by simp, by simp⟩]
    simp [rootStep, Term.natRec, Term.arr, hz, Term.star]

/-- The step of the fold with parameters at the fold of a term. -/
theorem subst_iterStep (c : PartialHorn.Tree) (r : Term) :
    Term.subst (iterStep c) (instVar r) = Term.lam (FreeTopos.prod c (FreeTopos.exp c c))
      (Term.app (Term.snd (Term.var 0)) (Term.app (weaken1 r) (Term.var 0))) := rfl

/-- The computation of the fold with parameters at a successor: the step at the fold of the
predecessor. -/
theorem check_natSuccLhs (hi : G.defs[ki]? = some (.language FreeTopos.Internal.iterDefn))
    (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim) (c : PartialHorn.Tree) {m : Term}
    (hm : Term.VarLeaves m = true) (z s : Term) :
    (check G E n (natSuccLhsD ks)).1 Γ Φ
      (Term.defn ki [c] [Term.arr ks [] m, Term.pair z (Term.lam c s)]) =
      some (Term.subst s (instVar (Term.app (Term.natRec (iterStart c) (iterStep c) m)
        (Term.pair z (Term.lam c s))))) := by
  set p := Term.pair z (Term.lam c s)
  set R := Term.natRec (iterStart c) (iterStep c) m
  have h₁ : (check G E n (nd .cong [ruleD (.natSucc ks), reflD])).1 Γ Φ
      (Term.app (Term.natRec (iterStart c) (iterStep c) (Term.arr ks [] m)) p) =
      some (Term.app (Term.subst (iterStep c) (instVar R)) p) := by
    refine check_cong₂ rfl rfl ?_ (check_refl _)
    rw [check_rule _ ⟨by simp, by simp, by simp⟩]
    simp [rootStep, Term.natRec, Term.arr, hs, R]
  have hR : Term.subst (weaken1 R) (instVar p) = R := by
    simp only [weaken1, R, Term.natRec, Term.rename_node, Term.renameStep, List.map_cons,
      List.map_nil, Term.subst_node, Term.substStep]
    rw [Term.subst_rename m (· + 1) (instVar p) Term.var fun _ ↦ rfl,
      Term.subst_id m hm _ fun _ ↦ rfl]
  have h₂ : (check G E n (ruleD .beta)).1 Γ Φ (Term.app (Term.subst (iterStep c) (instVar R)) p) =
      some (Term.app (Term.snd p) (Term.app R p)) := by
    rw [subst_iterStep, check_beta]
    simp only [Term.app, Term.snd, Term.subst_node, Term.substStep, List.map_cons,
      List.map_nil, Term.var, instVar]
    rw [hR]
  have h₃ : (check G E n (nd .cong [ruleD .sndPair, reflD])).1 Γ Φ
      (Term.app (Term.snd p) (Term.app R p)) = some (Term.app (Term.lam c s) (Term.app R p)) :=
    check_cong₂ rfl rfl (check_sndPair _ _) (check_refl _)
  simp only [natSuccLhsD, check_trans, check_delta_iter hi, Option.bind_some, h₁, h₂, h₃,
    check_beta]

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

/-- Iterated maps of a list, at an index. -/
theorem getElem?_iterate_map {α : Type*} (f : α → α) (l : List α) (i : ℕ) :
    ∀ k : ℕ, ((List.map f)^[k] l)[i]? = (l[i]?).map (f^[k]) :=
  Nat.rec (by simp) fun k ih ↦ by
    rw [Function.iterate_succ_apply', List.getElem?_map, ih, Option.map_map,
      ← Function.iterate_succ']

/-- Iterated weakening of an equation. -/
theorem weaken1_iterate_eq (t u : Term) :
    ∀ k : ℕ, weaken1^[k] (Term.eq t u) = Term.eq (weaken1^[k] t) (weaken1^[k] u) :=
  Nat.rec rfl fun k ih ↦ by
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    rfl

/-- The substitution at the innermost variable is the instantiation. -/
theorem substAt_zero (u : Term) : substAt 0 u = instVar u := by
  funext i
  rcases i with _ | i
  · rfl
  · simp [substAt, instVar]

/-- The substitution of equals: the motive at {lit}`u`, from the equation {lit}`t = u` and the
motive at {lit}`t`. -/
theorem check_leibD {pb t u : Term} {Dh Dp : Deriv} (hpb : Term.Simple pb = true)
    (hψ : typeIn G n Γ (Term.eq t u) = some FreeTopos.omega)
    (hh : (check G E n Dh).2 Γ Φ (Term.eq t u) = true)
    (hp : (check G E n Dp).2 Γ (Φ ++ [Term.eq t u]) (Term.subst pb (instVar t)) = true) :
    (check G E n (leibD pb t u Φ.length Dh Dp)).2 Γ Φ (Term.subst pb (instVar u)) = true := by
  refine check_cut hψ hh (check_conv ?_ hp)
  have hd : ∀ (k : ℕ) (Δ : List PartialHorn.Tree),
      (check G E n (ruleD (.rwHyp Φ.length true))).1 Δ
        ((List.map weaken1)^[k] (Φ ++ [Term.eq t u])) (weaken1^[k] u) = some (weaken1^[k] t) :=
    fun k Δ ↦ check_rwHyp (flip := true) (by
      rw [getElem?_iterate_map, List.getElem?_append_right (le_refl _), Nat.sub_self]
      simp [weaken1_iterate_eq])
  have := check_congAlong hd pb hpb 0 Γ
  simpa only [Function.iterate_zero, id, substAt_zero] using this

/-- The β-reduct of a term's weakening under a binder, abstracted and applied to the bound
variable, is the term. -/
theorem subst_rename_liftR_var0 {pb : Term} (h : Term.VarLeaves pb = true) :
    Term.subst (Term.rename pb (Term.liftR (· + 1))) (instVar (Term.var 0)) = pb := by
  rw [Term.subst_rename pb _ _ Term.var fun i ↦ by rcases i with _ | i <;> rfl,
    Term.subst_id pb h _ fun _ ↦ rfl]

/-- The induction on the natural numbers at a term: the motive at {lit}`n'`, from its base at
zero and its step, each under the hypothesis true, which the derivation's cut adds. -/
theorem check_natIndD (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim)
    (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim) {pb n' : Term} {D₀ Ds : Deriv}
    (hpb : typeIn G 0 (FreeTopos.nat :: Γ) pb = some FreeTopos.omega)
    (hn : typeIn G 0 Γ n' = some FreeTopos.nat)
    (hΦ : ∀ φ ∈ Φ, typeIn G 0 Γ φ = some FreeTopos.omega)
    (hD₀ : (check G E 0 D₀).2 Γ (Φ ++ [truth])
      (Term.subst pb (instVar (Term.arr kz [] Term.star))) = true)
    (hDs : (check G E 0 Ds).2 (FreeTopos.nat :: Γ) (Φ.map weaken1 ++ [truth] ++ [pb])
      (FreeTopos.Internal.natSuccAt ks pb) = true) :
    (check G E 0 (natIndD kz ks pb n' Φ.length D₀ Ds)).2 Γ Φ (Term.subst pb (instVar n')) =
      true := by
  have hnat : FreeTopos.Internal.IsTy G 0 FreeTopos.nat = true :=
    isTy_of_encTy G FreeTopos.nat nat rfl
  have hL := typeIn_lam (Γ := Γ) hnat hpb
  have hR := typeIn_lam (Γ := Γ) hnat (typeIn_truth (G := G) (Γ := FreeTopos.nat :: Γ))
  refine check_cut (typeIn_eq hL hR) (check_funExt hL ?_) ?_
  · refine check_conv (φ' := Term.eq pb truth) (check_cong₂ rfl rfl ?_ ?_) ?_
    · rw [show weaken1 (Term.lam FreeTopos.nat pb) =
        Term.lam FreeTopos.nat (Term.rename pb (Term.liftR (· + 1))) from rfl, check_beta,
        subst_rename_liftR_var0 (varLeaves_of_typeIn hpb)]
    · exact check_beta _ _ _
    · refine check_propExt hpb typeIn_truth (check_join (check_refl _) (check_refl _)) ?_
      refine check_natIndHyp ?_ hz hs hpb hD₀ hDs
      rw [show Φ.map weaken1 ++ [truth] = (Φ ++ [truth]).map weaken1 by
        rw [List.map_append]; rfl]
      refine lowerHyps_map_weaken1 fun φ hφ ↦ ?_
      rcases List.mem_append.mp hφ with hφ | hφ
      · exact hΦ φ hφ
      · obtain rfl := List.mem_singleton.mp hφ
        exact typeIn_truth
  · refine check_convFrom (typeIn_app hL hn) (check_beta _ _ _) ?_
    refine check_conv (φ' := Term.app (Term.lam FreeTopos.nat truth) n')
      (check_cong₂ rfl rfl (check_rwHyp (flip := false)
        (by rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl)) (check_refl _)) ?_
    exact check_conv (check_beta _ _ _) (check_join (check_refl _) (check_refl _))

end Geb.LF.Topos

end
