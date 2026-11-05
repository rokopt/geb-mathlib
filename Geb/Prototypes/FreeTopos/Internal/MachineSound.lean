/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Machine
public import Geb.Prototypes.FreeTopos.Internal.SyntaxLaws
public import Geb.Prototypes.FreeTopos.Literals
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The environment machine rewrites as the base checker does

The reduction of the environment machine ({name}`Geb.FreeTopos.Internal.machineReduce`) rewrites
a term to its result by a derivation the base checker accepts
({name}`Geb.FreeTopos.Literals.Reaches`), in every context and under all hypotheses, where the
term's and the definitions' bodies' variables are leaves and the definitions' bodies are terms in
their parameters: every value the machine computes reads back to a term to which the evaluated
term, with the environment's terms substituted, rewrites, and a delayed value's source rewrites to
its value wherever it reaches one. The rewriting is built of the base checker's rules at the root
and of congruences at children: in the node's context, in the context an abstraction's type
extends at its body, and in the context a fold's types extend at its step, those types being of
the fold's normal form, to which it rewrites first. Evaluation reads no context, so that a delayed
value's rewriting holds in every context and at every depth at which the value's levels are bound,
and a value read back under one binder more is its term weakened past it, so that no derivation is
weakened; where the machine's rewriting at the roots of its normal form is sound under the
hypotheses weakened past the binders it has passed, its rewritings are among them. The soundness
of the machine's reduction is that of the base checker at that derivation, which is not built.

## Main definitions

* {lit}`VLabel.Scoped` — a label in scope under a number of binders.
* {lit}`Good` — a value in scope whose delayed values reach their values from their sources, and
  whose terms' variables are leaves.
* {lit}`Machine.Sound` — the machine's operations rewrite as the base checker does.

## Main statements

* {lit}`readBack_succ` — a value read back under one binder more is its term weakened past it.
* {lit}`machine_sound` — the machine is sound at every depth.
* {lit}`machineReduce_reaches` — a term rewrites to its reduction by the machine.

## Tags

internal language, abstract machine, soundness, rewriting
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Literals (Reaches reaches_refl reaches_root reaches_node)
open Term (VarLeaves)

variable {D : ℕ}

/-! Reading back. -/

/-- A node reads back by its step at its children's terms. -/
theorem readBack_node (l : VLabel) (cs : List Val) :
    readBack D (RoseTree.node l cs) = readStep D l (cs.map (readBack D)) := by
  have hof : List.ofFn (fun i : Fin cs.length ↦ readBack D (cs.toArray[i.1]'(by simp))) =
      cs.map (readBack D) := by simp [List.ofFn_getElem_eq_map]
  conv_lhs => simp only [readBack, RoseTree.node, WType.elim]
  cases l
  case delay =>
    dsimp only
    by_cases h : cs.length = 2
    · simp only [h, ↓reduceDIte]
      obtain ⟨a, c, rfl⟩ : ∃ a c, cs = [a, c] := match cs, h with
        | [a, c], _ => ⟨a, c, rfl⟩
      rfl
    · simp only [h, ↓reduceDIte]
      exact congrArg _ hof
  all_goals (dsimp only; exact congrArg _ hof)

/-- A delayed value is the node of its value and its source. -/
theorem delayed_eq (th : Thunk (Option Val)) (src : Val) :
    delayed th src = vnode .delay [th.get.getD failV, src] := by
  unfold delayed
  exact (RoseTree.node_eq_mk .delay [th.get.getD failV, src] rfl _ fun i ↦ match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl).symm

/-- A delayed value reads back as its source. -/
theorem readBack_delayed (th : Thunk (Option Val)) (src : Val) :
    readBack D (delayed th src) = readBack D src := by
  rw [delayed_eq, readBack_node]
  rfl

/-- The delayed value of a term is the node of its evaluation and of the unevaluated term. -/
theorem Machine.delay_eq (o : Machine) (t : Term) (vs : List Val) (k : ℕ) :
    o.delay t vs k =
      vnode .delay [((o.eval t vs k).bind o.whnf).getD failV, vnode (.term t k) vs] :=
  delayed_eq _ _

/-- The delayed value of a term reads back as the term with its environment's terms
substituted. -/
theorem Machine.readBack_delay (o : Machine) (t : Term) (vs : List Val) (k : ℕ) :
    readBack D (o.delay t vs k) = Term.subst t (envSubst (vs.map (readBack D)) (D - k)) := by
  rw [Machine.delay, readBack_delayed, readBack_node]
  rfl

/-! The values whose delayed values reach their values. -/

/-- The terms a label holds: a closure's body, a fold's step and an unevaluated term. -/
def VLabel.terms : VLabel → List Term
  | .clo _ b _ => [b]
  | .natRec s _ | .listRec s _ | .roseRec _ s _ => [s]
  | .term t _ => [t]
  | _ => []

/-- A label is in scope under {lit}`D` binders: the level of a free variable is bound, and the
binders past a term's environment are among them. -/
def VLabel.Scoped (D : ℕ) : VLabel → Prop
  | .free l => l < D
  | .clo _ _ k | .natRec _ k | .listRec _ k | .roseRec _ _ k | .term _ k => k ≤ D
  | _ => True

/-- A label in scope under some binders is in scope under more. -/
theorem VLabel.Scoped.mono {D D' : ℕ} {l : VLabel} (h : l.Scoped D) (hD : D ≤ D') :
    l.Scoped D' := by
  cases l <;> simp only [VLabel.Scoped] at h ⊢ <;> omega

/-- One step of the test that a value is good under {lit}`D` binders, at a node of a label, from
its children with their tests: each child is good, the label's terms' variables are leaves, the
label is in scope, and a delayed value fails or is reached from its source, in every context and
under all hypotheses, at that depth and every greater one. -/
def goodStep (G : Globals) (E : Array Entry) (n D : ℕ) (l : VLabel) (cs : List (Val × Prop)) :
    Prop :=
  (∀ c ∈ cs, c.2) ∧ (∀ t ∈ l.terms, VarLeaves t = true) ∧ l.Scoped D ∧
    (l = .delay → ∀ r src, cs.map Prod.fst = [r, src] →
      r.label = .fail ∨ ∀ D', D ≤ D' → ∀ (Γ : List Tree) (Φ : List Term),
        Reaches G E n Γ Φ (readBack D' src) (readBack D' r))

/-- A value is good under {lit}`D` binders: it is in scope, each of its delayed values fails or is
reached from its source, and each term its labels hold has its variables as leaves. -/
def Good (G : Globals) (E : Array Entry) (n D : ℕ) : Val → Prop :=
  RoseTree.para (goodStep G E n D)

variable {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}

/-- A node is good exactly when its children are, its label's terms' variables are leaves, its
label is in scope, and, delayed, its value fails or is reached from its source. -/
theorem good_node {l : VLabel} {cs : List Val} :
    Good G E n D (RoseTree.node l cs) ↔ (∀ c ∈ cs, Good G E n D c) ∧
      (∀ t ∈ l.terms, VarLeaves t = true) ∧ l.Scoped D ∧
      (l = .delay → ∀ r src, cs = [r, src] →
        r.label = .fail ∨ ∀ D', D ≤ D' → ∀ (Γ : List Tree) (Φ : List Term),
          Reaches G E n Γ Φ (readBack D' src) (readBack D' r)) := by
  unfold Good
  rw [RoseTree.para_node]
  simp only [goodStep, List.mem_map, forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq,
    List.map_map, Function.comp_def, List.map_id']
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨fun c hc ↦ h₁ c _ c hc rfl rfl, h₂, h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨fun _ _ c hc _ h ↦ h ▸ h₁ c hc, h₂, h₃⟩

/-- A value good under some binders is good under more. -/
theorem Good.mono {D' : ℕ} (hD : D ≤ D') :
    ∀ v : Val, Good G E n D v → Good G E n D' v :=
  RoseTree.ind fun l cs ih hv ↦ by
    obtain ⟨hcs, ht, hs, hd⟩ := good_node.mp hv
    refine good_node.mpr ⟨fun c hc ↦ ih c hc (hcs c hc), ht, hs.mono hD, fun hl r src h ↦ ?_⟩
    rcases hd hl r src h with hf | hr
    · exact .inl hf
    · exact .inr fun D'' hD'' ↦ hr D'' (hD.trans hD'')

/-- A good value's children are good. -/
theorem Good.child {v c : Val} (h : Good G E n D v) (hc : c ∈ v.children) :
    Good G E n D c := by
  rw [← RoseTree.node_label_children v] at h
  exact (good_node.mp h).1 c hc

/-- A good value's label's terms' variables are leaves. -/
theorem Good.terms {v : Val} (h : Good G E n D v) : ∀ t ∈ v.label.terms, VarLeaves t = true := by
  rw [← RoseTree.node_label_children v] at h
  exact (good_node.mp h).2.1

/-- A node of a label holding no term, in scope, over good children is good, delayed or not. -/
theorem good_of_children {l : VLabel} {cs : List Val} (hl : l.terms = []) (hd : l ≠ .delay)
    (hcs : ∀ c ∈ cs, Good G E n D c) (hs : l.Scoped D := by trivial) :
    Good G E n D (RoseTree.node l cs) :=
  good_node.mpr ⟨hcs, by simp [hl], hs, fun h ↦ (hd h).elim⟩

/-! Substitution by environments. -/

/-- The substitution of a term for the innermost variable before a substitution. -/
def consSubst (u : Term) (σ : ℕ → Term) : ℕ → Term := fun i ↦ match i with
  | 0 => u
  | j + 1 => σ j

/-- The environment extended by a value stands for the substitution extended by its term. -/
theorem envSubst_cons (u : Term) (ts : List Term) (k : ℕ) :
    envSubst (u :: ts) k = consSubst u (envSubst ts k) := by
  funext i
  rcases i with _ | j
  · simp [envSubst, consSubst]
  · simp only [envSubst, consSubst, List.length_cons, Nat.add_lt_add_iff_right,
      List.getElem_cons_succ]
    rw [Nat.add_sub_add_right]

/-- The empty environment shifted by nothing stands for the identity substitution. -/
theorem envSubst_nil : envSubst [] 0 = Term.var := by
  funext i
  simp [envSubst]

/-- An environment shifted by its length stands for the substitution of its terms. -/
theorem envSubst_length (ts : List Term) : envSubst ts ts.length = Term.substList ts := by
  funext i
  simp only [envSubst, Term.substList]
  split
  · rename_i h
    simp [h]
  · rename_i h
    simp [List.getElem?_eq_none (Nat.le_of_not_lt h), Nat.sub_add_cancel (Nat.le_of_not_lt h)]

/-- An environment shifted by a number equal to its length stands for the substitution of its
terms. -/
theorem envSubst_of_length {ts : List Term} {m : ℕ} (h : m = ts.length) :
    envSubst ts m = Term.substList ts := h ▸ envSubst_length ts

/-- An environment stands at an index in it for the term of its substitution there, whatever it
is shifted by. -/
theorem envSubst_of_lt {ts : List Term} {i : ℕ} (h : i < ts.length) (m : ℕ) :
    envSubst ts m i = Term.substList ts i := by
  simp [envSubst, Term.substList, h]

/-- An environment of terms whose variables are leaves stands for such a substitution. -/
theorem varLeaves_envSubst {ts : List Term} (h : ∀ t ∈ ts, VarLeaves t = true) (k i : ℕ) :
    VarLeaves (envSubst ts k i) = true := by
  simp only [envSubst]
  split
  · exact h _ (List.getElem_mem _)
  · exact Term.varLeaves_var _

/-- A lifted substitution whose terms' variables are leaves is one. -/
theorem varLeaves_liftS {σ : ℕ → Term} (h : ∀ i, VarLeaves (σ i) = true) (i : ℕ) :
    VarLeaves (Term.liftS σ i) = true := by
  rcases i with _ | j
  · exact Term.varLeaves_var 0
  · exact Term.varLeaves_rename _ (h j) _

/-- A term weakened past one variable, the variable then instantiated, is the term. -/
theorem subst_rename_succ {t : Term} (ht : VarLeaves t = true) (σ : ℕ → Term)
    (hσ : ∀ i, σ (i + 1) = Term.var i) : Term.subst (Term.rename t Nat.succ) σ = t :=
  (Term.subst_rename t _ σ Term.var hσ).trans (Term.subst_id t ht _ fun _ ↦ rfl)

/-- The instantiation of the innermost variable after a lifted substitution is the substitution
extended by the term. -/
theorem subst_liftS_instVar (s : Term) {σ : ℕ → Term} (hσ : ∀ i, VarLeaves (σ i) = true)
    (u : Term) :
    Term.subst (Term.subst s (Term.liftS σ)) (instVar u) = Term.subst s (consSubst u σ) :=
  Term.subst_subst s _ _ _ fun i ↦ match i with
    | 0 => Term.subst_var 0 _
    | j + 1 => subst_rename_succ (hσ j) _ fun _ ↦ rfl

/-- The instantiation of the two innermost variables after a substitution lifted twice is the
substitution extended by the two terms. -/
theorem subst_liftS₂_instVar2 (s : Term) {σ : ℕ → Term} (hσ : ∀ i, VarLeaves (σ i) = true)
    (u w : Term) :
    Term.subst (Term.subst s (Term.liftS (Term.liftS σ))) (instVar2 u w) =
      Term.subst s (consSubst u (consSubst w σ)) :=
  Term.subst_subst s _ _ _ fun i ↦ match i with
    | 0 => Term.subst_var 0 _
    | 1 => by
      change Term.subst (Term.rename (Term.var 0) Nat.succ) _ = w
      rw [Term.subst_rename _ _ _ (fun i ↦ instVar2 u w (i + 1)) fun _ ↦ rfl, Term.subst_var]
      rfl
    | j + 2 => by
      change Term.subst (Term.rename (Term.rename (σ j) Nat.succ) Nat.succ) _ = σ j
      rw [Term.subst_rename _ _ _ (fun i ↦ instVar2 u w (i + 1)) fun _ ↦ rfl]
      exact subst_rename_succ (hσ j) _ fun _ ↦ rfl

/-- A rose-tree fold's step weakened past two variables, under three lifts of a substitution, is
the step under one lift, weakened. -/
theorem subst_weakenStep2 (s : Term) (σ : ℕ → Term) :
    Term.subst (weakenStep2 s) (Term.liftS (Term.liftS (Term.liftS σ))) =
      weakenStep2 (Term.subst s (Term.liftS σ)) := by
  unfold weakenStep2
  rw [Term.subst_rename s _ _ (fun i ↦ Term.rename (Term.liftS σ i) (Term.liftR (· + 2)))
    fun i ↦ ?_, Term.rename_subst s _ _ _ fun _ ↦ rfl]
  rcases i with _ | j
  · rfl
  · change Term.rename (Term.rename (Term.rename (σ j) Nat.succ) Nat.succ) Nat.succ =
      Term.rename (Term.rename (σ j) Nat.succ) (Term.liftR (· + 2))
    rw [Term.rename_rename (Term.rename (σ j) Nat.succ) Nat.succ Nat.succ (· + 2) fun _ ↦ rfl,
      Term.rename_rename (σ j) Nat.succ (· + 2) (· + 3) fun _ ↦ rfl,
      Term.rename_rename (σ j) Nat.succ (Term.liftR (· + 2)) (· + 3) fun _ ↦ rfl]

/-! Rewriting at folds. -/

/-- A natural-number fold rewrites by rewriting its start and its number. -/
theorem reaches_natRec {z z' s m m' : Term} (hz : Reaches G E n Γ Φ z z')
    (hm : Reaches G E n Γ Φ m m') :
    Reaches G E n Γ Φ (Term.natRec z s m) (Term.natRec z' s m') := by
  obtain ⟨dz, hz⟩ := hz
  obtain ⟨dm, hm⟩ := hm
  refine ⟨_, checked_cong_same (l := .natRec) (rs := [(z', dz), (s, dRefl), (m', dm)]) rfl
    (fun i h hs ↦ ?_) fun i h _ ↦ ?_⟩
  · rcases i with _ | _ | _ | i
    · simp [sameCtx] at hs
    · rfl
    · simp [sameCtx] at hs
    · exfalso
      simp only [List.length_cons, List.length_nil] at h
      omega
  · match i, h with
    | 0, _ => exact hz
    | 1, _ => exact checked_refl Γ Φ s
    | 2, _ => exact hm

/-- A list fold rewrites by rewriting its start and its list. -/
theorem reaches_listRec {z z' s m m' : Term} (hz : Reaches G E n Γ Φ z z')
    (hm : Reaches G E n Γ Φ m m') :
    Reaches G E n Γ Φ (Term.listRec z s m) (Term.listRec z' s m') := by
  obtain ⟨dz, hz⟩ := hz
  obtain ⟨dm, hm⟩ := hm
  refine ⟨_, checked_cong_same (l := .listRec) (rs := [(z', dz), (s, dRefl), (m', dm)]) rfl
    (fun i h hs ↦ ?_) fun i h _ ↦ ?_⟩
  · rcases i with _ | _ | _ | i
    · simp [sameCtx] at hs
    · rfl
    · simp [sameCtx] at hs
    · exfalso
      simp only [List.length_cons, List.length_nil] at h
      omega
  · match i, h with
    | 0, _ => exact hz
    | 1, _ => exact checked_refl Γ Φ s
    | 2, _ => exact hm

/-- A rose-tree fold rewrites by rewriting its tree. -/
theorem reaches_roseRec {c : Tree} {s m m' : Term} (hm : Reaches G E n Γ Φ m m') :
    Reaches G E n Γ Φ (Term.roseRec c s m) (Term.roseRec c s m') := by
  obtain ⟨dm, hm⟩ := hm
  refine ⟨_, checked_cong_same (l := .roseRec c) (rs := [(s, dRefl), (m', dm)]) rfl
    (fun i h hs ↦ ?_) fun i h _ ↦ ?_⟩
  · rcases i with _ | _ | i
    · rfl
    · simp [sameCtx] at hs
    · exfalso
      simp only [List.length_cons, List.length_nil] at h
      omega
  · match i, h with
    | 0, _ => exact checked_refl Γ Φ s
    | 1, _ => exact hm

/-- A natural-number fold rewrites its step in the context the type of its start extends. -/
theorem reaches_natRec_step {z s s' m : Term} {c : Tree} (hc : typeIn G n Γ z = some c)
    (h : Reaches G E n (c :: Γ) (Φ.map weaken1) s s') :
    Reaches G E n Γ Φ (Term.natRec z s m) (Term.natRec z s' m) := by
  obtain ⟨d, h⟩ := h
  refine ⟨_, Internal.checked_cong_child (l := .natRec) (rs := [(z, dRefl), (s', d), (m, dRefl)])
    (Γs := [(Γ, Φ), (c :: Γ, Φ.map weaken1), (Γ, Φ)]) (by simp [childCtxs, hc]) rfl
    fun i h₁ _ _ ↦ ?_⟩
  match i, h₁ with
  | 0, _ => exact checked_refl Γ Φ z
  | 1, _ => exact h
  | 2, _ => exact checked_refl Γ Φ m

/-- A list fold rewrites its step in the context the types of its start and its list's elements
extend. -/
theorem reaches_listRec_step {z s s' m : Term} {c a : Tree} (hc : typeIn G n Γ z = some c)
    (ha : (typeIn G n Γ m).bind listPart = some a)
    (h : Reaches G E n (c :: a :: Γ) (Φ.map weaken2) s s') :
    Reaches G E n Γ Φ (Term.listRec z s m) (Term.listRec z s' m) := by
  obtain ⟨d, h⟩ := h
  refine ⟨_, Internal.checked_cong_child (l := .listRec) (rs := [(z, dRefl), (s', d), (m, dRefl)])
    (Γs := [(Γ, Φ), (c :: a :: Γ, Φ.map weaken2), (Γ, Φ)]) (by simp [childCtxs, hc, ha]) rfl
    fun i h₁ _ _ ↦ ?_⟩
  match i, h₁ with
  | 0, _ => exact checked_refl Γ Φ z
  | 1, _ => exact h
  | 2, _ => exact checked_refl Γ Φ m

/-- A rose-tree fold rewrites its step in the context the pair of its tree's label and the list of
the children's values extends. -/
theorem reaches_roseRec_step {c : Tree} {s s' m : Term} {p : Tree × (Tree → Tree)}
    (hp : (typeIn G n Γ m).bind roseParts = some p)
    (h : Reaches G E n (prod p.1 (list c) :: Γ) (Φ.map weaken1) s s') :
    Reaches G E n Γ Φ (Term.roseRec c s m) (Term.roseRec c s' m) := by
  obtain ⟨d, h⟩ := h
  refine ⟨_, Internal.checked_cong_child (l := .roseRec c) (rs := [(s', d), (m, dRefl)])
    (Γs := [(prod p.1 (list c) :: Γ, Φ.map weaken1), (Γ, Φ)]) (by simp [childCtxs, hp]) rfl
    fun i h₁ _ _ ↦ ?_⟩
  match i, h₁ with
  | 0, _ => exact h
  | 1, _ => exact checked_refl Γ Φ m

/-- An abstraction rewrites by rewriting its body in the context its variable extends. -/
theorem reaches_lam {a : Tree} {b b' : Term}
    (h : Reaches G E n (a :: Γ) (Φ.map weaken1) b b') :
    Reaches G E n Γ Φ (Term.lam a b) (Term.lam a b') := by
  obtain ⟨d, h⟩ := h
  refine ⟨_, checked_cong_child (l := .lam a) (rs := [(b', d)]) rfl rfl fun i h₁ _ _ ↦ ?_⟩
  match i, h₁ with
  | 0, _ => exact h

/-- A node of one child in its context rewrites by rewriting the child. -/
theorem reaches_node₁ {l : Label} (hl : ∀ i, sameCtx l i = true) {t u : Term}
    (h : Reaches G E n Γ Φ t u) : Reaches G E n Γ Φ (RoseTree.node l [t]) (RoseTree.node l [u]) :=
  reaches_node hl (.cons h .nil)

/-- A node of two children in its context rewrites by rewriting the children. -/
theorem reaches_node₂ {l : Label} (hl : ∀ i, sameCtx l i = true) {t t' u u' : Term}
    (ht : Reaches G E n Γ Φ t t') (hu : Reaches G E n Γ Φ u u') :
    Reaches G E n Γ Φ (RoseTree.node l [t, u]) (RoseTree.node l [t', u']) :=
  reaches_node hl (.cons ht (.cons hu .nil))

/-! The readings back of good values. -/

/-- Object substitution keeps the variables of a term leaves. -/
theorem varLeaves_osubst (θ : List Tree) :
    ∀ t : Term, VarLeaves t = true → VarLeaves (Term.osubst θ t) = true :=
  RoseTree.ind fun l cs ih ht ↦ by
    obtain ⟨hv, hcs⟩ := (Term.varLeaves_node l cs).mp ht
    rw [Term.osubst_node]
    refine (Term.varLeaves_node _ _).mpr ⟨fun i hi ↦ ?_, fun c hc ↦ ?_⟩
    · cases l <;> simp only [Label.osubst, reduceCtorEq] at hi
      cases hi
      simp [hv _ rfl]
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hc
      exact ih c hc' (hcs c hc')

/-- A good value reads back to a term whose variables are leaves. -/
theorem varLeaves_readBack : ∀ v : Val, Good G E n D v → VarLeaves (readBack D v) = true :=
  RoseTree.ind fun l cs ih hv ↦ by
    obtain ⟨hcs, hterms, -, -⟩ := good_node.mp hv
    have hc : ∀ t ∈ cs.map (readBack D), VarLeaves t = true := fun t ht ↦ by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp ht
      exact ih c hc (hcs c hc)
    have plain : ∀ {l' : Label}, (∀ i, l' ≠ .var i) →
        VarLeaves (RoseTree.node l' (cs.map (readBack D))) = true :=
      fun hl ↦ Term.varLeaves_of_children hl hc
    have sub : ∀ (t : Term) (ht : VarLeaves t = true) (k : ℕ),
        VarLeaves (Term.subst t (Term.liftS (envSubst (cs.map (readBack D)) (D - k)))) = true :=
      fun t ht k ↦ Term.varLeaves_subst t ht _ (varLeaves_liftS (varLeaves_envSubst hc (D - k)))
    rw [readBack_node]
    cases l with
    | free _ => exact Term.varLeaves_var _
    | star => exact Term.varLeaves_of_children (by simp) (by simp)
    | clo a b k =>
      exact Term.varLeaves_of_children (by simp)
        (by simpa using sub b (hterms b (by simp [VLabel.terms])) k)
    | natRec s k =>
      rcases cs with _ | ⟨z, _ | ⟨m, cs⟩⟩
      · exact plain (by simp)
      · exact plain (by simp)
      · simp only [List.map_cons] at hc ⊢
        refine Term.varLeaves_of_children (by simp) fun t ht ↦ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact hc _ (by simp)
        · exact Term.varLeaves_subst s (hterms s (by simp [VLabel.terms])) _
            (varLeaves_liftS (varLeaves_envSubst (fun t ht ↦ hc t (by simp [ht])) (D - k)))
        · exact hc _ (by simp)
    | listRec s k =>
      rcases cs with _ | ⟨z, _ | ⟨m, cs⟩⟩
      · exact plain (by simp)
      · exact plain (by simp)
      · simp only [List.map_cons] at hc ⊢
        refine Term.varLeaves_of_children (by simp) fun t ht ↦ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl
        · exact hc _ (by simp)
        · exact Term.varLeaves_subst s (hterms s (by simp [VLabel.terms])) _
            (varLeaves_liftS (varLeaves_liftS
              (varLeaves_envSubst (fun t ht ↦ hc t (by simp [ht])) (D - k))))
        · exact hc _ (by simp)
    | roseRec c s k =>
      rcases cs with _ | ⟨m, cs⟩
      · exact plain (by simp)
      · simp only [List.map_cons] at hc ⊢
        refine Term.varLeaves_of_children (by simp) fun t ht ↦ ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact Term.varLeaves_subst s (hterms s (by simp [VLabel.terms])) _
            (varLeaves_liftS (varLeaves_envSubst (fun t ht ↦ hc t (by simp [ht])) (D - k)))
        · exact hc _ (by simp)
    | term t k =>
      exact Term.varLeaves_subst t (hterms t (by simp [VLabel.terms])) _
        (varLeaves_envSubst hc (D - k))
    | delay =>
      rcases cs with _ | ⟨r, _ | ⟨c, _ | ⟨_, _⟩⟩⟩
      all_goals simp only [List.map_cons, List.map_nil, readStep]
      · exact Term.varLeaves_of_children (by simp) (by simp)
      · exact Term.varLeaves_of_children (by simp) (by simp)
      · exact hc _ (by simp)
      · exact Term.varLeaves_of_children (by simp) (by simp)
    | fail => exact Term.varLeaves_of_children (by simp) (by simp)
    | pair | arr _ _ | app | fst | snd | defn _ _ | eq => exact plain (by simp)

/-- An environment of good values stands for a substitution whose terms' variables are
leaves. -/
theorem varLeaves_envSubst_good {vs : List Val} (h : ∀ w ∈ vs, Good G E n D w) (k i : ℕ) :
    VarLeaves (envSubst (vs.map (readBack D)) k i) = true :=
  varLeaves_envSubst (fun t ht ↦ by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ht
    exact varLeaves_readBack w (h w hw)) k i

/-! Reading back under a further binder. -/

/-- A variable renames to the variable of its index's image. -/
theorem rename_var (i : ℕ) (f : ℕ → ℕ) : Term.rename (Term.var i) f = Term.var (f i) := by
  simp [Term.var, Term.rename_node, Term.renameStep]

/-- The substitution of an environment, weakened past a variable, is the environment's terms
weakened past it and one more binder past the environment. -/
theorem rename_envSubst (ts : List Term) (m i : ℕ) :
    Term.rename (envSubst ts m i) Nat.succ =
      envSubst (ts.map (Term.rename · Nat.succ)) (m + 1) i := by
  simp only [envSubst, List.length_map]
  split
  · simp
  · rw [rename_var]
    rfl

/-- A lifted substitution renames, under a lifted renaming, as the lift of its renaming. -/
theorem rename_liftS {σ τ : ℕ → Term} {f : ℕ → ℕ} (h : ∀ i, Term.rename (σ i) f = τ i) (i : ℕ) :
    Term.rename (Term.liftS σ i) (Term.liftR f) = Term.liftS τ i := by
  rcases i with _ | j
  · simp [Term.liftS, Term.liftR, rename_var]
  · change Term.rename (Term.rename (σ j) Nat.succ) (Term.liftR f) = Term.rename (τ j) Nat.succ
    rw [← h j, Term.rename_rename (σ j) f Nat.succ (fun k ↦ f k + 1) fun _ ↦ rfl]
    exact Term.rename_rename _ _ _ _ fun _ ↦ rfl

/-- The step of reading back under one binder more, at a label in scope and the children's terms
weakened past it, is the step's term weakened past it. -/
theorem readStep_succ {l : VLabel} (hs : l.Scoped D) (ts : List Term) :
    readStep (D + 1) l (ts.map (Term.rename · Nat.succ)) =
      Term.rename (readStep D l ts) Nat.succ := by
  have envs : ∀ {k : ℕ}, k ≤ D → ∀ (ts : List Term) (i : ℕ),
      Term.rename (envSubst ts (D - k) i) Nat.succ =
        envSubst (ts.map (Term.rename · Nat.succ)) (D + 1 - k) i := fun {k} hk ts i ↦ by
    rw [rename_envSubst, show D - k + 1 = D + 1 - k by omega]
  have star : Term.rename Term.star Nat.succ = Term.star := by
    simp [Term.star, Term.rename_node, Term.renameStep]
  cases l with
  | free l =>
    simp only [VLabel.Scoped] at hs
    simp only [readStep]
    rw [rename_var]
    congr 1
    push_cast
    change _ = _ + 1
    omega
  | clo a b k =>
    simp only [VLabel.Scoped] at hs
    simp only [readStep, Term.lam, Term.rename_node, Term.renameStep, List.map_cons, List.map_nil]
    rw [Term.rename_subst _ _ _ _ (rename_liftS (envs hs ts))]
  | natRec s k =>
    simp only [VLabel.Scoped] at hs
    rcases ts with _ | ⟨z, _ | ⟨m, ts⟩⟩
    · simp [readStep, Term.rename_node, Term.renameStep]
    · simp [readStep, Term.rename_node, Term.renameStep]
    · simp only [readStep, Term.natRec, List.map_cons, Term.rename_node, Term.renameStep,
        List.map_nil]
      rw [Term.rename_subst _ _ _ _ (rename_liftS (envs hs ts))]
  | listRec s k =>
    simp only [VLabel.Scoped] at hs
    rcases ts with _ | ⟨z, _ | ⟨m, ts⟩⟩
    · simp [readStep, Term.rename_node, Term.renameStep]
    · simp [readStep, Term.rename_node, Term.renameStep]
    · simp only [readStep, Term.listRec, List.map_cons, Term.rename_node, Term.renameStep,
        List.map_nil]
      rw [Term.rename_subst _ _ _ _ (rename_liftS (rename_liftS (envs hs ts)))]
  | roseRec c s k =>
    simp only [VLabel.Scoped] at hs
    rcases ts with _ | ⟨m, ts⟩
    · simp [readStep, Term.rename_node, Term.renameStep]
    · simp only [readStep, Term.roseRec, List.map_cons, Term.rename_node, Term.renameStep,
        List.map_nil]
      rw [Term.rename_subst _ _ _ _ (rename_liftS (envs hs ts))]
  | term t k =>
    simp only [VLabel.Scoped] at hs
    simp only [readStep]
    rw [Term.rename_subst _ _ _ _ (envs hs ts)]
  | delay =>
    rcases ts with _ | ⟨r, _ | ⟨c, _ | ⟨x, ts⟩⟩⟩
    all_goals simp only [readStep, List.map_cons, List.map_nil, star]
  | fail => simp only [readStep, star]
  | star => simp only [readStep, star]
  | pair | arr _ _ | app | fst | snd | defn _ _ | eq =>
    simp [readStep, Term.rename_node, Term.renameStep, Function.comp_def]

/-- A good value reads back under one binder more to its term weakened past it. -/
theorem readBack_succ :
    ∀ v : Val, Good G E n D v → readBack (D + 1) v = Term.rename (readBack D v) Nat.succ :=
  RoseTree.ind fun l cs ih hv ↦ by
    obtain ⟨hcs, -, hs, -⟩ := good_node.mp hv
    rw [readBack_node, readBack_node, ← readStep_succ hs, List.map_map]
    exact congrArg _ (List.map_congr_left fun c hc ↦ ih c hc (hcs c hc))

/-- An environment of good values extended by the variable of the next level, read back under one
binder more, stands for the lift of the environment's substitution. -/
theorem envSubst_open {env : List Val} {k' : ℕ} (hk : k' ≤ D) (henv : ∀ w ∈ env, Good G E n D w) :
    envSubst ((vnode (.free D) [] :: env).map (readBack (D + 1))) (D + 1 - k') =
      Term.liftS (envSubst (env.map (readBack D)) (D - k')) := by
  have hmap : env.map (readBack (D + 1)) =
      (env.map (readBack D)).map (Term.rename · Nat.succ) := by
    rw [List.map_map]
    exact List.map_congr_left fun w hw ↦ readBack_succ w (henv w hw)
  have hv : readBack (D + 1) (vnode (.free D) []) = Term.var 0 := by
    rw [readBack_node]
    simp only [readStep]
    congr 1
    push_cast
    omega
  funext i
  rw [List.map_cons, hv, hmap, envSubst_cons]
  rcases i with _ | j
  · rfl
  · change envSubst _ _ j = Term.rename (envSubst (env.map (readBack D)) (D - k') j) Nat.succ
    rw [rename_envSubst, show D + 1 - k' = D - k' + 1 by omega]

/-- The variable of the next level is good under one binder more. -/
theorem good_free_next : Good G E n (D + 1) (vnode (.free D) []) :=
  good_of_children rfl (by simp) (by simp) (by
    simp only [VLabel.Scoped]
    push_cast
    omega)

/-- The environment extended by the variable of the next level is good under one binder more. -/
theorem good_open {env : List Val} (henv : ∀ w ∈ env, Good G E n D w) :
    ∀ w ∈ vnode (.free D) [] :: env, Good G E n (D + 1) w := fun w hw ↦ by
  rcases List.mem_cons.mp hw with rfl | hw
  · exact good_free_next
  · exact Good.mono (Nat.le_succ D) w (henv w hw)

/-! The machine's soundness. -/

variable {unfold : ℕ → Bool} {kl kc : ℕ} {Ψ : List Term}
  {rw : List Tree → ℕ → Term → Option Term}

/-- The machine's operations rewrite as the base checker does: an evaluation's value reads back
under {lit}`D` binders to a term to which the evaluated term, the environment's terms substituted,
rewrites; a weak head normal form's to one to which the value's term rewrites; and the normal form
of a value's term, under a number of binders by which the hypotheses are {lit}`Ψ` weakened, is one
to which it rewrites, whose variables are leaves; each at good values and terms whose variables
are leaves, and each value computed good. -/
structure Machine.Sound (G : Globals) (E : Array Entry) (n D : ℕ) (Γ : List Tree) (Φ Ψ : List Term)
    (o : Machine) : Prop where
  /-- An evaluation's value reads back to a term the evaluated term rewrites to. -/
  eval : ∀ (t : Term) (vs : List Val) (k : ℕ) (v : Val), VarLeaves t = true → k ≤ D →
    (∀ w ∈ vs, Good G E n D w) → o.eval t vs k = some v →
    Good G E n D v ∧
      Reaches G E n Γ Φ (Term.subst t (envSubst (vs.map (readBack D)) (D - k))) (readBack D v)
  /-- A weak head normal form reads back to a term the value's term rewrites to. -/
  whnf : ∀ v w : Val, Good G E n D v → o.whnf v = some w →
    Good G E n D w ∧ Reaches G E n Γ Φ (readBack D v) (readBack D w)
  /-- A normal form is a term the value's term rewrites to, whose variables are leaves. -/
  nf : ∀ (k : ℕ) (v : Val) (t : Term) (b : Bool), Φ = Ψ.map (weakenBy k) → Good G E n k v →
    o.nf Γ k v = some (t, b) → Reaches G E n Γ Φ (readBack k v) t ∧ VarLeaves t = true

/-- The value of a computation that does not reach one is good. -/
theorem good_failV : Good G E n D failV :=
  good_of_children rfl (by simp) (by simp)

/-- The delayed value of a term whose variables are leaves, in an environment of good values,
by a sound machine, is good. -/
theorem Machine.Sound.good_delay {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ) {t : Term}
    {vs : List Val} (k : ℕ) (hk : k ≤ D) (ht : VarLeaves t = true)
    (hvs : ∀ w ∈ vs, Good G E n D w) :
    Good G E n D (o.delay t vs k) := by
  rw [Machine.delay_eq]
  have hterm : Good G E n D (vnode (.term t k) vs) :=
    good_node.mpr ⟨hvs, by simp [VLabel.terms, ht], hk, fun h ↦ nomatch h⟩
  refine good_node.mpr ⟨fun c hc ↦ ?_, by simp [VLabel.terms], trivial, fun _ r src h ↦ ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · cases he : o.eval t vs k with
      | none => exact good_failV
      | some v =>
        obtain ⟨gv, -⟩ := (ho D [] []).eval t vs k v ht hk hvs he
        cases hw : o.whnf v with
        | none => simpa [hw] using good_failV
        | some w => simpa [hw] using ((ho D [] []).whnf v w gv hw).1
    · exact hterm
  · obtain ⟨rfl, rfl⟩ := List.cons.inj h |>.imp id fun h ↦ (List.cons.inj h).1
    cases he : o.eval t vs k with
    | none => exact .inl rfl
    | some v =>
      cases hw : o.whnf v with
      | none => exact .inl (by simp [hw])
      | some w =>
        refine .inr fun D' hD Γ Φ ↦ ?_
        obtain ⟨gv, rv⟩ := (ho D' Γ Φ).eval t vs k v ht (hk.trans hD)
          (fun x hx ↦ Good.mono hD x (hvs x hx)) he
        rw [readBack_node, Option.bind_some, hw, Option.getD_some]
        exact rv.trans ((ho D' Γ Φ).whnf v w gv hw).2

/-- The delayed weak head normal form of a good value, by a sound machine, its source the value,
is good. -/
theorem Machine.Sound.good_delayed {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ) {src : Val}
    (hsrc : Good G E n D src) :
    Good G E n D (delayed (Thunk.mk fun _ ↦ o.whnf src) src) := by
  rw [delayed_eq]
  refine good_node.mpr ⟨fun c hc ↦ ?_, by simp [VLabel.terms], trivial, fun _ r src' h ↦ ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · change Good G E n D ((o.whnf src).getD failV)
      cases he : o.whnf src with
      | none => exact good_failV
      | some w => exact ((ho D [] []).whnf src w hsrc he).1
    · exact hsrc
  · obtain ⟨rfl, rfl⟩ := List.cons.inj h |>.imp id fun h ↦ (List.cons.inj h).1
    change ((o.whnf src).getD failV).label = .fail ∨
      ∀ D', D ≤ D' → ∀ (Γ : List Tree) (Φ : List Term),
        Reaches G E n Γ Φ (readBack D' src) (readBack D' ((o.whnf src).getD failV))
    cases he : o.whnf src with
    | none => exact .inl rfl
    | some w =>
      exact .inr fun D' hD Γ Φ ↦ ((ho D' Γ Φ).whnf src w (Good.mono hD src hsrc) he).2

/-! Substitution at nodes. -/

/-- A plain label's node substitutes in each child, and its value's label reads back to it and
holds no term. -/
theorem Label.plain?_spec {l : Label} {l' : VLabel} (h : l.plain? = some l') :
    (∀ cs, readStep D l' cs = RoseTree.node l cs) ∧ l'.terms = [] ∧ l' ≠ .delay ∧ l'.Scoped D ∧
      ∀ cs σ, Term.subst (RoseTree.node l cs) σ = RoseTree.node l (cs.map (Term.subst · σ)) := by
  cases l <;> simp only [Label.plain?, reduceCtorEq, Option.some.injEq] at h <;> subst h <;>
    exact ⟨fun _ ↦ rfl, rfl, by simp, trivial, fun cs σ ↦ by
      simp [Term.subst_node, Term.substStep, Function.comp_def]⟩

/-- An abstraction substitutes in its body under one lift. -/
theorem subst_lam (a : Tree) (b : Term) (σ : ℕ → Term) :
    Term.subst (Term.lam a b) σ = Term.lam a (Term.subst b (Term.liftS σ)) := by
  simp [Term.lam, Term.subst_node, Term.substStep]

/-- A natural-number fold substitutes in its step under one lift. -/
theorem subst_natRec (z s m : Term) (σ : ℕ → Term) :
    Term.subst (Term.natRec z s m) σ =
      Term.natRec (Term.subst z σ) (Term.subst s (Term.liftS σ)) (Term.subst m σ) := by
  simp [Term.natRec, Term.subst_node, Term.substStep]

/-- A list fold substitutes in its step under two lifts. -/
theorem subst_listRec (z s m : Term) (σ : ℕ → Term) :
    Term.subst (Term.listRec z s m) σ = Term.listRec (Term.subst z σ)
      (Term.subst s (Term.liftS (Term.liftS σ))) (Term.subst m σ) := by
  simp [Term.listRec, Term.subst_node, Term.substStep]

/-- A rose-tree fold substitutes in its step under one lift. -/
theorem subst_roseRec (c : Tree) (s m : Term) (σ : ℕ → Term) :
    Term.subst (Term.roseRec c s m) σ =
      Term.roseRec c (Term.subst s (Term.liftS σ)) (Term.subst m σ) := by
  simp [Term.roseRec, Term.subst_node, Term.substStep]

/-- A definition's application substitutes in each argument. -/
theorem subst_defn (j : ℕ) (θ : List Tree) (ts : List Term) (σ : ℕ → Term) :
    Term.subst (RoseTree.node (.defn j θ) ts) σ =
      RoseTree.node (.defn j θ) (ts.map (Term.subst · σ)) := by
  simp [Term.subst_node, Term.substStep, Function.comp_def]

/-- An application substitutes in each child. -/
theorem subst_node₂ {l : Label} (hl : l.plain?.isSome) (t u : Term) (σ : ℕ → Term) :
    Term.subst (RoseTree.node l [t, u]) σ = RoseTree.node l [Term.subst t σ, Term.subst u σ] := by
  obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp hl
  simp [(Label.plain?_spec (D := 0) hl').2.2.2.2]

/-- A component substitutes in its child. -/
theorem subst_node₁ {l : Label} (hl : l.plain?.isSome) (t : Term) (σ : ℕ → Term) :
    Term.subst (RoseTree.node l [t]) σ = RoseTree.node l [Term.subst t σ] := by
  obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp hl
  simp [(Label.plain?_spec (D := 0) hl').2.2.2.2]

/-- The delayed values of terms whose variables are leaves are good. -/
theorem Machine.Sound.good_delays {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ)
    {ts : List Term} {vs : List Val} (k : ℕ) (hk : k ≤ D) (hts : ∀ t ∈ ts, VarLeaves t = true)
    (hvs : ∀ w ∈ vs, Good G E n D w) :
    ∀ w ∈ ts.map fun u ↦ o.delay u vs k, Good G E n D w := fun w hw ↦ by
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hw
  exact Machine.Sound.good_delay ho k hk (hts u hu) hvs

/-- The delayed values of terms read back as the terms with the environment substituted. -/
theorem Machine.readBack_delays (o : Machine) (ts : List Term) (vs : List Val) (k : ℕ) :
    (ts.map fun u ↦ o.delay u vs k).map (readBack D) =
      ts.map (Term.subst · (envSubst (vs.map (readBack D)) (D - k))) := by
  simp [Function.comp_def, Machine.readBack_delay]

variable (unfold) in
/-- One step of the evaluation is sound at a sound machine. -/
theorem Machine.Sound.evalStep {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ)
    (hdefs : ∀ (j : ℕ) (d : Defn), G.defs[j]? = some (.language d) → VarLeaves d.body = true ∧
      ∀ i, Term.occurs d.body i = true → i < d.params.length)
    (t : Term) (vs : List Val) (k : ℕ) (v : Val) (ht : VarLeaves t = true)
    (hk : k ≤ D) (hvs : ∀ w ∈ vs, Good G E n D w)
    (h : Machine.evalStep G unfold o t vs k = some v) :
    Good G E n D v ∧
      Reaches G E n Γ Φ (Term.subst t (envSubst (vs.map (readBack D)) (D - k))) (readBack D v) := by
  obtain ⟨l, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children t).symm⟩
  obtain ⟨hlv, hcs⟩ := (Term.varLeaves_node l cs).mp ht
  -- a node of a plain label over its children delayed
  have plain : ∀ {l' : VLabel}, l.plain? = some l' →
      Good G E n D (vnode l' (cs.map fun u ↦ o.delay u vs k)) ∧
        Reaches G E n Γ Φ (Term.subst (RoseTree.node l cs) (envSubst (vs.map (readBack D)) (D - k)))
          (readBack D (vnode l' (cs.map fun u ↦ o.delay u vs k))) := fun hl ↦ by
    obtain ⟨hr, hterms, hd, hsc, hs⟩ := Label.plain?_spec (D := D) hl
    refine ⟨good_of_children hterms hd (Machine.Sound.good_delays ho k hk hcs hvs) hsc, ?_⟩
    rw [readBack_node, hr, Machine.readBack_delays, hs]
    exact reaches_refl _
  have generic : (do let l' ← l.plain?; some (vnode l' (cs.map fun u ↦ o.delay u vs k))) =
      some v → Good G E n D v ∧
        Reaches G E n Γ Φ (Term.subst (RoseTree.node l cs) (envSubst (vs.map (readBack D)) (D - k)))
          (readBack D v) := fun h ↦ by
    cases hl : l.plain? with
    | none => simp [hl] at h
    | some l' =>
      simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
      subst h
      exact plain hl
  have hmem : ∀ {c : Term}, c ∈ cs → VarLeaves c = true := fun hc ↦ hcs _ hc
  cases l with
  | var i =>
    obtain rfl := hlv i rfl
    simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
      Option.some.injEq] at h
    subst h
    rw [Term.subst_var_node]
    split
    · rename_i hi
      refine ⟨hvs _ (List.getElem_mem hi), ?_⟩
      rw [show envSubst (vs.map (readBack D)) (D - k) i = readBack D vs[i] by simp [envSubst, hi]]
      exact reaches_refl _
    · rename_i hi
      refine ⟨good_of_children rfl (by simp) (by simp) (by simp only [VLabel.Scoped]; omega), ?_⟩
      have e : ((D : ℤ) - 1 - ((k : ℤ) - 1 - ((i - vs.length : ℕ) : ℤ))).toNat =
          i - vs.length + (D - k) := by omega
      rw [show envSubst (vs.map (readBack D)) (D - k) i = Term.var (i - vs.length + (D - k)) by
        simp [envSubst, hi], readBack_node]
      simp only [readStep, e]
      exact reaches_refl _
  | star =>
    rcases cs with _ | ⟨c, cs⟩
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.some.injEq] at h
      subst h
      exact ⟨good_of_children rfl (by simp) (by simp), by
        rw [Term.subst_node, readBack_node]; exact reaches_refl _⟩
    · simp [Machine.evalStep, Label.plain?] at h
  | lam a =>
    rcases cs with _ | ⟨b, _ | ⟨b', cs⟩⟩
    · simp [Machine.evalStep, Label.plain?] at h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.some.injEq] at h
      subst h
      refine ⟨good_node.mpr ⟨hvs, by simpa [VLabel.terms] using hmem (by simp), hk,
        fun h ↦ nomatch h⟩, ?_⟩
      rw [show RoseTree.node (Label.lam a) [b] = Term.lam a b from rfl, subst_lam, readBack_node]
      exact reaches_refl _
    · simp [Machine.evalStep, Label.plain?] at h
  | fst | snd =>
    rcases cs with _ | ⟨p, _ | ⟨q, cs⟩⟩
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
      exact generic h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨pv, hp, hw⟩ := h
      obtain ⟨gp, rp⟩ := (ho D Γ Φ).eval p vs k pv (hmem (by simp)) hk hvs hp
      obtain ⟨gv, rv⟩ := (ho D Γ Φ).whnf _ v (good_of_children rfl (by simp) (by simpa using gp)) hw
      refine ⟨gv, Reaches.trans ?_ rv⟩
      rw [subst_node₁ rfl, readBack_node]
      exact reaches_node₁ (fun _ ↦ rfl) rp
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
      exact generic h
  | app =>
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
      exact generic h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
      exact generic h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨fv, hf, hw⟩ := h
      obtain ⟨gf, rf⟩ := (ho D Γ Φ).eval f vs k fv (hmem (by simp)) hk hvs hf
      have gn : Good G E n D (vnode .app [fv, o.delay u vs k]) :=
        good_of_children rfl (by simp) fun c hc ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl
          · exact gf
          · exact Machine.Sound.good_delay ho k hk (hmem (by simp)) hvs
      obtain ⟨gv, rv⟩ := (ho D Γ Φ).whnf _ v gn hw
      refine ⟨gv, Reaches.trans ?_ rv⟩
      rw [subst_node₂ rfl, readBack_node]
      simp only [List.map_cons, List.map_nil, Machine.readBack_delay]
      exact reaches_node₂ (fun _ ↦ rfl) rf (reaches_refl _)
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
      exact generic h
  | pair | arr _ _ | eq =>
    simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
    exact generic h
  | natRec =>
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩
    · simp [Machine.evalStep, Label.plain?] at h
    · simp [Machine.evalStep, Label.plain?] at h
    · simp [Machine.evalStep, Label.plain?] at h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨mv, hm, hw⟩ := h
      obtain ⟨gm, rm⟩ := (ho D Γ Φ).eval m vs k mv (hmem (by simp)) hk hvs hm
      have gc : ∀ c ∈ o.delay z vs k :: mv :: vs, Good G E n D c := by
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | rfl | hc
        · exact Machine.Sound.good_delay ho k hk (hmem (by simp)) hvs
        · exact gm
        · exact hvs c hc
      have hsl : VarLeaves s = true := hmem (by simp)
      obtain ⟨gv, rv⟩ := (ho D Γ Φ).whnf (vnode (.natRec s k) (o.delay z vs k :: mv :: vs)) v
        (good_node.mpr ⟨gc, by simpa [VLabel.terms] using hsl, hk, fun h ↦ nomatch h⟩) hw
      refine ⟨gv, Reaches.trans ?_ rv⟩
      rw [readBack_node]
      simp only [List.map_cons, Machine.readBack_delay, readStep]
      rw [show RoseTree.node Label.natRec [z, s, m] = Term.natRec z s m from rfl, subst_natRec]
      exact reaches_natRec (reaches_refl _) rm
    · simp [Machine.evalStep, Label.plain?] at h
  | listRec =>
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩
    · simp [Machine.evalStep, Label.plain?] at h
    · simp [Machine.evalStep, Label.plain?] at h
    · simp [Machine.evalStep, Label.plain?] at h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨mv, hm, hw⟩ := h
      obtain ⟨gm, rm⟩ := (ho D Γ Φ).eval m vs k mv (hmem (by simp)) hk hvs hm
      have gc : ∀ c ∈ o.delay z vs k :: mv :: vs, Good G E n D c := by
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | rfl | hc
        · exact Machine.Sound.good_delay ho k hk (hmem (by simp)) hvs
        · exact gm
        · exact hvs c hc
      have hsl : VarLeaves s = true := hmem (by simp)
      obtain ⟨gv, rv⟩ := (ho D Γ Φ).whnf (vnode (.listRec s k) (o.delay z vs k :: mv :: vs)) v
        (good_node.mpr ⟨gc, by simpa [VLabel.terms] using hsl, hk, fun h ↦ nomatch h⟩) hw
      refine ⟨gv, Reaches.trans ?_ rv⟩
      rw [readBack_node]
      simp only [List.map_cons, Machine.readBack_delay, readStep]
      rw [show RoseTree.node Label.listRec [z, s, m] = Term.listRec z s m from rfl, subst_listRec]
      exact reaches_listRec (reaches_refl _) rm
    · simp [Machine.evalStep, Label.plain?] at h
  | roseRec c =>
    rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩
    · simp [Machine.evalStep, Label.plain?] at h
    · simp [Machine.evalStep, Label.plain?] at h
    · simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨mv, hm, hw⟩ := h
      obtain ⟨gm, rm⟩ := (ho D Γ Φ).eval m vs k mv (hmem (by simp)) hk hvs hm
      have gc : ∀ c ∈ mv :: vs, Good G E n D c := by
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact gm
        · exact hvs c hc
      have hsl : VarLeaves s = true := hmem (by simp)
      obtain ⟨gv, rv⟩ := (ho D Γ Φ).whnf (vnode (.roseRec c s k) (mv :: vs)) v
        (good_node.mpr ⟨gc, by simpa [VLabel.terms] using hsl, hk, fun h ↦ nomatch h⟩) hw
      refine ⟨gv, Reaches.trans ?_ rv⟩
      rw [readBack_node]
      simp only [List.map_cons, readStep]
      rw [show RoseTree.node (Label.roseRec c) [s, m] = Term.roseRec c s m from rfl, subst_roseRec]
      exact reaches_roseRec rm
    · simp [Machine.evalStep, Label.plain?] at h
  | defn j θ =>
    simp only [Machine.evalStep, RoseTree.label_node, RoseTree.children_node] at h
    have gus := Machine.Sound.good_delays ho k hk hcs hvs
    split at h
    · rename_i d hd
      have hd' : (G.defs[j]?).bind Definition.language? = some d := by
        split at hd
        · exact hd
        · cases hd
      obtain ⟨df, hdf, hl⟩ := Option.bind_eq_some_iff.mp hd'
      cases df with
      | object _ _ => cases hl
      | language d' =>
        obtain rfl := Option.some.inj hl
        have hb : VarLeaves (if θ.isEmpty then d'.body else Term.osubst θ d'.body) = true := by
          split
          · exact (hdefs j d' hdf).1
          · exact varLeaves_osubst θ _ (hdefs j d' hdf).1
        split at h
        · rename_i hlen
          obtain ⟨gv, rv⟩ := (ho D Γ Φ).eval _ _ _ v hb hk gus h
          refine ⟨gv, Reaches.trans (reaches_root (l := .delta) ?_) rv⟩
          rw [subst_defn]
          simp only [rootStep, RoseTree.label_node, RoseTree.children_node, hd', Option.map_some,
            Option.some.injEq, Machine.readBack_delays]
          have hagree : ∀ {t : Term}, (∀ i, Term.occurs t i = true → i < d'.params.length) →
              Term.subst t (Term.substList (cs.map (Term.subst · (envSubst (vs.map (readBack D))
                (D - k))))) = Term.subst t (envSubst (cs.map (Term.subst · (envSubst
                  (vs.map (readBack D)) (D - k)))) (D - k)) := fun {t} ht ↦
            Term.subst_congr _ _ _ fun i hi ↦
              (envSubst_of_lt (by simpa [hlen] using ht i hi) _).symm
          have hocc := (hdefs j d' hdf).2
          split
          · rename_i hθ
            rw [List.isEmpty_iff.mp hθ, Term.osubst_nil]
            exact hagree hocc
          · exact hagree (t := Term.osubst θ d'.body) fun i hi ↦ hocc i (by
              rwa [occurs_osubst] at hi)
        · simp only [Option.some.injEq] at h
          subst h
          refine ⟨good_of_children rfl (by simp) gus, ?_⟩
          rw [subst_defn, readBack_node, readStep, Machine.readBack_delays]
          exact reaches_refl _
    · simp only [Option.some.injEq] at h
      subst h
      refine ⟨good_of_children rfl (by simp) gus, ?_⟩
      rw [subst_defn, readBack_node, readStep, Machine.readBack_delays]
      exact reaches_refl _

/-! The base checker's rules at the root, at the terms the machine reduces. -/

section RootSteps

variable {G : Globals} {E : Array Entry} {n : ℕ} {Γ : List Tree} {Φ : List Term}

/-- β at the application of an abstraction. -/
theorem rootStep_beta (a : Tree) (b u : Term) :
    rootStep G E n Γ Φ .beta (Term.app (Term.lam a b) u) = some (Term.subst b (instVar u)) := by
  simp [rootStep, Term.app, Term.lam]

/-- The first component of a pair. -/
theorem rootStep_fstPair (a b : Term) :
    rootStep G E n Γ Φ .fstPair (Term.fst (Term.pair a b)) = some a := by
  simp [rootStep, Term.fst, Term.pair]

/-- The second component of a pair. -/
theorem rootStep_sndPair (a b : Term) :
    rootStep G E n Γ Φ .sndPair (Term.snd (Term.pair a b)) = some b := by
  simp [rootStep, Term.snd, Term.pair]

/-- The fold of zero. -/
theorem rootStep_natZero {j : ℕ} (h : G.prims[j]? = some zeroPrim) (z s : Term) :
    rootStep G E n Γ Φ (.natZero j) (Term.natRec z s (Term.arr j [] Term.star)) = some z := by
  simp [rootStep, Term.natRec, Term.arr, h]

/-- The fold of a successor. -/
theorem rootStep_natSucc {j : ℕ} (h : G.prims[j]? = some succPrim) (z s c : Term) :
    rootStep G E n Γ Φ (.natSucc j) (Term.natRec z s (Term.arr j [] c)) =
      some (Term.subst s (instVar (Term.natRec z s c))) := by
  simp [rootStep, Term.natRec, Term.arr, h]

/-- The fold of the empty list. -/
theorem rootStep_listNil {j : ℕ} (h : G.prims[j]? = some nilPrim) (a : Tree) (z s : Term) :
    rootStep G E n Γ Φ (.listNil j) (Term.listRec z s (Term.arr j [a] Term.star)) = some z := by
  simp [rootStep, Term.listRec, Term.arr, h]

/-- The fold of a construction. -/
theorem rootStep_listCons {j : ℕ} (h : G.prims[j]? = some consPrim) (a : Tree)
    (z s hd tl : Term) :
    rootStep G E n Γ Φ (.listCons j) (Term.listRec z s (Term.arr j [a] (Term.pair hd tl))) =
      some (Term.subst s (instVar2 (Term.listRec z s tl) hd)) := by
  simp [rootStep, Term.listRec, Term.arr, Term.pair, h]

/-- The fold of a rose tree's construction. -/
theorem rootStep_roseNode {j kl kc : ℕ}
    (h : G.prims[j]? = some nodePrim ∨ G.prims[j]? = some lnodePrim)
    (hl : G.prims[kl]? = some nilPrim) (hc : G.prims[kc]? = some consPrim) (c : Tree)
    (θ : List Tree) (s l cs : Term) :
    rootStep G E n Γ Φ (.roseNode j kl kc) (Term.roseRec c s (Term.arr j θ (Term.pair l cs))) =
      some (Term.subst s (instVar (Term.pair l (Term.listRec (Term.arr kl [c] Term.star)
        (Term.arr kc [c] (Term.pair (Term.roseRec c (weakenStep2 s) (Term.var 1)) (Term.var 0)))
        cs)))) := by
  simp [rootStep, Term.roseRec, Term.arr, Term.pair, h, hl, hc]

/-- The case analysis at a left injection. -/
theorem rootStep_caseInl {j j' : ℕ} (h : G.prims[j]? = some casePrim)
    (h' : G.prims[j']? = some inlPrim) (θ θ' : List Tree) (g g' w : Term) :
    rootStep G E n Γ Φ (.caseInl j j')
      (Term.app (Term.arr j θ (Term.pair g g')) (Term.arr j' θ' w)) = some (Term.app g w) := by
  simp [rootStep, Term.app, Term.arr, Term.pair, h, h']

/-- The case analysis at a right injection. -/
theorem rootStep_caseInr {j j' : ℕ} (h : G.prims[j]? = some casePrim)
    (h' : G.prims[j']? = some inrPrim) (θ θ' : List Tree) (g g' w : Term) :
    rootStep G E n Γ Φ (.caseInr j j')
      (Term.app (Term.arr j θ (Term.pair g g')) (Term.arr j' θ' w)) = some (Term.app g' w) := by
  simp [rootStep, Term.app, Term.arr, Term.pair, h, h']

end RootSteps

/-! The weak head normal form. -/

/-- A value is a node of its label over its children. -/
theorem exists_node (v : Val) : ∃ l cs, v = RoseTree.node l cs :=
  ⟨_, _, (RoseTree.node_label_children v).symm⟩

/-- The step of the list of a rose tree's children's folds: the pair of the fold of the element
by the fold's step, weakened past the list fold's variables, and the recursion's value. -/
abbrev roseStep (kc : ℕ) (c : Tree) (s : Term) : Term :=
  Term.arr kc [c] (Term.pair (Term.roseRec c (weakenStep2 s) (Term.var 1)) (Term.var 0))

/-- The step of the list of a rose tree's children's folds, under two lifts of a substitution, is
that of the fold's step under one. -/
theorem subst_roseStep (kc : ℕ) (c : Tree) (s : Term) (σ : ℕ → Term) :
    Term.subst (roseStep kc c s) (Term.liftS (Term.liftS σ)) =
      roseStep kc c (Term.subst s (Term.liftS σ)) := by
  simp only [roseStep, Term.arr, Term.pair]
  rw [subst_node₁ rfl, subst_node₂ rfl, subst_roseRec, subst_weakenStep2, Term.subst_var,
    Term.subst_var]
  rfl

/-- The step of the list of a rose tree's children's folds has its variables as leaves, where
the fold's step has. -/
theorem varLeaves_roseStep (kc : ℕ) (c : Tree) {s : Term} (hs : VarLeaves s = true) :
    VarLeaves (roseStep kc c s) = true := by
  have h1 : VarLeaves (weakenStep2 s) = true := Term.varLeaves_rename s hs _
  refine Term.varLeaves_of_children (by simp) fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht
  refine Term.varLeaves_of_children (by simp) fun t ht ↦ ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · refine Term.varLeaves_of_children (by simp) fun t ht ↦ ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h1
    · exact Term.varLeaves_var 1
  · exact Term.varLeaves_var 0

/-- A stuck natural-number fold, its number reduced, is reached from the fold. -/
theorem reaches_natRec_stuck {s : Term} {k : ℕ} {z m m' : Val} {env : List Val}
    (hm : Reaches G E n Γ Φ (readBack D m) (readBack D m')) :
    Reaches G E n Γ Φ (readBack D (vnode (.natRec s k) (z :: m :: env)))
      (readBack D (vnode (.natRec s k) (z :: m' :: env))) := by
  simp only [readBack_node, List.map_cons, readStep]
  exact reaches_natRec (reaches_refl _) hm

/-- A stuck list fold, its list reduced, is reached from the fold. -/
theorem reaches_listRec_stuck {s : Term} {k : ℕ} {z m m' : Val} {env : List Val}
    (hm : Reaches G E n Γ Φ (readBack D m) (readBack D m')) :
    Reaches G E n Γ Φ (readBack D (vnode (.listRec s k) (z :: m :: env)))
      (readBack D (vnode (.listRec s k) (z :: m' :: env))) := by
  simp only [readBack_node, List.map_cons, readStep]
  exact reaches_listRec (reaches_refl _) hm

/-- A stuck rose-tree fold, its tree reduced, is reached from the fold. -/
theorem reaches_roseRec_stuck {c : Tree} {s : Term} {k : ℕ} {m m' : Val} {env : List Val}
    (hm : Reaches G E n Γ Φ (readBack D m) (readBack D m')) :
    Reaches G E n Γ Φ (readBack D (vnode (.roseRec c s k) (m :: env)))
      (readBack D (vnode (.roseRec c s k) (m' :: env))) := by
  simp only [readBack_node, List.map_cons, readStep]
  exact reaches_roseRec hm

/-- A good node of a label of one term over a list whose first child is replaced by a good value
stays good. -/
theorem Good.replace_head {l : VLabel} {c c' : Val} {cs : List Val} (hl : l ≠ .delay)
    (h : Good G E n D (RoseTree.node l (c :: cs))) (hc : Good G E n D c') :
    Good G E n D (RoseTree.node l (c' :: cs)) := by
  obtain ⟨hcs, ht, hs, -⟩ := good_node.mp h
  refine good_node.mpr ⟨fun x hx ↦ ?_, ht, hs, fun h ↦ (hl h).elim⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  · exact hcs x (List.mem_cons_of_mem _ hx)

/-- A good node of a label over a list whose second child is replaced by a good value stays
good. -/
theorem Good.replace_second {l : VLabel} {z c c' : Val} {cs : List Val} (hl : l ≠ .delay)
    (h : Good G E n D (RoseTree.node l (z :: c :: cs))) (hc : Good G E n D c') :
    Good G E n D (RoseTree.node l (z :: c' :: cs)) := by
  obtain ⟨hcs, ht, hs, -⟩ := good_node.mp h
  refine good_node.mpr ⟨fun x hx ↦ ?_, ht, hs, fun h ↦ (hl h).elim⟩
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | hx
  · exact hcs x (by simp)
  · exact hc
  · exact hcs x (by simp [hx])

variable (kl kc) in
/-- One step of the weak head normal form is sound at a sound machine. -/
theorem Machine.Sound.whnfStep {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ) (v w : Val)
    (hv : Good G E n D v) (h : Machine.whnfStep G kl kc o v = some w) :
    Good G E n D w ∧ Reaches G E n Γ Φ (readBack D v) (readBack D w) := by
  obtain ⟨l, cs, rfl⟩ := exists_node v
  obtain ⟨hcs, hterms, hscope, hdel⟩ := good_node.mp hv
  have self : RoseTree.node l cs = w → Good G E n D w ∧
      Reaches G E n Γ Φ (readBack D (RoseTree.node l cs)) (readBack D w) :=
    fun h ↦ h ▸ ⟨hv, reaches_refl _⟩
  have child : ∀ {c}, c ∈ cs → Good G E n D c := fun hc ↦ hcs _ hc
  cases l with
  | delay =>
    rcases cs with _ | ⟨r, _ | ⟨src, _ | ⟨x, cs⟩⟩⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node] at h
    · exact self (Option.some.inj h)
    · exact self (Option.some.inj h)
    · split at h
      · cases h
      · rename_i hr
        obtain rfl := Option.some.inj h
        refine ⟨child (by simp), ?_⟩
        rcases hdel rfl r src rfl with hf | hrs
        · exact (hr hf).elim
        · rw [readBack_node]
          exact hrs D le_rfl Γ Φ
    · exact self (Option.some.inj h)
  | fst =>
    rcases cs with _ | ⟨p, _ | ⟨q, cs⟩⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    · exact self (Option.some.inj h)
    pick_goal 2
    · exact self (Option.some.inj h)
    obtain ⟨p', hp, h⟩ := h
    obtain ⟨gp, rp⟩ := (ho D Γ Φ).whnf p p' (child (by simp)) hp
    obtain ⟨pl, pcs, rfl⟩ := exists_node p'
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · rename_i a b
      obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf a w ((good_node.mp gp).1 a (by simp)) h
      have r₁ : Reaches G E n Γ Φ (readBack D (RoseTree.node .fst [p]))
          (Term.fst (Term.pair (readBack D a) (readBack D b))) := by
        rw [readBack_node]
        rw [readBack_node] at rp
        exact reaches_node₁ (fun _ ↦ rfl) rp
      exact ⟨gw, r₁.trans ((reaches_root (rootStep_fstPair _ _)).trans rw)⟩
    · obtain rfl := Option.some.inj h
      refine ⟨good_of_children rfl (by simp) (by simpa using gp), ?_⟩
      simp only [readBack_node, List.map_cons, List.map_nil]
      exact reaches_node₁ (fun _ ↦ rfl) (by rwa [readBack_node] at rp)
  | snd =>
    rcases cs with _ | ⟨p, _ | ⟨q, cs⟩⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    · exact self (Option.some.inj h)
    pick_goal 2
    · exact self (Option.some.inj h)
    obtain ⟨p', hp, h⟩ := h
    obtain ⟨gp, rp⟩ := (ho D Γ Φ).whnf p p' (child (by simp)) hp
    obtain ⟨pl, pcs, rfl⟩ := exists_node p'
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · rename_i a b
      obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf b w ((good_node.mp gp).1 b (by simp)) h
      have r₁ : Reaches G E n Γ Φ (readBack D (RoseTree.node .snd [p]))
          (Term.snd (Term.pair (readBack D a) (readBack D b))) := by
        rw [readBack_node]
        rw [readBack_node] at rp
        exact reaches_node₁ (fun _ ↦ rfl) rp
      exact ⟨gw, r₁.trans ((reaches_root (rootStep_sndPair _ _)).trans rw)⟩
    · obtain rfl := Option.some.inj h
      refine ⟨good_of_children rfl (by simp) (by simpa using gp), ?_⟩
      simp only [readBack_node, List.map_cons, List.map_nil]
      exact reaches_node₁ (fun _ ↦ rfl) (by rwa [readBack_node] at rp)
  | free _ | star | pair | clo _ _ _ | arr _ _ | defn _ _ | eq | term _ _ | fail =>
    simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node] at h
    exact self (Option.some.inj h)
  | app =>
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨x, cs⟩⟩⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    · exact self (Option.some.inj h)
    · exact self (Option.some.inj h)
    pick_goal 2
    · exact self (Option.some.inj h)
    obtain ⟨f', hf, h⟩ := h
    have gf : Good G E n D f := child (by simp)
    have gu : Good G E n D u := child (by simp)
    obtain ⟨gf', rf⟩ := (ho D Γ Φ).whnf f f' gf hf
    have stuck : ∀ {u' : Val}, Good G E n D u' → Reaches G E n Γ Φ (readBack D u) (readBack D u') →
        vnode .app [f', u'] = w → Good G E n D w ∧
          Reaches G E n Γ Φ (readBack D (RoseTree.node .app [f, u])) (readBack D w) := by
      rintro u' gu' ru' rfl
      refine ⟨good_of_children rfl (by simp) fun c hc ↦ ?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact gf'
        · exact gu'
      · simp only [readBack_node, List.map_cons, List.map_nil]
        exact reaches_node₂ (fun _ ↦ rfl) rf ru'
    obtain ⟨fl, fcs, rfl⟩ := exists_node f'
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · rename_i a b k
      obtain ⟨w₁, he, hw⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨gfc, hfb, hfk, -⟩ := good_node.mp gf'
      have genv : ∀ c ∈ u :: fcs, Good G E n D c := fun c hc ↦ by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact gu
        · exact gfc c hc
      obtain ⟨g₁, r₁⟩ := (ho D Γ Φ).eval b (u :: fcs) k w₁ (hfb b (by simp [VLabel.terms]))
        hfk genv he
      obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf w₁ w g₁ hw
      have r₀ : Reaches G E n Γ Φ (readBack D (RoseTree.node .app [f, u]))
          (Term.app
            (Term.lam a (Term.subst b (Term.liftS (envSubst (fcs.map (readBack D)) (D - k)))))
            (readBack D u)) := by
        rw [readBack_node] at rf ⊢
        exact reaches_node₂ (fun _ ↦ rfl) rf (reaches_refl _)
      refine ⟨gw, r₀.trans ((reaches_root (rootStep_beta _ _ _)).trans ?_)⟩
      rw [subst_liftS_instVar b (varLeaves_envSubst_good gfc (D - k)), ← envSubst_cons,
        ← List.map_cons]
      exact r₁.trans rw
    · rename_i j θ p
      split at h
      · rename_i hcase
        obtain ⟨u', hu, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨gu', ru⟩ := (ho D Γ Φ).whnf u u' gu hu
        obtain ⟨ul, ucs, rfl⟩ := exists_node u'
        simp only [RoseTree.label_node, RoseTree.children_node] at h
        split at h
        · rename_i j' θ' w₀
          split at h
          · rename_i hinj
            obtain ⟨p', hp, h⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨gp, -, -, -⟩ := good_node.mp gf'
            obtain ⟨gp', rp⟩ := (ho D Γ Φ).whnf p p' (gp p (by simp)) hp
            obtain ⟨pl, pcs, rfl⟩ := exists_node p'
            simp only [RoseTree.label_node, RoseTree.children_node] at h
            split at h
            · rename_i g g'
              obtain ⟨gpc, -, -, -⟩ := good_node.mp gp'
              obtain ⟨guc, -, -, -⟩ := good_node.mp gu'
              have r₀ : Reaches G E n Γ Φ (readBack D (RoseTree.node .app [f, u]))
                  (Term.app (Term.arr j θ (Term.pair (readBack D g) (readBack D g')))
                    (Term.arr j' θ' (readBack D w₀))) := by
                rw [readBack_node] at rf ru rp ⊢
                exact reaches_node₂ (fun _ ↦ rfl)
                  (rf.trans (reaches_node₁ (fun _ ↦ rfl) rp)) ru
              have gsel : ∀ x ∈ [g, g'], Good G E n D (vnode .app [x, w₀]) := fun x hx ↦
                good_of_children rfl (by simp) fun c hc ↦ by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
                  rcases hc with rfl | rfl
                  · exact gpc c hx
                  · exact guc c (by simp)
              by_cases hi : G.prims[j']? = some inlPrim
              · simp only [hi, ↓reduceIte] at h
                obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf _ w (gsel g (by simp)) h
                rw [readBack_node] at rw
                exact ⟨gw, r₀.trans ((reaches_root (rootStep_caseInl hcase hi _ _ _ _ _)).trans rw)⟩
              · simp only [hi, ↓reduceIte] at h
                obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf _ w (gsel g' (by simp)) h
                rw [readBack_node] at rw
                exact ⟨gw, r₀.trans ((reaches_root
                  (rootStep_caseInr hcase (hinj.resolve_left hi) _ _ _ _ _)).trans rw)⟩
            · exact stuck gu' ru (Option.some.inj h)
          · exact stuck gu' ru (Option.some.inj h)
        · exact stuck gu' ru (Option.some.inj h)
      · exact stuck gu (reaches_refl _) (Option.some.inj h)
    · exact stuck gu (reaches_refl _) (Option.some.inj h)
  | natRec s k =>
    rcases cs with _ | ⟨z, _ | ⟨m, env⟩⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    · exact self (Option.some.inj h)
    · exact self (Option.some.inj h)
    obtain ⟨m', hm, h⟩ := h
    have gz : Good G E n D z := child (by simp)
    have genv : ∀ c ∈ env, Good G E n D c := fun c hc ↦ child (by simp [hc])
    have hs : VarLeaves s = true := hterms s (by simp [VLabel.terms])
    obtain ⟨gm', rm⟩ := (ho D Γ Φ).whnf m m' (child (by simp)) hm
    have stuck : vnode (.natRec s k) (z :: m' :: env) = w → Good G E n D w ∧
        Reaches G E n Γ Φ (readBack D (RoseTree.node (.natRec s k) (z :: m :: env)))
          (readBack D w) := by
      rintro rfl
      exact ⟨hv.replace_second (fun h ↦ nomatch h) gm', reaches_natRec_stuck rm⟩
    obtain ⟨ml, mcs, rfl⟩ := exists_node m'
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · rename_i j c
      have gc : Good G E n D c := (good_node.mp gm').1 c (by simp)
      have r₀ : Reaches G E n Γ Φ (readBack D (RoseTree.node (.natRec s k) (z :: m :: env)))
          (Term.natRec (readBack D z)
            (Term.subst s (Term.liftS (envSubst (env.map (readBack D)) (D - k))))
            (Term.arr j [] (readBack D c))) := by
        have := reaches_natRec_stuck (s := s) (k := k) (z := z) (env := env) rm
        simp only [readBack_node, List.map_cons, List.map_nil, readStep] at this ⊢
        exact this
      split at h
      · rename_i hz
        obtain ⟨c', hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨gc', rc⟩ := (ho D Γ Φ).whnf c c' gc hc
        obtain ⟨cl, ccs, rfl⟩ := exists_node c'
        simp only [RoseTree.label_node, RoseTree.children_node] at h
        split at h
        · obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf z w gz h
          rw [readBack_node] at rc
          exact ⟨gw, r₀.trans ((reaches_natRec (reaches_refl _)
            (reaches_node₁ (fun _ ↦ rfl) rc)).trans
              ((reaches_root (rootStep_natZero hz _ _)).trans rw))⟩
        · exact stuck (Option.some.inj h)
      · split at h
        · rename_i _ hsc
          obtain ⟨w₁, he, hw⟩ := Option.bind_eq_some_iff.mp h
          have gsrc : Good G E n D (vnode (.natRec s k) (z :: c :: env)) :=
            good_node.mpr ⟨fun x hx ↦ by
              simp only [List.mem_cons] at hx
              rcases hx with rfl | rfl | hx
              · exact gz
              · exact gc
              · exact genv x hx, by simpa [VLabel.terms] using hs, hscope, fun h ↦ nomatch h⟩
          have genv' : ∀ x ∈ delayed (Thunk.mk fun _ ↦ o.whnf (vnode (.natRec s k) (z :: c :: env)))
              (vnode (.natRec s k) (z :: c :: env)) :: env, Good G E n D x := fun x hx ↦ by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact Machine.Sound.good_delayed ho gsrc
            · exact genv x hx
          obtain ⟨g₁, r₁⟩ := (ho D Γ Φ).eval s _ k w₁ hs hscope genv' he
          obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf w₁ w g₁ hw
          refine ⟨gw, r₀.trans ((reaches_root (rootStep_natSucc hsc _ _ _)).trans ?_)⟩
          rw [subst_liftS_instVar s (varLeaves_envSubst_good genv (D - k))]
          rw [List.map_cons, envSubst_cons, readBack_delayed, readBack_node] at r₁
          exact r₁.trans rw
        · exact stuck (Option.some.inj h)
    · exact stuck (Option.some.inj h)
  | listRec s k =>
    rcases cs with _ | ⟨z, _ | ⟨m, env⟩⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    · exact self (Option.some.inj h)
    · exact self (Option.some.inj h)
    obtain ⟨m', hm, h⟩ := h
    have gz : Good G E n D z := child (by simp)
    have genv : ∀ c ∈ env, Good G E n D c := fun c hc ↦ child (by simp [hc])
    have hs : VarLeaves s = true := hterms s (by simp [VLabel.terms])
    obtain ⟨gm', rm⟩ := (ho D Γ Φ).whnf m m' (child (by simp)) hm
    have stuck : vnode (.listRec s k) (z :: m' :: env) = w → Good G E n D w ∧
        Reaches G E n Γ Φ (readBack D (RoseTree.node (.listRec s k) (z :: m :: env)))
          (readBack D w) := by
      rintro rfl
      exact ⟨hv.replace_second (fun h ↦ nomatch h) gm', reaches_listRec_stuck rm⟩
    obtain ⟨ml, mcs, rfl⟩ := exists_node m'
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · rename_i j a c
      have gc : Good G E n D c := (good_node.mp gm').1 c (by simp)
      have r₀ : Reaches G E n Γ Φ (readBack D (RoseTree.node (.listRec s k) (z :: m :: env)))
          (Term.listRec (readBack D z)
            (Term.subst s (Term.liftS (Term.liftS (envSubst (env.map (readBack D)) (D - k)))))
            (Term.arr j [a] (readBack D c))) := by
        have := reaches_listRec_stuck (s := s) (k := k) (z := z) (env := env) rm
        simp only [readBack_node, List.map_cons, List.map_nil, readStep] at this ⊢
        exact this
      split at h
      · rename_i hnil
        obtain ⟨c', hc, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨gc', rc⟩ := (ho D Γ Φ).whnf c c' gc hc
        obtain ⟨cl, ccs, rfl⟩ := exists_node c'
        simp only [RoseTree.label_node, RoseTree.children_node] at h
        split at h
        · obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf z w gz h
          rw [readBack_node] at rc
          exact ⟨gw, r₀.trans ((reaches_listRec (reaches_refl _)
            (reaches_node₁ (fun _ ↦ rfl) rc)).trans
              ((reaches_root (rootStep_listNil hnil _ _ _)).trans rw))⟩
        · exact stuck (Option.some.inj h)
      · split at h
        · rename_i _ hcons
          obtain ⟨c', hc, h⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨gc', rc⟩ := (ho D Γ Φ).whnf c c' gc hc
          obtain ⟨cl, ccs, rfl⟩ := exists_node c'
          simp only [RoseTree.label_node, RoseTree.children_node] at h
          split at h
          · rename_i hd tl
            obtain ⟨w₁, he, hw⟩ := Option.bind_eq_some_iff.mp h
            obtain ⟨gcc, -, -, -⟩ := good_node.mp gc'
            have gsrc : Good G E n D (vnode (.listRec s k) (z :: tl :: env)) :=
              good_node.mpr ⟨fun x hx ↦ by
                simp only [List.mem_cons] at hx
                rcases hx with rfl | rfl | hx
                · exact gz
                · exact gcc x (by simp)
                · exact genv x hx, by simpa [VLabel.terms] using hs, hscope, fun h ↦ nomatch h⟩
            have genv' : ∀ x ∈ delayed
                (Thunk.mk fun _ ↦ o.whnf (vnode (.listRec s k) (z :: tl :: env)))
                (vnode (.listRec s k) (z :: tl :: env)) :: hd :: env, Good G E n D x :=
              fun x hx ↦ by
                simp only [List.mem_cons] at hx
                rcases hx with rfl | rfl | hx
                · exact Machine.Sound.good_delayed ho gsrc
                · exact gcc x (by simp)
                · exact genv x hx
            obtain ⟨g₁, r₁⟩ := (ho D Γ Φ).eval s _ k w₁ hs hscope genv' he
            obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf w₁ w g₁ hw
            rw [readBack_node] at rc
            refine ⟨gw, r₀.trans ((reaches_listRec (reaches_refl _)
              (reaches_node₁ (fun _ ↦ rfl) rc)).trans
                ((reaches_root (rootStep_listCons hcons _ _ _ _ _)).trans ?_))⟩
            rw [subst_liftS₂_instVar2 s (varLeaves_envSubst_good genv (D - k))]
            rw [List.map_cons, List.map_cons, envSubst_cons, envSubst_cons, readBack_delayed,
              readBack_node] at r₁
            exact r₁.trans rw
          · exact stuck (Option.some.inj h)
        · exact stuck (Option.some.inj h)
    · exact stuck (Option.some.inj h)
  | roseRec c s k =>
    rcases cs with _ | ⟨m, env⟩
    all_goals simp only [Machine.whnfStep, RoseTree.label_node, RoseTree.children_node,
      Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    · exact self (Option.some.inj h)
    obtain ⟨m', hm, h⟩ := h
    have genv : ∀ x ∈ env, Good G E n D x := fun x hx ↦ child (by simp [hx])
    have hs : VarLeaves s = true := hterms s (by simp [VLabel.terms])
    obtain ⟨gm', rm⟩ := (ho D Γ Φ).whnf m m' (child (by simp)) hm
    have stuck : vnode (.roseRec c s k) (m' :: env) = w → Good G E n D w ∧
        Reaches G E n Γ Φ (readBack D (RoseTree.node (.roseRec c s k) (m :: env)))
          (readBack D w) := by
      rintro rfl
      exact ⟨hv.replace_head (fun h ↦ nomatch h) gm', reaches_roseRec_stuck rm⟩
    obtain ⟨ml, mcs, rfl⟩ := exists_node m'
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · rename_i j θ p
      split at h
      · rename_i hprims
        obtain ⟨hn, hl, hc⟩ := hprims
        obtain ⟨p', hp, h⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨gp', rp⟩ := (ho D Γ Φ).whnf p p' ((good_node.mp gm').1 p (by simp)) hp
        obtain ⟨pl, pcs, rfl⟩ := exists_node p'
        simp only [RoseTree.label_node, RoseTree.children_node] at h
        split at h
        · rename_i l cs
          obtain ⟨w₁, he, hw⟩ := Option.bind_eq_some_iff.mp h
          obtain ⟨gpc, -, -, -⟩ := good_node.mp gp'
          have gfolds : Good G E n D (vnode (.listRec (roseStep kc c s) k)
              (vnode (.arr kl [c]) [vnode .star []] :: cs :: env)) :=
            good_node.mpr ⟨fun x hx ↦ by
              simp only [List.mem_cons] at hx
              rcases hx with rfl | rfl | hx
              · exact good_of_children rfl (by simp) fun y hy ↦ by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                  subst hy
                  exact good_of_children rfl (by simp) (by simp)
              · exact gpc x (by simp)
              · exact genv x hx,
              by simpa [VLabel.terms] using varLeaves_roseStep kc c hs, hscope, fun h ↦ nomatch h⟩
          have genv' : ∀ x ∈ vnode .pair [l, delayed (Thunk.mk fun _ ↦ o.whnf
              (vnode (.listRec (roseStep kc c s) k)
                (vnode (.arr kl [c]) [vnode .star []] :: cs :: env)))
              (vnode (.listRec (roseStep kc c s) k)
                (vnode (.arr kl [c]) [vnode .star []] :: cs :: env))] :: env,
              Good G E n D x := fun x hx ↦ by
            rcases List.mem_cons.mp hx with rfl | hx
            · exact good_of_children rfl (by simp) fun y hy ↦ by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
                rcases hy with rfl | rfl
                · exact gpc y (by simp)
                · exact Machine.Sound.good_delayed ho gfolds
            · exact genv x hx
          obtain ⟨g₁, r₁⟩ := (ho D Γ Φ).eval s _ k w₁ hs hscope genv' he
          obtain ⟨gw, rw⟩ := (ho D Γ Φ).whnf w₁ w g₁ hw
          have r₀ : Reaches G E n Γ Φ (readBack D (RoseTree.node (.roseRec c s k) (m :: env)))
              (Term.roseRec c (Term.subst s (Term.liftS (envSubst (env.map (readBack D)) (D - k))))
                (Term.arr j θ (Term.pair (readBack D l) (readBack D cs)))) := by
            have := reaches_roseRec_stuck (c := c) (s := s) (k := k) (env := env) rm
            rw [readBack_node] at rp
            simp only [readBack_node, List.map_cons, List.map_nil, readStep] at this ⊢
            exact this.trans (reaches_roseRec (reaches_node₁ (fun _ ↦ rfl) rp))
          refine ⟨gw, r₀.trans ((reaches_root (rootStep_roseNode hn hl hc _ _ _ _ _)).trans ?_)⟩
          rw [subst_liftS_instVar s (varLeaves_envSubst_good genv (D - k))]
          rw [List.map_cons, envSubst_cons] at r₁
          simp only [readBack_node, readBack_delayed, List.map_cons, List.map_nil, readStep,
            subst_roseStep] at r₁
          exact r₁.trans rw
        · exact stuck (Option.some.inj h)
      · exact stuck (Option.some.inj h)
    · exact stuck (Option.some.inj h)

/-! The normal form, and the machine at every depth. -/

/-- The hypotheses weakened past a number of binders, weakened past one more. -/
theorem map_weaken1_weakenBy (Ψ : List Term) (k : ℕ) :
    (Ψ.map (weakenBy k)).map weaken1 = Ψ.map (weakenBy (k + 1)) := by
  simp only [List.map_map, Function.comp_def, weaken1_weakenBy]

/-- The hypotheses weakened past a number of variables and past two more are weakened past them
all. -/
theorem map_weaken2_weakenBy (Ψ : List Term) (k : ℕ) :
    (Ψ.map (weakenBy k)).map weaken2 = Ψ.map (weakenBy (k + 2)) := by
  simp only [List.map_map, Function.comp_def, weaken2_weakenBy]

/-- The normal form of a term's value in the empty environment is sound at a sound machine. -/
theorem Machine.Sound.renorm {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ) {k : ℕ}
    {u t : Term} {b : Bool} (hΦ : Φ = Ψ.map (weakenBy k)) (hu : VarLeaves u = true)
    (h : o.renorm Γ k u = some (t, b)) : Reaches G E n Γ Φ u t ∧ VarLeaves t = true := by
  simp only [Machine.renorm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨v, hv, ⟨t', b'⟩, ht, h⟩ := h
  obtain ⟨rfl, -⟩ := Prod.mk.inj h
  obtain ⟨gv, rv⟩ := (ho k Γ Φ).eval u [] k v hu le_rfl (by simp) hv
  rw [List.map_nil, Nat.sub_self, envSubst_nil, Term.subst_id _ hu _ fun _ ↦ rfl] at rv
  obtain ⟨rt, lt⟩ := (ho k Γ Φ).nf k v t' b' hΦ gv ht
  exact ⟨rv.trans rt, lt⟩

/-- The normal form of a good weak head normal form's node is sound at a machine sound in every
context. -/
theorem Machine.Sound.nfNode {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ) {k : ℕ} (w : Val)
    (t : Term) (b : Bool) (hΦ : Φ = Ψ.map (weakenBy k)) (gw : Good G E n k w)
    (h : o.nfNode G n Γ k w = some (t, b)) :
    Reaches G E n Γ Φ (readBack k w) t ∧ VarLeaves t = true := by
  obtain ⟨l, cs, rfl⟩ := exists_node w
  have hl := varLeaves_readBack _ gw
  obtain ⟨gcs, hterms, hsc, -⟩ := good_node.mp gw
  have nf : ∀ {c t b}, c ∈ cs → o.nf Γ k c = some (t, b) →
      Reaches G E n Γ Φ (readBack k c) t ∧ VarLeaves t = true :=
    fun hc ht ↦ (ho k Γ Φ).nf k _ _ _ hΦ (gcs _ hc) ht
  have plain : ∀ {l' : Label}, (∀ i, sameCtx l' i = true) → (∀ i, l' ≠ .var i) →
      ∀ {rs : List (Term × Bool)}, cs.mapM (o.nf Γ k) = some rs →
      Reaches G E n Γ Φ (RoseTree.node l' (cs.map (readBack k)))
          (RoseTree.node l' (rs.map Prod.fst))
        ∧ VarLeaves (RoseTree.node l' (rs.map Prod.fst)) = true := fun hl hv rs hrs ↦ by
    have h₂ := ((List.forall₂_and_left _ _).mpr ⟨gcs, forall₂_of_mapM cs hrs⟩).imp
      fun c r h ↦ (ho k Γ Φ).nf k c r.1 r.2 hΦ h.1 h.2
    refine ⟨reaches_node hl (List.forall₂_map_left_iff.mpr
      (List.forall₂_map_right_iff.mpr (h₂.imp fun _ _ h ↦ h.1))), ?_⟩
    have hvs : ∀ r ∈ rs, VarLeaves r.1 = true := ((List.forall₂_and_left
      (p := fun r : Term × Bool ↦ VarLeaves r.1 = true) (R := fun _ (_ : Val) ↦ True) _ _).mp
      (List.Forall₂.flip (R := fun r (_ : Val) ↦ VarLeaves r.1 = true ∧ True)
        (h₂.imp fun _ _ h ↦ ⟨h.2, trivial⟩))).1
    refine Term.varLeaves_of_children hv fun c hc ↦ ?_
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
    exact hvs r hr
  unfold Machine.nfNode at h
  simp only [RoseTree.label_node, RoseTree.children_node] at h
  rw [readBack_node] at hl ⊢
  split at h
  · rename_i s k' z m env
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨z', bz⟩, hz, ⟨m', bm⟩, hm, c, hc, u, hu, ⟨s', bs⟩, hs', h⟩ := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    obtain ⟨rz, lz⟩ := nf (by simp) hz
    obtain ⟨rm, lm⟩ := nf (by simp) hm
    have genv : ∀ w ∈ env, Good G E n k w := fun w hw ↦ gcs w (by simp [hw])
    have hk' : k' ≤ k := hsc
    have ho' := ho (k + 1) (c :: Γ) (Φ.map weaken1)
    obtain ⟨gu, ru⟩ := ho'.eval s _ k' u (hterms s (by simp [VLabel.terms])) (by omega)
      (good_open genv) hu
    rw [envSubst_open hk' genv] at ru
    obtain ⟨rs, ls⟩ := ho'.nf (k + 1) u s' bs (hΦ ▸ map_weaken1_weakenBy Ψ k) gu hs'
    simp only [List.map_cons, readStep]
    refine ⟨(reaches_natRec rz rm).trans (reaches_natRec_step hc (ru.trans rs)),
      Term.varLeaves_of_children (by simp) fun t ht ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    exacts [lz, ls, lm]
  · rename_i s k' z m env
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨z', bz⟩, hz, ⟨m', bm⟩, hm, c, hc, a, ⟨q, hq, ha⟩, u, hu, ⟨s', bs⟩, hs', h⟩ := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    obtain ⟨rz, lz⟩ := nf (by simp) hz
    obtain ⟨rm, lm⟩ := nf (by simp) hm
    have genv : ∀ w ∈ env, Good G E n k w := fun w hw ↦ gcs w (by simp [hw])
    have hk' : k' ≤ k := hsc
    have ho' := ho (k + 2) (c :: a :: Γ) (Φ.map weaken2)
    obtain ⟨gu, ru⟩ := ho'.eval s _ k' u (hterms s (by simp [VLabel.terms])) (by omega)
      (good_open (good_open genv)) hu
    have ru' : Reaches G E n (c :: a :: Γ) (Φ.map weaken2)
        (Term.subst s (Term.liftS (Term.liftS (envSubst (env.map (readBack k)) (k - k')))))
        (readBack (k + 2) u) := by
      rw [← envSubst_open hk' genv, ← envSubst_open (by omega) (good_open genv)]
      exact ru
    obtain ⟨rs, ls⟩ := ho'.nf (k + 2) u s' bs (hΦ ▸ map_weaken2_weakenBy Ψ k) gu hs'
    simp only [List.map_cons, readStep]
    refine ⟨(reaches_listRec rz rm).trans (reaches_listRec_step hc (by rw [hq]; exact ha)
      (ru'.trans rs)), Term.varLeaves_of_children (by simp) fun t ht ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    exacts [lz, ls, lm]
  · rename_i c s k' m env
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨⟨m', bm⟩, hm, p, ⟨q, hq, hp⟩, u, hu, ⟨s', bs⟩, hs', h⟩ := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    obtain ⟨rm, lm⟩ := nf (by simp) hm
    have genv : ∀ w ∈ env, Good G E n k w := fun w hw ↦ gcs w (by simp [hw])
    have hk' : k' ≤ k := hsc
    have ho' := ho (k + 1) (prod p.1 (list c) :: Γ) (Φ.map weaken1)
    obtain ⟨gu, ru⟩ := ho'.eval s _ k' u (hterms s (by simp [VLabel.terms])) (by omega)
      (good_open genv) hu
    rw [envSubst_open hk' genv] at ru
    obtain ⟨rs, ls⟩ := ho'.nf (k + 1) u s' bs (hΦ ▸ map_weaken1_weakenBy Ψ k) gu hs'
    simp only [List.map_cons, readStep]
    refine ⟨(reaches_roseRec rm).trans (reaches_roseRec_step (by rw [hq]; exact hp) (ru.trans rs)),
      Term.varLeaves_of_children (by simp) fun t ht ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    exacts [ls, lm]
  · rename_i a bb k'
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨u, hu, ⟨b', bb'⟩, hb', h⟩ := h
    obtain ⟨rfl, -⟩ := Prod.mk.inj h
    have hk' : k' ≤ k := hsc
    have ho' := ho (k + 1) (a :: Γ) (Φ.map weaken1)
    obtain ⟨gu, ru⟩ := ho'.eval bb _ k' u (hterms bb (by simp [VLabel.terms])) (by omega)
      (good_open gcs) hu
    rw [envSubst_open hk' gcs] at ru
    obtain ⟨rb, lb⟩ := ho'.nf (k + 1) u b' bb' (hΦ ▸ map_weaken1_weakenBy Ψ k) gu hb'
    exact ⟨reaches_lam (ru.trans rb), Term.varLeaves_of_children (by simp) (by simpa using lb)⟩
  all_goals try (simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h)
  all_goals try (obtain ⟨rs, hrs, h⟩ := h; obtain ⟨rfl, -⟩ := Prod.mk.inj h)
  · exact ⟨reaches_refl _, Term.varLeaves_var _⟩
  · exact ⟨reaches_refl _, Term.varLeaves_of_children (by simp) (by simp)⟩
  all_goals first
    | exact plain (fun _ ↦ rfl) (by simp) hrs
    | (obtain ⟨rfl, -⟩ := Prod.mk.inj h
       rw [readBack_node]
       exact ⟨reaches_refl _, hl⟩)
    | cases h

/-- One step of the normal form is sound at a machine sound in every context, where the
rewriting at the root is sound. -/
theorem Machine.Sound.nfStep {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ)
    (hrw : ∀ Γ k t u, rw Γ k t = some u → Reaches G E n Γ (Ψ.map (weakenBy k)) t u) (k : ℕ)
    (v : Val) (t : Term) (b : Bool) (hΦ : Φ = Ψ.map (weakenBy k)) (hv : Good G E n k v)
    (h : Machine.nfStep G n rw o Γ k v = some (t, b)) :
    Reaches G E n Γ Φ (readBack k v) t ∧ VarLeaves t = true := by
  simp only [Machine.nfStep, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, ⟨t₀, b₀⟩, ht₀, h⟩ := h
  obtain ⟨gw, rw₀⟩ := (ho k Γ Φ).whnf v w hv hw
  obtain ⟨r₀, l₀⟩ := Machine.Sound.nfNode ho w t₀ b₀ hΦ gw ht₀
  have r := rw₀.trans r₀
  dsimp only at h
  split at h
  · obtain ⟨r₁, l₁⟩ := Machine.Sound.renorm ho hΦ l₀ h
    exact ⟨r.trans r₁, l₁⟩
  · split at h
    · rename_i u hu
      split at h
      · obtain ⟨r₁, l₁⟩ := Machine.Sound.renorm ho hΦ (by assumption) h
        exact ⟨r.trans ((hΦ ▸ hrw Γ k t₀ u hu).trans r₁), l₁⟩
      · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨r, l₀⟩
    · obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨r, l₀⟩

/-- The machine at the operations of a machine sound in every context is sound, where the
rewriting at the root is sound. -/
theorem Machine.Sound.step {o : Machine} (ho : ∀ D Γ Φ, o.Sound G E n D Γ Φ Ψ)
    (hrw : ∀ Γ k t u, rw Γ k t = some u → Reaches G E n Γ (Ψ.map (weakenBy k)) t u)
    (hdefs : ∀ (j : ℕ) (d : Defn), G.defs[j]? = some (.language d) → VarLeaves d.body = true ∧
      ∀ i, Term.occurs d.body i = true → i < d.params.length) :
    Machine.Sound G E n D Γ Φ Ψ
      ⟨Machine.evalStep G unfold o, Machine.whnfStep G kl kc o, Machine.nfStep G n rw o⟩ :=
  ⟨Machine.Sound.evalStep unfold ho hdefs, Machine.Sound.whnfStep kl kc ho,
    fun k v t b hΦ hv h ↦ Machine.Sound.nfStep ho hrw k v t b hΦ hv h⟩

variable (unfold kl kc) in
/-- The machine is sound at every depth, where the rewriting at the root is sound. -/
theorem machine_sound
    (hrw : ∀ Γ k t u, rw Γ k t = some u → Reaches G E n Γ (Ψ.map (weakenBy k)) t u)
    (hdefs : ∀ (j : ℕ) (d : Defn), G.defs[j]? = some (.language d) → VarLeaves d.body = true ∧
      ∀ i, Term.occurs d.body i = true → i < d.params.length)
    (fuel : ℕ) : (machine G n unfold kl kc rw fuel).Sound G E n D Γ Φ Ψ :=
  fuel.rec (motive := fun fuel ↦ ∀ D Γ Φ, (machine G n unfold kl kc rw fuel).Sound G E n D Γ Φ Ψ)
    (fun _ _ _ ↦ ⟨fun _ _ _ _ _ _ _ h ↦ (nomatch h), fun _ _ _ h ↦ (nomatch h),
      fun _ _ _ _ _ _ h ↦ (nomatch h)⟩)
    (fun _ ho _ _ _ ↦ Machine.Sound.step ho hrw hdefs) D Γ Φ

variable (unfold kl kc) in
/-- A term whose variables are leaves rewrites to its reduction by the machine, by a derivation
the base checker accepts, where the definitions' bodies are terms in their parameters whose
variables are leaves and the rewriting at the root is sound under the hypotheses. -/
theorem machineReduce_reaches
    (hrw : ∀ Γ k t u, rw Γ k t = some u → Reaches G E n Γ (Φ.map (weakenBy k)) t u)
    (hdefs : ∀ (j : ℕ) (d : Defn), G.defs[j]? = some (.language d) → VarLeaves d.body = true ∧
      ∀ i, Term.occurs d.body i = true → i < d.params.length)
    {fuel : ℕ} {t t' : Term} (ht : VarLeaves t = true)
    (h : machineReduce G n unfold kl kc rw fuel Γ t = some t') : Reaches G E n Γ Φ t t' := by
  have hm := machine_sound (E := E) (n := n) (D := 0) (Γ := Γ) (Φ := Φ) (Ψ := Φ) unfold kl kc hrw
    hdefs fuel
  simp only [machineReduce, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨v, hv, ⟨t₁, b⟩, h₁, h⟩ := h
  obtain rfl := Option.some.inj h
  obtain ⟨gv, rv⟩ := hm.eval t [] 0 v ht le_rfl (by simp) hv
  rw [List.map_nil, Nat.sub_self, envSubst_nil, Term.subst_id t ht _ fun _ ↦ rfl] at rv
  exact rv.trans (hm.nf 0 v t₁ b (map_weakenBy_zero Φ).symm gv h₁).1

end Geb.FreeTopos.Internal

end
