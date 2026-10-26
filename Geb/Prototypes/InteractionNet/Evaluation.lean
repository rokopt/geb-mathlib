/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Expression
public import Geb.Prototypes.InteractionNet.FiniteSum
import Geb.Prototypes.InteractionNet.ProgramCorrect
import Geb.Prototypes.InteractionNet.Substitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Composition of expression evaluations

The evaluation of a compound expression has an environment-copying phase and a
child-evaluation phase. The two phases use disjoint fresh wire families. The continuation
contains one consumer of each child result and one consumer of each copied environment
entry. Closed result delivery therefore fills precisely the next phase's inputs.

## Main definitions

* {lit}`evalLayer` — child evaluators and the equation consuming their result wires.

## Main statements

* {lit}`evalLayer_count` — the occurrences of environment and result wires in a layer.
* {lit}`evaluates_agent` — child evaluations and their parent operation compose contextually.
* {lit}`evaluates_con`, {lit}`evaluates_call` — constructor and call introduction rules.

## Tags

interaction net, expression, evaluation, composition, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- Pending child evaluators, followed by the equation finishing their parent expression. -/
def evalLayer {n : ℕ} (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (envs : Fin n → Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ℕ)
    (rs : Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ℕ)
    (out : Term (netArity (φ := φ) dataArity) ℕ) (c : Config (netArity (φ := φ) dataArity)) :
    Config (netArity (φ := φ) dataArity) :=
  { c with equations := (List.ofFn fun j ↦
      (Term.agent (ev dataArity (es j)) (fun _ ↦ rs j),
        Term.agent (env dataArity n) (fun i ↦ envs i j))) ++
      finish dataArity a out rs :: c.equations }

/-- Every copied environment entry occurs once, and every child result occurs twice. -/
theorem evalLayer_count {n : ℕ} (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (envs : Fin n → Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ℕ)
    (rs : Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ℕ)
    (out : Term (netArity (φ := φ) dataArity) ℕ) (c : Config (netArity (φ := φ) dataArity))
    (x : ℕ) :
    (evalLayer dataArity a es envs rs out c).names.count x =
      c.names.count x + out.names.count x + finSum (fun j ↦ (rs j).names.count x) +
        finSum (fun j ↦ (rs j).names.count x + finSum (fun i ↦ (envs i j).names.count x)) := by
  simp only [evalLayer, Config.names, List.flatMap_append, List.flatMap_cons,
    List.count_append, List.count_flatMap, List.map_ofFn, Function.comp_def,
    finish_count, Term.names_agent, List.count_flatten, finSum_ofFn, finSum_one, finSum_add]
  dsimp only [env, netArity, constructorArity]
  omega

/-- Substitution commutes with the equation finishing an expression root. -/
theorem finish_subst {ν μ : Type} (a : Symbol (δ := δ) (φ := φ))
    (out : Term (netArity (φ := φ) dataArity) ν)
    (rs : Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ν)
    (σ : ν → Term (netArity (φ := φ) dataArity) μ) :
    ((finish dataArity a out rs).1.subst σ, (finish dataArity a out rs).2.subst σ) =
      finish dataArity a (out.subst σ) (fun i ↦ (rs i).subst σ) := by
  cases a with
  | inl a => rfl
  | inr fk =>
    rcases fk with ⟨f, k⟩
    apply Prod.ext
    · apply congrArg (Term.agent (app dataArity f k))
      funext i
      exact Fin.cases rfl (fun _ ↦ rfl) i
    · rfl

/-- Substitution acts on a layer's environments, result ports, and continuation. -/
theorem evalLayer_subst {n : ℕ} (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (envs : Fin n → Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ℕ)
    (rs : Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ℕ)
    (out : Term (netArity (φ := φ) dataArity) ℕ) (c : Config (netArity (φ := φ) dataArity))
    (σ : ℕ → Term (netArity (φ := φ) dataArity) ℕ) :
    (evalLayer dataArity a es envs rs out c).subst σ =
      evalLayer dataArity a es (fun i j ↦ (envs i j).subst σ)
        (fun j ↦ (rs j).subst σ) (out.subst σ) (c.subst σ) := by
  simp only [evalLayer, Config.subst, List.map_append, List.map_cons, List.map_ofFn,
    Function.comp_def, Term.subst_agent, finish_subst]

/-- A compound evaluator allocates environment copies and child results in separate blocks. -/
theorem eval_agent_step (p : Program (φ := φ) dataArity) {n : ℕ}
    (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (ρ : Fin n → Value dataArity) (out : ℕ) (v : Value dataArity)
    (c : Config (netArity dataArity)) :
    (system dataArity p).step (tasks [evalTask dataArity (Term.agent a es) ρ out v] c) =
      some (tasks (List.ofFn fun i ↦ copyTask dataArity (ρ i)
        (fun j : Fin (exprArity dataArity a) ↦ copyWire c.nextName j i))
        (evalLayer dataArity a es (fun i j ↦ Term.var (copyWire c.nextName j i))
          (fun j ↦ Term.var (c.nextName + exprArity dataArity a * n + j.val)) (Term.var out)
          { c with nextName :=
            c.nextName + exprArity dataArity a * n + exprArity dataArity a })) := by
  apply System.step_cons
  simp only [System.contract, evalTask, Term.agent, system, ev, env]
  change some { c with
    equations := (evalRule dataArity (.liftBind a es)).instantiate c.nextName
      (fun _ ↦ Term.var out) (fun i ↦ Value.embed dataArity (ρ i)) ++ c.equations
    nextName := c.nextName + (evalRule dataArity (.liftBind a es)).fresh } = _
  simp only [evalRule, Rule.instantiate, List.map_append, List.map_cons,
    List.map_nil, List.map_ofFn, Function.comp_def, Term.subst_agent, Term.subst_var,
    Sum.elim_inl, Sum.elim_inr, Rule.allocated, copyWire, tasks, copyTask, evalLayer,
    List.append_assoc, finish_subst, Fin.val_castAdd, Fin.val_natAdd, Nat.add_assoc,
    List.singleton_append]

/-- The environment-copying phase fills each child's private environment. -/
theorem reaches_eval_environments (p : Program (φ := φ) dataArity) {n : ℕ}
    (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (ρ : Fin n → Value dataArity) (out : ℕ) (c : Config (netArity dataArity))
    (hc : ∀ x ∈ c.names, x < c.nextName) (ho : out < c.nextName) :
    let m := exprArity dataArity a
    let w := fun (i : Fin n) (j : Fin m) ↦ copyWire c.nextName j i
    let r := fun j : Fin m ↦ c.nextName + m * n + j.val
    let next := c.nextName + m * n + m
    ∃ N, next ≤ N ∧ (system dataArity p).Reaches
      (tasks (List.ofFn fun i ↦ copyTask dataArity (ρ i) (w i))
        (evalLayer dataArity a es (fun i j ↦ Term.var (w i j))
          (fun j ↦ Term.var (r j)) (Term.var out) { c with nextName := next }))
      (evalLayer dataArity a es (fun i _ ↦ Value.embed dataArity (ρ i))
        (fun j ↦ Term.var (r j)) (Term.var out) { c with nextName := N }) := by
  dsimp only
  let m := exprArity dataArity a
  let w := fun (i : Fin n) (j : Fin m) ↦ copyWire c.nextName j i
  let r := fun j : Fin m ↦ c.nextName + m * n + j.val
  let next := c.nextName + m * n + m
  let ts := List.ofFn fun i ↦ copyTask (φ := φ) dataArity (ρ i) (w i)
  let bs := ts.flatMap ClosedTask.results
  let d := evalLayer dataArity a es (fun i j ↦ Term.var (w i j))
    (fun j ↦ Term.var (r j)) (Term.var out) { c with nextName := next }
  have hw : ∀ i i' j j', w i j = w i' j' ↔ i = i' ∧ j = j' := by
    intro i i' j j'
    exact (copyWire_eq_iff c.nextName j j' i i').trans and_comm
  have hlow : ∀ i j, c.nextName ≤ w i j := fun _ _ ↦ Nat.le_add_right _ _
  have hhigh : ∀ i j, w i j < c.nextName + m * n := fun i j ↦ copyWire_lt _ j i
  have hrlo : ∀ j, c.nextName + m * n ≤ r j := fun _ ↦ Nat.le_add_right _ _
  have hrhi : ∀ j, r j < next := fun j ↦ Nat.add_lt_add_left j.isLt _
  have hkeys : bs.map Prod.fst = (List.ofFn fun i ↦ List.ofFn (w i)).flatten := by
    simp only [bs, ts, List.flatMap, copyTask, List.map_flatten,
      List.map_ofFn, Function.comp_def]
  have hn : (bs.map Prod.fst).Nodup := by rw [hkeys]; exact nodup_matrix w hw
  have hclosed : ∀ b ∈ bs, b.2.names = [] := by
    intro b hb
    obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hb
    exact t.closed b ht
  have hcnt : ∀ x, d.names.count x = c.names.count x + (if out = x then 1 else 0) +
      (finSum fun j ↦ if r j = x then 1 else 0) +
      finSum (fun j ↦ (if r j = x then 1 else 0) +
        finSum (fun i ↦ if w i j = x then 1 else 0)) := by
    intro x
    rw [evalLayer_count]
    simp only [Term.names_var, List.count_singleton, beq_iff_eq]
    rfl
  have hc0 : ∀ x, c.nextName ≤ x → c.names.count x = 0 := by
    intro x hx
    apply List.count_eq_zero_of_not_mem
    intro hm
    have hh := hc x hm
    omega
  have hbound : ∀ x ∈ d.names, x < d.nextName := by
    intro x hx
    change x < next
    have hp := List.count_pos_iff.mpr hx
    by_contra! h
    have hco : c.names.count x = 0 := hc0 x (by dsimp only [next] at h; omega)
    have hoo : out ≠ x := by dsimp only [next] at h; omega
    have hro : ∀ j, r j ≠ x := by intro j; have hh := hrhi j; omega
    have hwo : ∀ i j, w i j ≠ x := by
      intro i j
      have hh := hhigh i j
      dsimp only [next] at h
      omega
    rw [hcnt] at hp
    simp only [hco, hoo, hro, hwo, ↓reduceIte, finSum_const_zero, Nat.zero_add] at hp
    omega
  have hcount : ∀ b ∈ bs, d.names.count b.1 = 1 := by
    intro b hb
    obtain ⟨t, ht, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    have hoo : out ≠ w i j := by have hh := hlow i j; omega
    have hro : ∀ l, r l ≠ w i j := by
      intro l
      have hh := hhigh i j
      have hl := hrlo l
      omega
    have hsum : ∀ l, (finSum fun u ↦ if w u l = w i j then 1 else 0) =
        if l = j then 1 else 0 := by
      intro l
      simp only [hw]
      by_cases h : l = j <;> simp [h]
    rw [hcnt]
    simp only [hc0 _ (hlow i j), hoo, hro, ↓reduceIte, finSum_const_zero,
      Nat.zero_add, hsum, finSum_ite_eq]
  obtain ⟨N, hN, hs⟩ := reaches_tasks (system dataArity p) ts
    (by intro t ht; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
        exact copy_realizes dataArity p (ρ i) (w i)) d hbound hn hcount
  let σ := deliverySubst bs
  have hfixed : ∀ x, (∀ i j, x ≠ w i j) → σ x = Term.var x := by
    intro x hx
    apply deliverySubst_of_not_mem
    rw [hkeys]
    intro hm
    obtain ⟨row, hr, hm⟩ := List.mem_flatten.mp hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨j, he⟩ := List.mem_ofFn.mp hm
    exact hx i j he.symm
  have hσold : ∀ x, x < c.nextName → σ x = Term.var x := by
    intro x hx
    apply hfixed x
    intro i j
    have hh := hlow i j
    omega
  have hσr : ∀ j, σ (r j) = Term.var (r j) := by
    intro j
    apply hfixed
    intro i l
    have hh := hhigh i l
    have hl := hrlo j
    omega
  have hσw : ∀ i j, σ (w i j) = Value.embed dataArity (ρ i) := by
    intro i j
    apply deliverySubst_of_mem bs hn (w i j, Value.embed dataArity (ρ i))
    exact List.mem_flatMap.mpr ⟨copyTask dataArity (ρ i) (w i),
      List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩
  have hσc : ({ c with nextName := next } : Config (netArity dataArity)).subst σ =
      { c with nextName := next } :=
    (Config.subst_congr σ Term.var { c with nextName := next }
      (fun x hx ↦ hσold x (hc x hx))).trans (Config.subst_var_self _)
  have hd : resolve bs d = evalLayer dataArity a es
      (fun i _ ↦ Value.embed dataArity (ρ i)) (fun j ↦ Term.var (r j)) (Term.var out)
      { c with nextName := next } := by
    rw [resolve_eq_subst bs d hclosed]
    change (evalLayer dataArity a es _ _ _ _).subst σ = _
    rw [evalLayer_subst]
    simp only [Term.subst_var, hσold out ho, hσr, hσw, hσc]
  rw [hd] at hs
  exact ⟨N, hN, hs⟩

/-- The child-evaluation phase supplies the closed arguments of the parent operation. -/
theorem reaches_eval_children (p : Program (φ := φ) dataArity) {n : ℕ}
    (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (ρ : Fin n → Value dataArity) (vs : Fin (exprArity dataArity a) → Value dataArity)
    (hv : ∀ j, Evaluates dataArity p (es j) ρ (vs j))
    (r : Fin (exprArity dataArity a) → ℕ) (hi : Function.Injective r)
    (out : ℕ) (c : Config (netArity dataArity))
    (hc : ∀ x ∈ c.names, x < c.nextName) (ho : out < c.nextName)
    (hr : ∀ j, r j < c.nextName) (hro : ∀ j, r j ≠ out) (hrc : ∀ j, r j ∉ c.names) :
    ∃ N, c.nextName ≤ N ∧ (system dataArity p).Reaches
      (evalLayer dataArity a es (fun i _ ↦ Value.embed dataArity (ρ i))
        (fun j ↦ Term.var (r j)) (Term.var out) c)
      { c with
        equations := finish dataArity a (Term.var out)
          (fun j ↦ Value.embed dataArity (vs j)) :: c.equations
        nextName := N } := by
  let ts := List.ofFn fun j ↦ evalTask dataArity (es j) ρ (r j) (vs j)
  let bs := ts.flatMap ClosedTask.results
  let d : Config (netArity dataArity) :=
    { c with
      equations := finish dataArity a (Term.var out) (fun j ↦ Term.var (r j)) :: c.equations }
  have hbs : bs = List.ofFn (fun j ↦ (r j, Value.embed dataArity (vs j))) := by
    simp only [bs, ts, List.flatMap, List.map_ofFn, Function.comp_def, evalTask]
    simpa only [List.flatMap, List.map_ofFn, Function.comp_def] using
      List.flatMap_singleton' (List.ofFn fun j ↦ (r j, Value.embed (φ := φ) dataArity (vs j)))
  have hkeys : bs.map Prod.fst = List.ofFn r := by
    rw [hbs]
    simp only [List.map_ofFn, Function.comp_def]
  have hn : (bs.map Prod.fst).Nodup := by
    rw [hkeys]
    apply List.nodup_iff_count_of_mem.mpr
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    simp only [count_ofFn_eq_finSum, hi.eq_iff, finSum_ite_eq]
  have hclosed : ∀ b ∈ bs, b.2.names = [] := by
    intro b hb
    obtain ⟨t, _, ht⟩ := List.mem_flatMap.mp hb
    exact t.closed b ht
  have hcnt : ∀ x, d.names.count x = c.names.count x +
      (if out = x then 1 else 0) + finSum (fun j ↦ if r j = x then 1 else 0) := by
    intro x
    simp only [d, Config.names, List.flatMap_cons, List.count_append, finish_count,
      Term.names_var, List.count_singleton, beq_iff_eq]
    omega
  have hbound : ∀ x ∈ d.names, x < d.nextName := by
    intro x hx
    have hp := List.count_pos_iff.mpr hx
    change x < c.nextName
    by_contra! h
    have hcx : c.names.count x = 0 := List.count_eq_zero_of_not_mem (by
      intro hm
      have hh := hc x hm
      omega)
    have hox : out ≠ x := by omega
    have hrx : ∀ j, r j ≠ x := by intro j; have hh := hr j; omega
    rw [hcnt] at hp
    simp only [hcx, hox, hrx, ↓reduceIte, finSum_const_zero, Nat.zero_add] at hp
    omega
  have hcount : ∀ b ∈ bs, d.names.count b.1 = 1 := by
    intro b hb
    rw [hbs] at hb
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hb
    rw [hcnt]
    simp only [List.count_eq_zero_of_not_mem (hrc j), Ne.symm (hro j), ↓reduceIte,
      Nat.zero_add, hi.eq_iff, finSum_ite_eq]
  obtain ⟨N, hN, hs⟩ := reaches_tasks (system dataArity p) ts
    (by intro t ht; obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht; exact hv j (r j))
    d hbound hn hcount
  let σ := deliverySubst bs
  have hσr : ∀ j, σ (r j) = Value.embed dataArity (vs j) := by
    intro j
    apply deliverySubst_of_mem bs hn (r j, Value.embed dataArity (vs j))
    rw [hbs]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩
  have hσout : σ out = Term.var out := by
    apply deliverySubst_of_not_mem
    rw [hkeys]
    intro hm
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
    exact hro j hj
  have hσc : c.subst σ = c := by
    apply (Config.subst_congr σ Term.var c ?_).trans (Config.subst_var_self c)
    intro x hx
    apply deliverySubst_of_not_mem
    rw [hkeys]
    intro hm
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hm
    exact hrc j hx
  have hd : resolve bs d =
      { c with
        equations := finish dataArity a (Term.var out)
          (fun j ↦ Value.embed dataArity (vs j)) :: c.equations } := by
    rw [resolve_eq_subst bs d hclosed]
    change { c.subst σ with equations :=
      ((finish dataArity a (Term.var out) (fun j ↦ Term.var (r j))).1.subst σ,
       (finish dataArity a (Term.var out) (fun j ↦ Term.var (r j))).2.subst σ) ::
         (c.subst σ).equations } = _
    rw [finish_subst]
    simp only [Term.subst_var, hσout, hσr, hσc]
  rw [hd] at hs
  refine ⟨N, hN, ?_⟩
  simpa only [ts, tasks, List.map_ofFn, Function.comp_def, evalTask, evalLayer, d] using hs

/-- Contextual evaluations of the children and parent operation compose to evaluate the
compound expression through the actual sequential interaction rules. -/
theorem evaluates_agent (p : Program (φ := φ) dataArity) {n : ℕ}
    (a : Symbol (δ := δ) (φ := φ))
    (es : Fin (exprArity dataArity a) → Expr (φ := φ) dataArity n)
    (ρ : Fin n → Value dataArity) (vs : Fin (exprArity dataArity a) → Value dataArity)
    (v : Value dataArity) (hv : ∀ j, Evaluates dataArity p (es j) ρ (vs j))
    (hf : ∀ out, (finishTask dataArity a vs out v).Realizes (system dataArity p)) :
    Evaluates dataArity p (Term.agent a es) ρ v := by
  intro out c hc hn hx
  have ho : out < c.nextName := hc out (List.count_pos_iff.mp (by
    rw [hx (out, Value.embed dataArity v) (List.mem_singleton_self _)]; omega))
  let m := exprArity dataArity a
  let r := fun j : Fin m ↦ c.nextName + m * n + j.val
  let next := c.nextName + m * n + m
  obtain ⟨N₁, hN₁, hs₁⟩ := reaches_eval_environments dataArity p a es ρ out c hc ho
  have hbase : c.nextName ≤ N₁ :=
    Nat.le_trans (by change c.nextName ≤ next; dsimp [next]; omega) hN₁
  let c₁ := { c with nextName := N₁ }
  have hc₁ : ∀ x ∈ c₁.names, x < c₁.nextName :=
    fun x hx ↦ Nat.lt_of_lt_of_le (hc x hx) hbase
  have hri : Function.Injective r := by
    intro i j h
    exact Fin.ext (Nat.add_left_cancel h)
  have hrl : ∀ j, c.nextName ≤ r j := by intro j; dsimp only [r]; omega
  have hrh : ∀ j, r j < N₁ := by
    intro j
    have hj := j.isLt
    dsimp only [r]
    change c.nextName + m * n + m ≤ N₁ at hN₁
    omega
  obtain ⟨N₂, hN₂, hs₂⟩ := reaches_eval_children dataArity p a es ρ vs hv r hri out c₁ hc₁
    (Nat.lt_of_lt_of_le ho hbase) hrh
    (by intro j; have hh := hrl j; omega)
    (by intro j hj; have hh := hc (r j) hj; have hl := hrl j; omega)
  let c₂ := { c with nextName := N₂ }
  have hbase₂ : c.nextName ≤ N₂ := Nat.le_trans hbase hN₂
  obtain ⟨N₃, hN₃, hs₃⟩ := hf out c₂
    (fun x hx ↦ Nat.lt_of_lt_of_le (hc x hx) hbase₂)
    (by simpa only [finishTask, evalTask] using hn)
    (by simpa only [finishTask, evalTask, c₂, Config.names] using hx)
  rw [resolve_with_nextName _ c N₂ (finishTask dataArity a vs out v).closed] at hs₃
  refine ⟨N₃, Nat.le_trans hbase₂ hN₃, ?_⟩
  have hs := System.reaches_trans _
    (System.reaches_of_step _ (eval_agent_step dataArity p a es ρ out v c)) hs₁
  have hs' := System.reaches_trans _ hs hs₂
  exact System.reaches_trans _ hs' hs₃

/-- A constructor expression evaluates its fields and returns their constructor value. -/
theorem evaluates_con (p : Program (φ := φ) dataArity) {n : ℕ} (a : δ)
    (es : Fin (dataArity a) → Expr (φ := φ) dataArity n)
    (ρ : Fin n → Value dataArity) (vs : Fin (dataArity a) → Value dataArity)
    (hv : ∀ j, Evaluates dataArity p (es j) ρ (vs j)) :
    Evaluates dataArity p (Expr.con a es) ρ (Term.agent (.inl a) vs) :=
  evaluates_agent dataArity p (.inl a) es ρ vs _ hv (finish_con_realizes dataArity p a vs)

/-- A call expression evaluates its arguments and then performs the resulting closed call. -/
theorem evaluates_call (p : Program (φ := φ) dataArity) {n : ℕ} (f : φ)
    (x : Expr (φ := φ) dataArity n) (xs : List (Expr (φ := φ) dataArity n))
    (ρ : Fin n → Value dataArity) (v result : Value dataArity)
    (vs : Fin xs.length → Value dataArity)
    (hx : Evaluates dataArity p x ρ v)
    (hxs : ∀ j, Evaluates dataArity p (xs.get j) ρ (vs j))
    (hc : Calls dataArity p f v (List.ofFn vs) result) :
    Evaluates dataArity p (Expr.call f x xs) ρ result := by
  apply evaluates_agent dataArity p (.inr (f, xs.length)) (Fin.cases x xs.get) ρ
    (Fin.cases v vs) result
  · intro j
    exact Fin.cases hx (fun j ↦ hxs j) j
  · intro out
    have he := finishTask_call_congr dataArity f (List.length_ofFn (f := vs)) v
      (List.ofFn vs).get vs (fun i ↦ List.get_ofFn vs i) out result
    exact he ▸ hc out

end Geb.InteractionNet.FirstOrder

end
