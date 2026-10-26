/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

import Geb.Prototypes.InteractionNet.Substitution
public import Geb.Prototypes.InteractionNet.Calculus
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Delivering closed results

A computed value is delivered by an equation between its output name and a closed term.
If the output name has one occurrence in the remaining configuration, the sequential
reducer substitutes the value there. Deliveries with distinct output names compose: they
cannot capture each other's wires because the delivered values are closed.

## Main definitions

* {lit}`deliveries` — a list of output equations in front of a continuation configuration.
* {lit}`resolve` — substitute a list of closed results into their continuation.

## Main statements

* {lit}`reaches_delivery` — the reducer delivers one computed value.
* {lit}`deliveries_count` — the wire counts of pending closed deliveries.
* {lit}`reaches_resolve` — distinct closed deliveries compose in the sequential reducer.
* {lit}`resolve_eq_subst` — a closed delivery batch is one simultaneous substitution.

## Tags

interaction calculus, evaluation, continuation, substitution, output
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

/-- Pending output equations before a continuation configuration. -/
def deliveries (bs : List (ℕ × Term arity ℕ)) (c : Config arity) : Config arity :=
  { c with equations := (bs.map fun b ↦ (Term.var b.1, b.2)) ++ c.equations }

/-- Substitute the computed results in their listed order. -/
def resolve (bs : List (ℕ × Term arity ℕ)) (c : Config arity) : Config arity :=
  bs.foldl (fun d b ↦ d.subst fun x ↦ if x = b.1 then b.2 else Term.var x) c

/-- The simultaneous substitution specified by a list of closed deliveries. -/
def deliverySubst (bs : List (ℕ × Term arity ℕ)) (x : ℕ) : Term arity ℕ :=
  (bs.lookup x).getD (Term.var x)

/-- A substitution fixing the output names acts on the pending result terms. -/
theorem subst_deliveries_of_fixed (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (σ : ℕ → Term arity ℕ) (h : ∀ b ∈ bs, σ b.1 = Term.var b.1) :
    (deliveries bs c).subst σ =
      deliveries (bs.map fun b ↦ (b.1, b.2.subst σ)) (c.subst σ) := by
  have he : bs.map (fun b ↦ ((Term.var b.1).subst σ, b.2.subst σ)) =
      bs.map (fun b ↦ (Term.var b.1, b.2.subst σ)) := by
    apply List.map_congr_left
    intro b hb
    simp only [Term.subst_var, h b hb]
  simp only [deliveries, Config.subst, List.map_append, List.map_map, Function.comp_def, he]

/-- Resolving closed deliveries is one simultaneous substitution. -/
theorem resolve_eq_subst (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (hc : ∀ b ∈ bs, b.2.names = []) : resolve bs c = c.subst (deliverySubst bs) := by
  apply List.rec (motive := fun bs ↦ ∀ c : Config arity,
    (∀ b ∈ bs, b.2.names = []) → resolve bs c = c.subst (deliverySubst bs))
    (fun c _ ↦ (Config.subst_var_self c).symm) (fun b bs ih c h ↦ ?_) bs c hc
  rcases b with ⟨y, t⟩
  rw [resolve, List.foldl_cons]
  change resolve bs (c.subst _) = _
  rw [ih _ (fun d hd ↦ h d (List.mem_cons_of_mem _ hd)), Config.subst_subst]
  apply congrArg (fun σ ↦ c.subst σ)
  funext x
  by_cases hx : x = y
  · simp only [hx, ↓reduceIte,
      Term.subst_of_names_eq_nil _ t (h (y, t) (List.mem_cons_self ..)),
      deliverySubst, List.lookup_cons_self, Option.getD_some]
  · have hxy : (x == y) = false := by simp [hx]
    simp [hx, deliverySubst, List.lookup_cons, hxy]

/-- A wire outside the delivery list is left as a variable. -/
theorem deliverySubst_of_not_mem (bs : List (ℕ × Term arity ℕ)) (x : ℕ)
    (h : x ∉ bs.map Prod.fst) : deliverySubst bs x = Term.var x := by
  have hn : bs.lookup x = none := by
    apply List.lookup_eq_none_iff.mpr
    intro b hb
    have hx : x ≠ b.1 := fun he ↦ h (he ▸ List.mem_map_of_mem hb)
    simpa using hx
  simp only [deliverySubst, hn, Option.getD_none]

/-- A delivery on a unique wire supplies that wire's replacement. -/
theorem deliverySubst_of_mem (bs : List (ℕ × Term arity ℕ))
    (hn : (bs.map Prod.fst).Nodup) (b : ℕ × Term arity ℕ) (hb : b ∈ bs) :
    deliverySubst bs b.1 = b.2 := by
  apply List.rec (motive := fun bs ↦ (bs.map Prod.fst).Nodup →
    ∀ b ∈ bs, deliverySubst bs b.1 = b.2)
    (fun _ b hb ↦ False.elim (List.not_mem_nil hb)) (fun d ds ih h b hb ↦ ?_) bs hn b hb
  rcases d with ⟨x, t⟩
  have hd := List.nodup_cons.mp h
  rcases List.mem_cons.mp hb with rfl | hb
  · simp [deliverySubst]
  · have hx : (b.1 == x) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro he
      have hm : b.1 ∈ ds.map Prod.fst := List.mem_map_of_mem hb
      exact hd.1 (he ▸ hm)
    simpa only [deliverySubst, List.lookup_cons, hx] using ih hd.2 b hb

/-- Resolving two batches is the composition of their resolutions. -/
theorem resolve_append (bs ds : List (ℕ × Term arity ℕ)) (c : Config arity) :
    resolve (bs ++ ds) c = resolve ds (resolve bs c) := by
  exact List.foldl_append

/-- Resolution never changes the next-name supply. -/
@[simp] theorem resolve_nextName (bs : List (ℕ × Term arity ℕ)) (c : Config arity) :
    (resolve bs c).nextName = c.nextName := by
  apply List.rec (motive := fun bs ↦ ∀ c : Config arity,
    (resolve bs c).nextName = c.nextName) (fun _ ↦ rfl)
    (fun b bs ih c ↦ ih (c.subst _)) bs c

/-- Changing the supply commutes with delivery of closed results. -/
theorem resolve_with_nextName (bs : List (ℕ × Term arity ℕ)) (c : Config arity) (n : ℕ)
    (hc : ∀ b ∈ bs, b.2.names = []) :
    resolve bs { c with nextName := n } = { resolve bs c with nextName := n } := by
  rw [resolve_eq_subst bs _ hc, resolve_eq_subst bs _ hc]
  rfl

/-- Closed deliveries preserve the count of every other wire. -/
theorem resolve_count_of_not_mem (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (hc : ∀ b ∈ bs, b.2.names = []) (x : ℕ) (hx : x ∉ bs.map Prod.fst) :
    (resolve bs c).names.count x = c.names.count x := by
  apply List.rec (motive := fun bs ↦ ∀ c : Config arity,
    (∀ b ∈ bs, b.2.names = []) → x ∉ bs.map Prod.fst →
    (resolve bs c).names.count x = c.names.count x)
    (fun _ _ _ ↦ rfl) (fun b bs ih c h hn ↦ ?_) bs c hc hx
  have hn' : x ≠ b.1 ∧ x ∉ bs.map Prod.fst := by simpa only [List.map_cons,
    List.mem_cons, not_or] using hn
  change (resolve bs (c.subst _)).names.count x = _
  rw [ih _ (fun d hd ↦ h d (List.mem_cons_of_mem _ hd)) hn'.2]
  exact c.count_names_subst_closed b.1 x b.2 (h b (List.mem_cons_self ..)) hn'.1

/-- Resolving closed results cannot introduce any free name. -/
theorem names_resolve_subset (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (hc : ∀ b ∈ bs, b.2.names = []) : (resolve bs c).names ⊆ c.names := by
  apply List.rec (motive := fun bs ↦ ∀ c : Config arity,
    (∀ b ∈ bs, b.2.names = []) → (resolve bs c).names ⊆ c.names)
    (fun c _ ↦ List.Subset.refl c.names) (fun b bs ih c h ↦ ?_) bs c hc
  change (resolve bs (c.subst _)).names ⊆ c.names
  apply List.Subset.trans (ih _ (fun d hd ↦ h d (List.mem_cons_of_mem _ hd)))
  rw [Config.names_subst_closed _ _ _ (h b (List.mem_cons_self ..))]
  exact fun _ hx ↦ (List.mem_filter.mp hx).1

/-- A context containing none of the delivered wires is unchanged by their resolution. -/
theorem resolve_eq_self (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (hc : ∀ b ∈ bs, b.2.names = [])
    (hd : ∀ x ∈ c.names, x ∉ bs.map Prod.fst) : resolve bs c = c := by
  rw [resolve_eq_subst bs c hc]
  exact (c.subst_congr _ _ (fun x hx ↦ deliverySubst_of_not_mem bs x (hd x hx))).trans
    (Config.subst_var_self c)

/-- The reducer delivers a closed value to a wire that has exactly one remaining end. -/
theorem reaches_delivery (s : System arity) (c : Config arity) (x : ℕ) (t : Term arity ℕ)
    (ht : t.names = []) (hx : c.names.count x = 1) :
    s.Reaches (deliveries [(x, t)] c)
      (c.subst fun y ↦ if y = x then t else Term.var y) := by
  apply s.reaches_of_step
  apply s.step_cons (Term.var x, t) c
  cases t with
  | pure y => simp [-List.count_eq_one_of_mem, Term.names] at ht
  | liftBind a ts =>
    change c.eliminate x (.liftBind a ts) = _
    simp only [Config.eliminate, ht, List.not_mem_nil, not_false_eq_true, hx, and_self,
      ↓reduceIte]

/-- Closed delivery equations add only their output names to the continuation's counts. -/
theorem deliveries_count (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (h : ∀ b ∈ bs, b.2.names = []) (x : ℕ) :
    (deliveries bs c).names.count x = c.names.count x + (bs.map Prod.fst).count x := by
  have he : (bs.flatMap fun b ↦ [b.1] ++ b.2.names) = bs.map Prod.fst := by
    rw [List.map_eq_flatMap]
    apply List.flatMap_congr
    intro b hb
    simp [-List.count_eq_one_of_mem, h b hb]
  simp only [deliveries, Config.names, List.flatMap_append, List.flatMap_map,
    Term.names_var, he, List.count_append]
  omega

/-- Substituting a closed result leaves pending deliveries on other wires unchanged. -/
theorem subst_deliveries (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (x : ℕ) (t : Term arity ℕ) (hclosed : ∀ b ∈ bs, b.2.names = [])
    (hnot : x ∉ bs.map Prod.fst) :
    (deliveries bs c).subst (fun y ↦ if y = x then t else Term.var y) =
      deliveries bs (c.subst fun y ↦ if y = x then t else Term.var y) := by
  let σ := fun y ↦ if y = x then t else Term.var y
  have he : bs.map (fun b ↦ ((Term.var b.1).subst σ, b.2.subst σ)) =
      bs.map (fun b ↦ (Term.var b.1, b.2)) := by
    apply List.map_congr_left
    intro b hb
    have hne : b.1 ≠ x := by
      intro heq
      exact hnot (heq ▸ List.mem_map_of_mem hb)
    simp only [Term.subst_var, σ, hne, ↓reduceIte,
      Term.subst_of_names_eq_nil σ b.2 (hclosed b hb)]
  cases c
  simp only [deliveries, Config.subst, List.map_append, List.map_map]
  change Config.mk _ (bs.map (fun b ↦ ((Term.var b.1).subst σ, b.2.subst σ)) ++ _) _ = _
  rw [he]

/-- A list of closed results on distinct wires is delivered to its continuation in order. -/
theorem reaches_resolve (s : System arity) (bs : List (ℕ × Term arity ℕ)) (c : Config arity)
    (hclosed : ∀ b ∈ bs, b.2.names = []) (hnodup : (bs.map Prod.fst).Nodup)
    (hcount : ∀ b ∈ bs, c.names.count b.1 = 1) :
    s.Reaches (deliveries bs c) (resolve bs c) := by
  apply List.rec (motive := fun bs ↦ ∀ c : Config arity,
    (∀ b ∈ bs, b.2.names = []) → (bs.map Prod.fst).Nodup →
    (∀ b ∈ bs, c.names.count b.1 = 1) → s.Reaches (deliveries bs c) (resolve bs c))
    (fun c _ _ _ ↦ s.reaches_refl c) (fun b bs ih c hc hn hx ↦ ?_) bs c hclosed hnodup hcount
  have hb := hc b (List.mem_cons_self ..)
  have hbs : ∀ d ∈ bs, d.2.names = [] := fun d hd ↦ hc d (List.mem_cons_of_mem _ hd)
  have hnd : b.1 ∉ bs.map Prod.fst ∧ (bs.map Prod.fst).Nodup := List.nodup_cons.mp hn
  have hwire : (deliveries bs c).names.count b.1 = 1 := by
    rw [deliveries_count bs c hbs, List.count_eq_zero_of_not_mem hnd.1, Nat.add_zero]
    exact hx b (List.mem_cons_self ..)
  have hstep := reaches_delivery s (deliveries bs c) b.1 b.2 hb hwire
  rw [subst_deliveries bs c b.1 b.2 hbs hnd.1] at hstep
  apply s.reaches_trans hstep
  apply ih _ hbs hnd.2
  intro d hd
  have hne : d.1 ≠ b.1 := by
    intro heq
    exact hnd.1 (heq ▸ List.mem_map_of_mem hd)
  rw [Config.count_names_subst_closed c b.1 d.1 b.2 hb hne]
  exact hx d (List.mem_cons_of_mem _ hd)

end Geb.InteractionNet

end
