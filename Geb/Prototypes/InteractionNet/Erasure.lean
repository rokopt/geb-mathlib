/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Program
import Geb.Cslib.Foundations.Data.PFunctor.Free
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Erasure of constructor values

A value contains only constructors and their finite trees of fields, including captured
environments. A zero-output fan erases such a value constructor by constructor. The proof
follows the sequential reducer itself: the pending child erasures precede the continuation,
so no step of that continuation is taken before erasure finishes. No names are allocated.

## Main definitions

* {lit}`Value`, {lit}`Value.embed` — closed constructor values and their net representation.
* {lit}`eraseTasks` — pending erasures before a continuation configuration.

## Main statements

* {lit}`Value.embed_names` — embedded values have no wire names.
* {lit}`reaches_erase` — erasure terminates on every finite constructor value.

## Tags

interaction net, erasure, termination, constructor, continuation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- A finite tree of data and environment constructors, with no free wire names. -/
abbrev Value := Term (constructorArity dataArity) Empty

/-- Include a constructor value in the interaction system's larger signature. -/
def Value.embed : Value dataArity → Term (netArity (φ := φ) dataArity) ℕ :=
  PFunctor.FreeM.rec Empty.elim (fun a _ es ↦ Term.agent (.inl a) es)

/-- Embedding a constructor embeds each of its fields. -/
@[simp] theorem Value.embed_agent (a : δ ⊕ ℕ)
    (vs : Fin (constructorArity dataArity a) → Value dataArity) :
    Value.embed (φ := φ) dataArity (Term.agent a vs) =
      Term.agent (.inl a) (fun i ↦ Value.embed dataArity (vs i)) := rfl

/-- Constructor values contain no wire occurrences. -/
@[simp] theorem Value.embed_names (v : Value dataArity) :
    (Value.embed (φ := φ) dataArity v).names = [] :=
  PFunctor.FreeM.rec (fun x ↦ x.elim) (fun a vs ih ↦ by
    change (Term.agent (.inl a) (fun i ↦ Value.embed dataArity (vs i))).names = []
    simp [Term.names_agent, ih]) v

/-- Place zero-output fans on the listed terms before a continuation. -/
def eraseTasks (ts : List (Term (netArity (φ := φ) dataArity) ℕ))
    (c : Config (netArity (φ := φ) dataArity)) :
    Config (netArity (φ := φ) dataArity) :=
  { c with equations := ts.map (fun t ↦ (Term.agent (fan dataArity 0) Fin.elim0, t)) ++
      c.equations }

/-- Erasing a constructor exposes precisely the erasures of its fields. -/
theorem erase_step (p : Program (φ := φ) dataArity) (a : δ ⊕ ℕ)
    (ts : Fin (constructorArity dataArity a) → Term (netArity dataArity) ℕ)
    (c : Config (netArity dataArity)) :
    (system dataArity p).step (eraseTasks dataArity [Term.agent (.inl a) ts] c) =
      some (eraseTasks dataArity (List.ofFn ts) c) := by
  apply System.step_cons
  change some { c with
    equations := (fanRule (φ := φ) dataArity 0 a).instantiate c.nextName Fin.elim0 ts ++
      c.equations
    nextName := c.nextName + (fanRule (φ := φ) dataArity 0 a).fresh } = _
  simp only [fanRule, Rule.instantiate, Nat.mul_zero,
    List.ofFn_zero, List.append_nil, List.map_ofFn, Term.subst_agent, Term.subst_var,
    Sum.elim_inl, Sum.elim_inr, Nat.add_zero, eraseTasks, Function.comp_def]
  congr 1
  congr 1
  apply congrArg (fun es ↦ es ++ c.equations)
  apply congrArg List.ofFn
  funext i
  congr 1
  apply congrArg (Term.agent (fan dataArity 0))
  funext j
  exact j.elim0

/-- Independent erasures compose in the order used by the sequential reducer. -/
theorem reaches_eraseTasks (p : Program (φ := φ) dataArity)
    (ts : List (Term (netArity dataArity) ℕ))
    (h : ∀ t ∈ ts, ∀ c, (system dataArity p).Reaches (eraseTasks dataArity [t] c) c)
    (c : Config (netArity dataArity)) :
    (system dataArity p).Reaches (eraseTasks dataArity ts c) c := by
  apply List.rec (motive := fun ts ↦
    (∀ t ∈ ts, ∀ c, (system dataArity p).Reaches (eraseTasks dataArity [t] c) c) →
    (system dataArity p).Reaches (eraseTasks dataArity ts c) c)
    (fun _ ↦ System.reaches_refl _ c) (fun t ts ih ht ↦ ?_) ts h
  apply System.reaches_trans _ (ht t (List.mem_cons_self ..) (eraseTasks dataArity ts c))
  exact ih (fun u hu ↦ ht u (List.mem_cons_of_mem _ hu))

/-- The actual sequential reducer erases every constructor value in finitely many steps,
leaving the entire continuation and its name supply unchanged. -/
theorem reaches_erase (p : Program (φ := φ) dataArity) (v : Value dataArity)
    (c : Config (netArity dataArity)) :
    (system dataArity p).Reaches (eraseTasks dataArity [Value.embed dataArity v] c) c := by
  apply PFunctor.FreeM.rec (motive := fun v ↦ ∀ c,
    (system dataArity p).Reaches (eraseTasks dataArity [Value.embed dataArity v] c) c)
    (fun x ↦ x.elim) (fun a vs ih c ↦ ?_) v c
  apply System.reaches_trans _ (System.reaches_of_step _ (erase_step dataArity p a _ c))
  apply reaches_eraseTasks
  intro t ht
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
  exact ih i

end Geb.InteractionNet.FirstOrder

end
