/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.Compose
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Theorems as constants of an extension of the signature

The theorems of a development of the internal language enter the signature
{name}`Geb.LF.Topos.sig` as constants of an extension of it, past its own declarations, as a
logical framework's signature takes each proved lemma as a constant
({cite}`HarperLicata2007`, Section 2). A theorem in no object variables, of the variables of its
context, hypotheses and a conclusion, is the constant of the product over a family of terms of
each variable's type, the outermost first, of the products over the families of proofs of its
hypotheses, none in the scope of another, into the family of proofs of its conclusion
({lit}`thmTy`): its context is encoded as {name}`Geb.LF.Topos.encCtx` encodes one, and its
formulas as {name}`Geb.LF.Topos.enc` encodes them, in the scope of the variables. An application
of the constant decodes to the language's application of the theorem's entry
({lit}`Geb.LF.Topos.decPfThm`).

The application instantiates the declaration along its spine. The domains of the variables are
closed, so the leading arguments are substituted, one after another, into the declaration's body
alone ({lit}`hsubs`, {lit}`spine_piTele`), and the substitution passes into each hypothesis and
the conclusion ({lit}`hsubs_arrows_pf`). Passing under a hypothesis's binder needs the inversion
of substitution into a weakened expression, which holds at the base type of the terms, where a
reduction has a value exactly at the empty spine ({lit}`hsub_shift_inv`). Decoding commutes with
the substitutions ({lit}`dec_hsubs`), so the substituted formulas decode to the instances of the
theorem's formulas that the language's checker compares.

## Main definitions

* {lit}`piTele`, {lit}`arrows` — the products over a list of domains, and the arrows from a list
  of families.
* {lit}`hsubs` — the substitutions of a list of terms for the variables of a scope.
* {lit}`thmTy` — the declaration of a theorem.
* {lit}`ThmsDecl` — an extension of the signature declares the theorems that a table names.

## Main statements

* {lit}`hsub_shift_inv` — at a base type, the substitution into a weakened expression is the
  weakened substitution.
* {lit}`spine_piTele`, {lit}`spine_arrows` — the instantiation of a theorem's declaration.
* {lit}`dec_hsubs` — decoding commutes with the substitutions.

## References

* {cite}`HarperLicata2007`, Section 2, for signatures and their constants.

## Tags

logical framework, LF, signature, theorem, lemma, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Globals Entry Thm ctxObj stdEnv)

/-- The products over each of a list of domains, the outermost first, into a body. -/
def piTele (Ds : List Expr) (R : Expr) : Expr := Ds.foldr Expr.pi R

/-- The products over each of a list of domains, none in the scope of another, the first
outermost, into a codomain. -/
def arrows (Hs : List Expr) (C : Expr) : Expr := Hs.foldr Expr.arrow C

/-- The products over a list of domains, at its first. -/
theorem piTele_cons (D : Expr) (Ds : List Expr) (R : Expr) :
    piTele (D :: Ds) R = Expr.pi D (piTele Ds R) :=
  rfl

/-- The arrows from a list of domains, at its first. -/
theorem arrows_cons (H : Expr) (Hs : List Expr) (C : Expr) :
    arrows (H :: Hs) C = Expr.arrow H (arrows Hs C) :=
  rfl

/-- A decision that holds is of a proposition that holds, at the decision procedure the decision
is stated at, which is unified rather than synthesized. -/
theorem of_decide_eq_true_at {p : Prop} {inst : Decidable p} (h : @decide p inst = true) : p :=
  of_decide_eq_true h

/-- A lifted renaming moves an index past the binders as the renaming moves the index below
them. -/
theorem iterate_liftR_add (ρ : ℕ → ℕ) (j : ℕ) :
    ∀ b, liftR^[b] ρ (j + b) = ρ j + b :=
  Nat.rec rfl fun b ih ↦ by
    rw [Function.iterate_succ_apply']
    exact congrArg (· + 1) ih

/-- Lifting preserves the injectivity of a renaming. -/
theorem liftR_injective {ρ : ℕ → ℕ} (h : Function.Injective ρ) : Function.Injective (liftR ρ) :=
  fun i i' e ↦ by
    rcases i with _ | i <;> rcases i' with _ | i'
    · rfl
    · exact Nat.noConfusion (show 0 = ρ i' + 1 from e)
    · exact Nat.noConfusion (show ρ i + 1 = 0 from e)
    · exact congrArg (· + 1) (h (Nat.succ.inj e))

/-- Iterated lifting preserves the injectivity of a renaming. -/
theorem iterate_liftR_injective {ρ : ℕ → ℕ} (h : Function.Injective ρ) :
    ∀ b, Function.Injective (liftR^[b] ρ) :=
  Nat.rec h fun b ih ↦ by
    rw [Function.iterate_succ_apply']
    exact liftR_injective ih

/-- A list of partial values has a list of values exactly when each has a value. -/
theorem isSome_mapM_id {β : Type} : ∀ xs : List (Option β),
    (xs.mapM id).isSome = xs.all Option.isSome :=
  List.rec rfl fun x xs ih ↦ by
    rcases x with _ | x
    · rfl
    · rw [List.all_cons, Option.isSome_some, Bool.true_and, ← ih]
      cases h : xs.mapM id <;> simp [List.mapM_cons, h]

/-- Where a reduction's having a value depends only on the length of the spine, the substitution
into an expression renamed by an injective map has a value only where the substitution into the
expression has one, whatever the substituted terms. -/
theorem hsubWith_isSome_of_rename {red : Expr → List Expr → Option Expr}
    (hred : ∀ n n' ms ms', ms.length = ms'.length → (red n ms).isSome = (red n' ms').isSome) :
    ∀ (e : Expr) (ρ : ℕ → ℕ), Function.Injective ρ → ∀ (n n' : Expr) (j : ℕ),
      (hsubWith red (e.rename ρ) n' (ρ j)).isSome = true →
        (hsubWith red e n j).isSome = true :=
  RoseTree.ind fun l cs ih ρ hρ n n' j h ↦ by
    have nonvar : (∀ i, l ≠ .app (.var i)) →
        (hsubWith red (RoseTree.node l cs) n j).isSome = true := by
      intro hl
      rw [rename_node, Label.rename_of_ne hl, hsubWith_node_of_ne red l hl] at h
      rw [hsubWith_node_of_ne red l hl]
      simp only [Option.map_eq_map, Option.isSome_map, isSome_mapM_id, List.all_eq_true] at h ⊢
      intro x hx
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
      have hk' := h _ (List.getElem_mem (by simpa using hk))
      simp only [List.getElem_map, List.getElem_zipIdx, zero_add] at hk' ⊢
      rw [← iterate_liftR_add] at hk'
      exact ih _ (List.getElem_mem _) _ (iterate_liftR_injective hρ _) _ _ _ hk'
    rcases l with _ | _ | _ | (i | c)
    · exact nonvar fun i h ↦ by cases h
    · exact nonvar fun i h ↦ by cases h
    · exact nonvar fun i h ↦ by cases h
    · rw [show RoseTree.node (.app (.var i)) cs = Expr.var i cs from rfl, rename_var,
        Expr.var, Expr.app, hsubWith_var] at h
      rw [hsubWith_var]
      rcases hms' : ((cs.map fun m ↦ Expr.rename m ρ).map fun c ↦ hsubWith red c n' (ρ j)).mapM id
        with _ | ms'
      · rw [hms'] at h
        exact absurd h (by simp)
      have hall : ((cs.map fun c ↦ hsubWith red c n j).mapM id).isSome = true := by
        rw [isSome_mapM_id, List.all_eq_true]
        have h' := (isSome_mapM_id _).symm.trans (congrArg Option.isSome hms')
        rw [Option.isSome_some, List.all_eq_true] at h'
        intro x hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact ih c hc ρ hρ n n' j (h' _ (List.mem_map_of_mem (List.mem_map_of_mem hc)))
      obtain ⟨ms, hms⟩ := Option.isSome_iff_exists.mp hall
      rw [hms, Option.bind_some]
      rw [hms', Option.bind_some] at h
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte] at h ⊢
        rw [hred n n' ms ms' (by
          rw [(getElem_of_mapM_id_eq_some hms).1.symm, (getElem_of_mapM_id_eq_some hms').1.symm]
          simp)]
        exact h
      · simp only [hij, ↓reduceIte, Option.isSome_some]
    · exact nonvar fun i h ↦ by cases h

/-- At a base type a reduction has a value exactly at the empty spine. -/
theorem isSome_reduce_base (c : ℕ) (n : Expr) (ms : List Expr) :
    (reduce (RoseTree.node (.base c) []) n ms).isSome = ms.isEmpty := by
  rw [reduce_node]
  rcases ms with _ | ⟨m, ms⟩ <;> rfl

/-- Weakening agrees with itself around a variable and its successor. -/
theorem holeRen_succ (j : ℕ) : HoleRen Nat.succ Nat.succ j (j + 1) := by
  refine ⟨rfl, fun i hi ↦ ⟨fun e ↦ hi (Nat.succ.inj e), ?_⟩⟩
  unfold renumber
  by_cases h : j < i
  · rw [ite_eq_left h, ite_eq_left (Nat.succ_lt_succ h)]
    omega
  · rw [ite_eq_right h, ite_eq_right fun h' ↦ h (Nat.lt_of_succ_lt_succ h')]

/-- At a base type the substitution into a weakened expression, of the weakened term for the
successor of a variable, has a value only where the substitution into the expression for the
variable has one, the former the weakening of the latter. -/
theorem hsub_shift_inv {c : ℕ} {n B b : Expr} {j : ℕ}
    (h : hsub (RoseTree.node (.base c) []) n.shift B.shift (j + 1) = some b) :
    ∃ B', hsub (RoseTree.node (.base c) []) n B j = some B' ∧ b = B'.shift := by
  have hs := hsubWith_isSome_of_rename (red := reduce (RoseTree.node (.base c) []))
    (fun n n' ms ms' hl ↦ by
      rw [isSome_reduce_base, isSome_reduce_base]
      rcases ms with _ | _ <;> rcases ms' with _ | _ <;> first | rfl | exact Nat.noConfusion hl)
    B Nat.succ (fun _ _ e ↦ Nat.succ.inj e) n n.shift j (Option.isSome_iff_exists.mpr ⟨b, h⟩)
  obtain ⟨B', hB'⟩ := Option.isSome_iff_exists.mp hs
  refine ⟨B', hB', ?_⟩
  have hf := hsubWith_holeRen (reduce_rename _) B n j (j + 1) Nat.succ Nat.succ B'
    (holeRen_succ j) hB'
  rw [← hsub_eq] at hf
  exact Option.some.inj (h.symm.trans hf)

/-- At a base type, the substitution into products over closed domains substitutes into their
body under them. -/
theorem hsub_piTele {α : SimpleTy} {R : Expr} :
    ∀ {Ds : List Expr}, (∀ D ∈ Ds, D.FreeBelow 0 = true) → ∀ {n c : Expr} {j : ℕ},
      hsub α n (piTele Ds R) j = some c →
        ∃ R', hsub α (Expr.shift^[Ds.length] n) R (j + Ds.length) = some R' ∧ c = piTele Ds R' := by
  intro Ds
  refine List.rec (motive := fun Ds ↦ (∀ D ∈ Ds, D.FreeBelow 0 = true) → ∀ {n c : Expr} {j : ℕ},
      hsub α n (piTele Ds R) j = some c →
        ∃ R', hsub α (Expr.shift^[Ds.length] n) R (j + Ds.length) = some R' ∧ c = piTele Ds R')
    (fun _ {_ _ _} h ↦ ⟨_, h, rfl⟩) (fun D Ds ih hDs {n c j} h ↦ ?_) Ds
  obtain ⟨a', b', ha, hb, rfl⟩ := hsub_pi α n D (piTele Ds R) j c h
  rw [hsub_eq, hsubWith_closed (hDs D List.mem_cons_self)] at ha
  obtain rfl := Option.some.inj ha
  obtain ⟨R', hR', rfl⟩ := ih (fun D' hD' ↦ hDs D' (List.mem_cons_of_mem _ hD')) hb
  refine ⟨R', ?_, rfl⟩
  rw [List.length_cons, Function.iterate_succ_apply, show j + (Ds.length + 1) = j + 1 + Ds.length
    by omega]
  exact hR'

/-- At a base type, the substitution into the arrows from families substitutes into each family
and into the codomain. -/
theorem hsub_arrows {c₀ : ℕ} {C : Expr} :
    ∀ {Hs : List Expr} {n c : Expr} {j : ℕ},
      hsub (RoseTree.node (.base c₀) []) n (arrows Hs C) j = some c →
        ∃ Hs' C', List.Forall₂ (fun H H' ↦ hsub (RoseTree.node (.base c₀) []) n H j = some H')
          Hs Hs' ∧ hsub (RoseTree.node (.base c₀) []) n C j = some C' ∧ c = arrows Hs' C' := by
  intro Hs
  refine List.rec (motive := fun Hs ↦ ∀ {n c : Expr} {j : ℕ},
      hsub (RoseTree.node (.base c₀) []) n (arrows Hs C) j = some c →
        ∃ Hs' C', List.Forall₂ (fun H H' ↦ hsub (RoseTree.node (.base c₀) []) n H j = some H')
          Hs Hs' ∧ hsub (RoseTree.node (.base c₀) []) n C j = some C' ∧ c = arrows Hs' C')
    (fun {_ _ _} h ↦ ⟨[], _, .nil, h, rfl⟩) (fun H Hs ih {n c j} h ↦ ?_) Hs
  obtain ⟨a', b', ha, hb, rfl⟩ := hsub_pi _ n H _ j c h
  obtain ⟨B', hB', rfl⟩ := hsub_shift_inv hb
  obtain ⟨Hs', C', hHs, hC, rfl⟩ := ih hB'
  exact ⟨a' :: Hs', C', .cons ha hHs, hC, rfl⟩

/-- Lists related pointwise by two relations in turn are related by a relation their composite
implies. -/
theorem forall₂_comp {α β γ : Type} {R₁ : α → β → Prop} {R₂ : β → γ → Prop} {R : α → γ → Prop}
    (hR : ∀ a b c, R₁ a b → R₂ b c → R a c) :
    ∀ {as : List α} {bs : List β} {cs : List γ},
      List.Forall₂ R₁ as bs → List.Forall₂ R₂ bs cs → List.Forall₂ R as cs := by
  intro as
  refine List.rec (motive := fun as ↦ ∀ {bs : List β} {cs : List γ},
      List.Forall₂ R₁ as bs → List.Forall₂ R₂ bs cs → List.Forall₂ R as cs)
    (fun {_ _} h₁ h₂ ↦ ?_) (fun a as ih {bs cs} h₁ h₂ ↦ ?_) as
  · cases h₁
    cases h₂
    exact .nil
  · rcases h₁ with _ | ⟨hab, h₁⟩
    rcases h₂ with _ | ⟨hbc, h₂⟩
    exact .cons (hR _ _ _ hab hbc) (ih h₁ h₂)

/-- The hereditary substitutions, at a simple type, of a list of terms, the first outermost, for
the variables of an expression in their scope, the last innermost: each term in turn for the
outermost variable remaining, weakened past the variables inside it. -/
def hsubs (α : SimpleTy) : List Expr → Expr → Option Expr :=
  List.rec some fun m ms r X ↦ (hsub α (Expr.shift^[ms.length] m) X ms.length).bind r

/-- The substitutions of a list of terms: the first, then the rest. -/
theorem hsubs_cons (α : SimpleTy) (m : Expr) (ms : List Expr) (X : Expr) :
    hsubs α (m :: ms) X = (hsub α (Expr.shift^[ms.length] m) X ms.length).bind (hsubs α ms) :=
  rfl

/-- The instantiation of products over closed domains of one simple type along a spine that
instantiates them to an atomic family: the leading arguments, one for each domain, check against
the domains, and the rest instantiate the body with the leading arguments substituted. -/
theorem spine_piTele {Γ : Ctx} {J : Expr → Ctx → Mode → Bool} {α : SimpleTy} {P : Expr}
    (hP : IsApp P = true) :
    ∀ {Ds : List Expr}, (∀ D ∈ Ds, D.FreeBelow 0 = true ∧ D.erase = α) →
      ∀ {ms : List Expr} {R : Expr}, spine Γ (piTele Ds R) (ms.map fun m ↦ (m, J m)) = some P →
        List.Forall₂ (fun m D ↦ J m Γ (.check D) = true) (ms.take Ds.length) Ds ∧
          ∃ R', hsubs α (ms.take Ds.length) R = some R' ∧
            spine Γ R' ((ms.drop Ds.length).map fun m ↦ (m, J m)) = some P := by
  intro Ds
  refine List.rec (motive := fun Ds ↦ (∀ D ∈ Ds, D.FreeBelow 0 = true ∧ D.erase = α) →
      ∀ {ms : List Expr} {R : Expr}, spine Γ (piTele Ds R) (ms.map fun m ↦ (m, J m)) = some P →
        List.Forall₂ (fun m D ↦ J m Γ (.check D) = true) (ms.take Ds.length) Ds ∧
          ∃ R', hsubs α (ms.take Ds.length) R = some R' ∧
            spine Γ R' ((ms.drop Ds.length).map fun m ↦ (m, J m)) = some P)
    (fun _ {_ _} h ↦ ⟨.nil, _, rfl, h⟩) (fun D Ds ih hDs {ms R} h ↦ ?_) Ds
  rcases ms with _ | ⟨m, ms⟩
  · obtain rfl := Option.some.inj h
    exact absurd hP (by rw [piTele_cons, Expr.pi]; exact Bool.false_ne_true)
  rw [List.map_cons, piTele_cons] at h
  obtain ⟨hm, b', hb', hS⟩ := spine_cons_inv h
  obtain ⟨hD, hα⟩ := hDs D List.mem_cons_self
  rw [hα] at hb'
  obtain ⟨R₁, hR₁, rfl⟩ := hsub_piTele (fun D' hD' ↦ (hDs D' (List.mem_cons_of_mem _ hD')).1) hb'
  obtain ⟨h₁, R', hR', hS'⟩ := ih (fun D' hD' ↦ hDs D' (List.mem_cons_of_mem _ hD')) hS
  refine ⟨by rw [List.length_cons, List.take_succ_cons]; exact .cons hm h₁, R', ?_,
    by rw [List.length_cons, List.drop_succ_cons]; exact hS'⟩
  rw [Nat.zero_add] at hR₁
  rw [List.length_cons, List.take_succ_cons, hsubs_cons, h₁.length_eq, hR₁, Option.bind_some]
  exact hR'

/-- The instantiation of the arrows from families of proofs into the family of proofs of a formula
along a spine that instantiates them to an atomic family: the arguments check against the
families of proofs of the hypotheses, one for each, and the result is the family of proofs of
the formula. -/
theorem spine_arrows {Γ : Ctx} {J : Expr → Ctx → Mode → Bool} {C P : Expr}
    (hP : IsApp P = true) :
    ∀ {Hs ps : List Expr}, spine Γ (arrows (Hs.map pf) (pf C)) (ps.map fun m ↦ (m, J m)) = some P →
      List.Forall₂ (fun p H ↦ J p Γ (.check (pf H)) = true) ps Hs ∧ P = pf C := by
  intro Hs
  refine List.rec (motive := fun Hs ↦ ∀ {ps : List Expr},
      spine Γ (arrows (Hs.map pf) (pf C)) (ps.map fun m ↦ (m, J m)) = some P →
        List.Forall₂ (fun p H ↦ J p Γ (.check (pf H)) = true) ps Hs ∧ P = pf C)
    (fun {ps} h ↦ ?_) (fun H Hs ih {ps} h ↦ ?_) Hs
  · rcases ps with _ | ⟨p, ps⟩
    · exact ⟨.nil, (Option.some.inj h).symm⟩
    · exact absurd h (by rw [List.map_cons]; exact fun h' ↦ nomatch h'.symm.trans rfl)
  rcases ps with _ | ⟨p, ps⟩
  · obtain rfl := Option.some.inj h
    exact absurd hP (by
      rw [List.map_cons, arrows_cons, Expr.arrow, Expr.pi]
      exact Bool.false_ne_true)
  rw [List.map_cons, List.map_cons, arrows_cons, Expr.arrow] at h
  obtain ⟨hp, b', hb', hS⟩ := spine_cons_inv h
  obtain rfl := Option.some.inj (hb'.symm.trans (hsubWith_vacuous _ _ _ 0))
  obtain ⟨h₁, rfl⟩ := ih hS
  exact ⟨.cons hp h₁, rfl⟩

/-- At a base type, the substitutions into the arrows from families substitute into each family
and into the codomain. -/
theorem hsubs_arrows {c₀ : ℕ} :
    ∀ {ms Hs : List Expr} {C X : Expr},
      hsubs (RoseTree.node (.base c₀) []) ms (arrows Hs C) = some X →
      ∃ Hs' C', List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H')
        Hs Hs' ∧ hsubs (RoseTree.node (.base c₀) []) ms C = some C' ∧ X = arrows Hs' C' := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ {Hs : List Expr} {C X : Expr},
      hsubs (RoseTree.node (.base c₀) []) ms (arrows Hs C) = some X →
        ∃ Hs' C', List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H')
          Hs Hs' ∧ hsubs (RoseTree.node (.base c₀) []) ms C = some C' ∧ X = arrows Hs' C')
    (fun {Hs C X} h ↦ ⟨Hs, C, List.forall₂_same.mpr fun _ _ ↦ rfl, rfl, (Option.some.inj h).symm⟩)
    (fun m ms ih {Hs C X} h ↦ ?_) ms
  rw [hsubs_cons] at h
  obtain ⟨X₁, hX₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Hs₁, C₁, hHs₁, hC₁, rfl⟩ := hsub_arrows hX₁
  obtain ⟨Hs', C', hHs', hC', rfl⟩ := ih h
  refine ⟨Hs', C', forall₂_comp (fun H H₁ H' h₁ h₂ ↦ ?_) hHs₁ hHs', ?_, rfl⟩
  · rw [hsubs_cons, h₁, Option.bind_some]
    exact h₂
  · rw [hsubs_cons, hC₁, Option.bind_some]
    exact hC'

/-- The substitutions into the family of proofs of a formula substitute into the formula. -/
theorem hsubs_pf {α : SimpleTy} :
    ∀ {ms : List Expr} {X Y : Expr}, hsubs α ms (pf X) = some Y →
      ∃ X', hsubs α ms X = some X' ∧ Y = pf X' := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ {X Y : Expr}, hsubs α ms (pf X) = some Y →
      ∃ X', hsubs α ms X = some X' ∧ Y = pf X')
    (fun {X Y} h ↦ ⟨X, rfl, (Option.some.inj h).symm⟩) (fun m ms ih {X Y} h ↦ ?_) ms
  rw [hsubs_cons] at h
  obtain ⟨Y₁, hY₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨X₁, hX₁, rfl⟩ := hsub_const₁ hY₁
  obtain ⟨X', hX', rfl⟩ := ih h
  exact ⟨X', by rw [hsubs_cons, hX₁, Option.bind_some]; exact hX', rfl⟩

/-- The substitution of a list of terms of the internal language, the first outermost, for the
variables of a scope as long as the list: a variable of the scope is replaced by its term, and a
variable past the scope is lowered past it. -/
def scopeSubst (us : List MTerm) : ℕ → MTerm := fun i ↦
  if i < us.length then Term.substList us.reverse i else Term.var (i - us.length)

variable {k : PrimIdx}

/-- Decoding commutes with the substitutions of a list of terms for the variables of a scope:
where the terms decode at an offset and the expression at the offset past the scope, each to a
term whose variables are leaves, the substituted expression decodes at the offset to the decoded
expression with the decoded terms substituted. -/
theorem dec_hsubs (α : SimpleTy) :
    ∀ (ms : List Expr) (X : Expr) (off : ℕ) (y : MTerm) (us : List MTerm) (X' : Expr),
      dec k X (off + ms.length) = some y → Term.VarLeaves y = true →
      List.Forall₂ (fun m u ↦ dec k m off = some u ∧ Term.VarLeaves u = true) ms us →
      hsubs α ms X = some X' → dec k X' off = some (Term.subst y (scopeSubst us)) := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ (X : Expr) (off : ℕ) (y : MTerm) (us : List MTerm)
      (X' : Expr), dec k X (off + ms.length) = some y → Term.VarLeaves y = true →
      List.Forall₂ (fun m u ↦ dec k m off = some u ∧ Term.VarLeaves u = true) ms us →
      hsubs α ms X = some X' → dec k X' off = some (Term.subst y (scopeSubst us)))
    (fun X off y us X' hX hy hus h ↦ ?_) (fun m ms ih X off y us X' hX hy hus h ↦ ?_) ms
  · cases hus
    obtain rfl := Option.some.inj h
    rw [Term.subst_id y hy _ fun i ↦ by
      simp only [scopeSubst, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero]]
    exact hX
  rcases hus with _ | ⟨⟨hu, hul⟩, hus⟩
  rename_i u us
  rw [hsubs_cons] at h
  obtain ⟨X₁, hX₁, h⟩ := Option.bind_eq_some_iff.mp h
  have hq := hus.length_eq
  have hn : dec k (Expr.shift^[ms.length] m) (off + ms.length + 1 - 1) =
      some (Term.rename u (· + ms.length)) := by
    rw [iterate_shift, Nat.add_sub_cancel]
    exact dec_rename m off _ _ u hu fun i _ ↦ by omega
  have hy₁ := dec_hsub α X _ ms.length (off + ms.length + 1) X₁ y _ hX hn (by omega) hX₁
  rw [Nat.add_sub_cancel] at hy₁
  have hl₁ : Term.VarLeaves (Term.subst y (substAt ms.length (Term.rename u (· + ms.length)))) =
      true := Term.varLeaves_subst y hy _ fun i ↦ by
    unfold substAt
    split_ifs
    · exact Term.varLeaves_var i
    · exact Term.varLeaves_rename u hul _
    · exact Term.varLeaves_var _
  rw [ih X₁ off _ us X' hy₁ hl₁ hus h, Term.subst_subst y _ _ _ fun _ ↦ rfl]
  refine congrArg (some ∘ Term.subst y) (funext fun i ↦ ?_)
  simp only [substAt, scopeSubst, List.length_cons, List.reverse_cons, hq, Term.substList]
  by_cases hlt : i < us.length
  · rw [ite_eq_left hlt, ite_eq_left (Nat.lt_succ_of_lt hlt), Term.subst_var, scopeSubst,
      ite_eq_left hlt, Term.substList,
      List.getElem?_append_left (by rw [List.length_reverse]; exact hlt)]
  · by_cases heq : i = us.length
    · subst heq
      rw [ite_eq_right hlt, ite_eq_left rfl, ite_eq_left (Nat.lt_succ_self _),
        List.getElem?_append_right (by rw [List.length_reverse]), List.length_reverse,
        Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [Term.subst_rename u _ _ (fun r ↦ Term.var r) fun r ↦ by
        rw [scopeSubst, ite_eq_right (by omega), Nat.add_sub_cancel]]
      exact Term.subst_id u hul _ fun _ ↦ rfl
    · rw [ite_eq_right hlt, ite_eq_right heq, ite_eq_right (by omega), Term.subst_var, scopeSubst,
        ite_eq_right (by omega), show i - 1 - us.length = i - (us.length + 1) by omega]

/-- The substitutions commute with renaming: the renamed terms substituted into the expression
renamed past the scope give the renamed result. -/
theorem hsubs_rename (α : SimpleTy) (ρ : ℕ → ℕ) :
    ∀ (ms : List Expr) (X X' : Expr), hsubs α ms X = some X' →
      hsubs α (ms.map fun m ↦ m.rename ρ) (X.rename (liftR^[ms.length] ρ)) =
        some (X'.rename ρ) := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ (X X' : Expr), hsubs α ms X = some X' →
      hsubs α (ms.map fun m ↦ m.rename ρ) (X.rename (liftR^[ms.length] ρ)) = some (X'.rename ρ))
    (fun X X' h ↦ by obtain rfl := Option.some.inj h; rfl) (fun m ms ih X X' h ↦ ?_) ms
  rw [hsubs_cons] at h
  obtain ⟨X₁, hX₁, h⟩ := Option.bind_eq_some_iff.mp h
  have hr := hsubWith_rename (reduce_rename α) X _ ms.length ρ X₁ hX₁
  rw [← iterate_shift_rename, ← hsub_eq] at hr
  rw [List.map_cons, hsubs_cons, List.length_map, List.length_cons, hr, Option.bind_some]
  exact ih X₁ X' h

/-- An iterated lifted renaming fixes the variables below the number of liftings. -/
theorem iterate_liftR_lt (ρ : ℕ → ℕ) : ∀ b i, i < b → liftR^[b] ρ i = i :=
  Nat.rec (fun _ h ↦ absurd h (Nat.not_lt_zero _)) fun b ih i hi ↦ by
    rw [Function.iterate_succ_apply']
    rcases i with _ | i
    · rfl
    · exact congrArg (· + 1) (ih i (by omega))

/-- An expression in scope below {lit}`b` is fixed by a renaming lifted past {lit}`b` binders. -/
theorem ScopedBelow.rename_iterate {b : ℕ} {X : Expr} (h : ScopedBelow b X) (ρ : ℕ → ℕ) :
    X.rename (liftR^[b] ρ) = X :=
  (h _ id fun i hi ↦ iterate_liftR_lt ρ b i hi).trans (rename_id X)

open FreeTopos.Internal (IsTy) in
/-- The encoding of a type in no object variables is closed. -/
theorem freeBelow_encTy {G : Globals} {a : PartialHorn.Tree} {off : ℕ} {A : Expr}
    (h : encTy off a = some A) (hty : IsTy G 0 a = true) : A.FreeBelow 0 = true :=
  judgeWith_freeBelow A [] _
    (encTy_checks sigExt_sig G (n := 0) a off A h hty [] fun _ hj ↦ absurd hj (Nat.not_lt_zero _))

/-- The family of terms of a closed type is closed. -/
theorem freeBelow_tm {A : Expr} (h : A.FreeBelow 0 = true) : (tm A).FreeBelow 0 = true := by
  refine freeBelow_node_iff.mpr ⟨fun _ h ↦ (by cases h), fun idx hidx ↦ ?_⟩
  rcases idx with _ | idx
  · exact h
  · exact absurd hidx (by simp)

open FreeTopos.Internal (IsTy) in
/-- The encoding of a context of types in no object variables: each declaration the family of
terms of a closed expression, the encoding of its type at every offset. -/
theorem encCtx_closed {G : Globals} :
    ∀ {Γ : List PartialHorn.Tree} {ΓT : Ctx}, encCtx 0 Γ = some ΓT → (∀ a ∈ Γ, IsTy G 0 a = true) →
      List.Forall₂ (fun D a ↦ ∃ A, D = tm A ∧ A.FreeBelow 0 = true ∧ ∀ off, encTy off a = some A)
        ΓT Γ := by
  intro Γ
  refine List.rec (motive := fun Γ ↦ ∀ {ΓT : Ctx}, encCtx 0 Γ = some ΓT →
      (∀ a ∈ Γ, IsTy G 0 a = true) →
      List.Forall₂ (fun D a ↦ ∃ A, D = tm A ∧ A.FreeBelow 0 = true ∧ ∀ off, encTy off a = some A)
        ΓT Γ)
    (fun {ΓT} h _ ↦ by obtain rfl := Option.some.inj h; exact .nil)
    (fun a Γ ih {ΓT} h hty ↦ ?_) Γ
  obtain ⟨A, ΓT', hA, hΓ', rfl⟩ := encCtx_cons_inv h
  have hcl := freeBelow_encTy hA (hty a List.mem_cons_self)
  refine .cons ⟨A, rfl, hcl, fun off ↦ ?_⟩ (ih hΓ' fun b hb ↦ hty b (List.mem_cons_of_mem _ hb))
  rw [encTy_rename a _ A hA off (fun i ↦ i - Γ.length + off) fun i hi ↦ by omega,
    rename_closed hcl]

open FreeTopos.Internal (IsTy compile) in
/-- The encoding of a term of the internal language that compiles in a context of types in no
object variables is in the scope of the context's variables. -/
theorem scopedBelow_enc {G : Globals} (hk : k.Valid G) {Γ : List PartialHorn.Tree} {ΓT : Ctx}
    (hty : ∀ a ∈ Γ, IsTy G 0 a = true) (hΓ : encCtx 0 Γ = some ΓT) {s : MTerm}
    {r : PartialHorn.Tree × PartialHorn.Tree} (hc : compile G 0 s (ctxObj Γ) (stdEnv Γ) = some r)
    {X : Expr} (he : enc G 0 k s (ctxObj Γ) (stdEnv Γ) = some X) : ScopedBelow Γ.length X := by
  obtain ⟨-, A, -, hj⟩ := enc_checks sigExt_sig hk s _ (stdEnv Γ) ΓT X r
    (fun p hp ↦ hty p.2
      (by rw [← FreeTopos.Internal.map_snd_stdEnv Γ]; exact List.mem_map_of_mem hp))
    (by rw [FreeTopos.Internal.map_snd_stdEnv]; exact hΓ) he hc
  have := judgeWith_freeBelow X ΓT _ hj
  rw [length_encCtx hΓ, Nat.add_zero] at this
  exact freeBelow_scoped X _ this

/-- Lists related pointwise to a third by values of a partial function: the function has values
at every element of the first, in a list related pointwise to the third. -/
theorem mapM_of_forall₂ {α β γ : Type} {f : α → Option β} {P : β → γ → Prop} :
    ∀ {xs : List α} {cs : List γ}, List.Forall₂ (fun x c ↦ ∃ y, f x = some y ∧ P y c) xs cs →
      ∃ ys, xs.mapM f = some ys ∧ List.Forall₂ P ys cs := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {cs : List γ},
      List.Forall₂ (fun x c ↦ ∃ y, f x = some y ∧ P y c) xs cs →
        ∃ ys, xs.mapM f = some ys ∧ List.Forall₂ P ys cs)
    (fun {cs} h ↦ by cases h; exact ⟨[], rfl, .nil⟩) (fun x xs ih {cs} h ↦ ?_) xs
  rcases h with _ | ⟨⟨y, hy, hP⟩, h⟩
  obtain ⟨ys, hys, hP'⟩ := ih h
  exact ⟨y :: ys, by simp [List.mapM_cons, hy, hys], .cons hP hP'⟩

/-- A list all of whose elements have values under a partial function is related pointwise to
the list of the values. -/
theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys →
      List.Forall₂ (fun x y ↦ f x = some y) xs ys := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List β}, xs.mapM f = some ys →
      List.Forall₂ (fun x y ↦ f x = some y) xs ys)
    (fun {ys} h ↦ by obtain rfl := Option.some.inj h; exact .nil) (fun x xs ih {ys} h ↦ ?_) xs
  simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨y, hy, ys', hys', rfl⟩ := h
  exact .cons hy (ih hys')

/-- Lists related pointwise are related pointwise with the first one's elements its members. -/
theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys →
      List.Forall₂ (fun x y ↦ x ∈ xs ∧ R x y) xs ys := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List β}, List.Forall₂ R xs ys →
      List.Forall₂ (fun x y ↦ x ∈ xs ∧ R x y) xs ys)
    (fun {ys} h ↦ by cases h; exact .nil) (fun x xs ih {ys} h ↦ ?_) xs
  rcases h with _ | ⟨hxy, h⟩
  exact .cons ⟨List.mem_cons_self, hxy⟩
    ((ih h).imp fun _ _ hr ↦ ⟨List.mem_cons_of_mem _ hr.1, hr.2⟩)

/-- Each element of a list related pointwise to another is related to an element of the other. -/
theorem forall₂_left_mem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → ∀ x ∈ xs, ∃ y, R x y := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List β}, List.Forall₂ R xs ys →
      ∀ x ∈ xs, ∃ y, R x y)
    (fun {ys} _ x hx ↦ absurd hx List.not_mem_nil) (fun x xs ih {ys} h z hz ↦ ?_) xs
  rcases h with _ | ⟨hxy, h⟩
  rcases List.mem_cons.mp hz with rfl | hz
  · exact ⟨_, hxy⟩
  · exact ih h z hz

/-- At a base type, the substitutions into the arrows from families of proofs into the family of
proofs of a formula substitute into each hypothesis and into the formula. -/
theorem hsubs_arrows_pf {c₀ : ℕ} {ms Hs : List Expr} {C X : Expr}
    (h : hsubs (RoseTree.node (.base c₀) []) ms (arrows (Hs.map pf) (pf C)) = some X) :
    ∃ Hs' C', List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H') Hs Hs' ∧
      hsubs (RoseTree.node (.base c₀) []) ms C = some C' ∧ X = arrows (Hs'.map pf) (pf C') := by
  obtain ⟨Hs₁, C₁, hHs, hC, rfl⟩ := hsubs_arrows h
  obtain ⟨C', hC', rfl⟩ := hsubs_pf hC
  have key : ∀ {Hs : List Expr} {Hs₁ : List Expr},
      List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H') (Hs.map pf) Hs₁ →
      ∃ Hs', List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H') Hs Hs' ∧
        Hs₁ = Hs'.map pf := by
    intro Hs
    refine List.rec (motive := fun Hs ↦ ∀ {Hs₁ : List Expr},
        List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H') (Hs.map pf)
          Hs₁ → ∃ Hs', List.Forall₂ (fun H H' ↦ hsubs (RoseTree.node (.base c₀) []) ms H = some H')
            Hs Hs' ∧ Hs₁ = Hs'.map pf)
      (fun {Hs₁} h ↦ by cases h; exact ⟨[], .nil, rfl⟩) (fun H Hs ih {Hs₁} h ↦ ?_) Hs
    rcases h with _ | ⟨hH, h⟩
    obtain ⟨H', hH', rfl⟩ := hsubs_pf hH
    obtain ⟨Hs', hHs', rfl⟩ := ih h
    exact ⟨H' :: Hs', .cons hH' hHs', rfl⟩
  obtain ⟨Hs', hHs', rfl⟩ := key hHs
  exact ⟨Hs', C', hHs', hC', rfl⟩

/-- The declaration of a theorem of the language: the products over the families of terms of its
variables' types, the outermost first, each encoded at the offset of the variables outside it,
of the products over the families of proofs of its hypotheses into the family of proofs of its
conclusion, the formulas encoded in the scope of the variables. -/
def thmTy (G : Globals) (k : PrimIdx) (a : Thm) : Option Expr := do
  let ΓT ← encCtx 0 a.ctx
  let Hs ← a.hyps.mapM fun h ↦ enc G 0 k h (ctxObj a.ctx) (stdEnv a.ctx)
  let C ← enc G 0 k a.concl (ctxObj a.ctx) (stdEnv a.ctx)
  pure (piTele ΓT.reverse (arrows (Hs.map pf) (pf C)))

/-- The parts of the declaration of a theorem. -/
theorem thmTy_eq_some {G : Globals} {k : PrimIdx} {a : Thm} {T : Expr} (h : thmTy G k a = some T) :
    ∃ ΓT Hs C, encCtx 0 a.ctx = some ΓT ∧
      a.hyps.mapM (fun h ↦ enc G 0 k h (ctxObj a.ctx) (stdEnv a.ctx)) = some Hs ∧
      enc G 0 k a.concl (ctxObj a.ctx) (stdEnv a.ctx) = some C ∧
      T = piTele ΓT.reverse (arrows (Hs.map pf) (pf C)) := by
  simp only [thmTy, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨ΓT, hΓ, Hs, hHs, C, hC, rfl⟩ := h
  exact ⟨ΓT, Hs, C, hΓ, hHs, hC, rfl⟩

/-- An extension of the signature declares the theorems that the table of the indices names:
the declaration at each position past the signature is that of the theorem of the entry at the
table's position, a well-formed theorem in no object variables of as many variables as the table
records. -/
def ThmsDecl (G : Globals) (E : Array Entry) (k : PrimIdx) (sg : Sig) : Prop :=
  ∀ i T, sg[sig.length + i]? = some T → ∃ j a, k.thms[i]? = some (j, a.ctx.length) ∧
    (E[j]?).bind Entry.language? = some a ∧ a.arity = 0 ∧ a.wellFormed G = true ∧
      thmTy G k a = some T

/-- The signature declares no theorems past itself. -/
theorem thmsDecl_sig (G : Globals) (E : Array Entry) (k : PrimIdx) : ThmsDecl G E k sig :=
  fun _ _ h ↦ absurd (List.getElem?_eq_some_iff.mp h).1 (by omega)

end Geb.LF.Topos

end
