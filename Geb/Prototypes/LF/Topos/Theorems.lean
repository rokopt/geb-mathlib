/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.ObjectSubst
public import Geb.Prototypes.LF.Topos.Compose
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Theorems as constants of an extension of the signature

The theorems of a development of the internal language enter the signature
{name}`Geb.LF.Topos.sig` as constants of an extension of it, past its own declarations, as a
logical framework's signature takes each proved lemma as a constant
({cite}`HarperLicata2007`, Section 2). A theorem, of object variables, of variables of types in
them, of hypotheses and of a conclusion, is the constant of the product over the kind of types,
one for each object variable, of the product over a family of terms of each variable's type, the
outermost first, of the products over the families of proofs of its hypotheses, none in the scope
of another, into the family of proofs of its conclusion ({lit}`thmTy`): its context is encoded as
{name}`Geb.LF.Topos.encCtx` encodes one, and its formulas as {name}`Geb.LF.Topos.enc` encodes
them, in the scope of the variables. An application of the constant decodes to the language's
application of the theorem's entry ({lit}`Geb.LF.Topos.decPfThm`).

The application instantiates the declaration along its spine, each argument substituted, one
after another, into the domains after it and into the body ({lit}`hsubs`, {lit}`spine_piTele_gen`),
and the substitution passes into each hypothesis and the conclusion ({lit}`hsubs_arrows_pf`).
Passing under a hypothesis's binder needs the inversion of substitution into a weakened
expression, which holds at the base types of the types and the terms, where a reduction has a
value exactly at the empty spine ({lit}`hsub_shift_inv`). Decoding commutes with the substitution
of a type for an object variable ({lit}`encTy_hsub_obj`, {lit}`dec_hsub_obj`) and of a term for a
variable ({lit}`dec_hsubs`), so the substituted domains are the encodings of the instances of the
variables' types and the substituted formulas decode to the instances of the theorem's formulas
that the language's checker compares. The types are substituted with the context's variables of
terms and proofs renamed away, where the decoding at the offset of the theorem's variables reads
each remaining LF variable as an object variable ({lit}`dec_hsubsPre_obj`).

## Main definitions

* {lit}`piTele`, {lit}`arrows` — the products over a list of domains, and the arrows from a list
  of families.
* {lit}`hsubs`, {lit}`hsubsPre` — the substitutions of a list of terms for the variables of a
  scope, and for its outermost variables under further ones.
* {lit}`thmTy` — the declaration of a theorem.
* {lit}`ThmsDecl` — an extension of the signature declares the theorems that a table names.

## Main statements

* {lit}`hsub_shift_inv` — at a base type, the substitution into a weakened expression is the
  weakened substitution.
* {lit}`spine_piTele_gen`, {lit}`spine_arrows` — the instantiation of a theorem's declaration.
* {lit}`encTy_hsub_obj`, {lit}`dec_hsub_obj` — encoding and decoding commute with the
  substitution of a type for an object variable.
* {lit}`dec_hsubs`, {lit}`dec_hsubsPre_obj`, {lit}`encTy_hsubsPre_obj` — decoding commutes with
  the substitutions of terms and of types.

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
/-- The encoding of a term of the internal language that compiles in a context of types in
{lit}`n` object variables is in the scope of the context's variables and the object
variables. -/
theorem scopedBelow_enc {G : Globals} {n : ℕ} (hk : k.Valid G) {Γ : List PartialHorn.Tree}
    {ΓT : Ctx} (hty : ∀ a ∈ Γ, IsTy G n a = true) (hΓ : encCtx n Γ = some ΓT) {s : MTerm}
    {r : PartialHorn.Tree × PartialHorn.Tree} (hc : compile G n s (ctxObj Γ) (stdEnv Γ) = some r)
    {X : Expr} (he : enc G n k s (ctxObj Γ) (stdEnv Γ) = some X) :
    ScopedBelow (Γ.length + n) X := by
  obtain ⟨-, A, -, hj⟩ := enc_checks sigExt_sig hk s _ (stdEnv Γ) ΓT X r
    (fun p hp ↦ hty p.2
      (by rw [← FreeTopos.Internal.map_snd_stdEnv Γ]; exact List.mem_map_of_mem hp))
    (by rw [FreeTopos.Internal.map_snd_stdEnv]; exact hΓ) he hc
  have := judgeWith_freeBelow X ΓT _ hj
  rw [length_encCtx hΓ] at this
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

/-- The encodings of two children of a node. -/
theorem map_encTy_eq_two {off : ℕ} {cs : List PartialHorn.Tree} {a b : Expr}
    (h : cs.map (encTy off) = [some a, some b]) :
    ∃ c₁ c₂, cs = [c₁, c₂] ∧ encTy off c₁ = some a ∧ encTy off c₂ = some b := by
  rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
  · exact absurd (congrArg List.length h) (by simp)
  · exact absurd (congrArg List.length h) (by simp)
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨c₁, c₂, rfl, h.1, h.2⟩
  · exact absurd (congrArg List.length h) (by simp)

/-- The encoding of the child of a node. -/
theorem map_encTy_eq_one {off : ℕ} {cs : List PartialHorn.Tree} {a : Expr}
    (h : cs.map (encTy off) = [some a]) : ∃ c₁, cs = [c₁] ∧ encTy off c₁ = some a := by
  rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
  · exact absurd h FreeTopos.Internal.nil_ne_singleton
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact ⟨c₁, rfl, h⟩
  · exact absurd h FreeTopos.Internal.cons_cons_ne_singleton

open FreeTopos.Internal (substF objAt substF_node_succ substF_node_zero) in
/-- At a base type, the substitution of the encoding of an object for the LF variable of an
object variable of the encoding of a type is the encoding of the type with the object substituted
for the object variable, the object variables above it lowered by one. -/
theorem encTy_hsub_obj {c₀ off j : ℕ} {n : Expr} {b : PartialHorn.Tree}
    (hb : encTy off b = some n) (hj : off ≤ j) :
    ∀ (a : PartialHorn.Tree) (A A' : Expr), encTy off a = some A →
      hsub (RoseTree.node (.base c₀) []) n A j = some A' →
        encTy off (substF (objAt (j - off) b) a) = some A' :=
  RoseTree.ind fun l cs ih A A' h hs ↦ by
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a₁, a₂, hcs, rfl⟩ | ⟨rfl, a₁, a₂, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a₁, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a₁, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a₁, a₂, hcs, rfl⟩
    · rw [substF_node_zero _ rfl, RoseTree.label_node]
      rw [hsub_eq, Expr.var, Expr.app, hsubWith_var] at hs
      change (if off + i = j then reduce (RoseTree.node (.base c₀) []) n []
        else some (Expr.var (if j < off + i then off + i - 1 else off + i) [])) = some A' at hs
      unfold objAt
      by_cases hij : off + i = j
      · rw [ite_eq_left hij] at hs
        obtain rfl := Option.some.inj hs
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        exact hb
      · rw [ite_eq_right hij] at hs
        obtain rfl := Option.some.inj hs
        by_cases hlt : i < j - off
        · rw [ite_eq_left hlt, ite_eq_right (by omega)]
          rfl
        · rw [ite_eq_right hlt, ite_eq_right (by omega), ite_eq_left (by omega)]
          change some (Expr.var (off + (i - 1))) = _
          rw [show off + (i - 1) = off + i - 1 by omega]
    · rw [one, hsub_const] at hs
      obtain rfl := Option.some.inj hs
      rw [substF_node_succ]
      exact h
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_encTy_eq_two hcs
      obtain ⟨a₁', a₂', hs₁, hs₂, rfl⟩ := hsub_const₂ hs
      rw [substF_node_succ]
      change encTy off (FreeTopos.prod _ _) = _
      rw [encTy_prod, ih c₁ (by simp) a₁ a₁' h₁ hs₁, ih c₂ (by simp) a₂ a₂' h₂ hs₂]
      rfl
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_encTy_eq_two hcs
      obtain ⟨a₁', a₂', hs₁, hs₂, rfl⟩ := hsub_const₂ hs
      rw [substF_node_succ]
      change encTy off (FreeTopos.exp _ _) = _
      rw [encTy_exp, ih c₁ (by simp) a₁ a₁' h₁ hs₁, ih c₂ (by simp) a₂ a₂' h₂ hs₂]
      rfl
    · rw [omega, hsub_const] at hs
      obtain rfl := Option.some.inj hs
      rw [substF_node_succ]
      exact h
    · rw [nat, hsub_const] at hs
      obtain rfl := Option.some.inj hs
      rw [substF_node_succ]
      exact h
    · obtain ⟨c₁, rfl, h₁⟩ := map_encTy_eq_one hcs
      obtain ⟨a₁', hs₁, rfl⟩ := hsub_const₁ hs
      rw [substF_node_succ]
      change encTy off (FreeTopos.list _) = _
      rw [encTy_list, ih c₁ (by simp) a₁ a₁' h₁ hs₁]
      rfl
    · rw [rose, hsub_const] at hs
      obtain rfl := Option.some.inj hs
      rw [substF_node_succ]
      exact h
    · obtain ⟨c₁, rfl, h₁⟩ := map_encTy_eq_one hcs
      obtain ⟨a₁', hs₁, rfl⟩ := hsub_const₁ hs
      rw [substF_node_succ]
      change encTy off (FreeTopos.lrose _) = _
      rw [encTy_lrose, ih c₁ (by simp) a₁ a₁' h₁ hs₁]
      rfl
    · rw [initial, hsub_const] at hs
      obtain rfl := Option.some.inj hs
      rw [substF_node_succ]
      exact h
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_encTy_eq_two hcs
      obtain ⟨a₁', a₂', hs₁, hs₂, rfl⟩ := hsub_const₂ hs
      rw [substF_node_succ]
      change encTy off (FreeTopos.coprod _ _) = _
      rw [encTy_coprod, ih c₁ (by simp) a₁ a₁' h₁ hs₁, ih c₂ (by simp) a₂ a₂' h₂ hs₂]
      rfl

open FreeTopos.Internal (substF objAt) in
/-- At a base type, the substitution of a type decoding to an object, at an offset, for the LF
variable of an object variable of a type decoding there gives a type decoding there to the
decoded type with the object substituted for the object variable, those above it lowered. -/
theorem decTy_hsub_obj {c₀ off j : ℕ} {A n A' : Expr} {a b : PartialHorn.Tree}
    (ha : decTy off A = some a) (hn : decTy off n = some b) (hj : off ≤ j)
    (hA : hsub (RoseTree.node (.base c₀) []) n A j = some A') :
    decTy off A' = some (substF (objAt (j - off) b) a) :=
  decTy_encTy _ _ _ (encTy_hsub_obj (encTy_decTy off n b hn) hj a A A'
    (encTy_decTy off A a ha) hA)

/-- Whether a label's node tests the occurrence of a variable in each child in its own context: a
label other than a variable and a binder. -/
def labelPlain : FreeTopos.Internal.Label → Bool
  | .var _ => false
  | .lam _ => false
  | .natRec => false
  | .listRec => false
  | .roseRec _ => false
  | _ => true

/-- A variable occurring in a child of a plain node occurs in the node. -/
theorem occurs_node_of_mem {l : FreeTopos.Internal.Label} (hl : labelPlain l = true)
    {cs : List MTerm} {c : MTerm} (hc : c ∈ cs) {d : ℕ} (h : Term.occurs c d = true) :
    Term.occurs (RoseTree.node l cs) d = true := by
  rw [Term.occurs_node]
  have hany : Term.occursStep l (cs.map fun c ↦ (c, Term.occurs c)) d =
      (cs.map fun c ↦ (c, Term.occurs c)).any fun c ↦ c.2 d := by
    cases l <;> first
      | exact absurd hl Bool.false_ne_true
      | (rcases cs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl)
  rw [hany, List.any_eq_true]
  exact ⟨(c, Term.occurs c), List.mem_map_of_mem hc, h⟩

/-- The variables of a child of a plain node are bounded as the node's are. -/
theorem bnd_plain {l : FreeTopos.Internal.Label} (hl : labelPlain l = true) {cs : List MTerm}
    {off : ℕ}
    (h : ∀ i, Term.occurs (RoseTree.node l cs) i = true → i < off) {c : MTerm} (hc : c ∈ cs) :
    ∀ i, Term.occurs c i = true → i < off :=
  fun i hi ↦ h i (occurs_node_of_mem hl hc hi)

/-- A disjunction of two Booleans holds where either does. -/
theorem or₂_of {a b : Bool} (h : a = true ∨ b = true) : (a || b) = true := by
  rcases h with rfl | rfl
  · exact Bool.true_or _
  · exact Bool.or_true _

/-- A disjunction of three Booleans holds where one does. -/
theorem or₃_of {a b c : Bool} (h : a = true ∨ b = true ∨ c = true) : (a || b || c) = true := by
  rcases h with h | h | h
  · exact or₂_of (.inl (or₂_of (.inl h)))
  · exact or₂_of (.inl (or₂_of (.inr h)))
  · exact or₂_of (.inr h)

/-- The variables of an abstraction are those of its body, lowered past the binder. -/
theorem occurs_of_lamBody {s r : MTerm} (h : lamBody s = some r) (d : ℕ) :
    Term.occurs s d = Term.occurs r (d + 1) := by
  obtain ⟨a, rfl⟩ := lamBody_eq_some.mp h
  rfl

/-- The replacement of an abstraction's type leaves its variables. -/
theorem occurs_of_relam {a : PartialHorn.Tree} {s r : MTerm} (h : relam a s = some r) :
    Term.occurs s = Term.occurs r := by
  obtain ⟨a', b, rfl, rfl⟩ := relam_eq_some.mp h
  rfl

open FreeTopos.Internal (substF) in
/-- The replacement of an abstraction's type commutes with the substitution of objects. -/
theorem relam_osubstF {a : PartialHorn.Tree} {s r : MTerm} (h : relam a s = some r)
    (τ : ℕ → PartialHorn.Tree) :
    relam (substF τ a) (Term.osubstF τ s) = some (Term.osubstF τ r) := by
  obtain ⟨a', b, rfl, rfl⟩ := relam_eq_some.mp h
  rfl

/-- The body of an abstraction with objects substituted is its body with them substituted. -/
theorem lamBody_osubstF {s b : MTerm} (h : lamBody s = some b) (τ : ℕ → PartialHorn.Tree) :
    lamBody (Term.osubstF τ s) = some (Term.osubstF τ b) := by
  obtain ⟨a, rfl⟩ := lamBody_eq_some.mp h
  rfl

open FreeTopos.Internal (substF objAt) in
/-- At a base type, decoding commutes with the substitution of a type for the LF variable of an
object variable: where an expression decodes at an offset to a term whose variables are below
the offset, and the type to an object, the substituted expression decodes there to the decoded
term with the object substituted for the object variable, those above it lowered. -/
theorem dec_hsub_obj {c₀ : ℕ} : ∀ (e n : Expr) (j off : ℕ) (e' : Expr) (s : MTerm)
    (β : PartialHorn.Tree), dec k e off = some s →
    (∀ i, Term.occurs s i = true → i < off) → decTy off n = some β → off ≤ j →
    hsub (RoseTree.node (.base c₀) []) n e j = some e' →
      dec k e' off = some (Term.osubstF (objAt (j - off) β) s) :=
  RoseTree.ind fun l cs ih n j off e' s β h hocc hn hj hs ↦ by
    rw [dec_node] at h
    unfold decStep at h
    split at h
    · next _ _ i heq =>
      obtain ⟨rfl, -⟩ := map_dec_eq heq
      simp only [List.map_nil] at hs
      obtain rfl := Option.some.inj h
      have hi : i < off := hocc i (beq_self_eq_true i)
      rw [show (RoseTree.node (.app (.var i)) [] : Expr) = Expr.var i [] from rfl, hsub_var] at hs
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.bind_some] at hs
      rw [ite_eq_right (show i ≠ j by omega), Option.some.injEq] at hs
      subst hs
      rw [show renumber j i = i from ite_eq_right (show ¬ j < i by omega), Expr.var, Expr.app,
        dec_node]
      rfl
    · next _ _ heq =>
      obtain ⟨rfl, -⟩ := map_dec_eq heq
      simp only [List.map_nil] at hs
      obtain rfl := Option.some.inj h
      rw [show (RoseTree.node (.app (.const 7)) [] : Expr) = Expr.const 7 [] from rfl,
        hsub_const] at hs
      simp only [List.map_nil, List.mapM_nil, Option.pure_def, Option.map_eq_map,
        Option.map_some, Option.some.injEq] at hs
      subst hs
      rfl
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨-, -, t', u', -, -, ht', hu', rfl⟩ := hsub_const₄ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht',
        ih u (by simp) n j off u' su β
          (by rw [hd (u, du) (by simp)]; exact hsu)
          (bnd_plain rfl hocc (by simp)) hn hj hu', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨-, -, t', -, -, ht', rfl⟩ := hsub_const₃ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨-, -, t', -, -, ht', rfl⟩ := hsub_const₃ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ A dA p₂ f df heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨A', -, f', hA', -, hf', rfl⟩ := hsub_const₃ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha',
        ih f (by simp) n j off f' sf β
          (by rw [hd (f, df) (by simp)]; exact hsf)
          (fun i hi ↦ hocc i (by rw [← occurs_of_relam h]; exact hi)) hn hj hf',
        Option.bind_eq_bind,
        Option.bind_some]
      exact relam_osubstF h _
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨-, -, t', u', -, -, ht', hu', rfl⟩ := hsub_const₄ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht',
        ih u (by simp) n j off u' su β
          (by rw [hd (u, du) (by simp)]; exact hsu)
          (bnd_plain rfl hocc (by simp)) hn hj hu', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨t', ht', rfl⟩ := hsub_const₁ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨t', ht', rfl⟩ := hsub_const₁ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ A dA z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', z', f', m', -, hz', hf', hm', rfl⟩ := hsub_const₄ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih z (by simp) n j off z' sz β (by rw [hd (z, dz) (by simp)]; exact hsz)
          (fun i hi ↦ hocc i (or₃_of (.inl hi))) hn hj hz',
        ih f (by simp) n j off f' sf β (by rw [hd (f, df) (by simp)]; exact hsf)
          (fun i hi ↦ hocc i (or₃_of (.inr (.inl ((occurs_of_lamBody hr i).symm.trans hi)))))
          hn hj hf',
        ih m (by simp) n j off m' sm β
          (by rw [hd (m, dm) (by simp)]; exact hsm)
          (fun i hi ↦ hocc i (or₃_of (.inr (.inr hi)))) hn hj hm', lamBody_osubstF hr _,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ p₁ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨-, t', u', -, ht', hu', rfl⟩ := hsub_const₃ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht',
        ih u (by simp) n j off u' su β
          (by rw [hd (u, du) (by simp)]; exact hsu)
          (bnd_plain rfl hocc (by simp)) hn hj hu', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', t', hA', ht', rfl⟩ := hsub_const₂ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', t', hA', ht', rfl⟩ := hsub_const₂ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA C dC z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r₁, hr₁, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', C', z', f', m', -, -, hz', hf', hm', rfl⟩ := hsub_const₅ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih z (by simp) n j off z' sz β (by rw [hd (z, dz) (by simp)]; exact hsz)
          (fun i hi ↦ hocc i (or₃_of (.inl hi))) hn hj hz',
        ih f (by simp) n j off f' sf β (by rw [hd (f, df) (by simp)]; exact hsf)
          (fun i hi ↦ hocc i (or₃_of (.inr (.inl ((occurs_of_lamBody hr (i + 1)).symm.trans
            ((occurs_of_lamBody hr₁ i).symm.trans hi)))))) hn hj hf',
        ih m (by simp) n j off m' sm β
          (by rw [hd (m, dm) (by simp)]; exact hsm)
          (fun i hi ↦ hocc i (or₃_of (.inr (.inr hi)))) hn hj hm', lamBody_osubstF hr₁ _,
        lamBody_osubstF hr _, Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨t', ht', rfl⟩ := hsub_const₁ hs
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep,
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.map_eq_map,
        Option.map_some]
      rfl
    · next _ _ C dC f df t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨C', f', t', hC', hf', ht', rfl⟩ := hsub_const₃ hs
      have hc' := decTy_hsub_obj hc hn hj hC'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, hc',
        ih f (by simp) n j off f' sf β (by rw [hd (f, df) (by simp)]; exact hsf)
          (fun i hi ↦ hocc i (or₂_of (.inl ((occurs_of_lamBody hr i).symm.trans hi)))) hn hj hf',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (fun i hi ↦ hocc i (or₂_of (.inr hi))) hn hj ht', lamBody_osubstF hr _,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', t', hA', ht', rfl⟩ := hsub_const₂ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A C dC f df t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', C', f', t', -, hC', hf', ht', rfl⟩ := hsub_const₄ hs
      have hc' := decTy_hsub_obj hc hn hj hC'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, hc',
        ih f (by simp) n j off f' sf β (by rw [hd (f, df) (by simp)]; exact hsf)
          (fun i hi ↦ hocc i (or₂_of (.inl ((occurs_of_lamBody hr i).symm.trans hi)))) hn hj hf',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (fun i hi ↦ hocc i (or₂_of (.inr hi))) hn hj ht', lamBody_osubstF hr _,
        Option.bind_eq_bind, Option.bind_some]
      rfl
    · next _ _ A dA B dB t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', B', t', hA', hB', ht', rfl⟩ := hsub_const₃ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      have hb' := decTy_hsub_obj hb hn hj hB'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha', hb',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA B dB t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', B', t', hA', hB', ht', rfl⟩ := hsub_const₃ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      have hb' := decTy_hsub_obj hb hn hj hB'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha', hb',
        ih t (by simp) n j off t' st β
          (by rw [hd (t, dt) (by simp)]; exact hst)
          (bnd_plain rfl hocc (by simp)) hn hj ht', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ A dA B dB C dC p dp heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sp, hsp, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      obtain ⟨A', B', C', p', hA', hB', hC', hp', rfl⟩ := hsub_const₄ hs
      have ha' := decTy_hsub_obj ha hn hj hA'
      have hb' := decTy_hsub_obj hb hn hj hB'
      have hc' := decTy_hsub_obj hc hn hj hC'
      rw [Expr.const, Expr.app, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, ha', hb', hc',
        ih p (by simp) n j off p' sp β
          (by rw [hd (p, dp) (by simp)]; exact hsp)
          (bnd_plain rfl hocc (by simp)) hn hj hp', Option.bind_eq_bind,
        Option.bind_some]
      rfl
    · next _ _ b db heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      simp only [List.map_cons, List.map_nil] at hs
      obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [show (RoseTree.node Label.lam [b] : Expr) = Expr.lam b from rfl, hsub_lam,
        Option.map_eq_map, Option.map_eq_some_iff] at hs
      obtain ⟨b', hb', rfl⟩ := hs
      have hb := ih b (by simp) n.shift (j + 1) (off + 1) b' sb β
        (by rw [hd (b, db) (by simp)]; exact hsb)
        (fun i hi ↦ by
          rcases i with _ | i
          · omega
          · exact Nat.succ_lt_succ (hocc i hi))
        (decTy_rename hn fun i _ ↦ by omega) (by omega) hb'
      rw [show j + 1 - (off + 1) = j - off by omega] at hb
      rw [Expr.lam, dec_node]
      simp only [List.map_cons, List.map_nil, decStep, hb, Option.map_eq_map, Option.map_some]
      rfl
    · exact absurd h (by simp)

open FreeTopos.Internal (substF substF_node_succ substF_var) in
/-- The encoding of a type at an offset raised by {lit}`q` is the encoding at the offset of the
type with its object variables raised by {lit}`q`. -/
theorem encTy_shiftObj {off q : ℕ} :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy (off + q) a = some A →
      encTy off (FreeTopos.Internal.shiftObj q a) = some A :=
  RoseTree.ind fun l cs ih A h ↦ by
    unfold FreeTopos.Internal.shiftObj at ih ⊢
    rcases encTy_node_eq_some h with ⟨rfl, i, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a₁, a₂, hcs, rfl⟩ | ⟨rfl, a₁, a₂, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a₁, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, a₁, hcs, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
        ⟨rfl, a₁, a₂, hcs, rfl⟩
    · rw [FreeTopos.Internal.substF_node_zero _ rfl, RoseTree.label_node, encTy_var]
      rw [show off + (i + q) = off + q + i by omega]
    · rw [substF_node_succ]
      rfl
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_encTy_eq_two hcs
      rw [substF_node_succ]
      change encTy off (FreeTopos.prod _ _) = _
      rw [encTy_prod, ih c₁ (by simp) a₁ h₁, ih c₂ (by simp) a₂ h₂]
      rfl
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_encTy_eq_two hcs
      rw [substF_node_succ]
      change encTy off (FreeTopos.exp _ _) = _
      rw [encTy_exp, ih c₁ (by simp) a₁ h₁, ih c₂ (by simp) a₂ h₂]
      rfl
    · rw [substF_node_succ]
      rfl
    · rw [substF_node_succ]
      rfl
    · obtain ⟨c₁, rfl, h₁⟩ := map_encTy_eq_one hcs
      rw [substF_node_succ]
      change encTy off (FreeTopos.list _) = _
      rw [encTy_list, ih c₁ (by simp) a₁ h₁]
      rfl
    · rw [substF_node_succ]
      rfl
    · obtain ⟨c₁, rfl, h₁⟩ := map_encTy_eq_one hcs
      rw [substF_node_succ]
      change encTy off (FreeTopos.lrose _) = _
      rw [encTy_lrose, ih c₁ (by simp) a₁ h₁]
      rfl
    · rw [substF_node_succ]
      rfl
    · obtain ⟨c₁, c₂, rfl, h₁, h₂⟩ := map_encTy_eq_two hcs
      rw [substF_node_succ]
      change encTy off (FreeTopos.coprod _ _) = _
      rw [encTy_coprod, ih c₁ (by simp) a₁ h₁, ih c₂ (by simp) a₂ h₂]
      rfl

/-- The hereditary substitutions, at a simple type, of a list of terms, the first outermost, for
the outermost variables of an expression's scope, inside which are {lit}`d` further variables:
each term in turn for the outermost variable remaining, weakened past the variables inside it. -/
def hsubsPre (α : SimpleTy) : List Expr → ℕ → Expr → Option Expr :=
  List.rec (fun _ X ↦ some X) fun m ms r d X ↦
    (hsub α (Expr.shift^[ms.length + d] m) X (ms.length + d)).bind (r d)

/-- The substitutions under further variables: the first term, then the rest. -/
theorem hsubsPre_cons (α : SimpleTy) (m : Expr) (ms : List Expr) (d : ℕ) (X : Expr) :
    hsubsPre α (m :: ms) d X =
      (hsub α (Expr.shift^[ms.length + d] m) X (ms.length + d)).bind (hsubsPre α ms d) :=
  rfl

/-- The substitutions of a list's two parts in turn: the first part's under the second's
variables, then the second's. -/
theorem hsubs_append (α : SimpleTy) (bs : List Expr) :
    ∀ (as : List Expr) (X : Expr),
      hsubs α (as ++ bs) X = (hsubsPre α as bs.length X).bind (hsubs α bs) := by
  intro as
  refine List.rec (motive := fun as ↦ ∀ X : Expr,
      hsubs α (as ++ bs) X = (hsubsPre α as bs.length X).bind (hsubs α bs))
    (fun X ↦ rfl) (fun a as ih X ↦ ?_) as
  rw [List.cons_append, hsubs_cons, hsubsPre_cons, List.length_append, Option.bind_assoc]
  exact congrArg _ (funext ih)

/-- The substitutions under further variables commute with renaming. -/
theorem hsubsPre_rename (α : SimpleTy) (ρ : ℕ → ℕ) (d : ℕ) :
    ∀ (ms : List Expr) (X X' : Expr), hsubsPre α ms d X = some X' →
      hsubsPre α (ms.map fun m ↦ m.rename ρ) d (X.rename (liftR^[ms.length + d] ρ)) =
        some (X'.rename (liftR^[d] ρ)) := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ (X X' : Expr), hsubsPre α ms d X = some X' →
      hsubsPre α (ms.map fun m ↦ m.rename ρ) d (X.rename (liftR^[ms.length + d] ρ)) =
        some (X'.rename (liftR^[d] ρ)))
    (fun X X' h ↦ by
      obtain rfl := Option.some.inj h
      rw [List.length_nil, Nat.zero_add]
      rfl) (fun m ms ih X X' h ↦ ?_) ms
  rw [hsubsPre_cons] at h
  obtain ⟨X₁, hX₁, h⟩ := Option.bind_eq_some_iff.mp h
  have hr := hsubWith_rename (reduce_rename α) X _ (ms.length + d) ρ X₁ hX₁
  rw [← iterate_shift_rename, ← hsub_eq] at hr
  rw [List.map_cons, hsubsPre_cons, List.length_map, List.length_cons,
    show ms.length + 1 + d = ms.length + d + 1 by omega, hr, Option.bind_some]
  exact ih X₁ X' h

/-- The substitutions into a constant applied to one argument substitute into the argument. -/
theorem hsubs_const₁ {α : SimpleTy} {c : ℕ} :
    ∀ {ms : List Expr} {X Y : Expr}, hsubs α ms (Expr.const c [X]) = some Y →
      ∃ X', hsubs α ms X = some X' ∧ Y = Expr.const c [X'] := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ {X Y : Expr}, hsubs α ms (Expr.const c [X]) = some Y →
      ∃ X', hsubs α ms X = some X' ∧ Y = Expr.const c [X'])
    (fun {X Y} h ↦ ⟨X, rfl, (Option.some.inj h).symm⟩) (fun m ms ih {X Y} h ↦ ?_) ms
  rw [hsubs_cons] at h
  obtain ⟨Y₁, hY₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨X₁, hX₁, rfl⟩ := hsub_const₁ hY₁
  obtain ⟨X', hX', rfl⟩ := ih h
  exact ⟨X', by rw [hsubs_cons, hX₁, Option.bind_some]; exact hX', rfl⟩

/-- The substitutions under further variables into a constant applied to one argument substitute
into the argument. -/
theorem hsubsPre_const₁ {α : SimpleTy} {c d : ℕ} :
    ∀ {ms : List Expr} {X Y : Expr}, hsubsPre α ms d (Expr.const c [X]) = some Y →
      ∃ X', hsubsPre α ms d X = some X' ∧ Y = Expr.const c [X'] := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ {X Y : Expr}, hsubsPre α ms d (Expr.const c [X]) =
      some Y → ∃ X', hsubsPre α ms d X = some X' ∧ Y = Expr.const c [X'])
    (fun {X Y} h ↦ ⟨X, rfl, (Option.some.inj h).symm⟩) (fun m ms ih {X Y} h ↦ ?_) ms
  rw [hsubsPre_cons] at h
  obtain ⟨Y₁, hY₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨X₁, hX₁, rfl⟩ := hsub_const₁ hY₁
  obtain ⟨X', hX', rfl⟩ := ih h
  exact ⟨X', by rw [hsubsPre_cons, hX₁, Option.bind_some]; exact hX', rfl⟩

open FreeTopos.Internal (shiftObj objScope objScope_cons objScope_nil objAt) in
/-- At a base type, decoding commutes with the substitutions of types for the outermost
variables of a scope, the object variables of the decoding inside {lit}`d` term variables: where
each type is the encoding of an object at every offset, and the expression decodes to a term
whose variables are below {lit}`d`, the substituted expression decodes to the decoded term with
the objects substituted for the scope's object variables. -/
theorem dec_hsubsPre_obj {c₀ d : ℕ} :
    ∀ (Xs : List Expr) (bs : List PartialHorn.Tree) (X X' : Expr) (y : MTerm),
      List.Forall₂ (fun Xk b ↦ ∀ e, encTy e b = some (Xk.rename (· + e))) Xs bs →
      dec k X d = some y → (∀ i, Term.occurs y i = true → i < d) →
      hsubsPre (RoseTree.node (.base c₀) []) Xs d X = some X' →
        dec k X' d = some (Term.osubstF (objScope bs) y) := by
  intro Xs
  refine List.rec (motive := fun Xs ↦ ∀ (bs : List PartialHorn.Tree) (X X' : Expr) (y : MTerm),
      List.Forall₂ (fun Xk b ↦ ∀ e, encTy e b = some (Xk.rename (· + e))) Xs bs →
      dec k X d = some y → (∀ i, Term.occurs y i = true → i < d) →
      hsubsPre (RoseTree.node (.base c₀) []) Xs d X = some X' →
        dec k X' d = some (Term.osubstF (objScope bs) y))
    (fun bs X X' y hbs hX _ h ↦ ?_) (fun X₁ Xs ih bs X X' y hbs hX hocc h ↦ ?_) Xs
  · cases hbs
    obtain rfl := Option.some.inj h
    rw [objScope_nil, Term.osubstF_var]
    exact hX
  rcases hbs with _ | ⟨hb₁, hbs⟩
  rename_i b₁ bs
  rw [hsubsPre_cons] at h
  obtain ⟨X₁', hX₁', h⟩ := Option.bind_eq_some_iff.mp h
  have hq := hbs.length_eq
  have hn : decTy d (Expr.shift^[Xs.length + d] X₁) = some (shiftObj Xs.length b₁) := by
    rw [iterate_shift]
    refine decTy_encTy _ _ _ (encTy_shiftObj (off := d) _ _ ?_)
    rw [Nat.add_comm d]
    exact hb₁ _
  have hy₁ := dec_hsub_obj (k := k) X _ (Xs.length + d) d X₁' y _ hX hocc hn (by omega) hX₁'
  rw [Nat.add_sub_cancel] at hy₁
  rw [ih bs X₁' X' _ hbs hy₁ (fun i hi ↦ hocc i (by rwa [Term.occurs_osubstF] at hi)) h,
    Term.osubstF_comp, hq]
  exact congrArg (some ∘ (Term.osubstF · y)) (funext (objScope_cons b₁ bs))

open FreeTopos.Internal (substF substF_comp shiftObj objScope objScope_cons objScope_nil
  substF_var_id) in
/-- At a base type, the substitutions of types, each the encoding of an object at every offset,
for the outermost variables of a scope, inside which are {lit}`d` term variables, into the
encoding of a type at the offset {lit}`d` give the encoding of the type with the objects
substituted for the scope's object variables. -/
theorem encTy_hsubsPre_obj {c₀ d : ℕ} :
    ∀ (Xs : List Expr) (bs : List PartialHorn.Tree) (a : PartialHorn.Tree) (A A' : Expr),
      List.Forall₂ (fun Xk b ↦ ∀ e, encTy e b = some (Xk.rename (· + e))) Xs bs →
      encTy d a = some A → hsubsPre (RoseTree.node (.base c₀) []) Xs d A = some A' →
        encTy d (substF (objScope bs) a) = some A' := by
  intro Xs
  refine List.rec (motive := fun Xs ↦ ∀ (bs : List PartialHorn.Tree) (a : PartialHorn.Tree)
      (A A' : Expr), List.Forall₂ (fun Xk b ↦ ∀ e, encTy e b = some (Xk.rename (· + e))) Xs bs →
      encTy d a = some A → hsubsPre (RoseTree.node (.base c₀) []) Xs d A = some A' →
        encTy d (substF (objScope bs) a) = some A')
    (fun bs a A A' hbs hA h ↦ ?_) (fun X₁ Xs ih bs a A A' hbs hA h ↦ ?_) Xs
  · cases hbs
    obtain rfl := Option.some.inj h
    rw [objScope_nil, substF_var_id]
    exact hA
  rcases hbs with _ | ⟨hb₁, hbs⟩
  rename_i b₁ bs
  rw [hsubsPre_cons] at h
  obtain ⟨A₁, hA₁, h⟩ := Option.bind_eq_some_iff.mp h
  have hq := hbs.length_eq
  have hn : encTy d (shiftObj Xs.length b₁) = some (Expr.shift^[Xs.length + d] X₁) := by
    rw [iterate_shift]
    refine encTy_shiftObj (off := d) _ _ ?_
    rw [Nat.add_comm d]
    exact hb₁ _
  have ha₁ := encTy_hsub_obj hn (by omega) a A A₁ hA hA₁
  rw [Nat.add_sub_cancel] at ha₁
  rw [← ih bs _ A₁ A' hbs ha₁ h, substF_comp, hq]
  exact congrArg (encTy d ∘ (substF · a)) (funext (objScope_cons b₁ bs)).symm

/-- The substitutions of terms for the term variables of the encoding of a type leave it the
encoding of the type at the offset below them. -/
theorem hsubs_encTy {α : SimpleTy} :
    ∀ (ms : List Expr) (a : PartialHorn.Tree) (A A' : Expr), encTy ms.length a = some A →
      hsubs α ms A = some A' → encTy 0 a = some A' := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ (a : PartialHorn.Tree) (A A' : Expr),
      encTy ms.length a = some A → hsubs α ms A = some A' → encTy 0 a = some A')
    (fun a A A' hA h ↦ by obtain rfl := Option.some.inj h; exact hA)
    (fun m ms ih a A A' hA h ↦ ?_) ms
  rw [hsubs_cons] at h
  obtain ⟨A₁, hA₁, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨A₂, hA₂, hs⟩ := hsubWith_encTy (reduce α) (j := ms.length) hA
    (by rw [List.length_cons]; omega) (Expr.shift^[ms.length] m)
  rw [← hsub_eq, hA₁, Option.some.injEq] at hs
  subst hs
  exact ih a A₁ A' (by simpa using hA₂) h

/-- At base types, the hereditary substitution does not depend on the base type. -/
theorem hsub_base_eq (c c' : ℕ) :
    hsub (RoseTree.node (.base c) []) = hsub (RoseTree.node (.base c') []) := by
  have : reduce (RoseTree.node (.base c) []) = reduce (RoseTree.node (.base c') []) :=
    funext fun n ↦ funext fun ms ↦ by
      rw [reduce_node, reduce_node]
      rcases ms with _ | _ <;> rfl
  funext n e j
  rw [hsub, hsub, this]

/-- Substitution into the kind of types or a family of terms gives the kind of types or a family
of terms. -/
theorem hsub_tpTm {α : SimpleTy} {n D D' : Expr} {j : ℕ} (hD : D = tp ∨ ∃ A, D = tm A)
    (h : hsub α n D j = some D') : D' = tp ∨ ∃ A', D' = tm A' := by
  rcases hD with rfl | ⟨A, rfl⟩
  · rw [tp, hsub_const] at h
    exact .inl (Option.some.inj h).symm
  · obtain ⟨A', -, rfl⟩ := hsub_const₁ h
    exact .inr ⟨A', rfl⟩

/-- The substitution into products: into each domain under the products before it, and into the
body under all of them. -/
theorem hsub_piTele_gen {α : SimpleTy} {R : Expr} :
    ∀ {Ds : List Expr} {n c : Expr} {j : ℕ}, hsub α n (piTele Ds R) j = some c →
      ∃ Ds' R', c = piTele Ds' R' ∧ Ds'.length = Ds.length ∧
        (∀ i D, Ds[i]? = some D →
          ∃ D', Ds'[i]? = some D' ∧ hsub α (Expr.shift^[i] n) D (j + i) = some D') ∧
        hsub α (Expr.shift^[Ds.length] n) R (j + Ds.length) = some R' := by
  intro Ds
  refine List.rec (motive := fun Ds ↦ ∀ {n c : Expr} {j : ℕ}, hsub α n (piTele Ds R) j = some c →
      ∃ Ds' R', c = piTele Ds' R' ∧ Ds'.length = Ds.length ∧
        (∀ i D, Ds[i]? = some D →
          ∃ D', Ds'[i]? = some D' ∧ hsub α (Expr.shift^[i] n) D (j + i) = some D') ∧
        hsub α (Expr.shift^[Ds.length] n) R (j + Ds.length) = some R')
    (fun {_ _ _} h ↦ ⟨[], _, rfl, rfl, fun _ _ h' ↦ by simp at h', h⟩)
    (fun D Ds ih {n c j} h ↦ ?_) Ds
  obtain ⟨a', b', ha, hb, rfl⟩ := hsub_pi α n D (piTele Ds R) j c h
  obtain ⟨Ds₁, R₁, rfl, hlen, hi, hR⟩ := ih hb
  refine ⟨a' :: Ds₁, R₁, rfl, by rw [List.length_cons, List.length_cons, hlen],
    fun i D' hD' ↦ ?_, ?_⟩
  · rcases i with _ | i
    · obtain rfl := Option.some.inj hD'
      exact ⟨a', rfl, ha⟩
    · obtain ⟨D₁, hD₁, hs⟩ := hi i D' hD'
      refine ⟨D₁, hD₁, ?_⟩
      rw [Function.iterate_succ_apply, show j + (i + 1) = j + 1 + i by omega]
      exact hs
  · rw [List.length_cons, Function.iterate_succ_apply,
      show j + (Ds.length + 1) = j + 1 + Ds.length by omega]
    exact hR

/-- The instantiation of products over the kind of types and families of terms along a spine that
instantiates them to an atomic family: each leading argument, one for each domain, checks
against its domain with the arguments before it substituted, and the rest instantiate the body
with the leading arguments substituted. -/
theorem spine_piTele_gen {Γ : Ctx} {J : Expr → Ctx → Mode → Bool} {P : Expr}
    (hP : IsApp P = true) {Ds : List Expr} (hDs : ∀ D ∈ Ds, D = tp ∨ ∃ A, D = tm A)
    {ms : List Expr} {R : Expr}
    (h : spine Γ (piTele Ds R) (ms.map fun m ↦ (m, J m)) = some P) :
    Ds.length ≤ ms.length ∧
      (∀ i D, Ds[i]? = some D → ∃ D' m,
        hsubs (RoseTree.node (.base 6) []) (ms.take i) D = some D' ∧ ms[i]? = some m ∧
          J m Γ (.check D') = true) ∧
      ∃ R', hsubs (RoseTree.node (.base 6) []) (ms.take Ds.length) R = some R' ∧
        spine Γ R' ((ms.drop Ds.length).map fun m ↦ (m, J m)) = some P := by
  refine Nat.rec (motive := fun N ↦ ∀ (Ds : List Expr), Ds.length = N →
      (∀ D ∈ Ds, D = tp ∨ ∃ A, D = tm A) →
      ∀ {ms : List Expr} {R : Expr}, spine Γ (piTele Ds R) (ms.map fun m ↦ (m, J m)) = some P →
        Ds.length ≤ ms.length ∧
        (∀ i D, Ds[i]? = some D → ∃ D' m,
          hsubs (RoseTree.node (.base 6) []) (ms.take i) D = some D' ∧ ms[i]? = some m ∧
            J m Γ (.check D') = true) ∧
        ∃ R', hsubs (RoseTree.node (.base 6) []) (ms.take Ds.length) R = some R' ∧
          spine Γ R' ((ms.drop Ds.length).map fun m ↦ (m, J m)) = some P)
    (fun Ds hN _ {_ _} h ↦ ?_) (fun N ih Ds hN hDs {ms R} h ↦ ?_) Ds.length Ds rfl hDs h
  · obtain rfl := List.length_eq_zero_iff.mp hN
    exact ⟨Nat.zero_le _, fun _ _ h' ↦ by simp at h', _, rfl, h⟩
  obtain ⟨D, Ds, rfl⟩ := List.exists_cons_of_length_eq_add_one hN
  rcases ms with _ | ⟨m, ms⟩
  · obtain rfl := Option.some.inj h
    exact absurd hP (by rw [piTele_cons, Expr.pi]; exact Bool.false_ne_true)
  rw [List.map_cons, piTele_cons] at h
  obtain ⟨hm, b', hb', hS⟩ := spine_cons_inv h
  have hcD : ∃ c, D.erase = RoseTree.node (.base c) [] := by
    rcases hDs D List.mem_cons_self with rfl | ⟨A, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨6, rfl⟩
  obtain ⟨c, hc⟩ := hcD
  rw [hc, hsub_base_eq c 6] at hb'
  obtain ⟨Ds₁, R₁, rfl, hlen, hi, hR⟩ := hsub_piTele_gen hb'
  have hDs₁ : ∀ D ∈ Ds₁, D = tp ∨ ∃ A, D = tm A := fun D₁ hD₁ ↦ by
    obtain ⟨i, hi₁, rfl⟩ := List.getElem_of_mem hD₁
    obtain ⟨D', hD', hs⟩ := hi i Ds[i] (List.getElem?_eq_getElem (by omega))
    rw [List.getElem?_eq_getElem hi₁, Option.some.injEq] at hD'
    subst hD'
    exact hsub_tpTm (hDs _ (List.mem_cons_of_mem _ (List.getElem_mem _))) hs
  obtain ⟨hle, hix, R', hR', hS'⟩ :=
    ih Ds₁ (by rw [hlen]; exact Nat.succ.inj hN) hDs₁ hS
  rw [hlen] at hle hR' hS'
  refine ⟨by rw [List.length_cons, List.length_cons]; omega, fun i D' hD' ↦ ?_, R', ?_,
    by rw [List.length_cons, List.drop_succ_cons]; exact hS'⟩
  · rcases i with _ | i
    · obtain rfl := Option.some.inj hD'
      exact ⟨D, m, rfl, rfl, hm⟩
    · have hD'' : Ds[i]? = some D' := hD'
      obtain ⟨D₁, hD₁, hs⟩ := hi i D' hD''
      have hlt : i < Ds.length := (List.getElem?_eq_some_iff.mp hD'').1
      obtain ⟨D₂, m', hD₂, hm', hJ⟩ := hix i D₁ hD₁
      refine ⟨D₂, m', ?_, hm', hJ⟩
      rw [List.take_succ_cons, hsubs_cons, List.length_take, Nat.min_eq_left (by omega)]
      rw [Nat.zero_add] at hs
      rw [hs, Option.bind_some]
      exact hD₂
  · rw [List.length_cons, List.take_succ_cons, hsubs_cons, List.length_take,
      Nat.min_eq_left (by omega)]
    rw [Nat.zero_add] at hR
    rw [hR, Option.bind_some]
    exact hR'

/-- The encoding of a context, reversed: the kind of types for each object variable, then the
families of terms of the variables' types, the outermost first, each encoded at the number of
variables outside it. -/
theorem encCtx_reverse {m : ℕ} :
    ∀ {Γ : List PartialHorn.Tree} {ΓT : Ctx}, encCtx m Γ = some ΓT →
      ∃ T', ΓT.reverse = List.replicate m tp ++ T' ∧ T'.length = Γ.length ∧
        ∀ i b, Γ.reverse[i]? = some b → ∃ A, T'[i]? = some (tm A) ∧ encTy i b = some A := by
  intro Γ
  refine List.rec (motive := fun Γ ↦ ∀ {ΓT : Ctx}, encCtx m Γ = some ΓT →
      ∃ T', ΓT.reverse = List.replicate m tp ++ T' ∧ T'.length = Γ.length ∧
        ∀ i b, Γ.reverse[i]? = some b → ∃ A, T'[i]? = some (tm A) ∧ encTy i b = some A)
    (fun {ΓT} h ↦ ?_) (fun a Γ ih {ΓT} h ↦ ?_) Γ
  · obtain rfl := Option.some.inj h
    exact ⟨[], by rw [List.reverse_replicate, List.append_nil], rfl, fun _ _ h' ↦ by simp at h'⟩
  obtain ⟨A, ΓT', hA, hΓ', rfl⟩ := encCtx_cons_inv h
  obtain ⟨T', hT', hlen, hi⟩ := ih hΓ'
  refine ⟨T' ++ [tm A], by rw [List.reverse_cons, hT', List.append_assoc],
    by rw [List.length_append, hlen]; rfl, fun i b hb ↦ ?_⟩
  rw [List.reverse_cons] at hb
  by_cases hlt : i < Γ.length
  · rw [List.getElem?_append_left (by rw [List.length_reverse]; exact hlt)] at hb
    obtain ⟨A', hA', he⟩ := hi i b hb
    exact ⟨A', by rw [List.getElem?_append_left (by rw [hlen]; exact hlt)]; exact hA', he⟩
  · rw [List.getElem?_append_right (by rw [List.length_reverse]; omega),
      List.length_reverse] at hb
    have hi' : i = Γ.length := by
      by_contra hne
      rw [List.getElem?_eq_none (by simp; omega)] at hb
      exact nomatch hb
    subst hi'
    rw [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hb
    subst hb
    exact ⟨A, by rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]; rfl, hA⟩

/-- The substitutions into the kind of types leave it. -/
theorem hsubs_tp {α : SimpleTy} :
    ∀ {ms : List Expr} {D : Expr}, hsubs α ms tp = some D → D = tp := by
  intro ms
  refine List.rec (motive := fun ms ↦ ∀ {D : Expr}, hsubs α ms tp = some D → D = tp)
    (fun {D} h ↦ (Option.some.inj h).symm) (fun m ms ih {D} h ↦ ?_) ms
  rw [hsubs_cons, tp, hsub_const] at h
  exact ih h

/-- The encoding of a node of label zero is that of a variable. -/
theorem encTy_zero_inv {off : ℕ} {ds : List PartialHorn.Tree} {A : Expr}
    (h : encTy off (RoseTree.node 0 ds) = some A) :
    ∃ i, ds = [RoseTree.node i []] ∧ A = Expr.var (off + i) := by
  rcases encTy_node_eq_some h with ⟨-, i, hds, rfl⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ |
      ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩ | ⟨h₁, -⟩
  · exact ⟨i, hds, rfl⟩
  all_goals exact absurd h₁ (by decide)

open FreeTopos.Internal (substF substF_node_succ shiftObj) in
/-- The encoding at an offset of a type with its object variables raised by {lit}`q` is the
encoding of the type at the offset raised by {lit}`q`. -/
theorem encTy_of_shiftObj {off q : ℕ} :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy off (shiftObj q a) = some A →
      encTy (off + q) a = some A :=
  RoseTree.ind fun l cs ih A h ↦ by
    unfold shiftObj at ih h
    rcases l with _ | k
    · rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
      · rw [FreeTopos.Internal.substF_node_zero_other _ fun _ ↦
          FreeTopos.Internal.nil_ne_singleton] at h
        obtain ⟨i, hds, -⟩ := encTy_zero_inv h
        exact absurd hds FreeTopos.Internal.nil_ne_singleton
      · rcases hcc : c.children with _ | ⟨d, ds⟩
        · have hc : c.children = [] := hcc
          rw [FreeTopos.Internal.substF_node_zero _ hc] at h
          change encTy off (PartialHorn.var (c.label + q)) = some A at h
          rw [encTy_var] at h
          obtain rfl := Option.some.inj h
          rw [← RoseTree.node_label_children c, hc]
          change encTy (off + q) (PartialHorn.var c.label) = _
          rw [encTy_var, show off + q + c.label = off + (c.label + q) by omega]
          rfl
        · have hc : c.children ≠ [] := by rw [hcc]; exact List.cons_ne_nil _ _
          rw [FreeTopos.Internal.substF_node_zero_of_not _ hc] at h
          obtain ⟨i, hds, -⟩ := encTy_zero_inv h
          rw [List.cons.injEq] at hds
          exact absurd (by rw [hds.1]; rfl) hc
      · rw [FreeTopos.Internal.substF_node_zero_other _ fun _ ↦
          FreeTopos.Internal.cons_cons_ne_singleton] at h
        obtain ⟨i, hds, -⟩ := encTy_zero_inv h
        exact absurd hds FreeTopos.Internal.cons_cons_ne_singleton
    rw [substF_node_succ] at h
    rcases encTy_node_eq_some h with ⟨h₁, -⟩ | ⟨h₁, hcs, rfl⟩ |
        ⟨h₁, a₁, a₂, hcs, rfl⟩ | ⟨h₁, a₁, a₂, hcs, rfl⟩ | ⟨h₁, hcs, rfl⟩ | ⟨h₁, hcs, rfl⟩ |
        ⟨h₁, a₁, hcs, rfl⟩ | ⟨h₁, hcs, rfl⟩ | ⟨h₁, a₁, hcs, rfl⟩ | ⟨h₁, hcs, rfl⟩ |
        ⟨h₁, a₁, a₂, hcs, rfl⟩
    · exact absurd h₁ (Nat.succ_ne_zero k)
    all_goals
      obtain rfl := Nat.succ.inj h₁
    · obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · obtain ⟨d₁, d₂, hds, h₁, h₂⟩ := map_encTy_eq_two hcs
      obtain ⟨c₁, c₂, rfl, rfl, rfl⟩ : ∃ c₁ c₂, cs = [c₁, c₂] ∧ substF _ c₁ = d₁ ∧
          substF _ c₂ = d₂ := by
        rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
        · exact absurd (congrArg List.length hds) (by simp)
        · exact absurd (congrArg List.length hds) (by simp)
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hds
          exact ⟨c₁, c₂, rfl, hds.1, hds.2⟩
        · exact absurd (congrArg List.length hds) (by simp)
      change encTy (off + q) (FreeTopos.prod c₁ c₂) = _
      rw [encTy_prod, ih c₁ (by simp) a₁ h₁, ih c₂ (by simp) a₂ h₂]
      rfl
    · obtain ⟨d₁, d₂, hds, h₁, h₂⟩ := map_encTy_eq_two hcs
      obtain ⟨c₁, c₂, rfl, rfl, rfl⟩ : ∃ c₁ c₂, cs = [c₁, c₂] ∧ substF _ c₁ = d₁ ∧
          substF _ c₂ = d₂ := by
        rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
        · exact absurd (congrArg List.length hds) (by simp)
        · exact absurd (congrArg List.length hds) (by simp)
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hds
          exact ⟨c₁, c₂, rfl, hds.1, hds.2⟩
        · exact absurd (congrArg List.length hds) (by simp)
      change encTy (off + q) (FreeTopos.exp c₁ c₂) = _
      rw [encTy_exp, ih c₁ (by simp) a₁ h₁, ih c₂ (by simp) a₂ h₂]
      rfl
    · obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · obtain ⟨d₁, hds, h₁⟩ := map_encTy_eq_one hcs
      obtain ⟨c₁, rfl, rfl⟩ : ∃ c₁, cs = [c₁] ∧ substF _ c₁ = d₁ := by
        rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
        · exact absurd hds FreeTopos.Internal.nil_ne_singleton
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hds
          exact ⟨c₁, rfl, hds⟩
        · exact absurd hds FreeTopos.Internal.cons_cons_ne_singleton
      change encTy (off + q) (FreeTopos.list c₁) = _
      rw [encTy_list, ih c₁ (by simp) a₁ h₁]
      rfl
    · obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · obtain ⟨d₁, hds, h₁⟩ := map_encTy_eq_one hcs
      obtain ⟨c₁, rfl, rfl⟩ : ∃ c₁, cs = [c₁] ∧ substF _ c₁ = d₁ := by
        rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
        · exact absurd hds FreeTopos.Internal.nil_ne_singleton
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hds
          exact ⟨c₁, rfl, hds⟩
        · exact absurd hds FreeTopos.Internal.cons_cons_ne_singleton
      change encTy (off + q) (FreeTopos.lrose c₁) = _
      rw [encTy_lrose, ih c₁ (by simp) a₁ h₁]
      rfl
    · obtain rfl := List.map_eq_nil_iff.mp hcs
      rfl
    · obtain ⟨d₁, d₂, hds, h₁, h₂⟩ := map_encTy_eq_two hcs
      obtain ⟨c₁, c₂, rfl, rfl, rfl⟩ : ∃ c₁ c₂, cs = [c₁, c₂] ∧ substF _ c₁ = d₁ ∧
          substF _ c₂ = d₂ := by
        rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
        · exact absurd (congrArg List.length hds) (by simp)
        · exact absurd (congrArg List.length hds) (by simp)
        · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hds
          exact ⟨c₁, c₂, rfl, hds.1, hds.2⟩
        · exact absurd (congrArg List.length hds) (by simp)
      change encTy (off + q) (FreeTopos.coprod c₁ c₂) = _
      rw [encTy_coprod, ih c₁ (by simp) a₁ h₁, ih c₂ (by simp) a₂ h₂]
      rfl

/-- Lists of one length whose elements at each position are related are related pointwise. -/
theorem forall₂_of_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, xs.length = ys.length →
      (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), R xs[i] ys[i]) → List.Forall₂ R xs ys := by
  intro xs
  refine List.rec (motive := fun xs ↦ ∀ {ys : List β}, xs.length = ys.length →
      (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), R xs[i] ys[i]) → List.Forall₂ R xs ys)
    (fun {ys} hl _ ↦ by
      obtain rfl := List.length_eq_zero_iff.mp hl.symm
      exact .nil)
    (fun x xs ih {ys} hl h ↦ ?_) xs
  rcases ys with _ | ⟨y, ys⟩
  · exact absurd hl (by simp)
  · exact .cons (h 0 (by simp) (by simp))
      (ih (Nat.succ.inj hl) fun i h₁ h₂ ↦ h (i + 1) (by simpa using h₁) (by simpa using h₂))

/-- The first {lit}`m + p` elements of a list are its first {lit}`m` and, after them, the next
{lit}`p`. -/
theorem take_add' {α : Type} (p : ℕ) :
    ∀ (m : ℕ) (l : List α), l.take (m + p) = l.take m ++ (l.drop m).take p :=
  Nat.rec (fun l ↦ by rw [Nat.zero_add, List.take_zero, List.drop_zero, List.nil_append])
    fun m ih l ↦ by
      rcases l with _ | ⟨x, l⟩
      · rw [List.take_nil, List.take_nil, List.drop_nil, List.take_nil, List.nil_append]
      · rw [Nat.succ_add, List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons, ih l,
          List.cons_append]

/-- The declaration of a theorem of the language: the products over the kind of types, one for
each of its object variables, of the products over the families of terms of its variables'
types, the outermost first, each encoded at the offset of the variables outside it, of the
products over the families of proofs of its hypotheses into the family of proofs of its
conclusion, the formulas encoded in the scope of the variables. -/
def thmTy (G : Globals) (k : PrimIdx) (a : Thm) : Option Expr := do
  let ΓT ← encCtx a.arity a.ctx
  let Hs ← a.hyps.mapM fun h ↦ enc G a.arity k h (ctxObj a.ctx) (stdEnv a.ctx)
  let C ← enc G a.arity k a.concl (ctxObj a.ctx) (stdEnv a.ctx)
  pure (piTele ΓT.reverse (arrows (Hs.map pf) (pf C)))

/-- The parts of the declaration of a theorem. -/
theorem thmTy_eq_some {G : Globals} {k : PrimIdx} {a : Thm} {T : Expr} (h : thmTy G k a = some T) :
    ∃ ΓT Hs C, encCtx a.arity a.ctx = some ΓT ∧
      a.hyps.mapM (fun h ↦ enc G a.arity k h (ctxObj a.ctx) (stdEnv a.ctx)) = some Hs ∧
      enc G a.arity k a.concl (ctxObj a.ctx) (stdEnv a.ctx) = some C ∧
      T = piTele ΓT.reverse (arrows (Hs.map pf) (pf C)) := by
  simp only [thmTy, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨ΓT, hΓ, Hs, hHs, C, hC, rfl⟩ := h
  exact ⟨ΓT, Hs, C, hΓ, hHs, hC, rfl⟩

/-- An extension of the signature declares the theorems that the table of the indices names:
the declaration at each position past the signature is that of the theorem of the entry at the
table's position, a well-formed theorem of as many object variables and variables as the table
records. -/
def ThmsDecl (G : Globals) (E : Array Entry) (k : PrimIdx) (sg : Sig) : Prop :=
  ∀ i T, sg[sig.length + i]? = some T → ∃ j a, k.thms[i]? = some (j, a.arity, a.ctx.length) ∧
    (E[j]?).bind Entry.language? = some a ∧ a.wellFormed G = true ∧ thmTy G k a = some T

/-- The signature declares no theorems past itself. -/
theorem thmsDecl_sig (G : Globals) (E : Array Entry) (k : PrimIdx) : ThmsDecl G E k sig :=
  fun _ _ h ↦ absurd (List.getElem?_eq_some_iff.mp h).1 (by omega)

end Geb.LF.Topos

end
