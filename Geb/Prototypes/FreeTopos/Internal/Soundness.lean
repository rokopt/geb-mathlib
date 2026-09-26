/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Square
public import Geb.Prototypes.FreeTopos.Recursion
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of the internal language's derivations

The checker {name}`Geb.FreeTopos.Internal.check` is sound. In every model of the theory extended
by the combinators' definitions and those the language's definitions compile to, every theorem of
a development that checks is valid ({lit}`valid_of_checkThms_ok`): its sides compile, in its
context's environment of projections, to arrows of one type that have one value at every
assignment of objects to its object variables. With every definition unfolded, its equation holds
in every model of the theory itself ({lit}`valid_unfoldAll_of_checkThms`).

A rewriting is sound in a context when, in every environment of arrows of the context's types, a
term that compiles rewrites to a term of its type whose arrow has its arrow's value
({lit}`RwSound`); an equation is sound when its sides, where both compile in such an environment,
have one type and arrows of one value ({lit}`EqSound`). Soundness is stated in every such
environment, not in the context's environment of projections alone, since congruence under an
abstraction and the instances of theorems reach environments of other forms. A term's type
depends on its environment's types alone ({name}`Geb.FreeTopos.Internal.compile_retype`), and its
arrow in an environment is its arrow in the context's environment of projections after the tuple
of the environment's arrows ({lit}`compile_of_stdEnv`).

Each equation of the language is sound by the equations of the combinators it compiles to: β by
substitution as composition and the evaluation of a currying, the components of a pair and the η
of pairs and of the terminal type by the product's equations, the unfolding of a definition by
its axiom, the computation of the folds by the recursions' equations, and an earlier theorem's
instance by the substitution of objects and of terms. Induction is sound by the uniqueness of the
folds with a parameter ({name}`Geb.FreeTopos.natRec_param_unique`,
{name}`Geb.FreeTopos.listRec_param_unique`), applied in the environment that extends the other
variables' environment by the induction variable, and carried to the given environment by the
arrow of the variable.

## Main definitions

* {lit}`RwSound`, {lit}`EqSound` — the soundness of a rewriting and of an equation in a context.
* {lit}`Thm.Valid` — the validity of a theorem in a model.
* {lit}`DefnsOk` — the definitions' bodies compile to the arrows their operations denote.

## Main statements

* {lit}`rootStep_sound`, {lit}`cong_sound` — the rewritings are sound.
* {lit}`natInd_sound`, {lit}`listInd_sound` — induction is sound.
* {lit}`check_sound` — the checker is sound.
* {lit}`valid_of_checkThms_ok`, {lit}`valid_unfoldAll_of_checkThms` — the theorems of a
  development that checks are valid, in the extension and in the theory.

## Tags

internal language, soundness, proof checker, induction, parametrised recursion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

section Environments

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

/-- A result is related to itself. -/
theorem ResEq.refl (r : Tree × Tree) : ResEq M ρ r r := ⟨rfl, rfl⟩

/-- Related results are related in the other order. -/
theorem ResEq.symm {r₁ r₂ : Tree × Tree} (h : ResEq M ρ r₁ r₂) : ResEq M ρ r₂ r₁ :=
  ⟨h.1.symm, h.2.symm⟩

/-- Results related to related results are related. -/
theorem ResEq.trans {r₁ r₂ r₃ : Tree × Tree} (h₁ : ResEq M ρ r₁ r₂) (h₂ : ResEq M ρ r₂ r₃) :
    ResEq M ρ r₁ r₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

/-- An environment has its own values. -/
theorem envEq_refl (e : List (Tree × Tree)) : EnvEq M ρ e e :=
  fun _ p hp ↦ ⟨p, hp, ResEq.refl p⟩

/-- The types of a context's environment of projections are the context's. -/
theorem map_snd_stdEnv : ∀ Γ : List Tree, (stdEnv Γ).map Prod.snd = Γ :=
  List.rec rfl fun a Γ ih ↦ by
    rcases Γ with _ | ⟨b, Γ⟩
    · rfl
    · change (extEnv (ctxObj (b :: Γ)) a (stdEnv (b :: Γ))).map Prod.snd = a :: b :: Γ
      simpa [extEnv, Function.comp_def] using ih


/-- Products of equal types have equal factors. -/
theorem prod_inj {a b a' b' : Tree} (h : prod a b = prod a' b') : a = a' ∧ b = b' := by
  have h₁ := prodParts_eq_some.mpr h
  rw [prodParts_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- Exponentials of equal types have equal exponents and bases. -/
theorem exp_inj {a b a' b' : Tree} (h : exp a b = exp a' b') : a = a' ∧ b = b' := by
  have h₁ := expParts_eq_some.mpr h
  rw [expParts_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- List types of equal types have equal element types. -/
theorem list_inj {a a' : Tree} (h : list a = list a') : a = a' := by
  have h₁ := listPart_eq_some.mpr h
  rw [listPart_eq_some.mpr rfl] at h₁
  simpa using h₁

/-- The element at an index of a list's results under a partial function is the result at the
list's element at the index. -/
theorem getElem?_of_mapM_eq {α β : Type} {f : α → Option β} {l : List α} {rs : List β}
    (h : l.mapM f = some rs) {i : ℕ} {r : β} (hr : rs[i]? = some r) :
    ∃ a, l[i]? = some a ∧ f a = some r := by
  rw [PartialHorn.mapM_eq_some_iff] at h
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map, hr, Option.map_some] at hi
  exact Option.map_eq_some_iff.mp hi

/-- Results of two partial functions at related elements of related lists, related whenever the
first has one, lift to the lists of results. -/
theorem mapM_forall₂ {α α' β β' : Type} {R₁ : α → α' → Prop} {R : β → β' → Prop}
    {f : α → Option β} {g : α' → Option β'}
    (hfg : ∀ a a' r, R₁ a a' → f a = some r → ∃ r', g a' = some r' ∧ R r r')
    {l : List α} {l' : List α'} (h : List.Forall₂ R₁ l l') :
    ∀ {rs : List β}, l.mapM f = some rs →
      ∃ rs', l'.mapM g = some rs' ∧ List.Forall₂ R rs rs' :=
  h.rec (motive := fun l l' _ ↦ ∀ {rs : List β}, l.mapM f = some rs →
      ∃ rs', l'.mapM g = some rs' ∧ List.Forall₂ R rs rs')
    (fun h ↦ by
      obtain rfl : [] = _ := by simpa using h
      exact ⟨[], rfl, .nil⟩)
    (fun {a a' _ _} hR _ ih rs h ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨r, hr, rs₀, hrs₀, rfl⟩ := h
      obtain ⟨r', hr', hRr⟩ := hfg a a' r hR hr
      obtain ⟨rs', hrs', hR'⟩ := ih hrs₀
      exact ⟨r' :: rs', by simp [List.mapM_cons, hr', hrs'], .cons hRr hR'⟩)

/-- Terms of types in a context compile, in every environment of the context's types, to those
types. -/
theorem mapM_compile_of_typeIn {G : Globals} {n : ℕ} {Γ : List Tree} {X : Tree}
    {e : List (Tree × Tree)} (hΓ : e.map Prod.snd = Γ) :
    ∀ (σ : List Term) (Δ : List Tree), σ.length = Δ.length →
      (σ.zip Δ).all (fun x ↦ decide (typeIn G n Γ x.1 = some x.2)) = true →
      ∃ rs, σ.mapM (fun u ↦ compile G n u X e) = some rs ∧ rs.map Prod.snd = Δ := fun σ ↦
  σ.rec (fun Δ hl _ ↦ by
      obtain rfl : Δ = [] := List.length_eq_zero_iff.mp hl.symm
      exact ⟨[], rfl, rfl⟩)
    fun u σ ih Δ hl hall ↦ by
      rcases Δ with _ | ⟨A, Δ⟩
      · simp at hl
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hall
      obtain ⟨⟨f₀, A₀⟩, hstd, hA⟩ := Option.map_eq_some_iff.mp hall.1
      obtain rfl : A₀ = A := hA
      obtain ⟨f, hf⟩ := compile_retype u _ _ _ hstd X e (hΓ.trans (map_snd_stdEnv Γ).symm)
      obtain ⟨rs, hrs, hsnd⟩ := ih Δ (by simpa using hl) hall.2
      exact ⟨(f, A₀) :: rs, by simp [List.mapM_cons, hf, hrs], by simp [hsnd]⟩

/-- The empty list's arrow at an object. -/
theorem subst_nil_x (a : Tree) : PartialHorn.subst [a] (nil (x 0)) = nil a := by
  simp [nil, subst_op, subst_x]

/-- Construction's arrow at an object. -/
theorem subst_cons_x (a : Tree) : PartialHorn.subst [a] (cons (x 0)) = cons a := by
  simp [cons, subst_op, subst_x]

/-- The list type at an object. -/
theorem subst_list_x (a : Tree) : PartialHorn.subst [a] (list (x 0)) = list a := by
  simp [subst_list, subst_x]

/-- The product of an object with its list type at an object. -/
theorem subst_prod_list_x (a : Tree) :
    PartialHorn.subst [a] (prod (x 0) (list (x 0))) = prod a (list a) := by
  simp [subst_prod, subst_list, subst_x]


/-- A list's results under a partial function are related to it elementwise. -/
theorem forall₂_of_mapM {α β : Type} {f : α → Option β} (l : List α) :
    ∀ {rs : List β}, l.mapM f = some rs → List.Forall₂ (fun a r ↦ f a = some r) l rs :=
  l.rec (motive := fun l ↦ ∀ {rs : List β}, l.mapM f = some rs →
      List.Forall₂ (fun a r ↦ f a = some r) l rs) (fun h ↦ by
      obtain rfl : [] = _ := by simpa using h
      exact .nil)
    fun a l ih rs h ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at h
      obtain ⟨r, hr, rs₀, hrs₀, rfl⟩ := h
      exact .cons hr (ih hrs₀)

/-- A relation on a list's elements paired with one context is a relation in that context. -/
theorem forall₂_zip_const {R : List Tree → Term → Term → Prop} {Γ : List Tree} (ts : List Term) :
    ∀ {ts' : List Term}, List.Forall₂ (fun (p : List Tree × Term) u ↦ R p.1 p.2 u)
      ((ts.map fun _ ↦ Γ).zip ts) ts' → List.Forall₂ (R Γ) ts ts' :=
  ts.rec (motive := fun ts ↦ ∀ {ts' : List Term},
      List.Forall₂ (fun (p : List Tree × Term) u ↦ R p.1 p.2 u) ((ts.map fun _ ↦ Γ).zip ts) ts' →
        List.Forall₂ (R Γ) ts ts') (fun h ↦ by
      obtain rfl := List.forall₂_nil_left_iff.mp h
      exact .nil)
    fun t ts ih ts' h ↦ by
      rcases h with _ | ⟨h₁, h₂⟩
      exact .cons h₁ (ih h₂)


/-- Zero compiles to its arrow after the arrow to the terminal object. -/
theorem compile_zeroT {G : Globals} {n kz : ℕ} (hk : G.prims[kz]? = some zeroPrim) (X : Tree)
    (e : List (Tree × Tree)) :
    compile G n (Term.arr kz [] Term.star) X e = some (comp zeroN (bang X), nat) :=
  compile_arr_iff.mpr ⟨Term.star, rfl, zeroPrim, hk, bang X,
    compile_star_iff.mpr ⟨rfl, by simp [zeroPrim, subst_one]⟩, rfl, rfl,
    by simp [zeroPrim, zeroN, subst_const, subst_nat]⟩

/-- The successor of a number compiles to the successor after its arrow. -/
theorem compile_succT {G : Globals} {n ks : ℕ} (hk : G.prims[ks]? = some succPrim) {c : Term}
    {X g : Tree} {e : List (Tree × Tree)} (hc : compile G n c X e = some (g, nat)) :
    compile G n (Term.arr ks [] c) X e = some (comp succ g, nat) :=
  compile_arr_iff.mpr ⟨c, rfl, succPrim, hk, g, by simpa [succPrim, subst_nat] using hc, rfl, rfl,
    by simp [succPrim, succ, subst_const, subst_nat]⟩

/-- The empty list compiles to its arrow after the arrow to the terminal object. -/
theorem compile_nilT {G : Globals} {n kn : ℕ} (hk : G.prims[kn]? = some nilPrim) {a : Tree}
    (ha : IsTy n a = true) (X : Tree) (e : List (Tree × Tree)) :
    compile G n (Term.arr kn [a] Term.star) X e = some (comp (nil a) (bang X), list a) :=
  compile_arr_iff.mpr ⟨Term.star, rfl, nilPrim, hk, bang X,
    compile_star_iff.mpr ⟨rfl, by simp [nilPrim, subst_one]⟩, rfl, by simp [ha],
    by rw [show nilPrim.arrow = nil (x 0) from rfl, subst_nil_x,
      show nilPrim.cod = list (x 0) from rfl, subst_list_x]⟩

/-- A construction compiles to construction after its argument's arrow. -/
theorem compile_consT {G : Globals} {n kc : ℕ} (hk : G.prims[kc]? = some consPrim) {a : Tree}
    (ha : IsTy n a = true) {c : Term} {X g : Tree} {e : List (Tree × Tree)}
    (hc : compile G n c X e = some (g, prod a (list a))) :
    compile G n (Term.arr kc [a] c) X e = some (comp (cons a) g, list a) :=
  compile_arr_iff.mpr ⟨c, rfl, consPrim, hk, g,
    by rw [show consPrim.dom = prod (x 0) (list (x 0)) from rfl, subst_prod_list_x]; exact hc,
    rfl, by simp [ha], by rw [show consPrim.arrow = cons (x 0) from rfl, subst_cons_x,
      show consPrim.cod = list (x 0) from rfl, subst_list_x]⟩


/-- A relation on a zip, implying one on its second list at elements of the first with a
property, gives the second on the second list. -/
theorem forall₂_zip_imp {α β γ : Type} {P : α → Prop} {R : α × β → γ → Prop}
    {S : β → γ → Prop} (hRS : ∀ a b c, P a → R (a, b) c → S b c) :
    ∀ (l₁ : List α) (l₂ : List β) (l₃ : List γ), l₂.length ≤ l₁.length → (∀ a ∈ l₁, P a) →
      List.Forall₂ R (l₁.zip l₂) l₃ → List.Forall₂ S l₂ l₃ := fun l₁ ↦
  l₁.rec (fun l₂ l₃ hl _ h ↦ by
      obtain rfl : l₂ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
      obtain rfl := List.forall₂_nil_left_iff.mp h
      exact .nil)
    fun a l₁ ih l₂ l₃ hl hP h ↦ by
      rcases l₂ with _ | ⟨b, l₂⟩
      · obtain rfl := List.forall₂_nil_left_iff.mp h
        exact .nil
      rcases h with _ | ⟨h₁, h₂⟩
      exact .cons (hRS a b _ (hP a List.mem_cons_self) h₁)
        (ih l₂ _ (by simpa using hl) (fun a' ha' ↦ hP a' (List.mem_cons_of_mem _ ha')) h₂)


section Arrows

variable (hM : IsModel (ext defs) M)
include hM

/-- Evaluation after the pairing of a currying with an argument is the curried arrow after the
pairing of the identity with the argument. -/
theorem ev_pair_curry {T g X A B : Tree} (hX : IsObj M ρ X) (hA : IsObj M ρ A)
    (hT : Hom M ρ T (prod X A) B) (hg : Hom M ρ g X A) :
    eval M ρ (comp (ev A B) (pair (curry X A T) g)) = eval M ρ (comp T (pair (idt X) g)) := by
  have hc := curry_hom hM hX hA hT
  have hi := idt_hom hM hX
  have hh := pair_hom hM hi hg
  have hfX := fst_hom hM hX hA
  have hsX := snd_hom hM hX hA
  have hP := pair_hom hM (comp_hom hM hfX hc) hsX
  have e₁ : eval M ρ (pair (curry X A T) g) = eval M ρ
      (comp (pair (comp (curry X A T) (fst X A)) (snd X A)) (pair (idt X) g)) :=
    ((pair_comp hM (comp_hom hM hfX hc) hsX hh).trans (eval_op₂_congr 9
      ((comp_assoc hM hh hfX hc).symm.trans ((eval_op₂_congr 3 rfl (fst_pair hM hi hg)).trans
        (comp_idt hM hc))) (snd_pair hM hi hg))).symm
  exact (eval_op₂_congr 3 rfl e₁).trans ((comp_assoc hM hh hP (ev_hom hM hA hT.isObj_cod)).trans
    (eval_op₂_congr 3 (ev_curry hM hX hA hT) rfl))

/-- An environment after the identity has its own values. -/
theorem envEq_precomp_idt {X : Tree} {e : List (Tree × Tree)}
    (he : ∀ p ∈ e, Hom M ρ p.1 X p.2) : EnvEq M ρ (precomp (idt X) e) e := by
  intro i p hp
  simp only [precomp, List.getElem?_map, Option.map_eq_some_iff] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  exact ⟨p₀, hp₀, rfl, (comp_idt hM (he p₀ (List.mem_of_getElem? hp₀))).symm⟩

/-- An environment after a composite has the values of the environment after the first arrow
and then the second. -/
theorem envEq_precomp_comp {X Y Z g h : Tree} {e : List (Tree × Tree)}
    (he : ∀ p ∈ e, Hom M ρ p.1 X p.2) (hg : Hom M ρ g Y X) (hh : Hom M ρ h Z Y) :
    EnvEq M ρ (precomp (comp g h) e) (precomp h (precomp g e)) := by
  intro i p hp
  simp only [precomp, List.getElem?_map, Option.map_eq_some_iff] at hp
  obtain ⟨p₀, hp₀, rfl⟩ := hp
  exact ⟨(comp (comp p₀.1 g) h, p₀.2), by simp [precomp, hp₀], rfl,
    (comp_assoc hM hh hg (he p₀ (List.mem_of_getElem? hp₀))).symm⟩

/-- An extended environment after an arrow into the product has the values of the new variable
at its second component and of the environment after its first. -/
theorem envEq_precomp_extEnv {X a Z h k v : Tree} {e e' : List (Tree × Tree)}
    (hX : IsObj M ρ X) (ha : IsObj M ρ a) (he : ∀ p ∈ e, Hom M ρ p.1 X p.2)
    (hh : Hom M ρ h Z (prod X a)) (hk : eval M ρ (comp (fst X a) h) = eval M ρ k)
    (hv : eval M ρ (comp (snd X a) h) = eval M ρ v) (he' : EnvEq M ρ (precomp k e) e') :
    EnvEq M ρ (precomp h (extEnv X a e)) ((v, a) :: e') := by
  intro i p hp
  rcases i with _ | j
  · obtain rfl : (comp (snd X a) h, a) = p := by simpa [precomp, extEnv] using hp
    exact ⟨(v, a), rfl, rfl, hv.symm⟩
  · simp only [precomp, extEnv, List.map_cons, List.getElem?_cons_succ, List.map_map,
      List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply] at hp
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q, hq, h₂, h₁⟩ := he' j (comp p₀.1 k, p₀.2) (by simp [precomp, hp₀])
    refine ⟨q, by simpa using hq, h₂, h₁.trans ?_⟩
    exact (eval_op₂_congr 3 rfl hk.symm).trans
      (comp_assoc hM hh (fst_hom hM hX ha) (he p₀ (List.mem_of_getElem? hp₀)))

end Arrows

end Environments

section Rewriting

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}

variable (M ρ) in
/-- A rewriting in a context is sound: in every environment of arrows of the context's types, a
term that compiles rewrites to a term of its type whose arrow has its arrow's value. -/
def RwSound (G : Globals) (n : ℕ) (Γ : List Tree) (t t' : Term) : Prop :=
  ∀ (X : Tree) (e : List (Tree × Tree)), EnvHom M ρ n X e → e.map Prod.snd = Γ →
    ∀ r, compile G n t X e = some r → ∃ r', compile G n t' X e = some r' ∧ ResEq M ρ r r'

variable (M ρ) in
/-- An equation in a context is sound: in every environment of arrows of the context's types,
its sides, where both compile, have one type and arrows of one value. -/
def EqSound (G : Globals) (n : ℕ) (Γ : List Tree) (t u : Term) : Prop :=
  ∀ (X : Tree) (e : List (Tree × Tree)), EnvHom M ρ n X e → e.map Prod.snd = Γ →
    ∀ r r', compile G n t X e = some r → compile G n u X e = some r' → ResEq M ρ r r'

variable (M) in
/-- A theorem is valid: its sides compile in its context's environment of projections to arrows
of one type, which, at every assignment of objects to its object variables, are arrows from the
context's product with one value. -/
def Thm.Valid (G : Globals) (a : Thm) : Prop :=
  a.ctx.all (IsTy a.arity) = true ∧ ∃ f g A,
    compile G a.arity a.lhs (ctxObj a.ctx) (stdEnv a.ctx) = some (f, A) ∧
    compile G a.arity a.rhs (ctxObj a.ctx) (stdEnv a.ctx) = some (g, A) ∧
    ∀ ρ : List M.Val, ρ.map Sigma.fst = List.replicate a.arity obj →
      Hom M ρ f (ctxObj a.ctx) A ∧ eval M ρ f = eval M ρ g

variable (M) in
/-- Each definition's body compiles in its parameters' environment to its value's type and an
arrow whose instance at types has the value of the definition's operation at them. -/
def DefnsOk (G : Globals) : Prop :=
  ∀ (k : ℕ) (d : Defn), G.defs[k]? = some d →
    ∃ F, compile G d.arity d.body (ctxObj d.params) (stdEnv d.params) = some (F, d.type) ∧
      ∀ (m : ℕ) (ρ : List M.Val) (θ : List Tree), ρ.map Sigma.fst = List.replicate m obj →
        θ.length = d.arity → θ.all (IsTy m) = true →
        eval M ρ (op (G.base + k) θ) = eval M ρ (PartialHorn.subst θ F)

/-- The identity rewriting is sound. -/
theorem RwSound.refl {G : Globals} {n : ℕ} (Γ : List Tree) (t : Term) : RwSound M ρ G n Γ t t :=
  fun _ _ _ _ r h ↦ ⟨r, h, ResEq.refl r⟩

/-- One sound rewriting after another is sound. -/
theorem RwSound.trans {G : Globals} {n : ℕ} {Γ : List Tree} {t t' t'' : Term}
    (h₁ : RwSound M ρ G n Γ t t') (h₂ : RwSound M ρ G n Γ t' t'') : RwSound M ρ G n Γ t t'' :=
  fun X e he hΓ r h ↦ by
    obtain ⟨r', h', hr'⟩ := h₁ X e he hΓ r h
    obtain ⟨r'', h'', hr''⟩ := h₂ X e he hΓ r' h'
    exact ⟨r'', h'', hr'.trans hr''⟩

/-- An equation whose sides rewrite soundly to one term is sound. -/
theorem EqSound.of_join {G : Globals} {n : ℕ} {Γ : List Tree} {t u v : Term}
    (h₁ : RwSound M ρ G n Γ t v) (h₂ : RwSound M ρ G n Γ u v) : EqSound M ρ G n Γ t u :=
  fun X e he hΓ r r' ht hu ↦ by
    obtain ⟨q, hq, hrq⟩ := h₁ X e he hΓ r ht
    obtain ⟨q', hq', hrq'⟩ := h₂ X e he hΓ r' hu
    obtain rfl : q = q' := Option.some_inj.mp (hq.symm.trans hq')
    exact hrq.trans hrq'.symm

/-- The checker at a node is its step at the node's children and their results. -/
theorem check_node (G : Globals) (E : Array Thm) (n : ℕ) (l : Rule) (cs : List Deriv) :
    check G E n (RoseTree.node l cs) = checkStep G E n l (cs.map fun c ↦ (c, check G E n c)) :=
  RoseTree.para_node _ l cs

variable (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF) {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
include hM hG hρ hps hds

/-- A term that compiles in an environment of arrows compiles in every environment of the values
of the first's after an arrow, to its arrow after the arrow. -/
theorem compile_precomp {s : Term} {Y X h : Tree} {e e' : List (Tree × Tree)} {r : Tree × Tree}
    (hs : compile G n s Y e = some r) (he : EnvHom M ρ n Y e) (hh : Hom M ρ h X Y)
    (he' : EnvEq M ρ (precomp h e) e') :
    ∃ r', compile G n s X e' = some r' ∧ ResEq M ρ (comp r.1 h, r.2) r' := by
  obtain ⟨r₁, h₁, hr₁⟩ := compile_comp hM hG hρ hps hds s Y e r hs he X h hh
  obtain ⟨r₂, h₂, hr₂⟩ := compile_envEq s X _ r₁ h₁ e' he'
  exact ⟨r₂, h₂, hr₁.trans hr₂⟩

/-- A term that compiles in a context's environment of projections compiles in every environment
of arrows of the context's types, to its arrow after their tuple. -/
theorem compile_of_stdEnv {Γ : List Tree} {s : Term} {r : Tree × Tree}
    (h : compile G n s (ctxObj Γ) (stdEnv Γ) = some r) {X : Tree} {e : List (Tree × Tree)}
    (he : EnvHom M ρ n X e) (hΓ : e.map Prod.snd = Γ) :
    ∃ r', compile G n s X e = some r' ∧
      ResEq M ρ (comp r.1 (tuple X (e.map Prod.fst)), r.2) r' := by
  subst hΓ
  have hΓ : (e.map Prod.snd).all (IsTy n) = true := by
    rw [List.all_map, List.all_eq_true]
    exact fun p hp ↦ (he.2 p hp).2
  exact compile_precomp hM hG hρ hps hds h (stdEnv_hom hM hρ _ hΓ)
    (tuple_hom hM he.1 e fun p hp ↦ (he.2 p hp).1) (proj_tuple hM hρ he.1 e he.2)

/-- A term that compiles in the empty environment compiles in every environment of arrows, to its
arrow after the arrow to the terminal object. -/
theorem compile_closed {s : Term} {r : Tree × Tree} (h : compile G n s one [] = some r)
    {X : Tree} {e : List (Tree × Tree)} (he : EnvHom M ρ n X e) :
    ∃ r', compile G n s X e = some r' ∧ ResEq M ρ (comp r.1 (bang X), r.2) r' :=
  compile_precomp hM hG hρ hps hds h ⟨isObj_one hM, by simp⟩ (bang_hom hM he.1)
    fun i p hp ↦ by simp [precomp] at hp

/-- β is sound: the application of an abstraction is its body with the argument substituted. -/
theorem beta_sound (Γ : List Tree) (a : Tree) (b u : Term) :
    RwSound M ρ G n Γ (Term.app (Term.lam a b) u) (Term.subst b (instVar u)) := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨f, u', hfu, F, A, B, hf, g, hu, rfl⟩ := compile_app_iff.mp h
  simp only [List.cons.injEq, and_true] at hfu
  obtain ⟨rfl, rfl⟩ := hfu
  obtain ⟨b', T, B', hb', hat, hb, hFT⟩ := compile_lam_iff.mp hf
  simp only [List.cons.injEq, and_true] at hb'
  subst hb'
  simp only [Prod.mk.injEq] at hFT
  obtain ⟨rfl, hAB⟩ := hFT
  obtain ⟨rfl, rfl⟩ := exp_inj hAB
  have hA := isObj_of_isTy hM hρ a hat
  have hT := (hty b _ _ _ hb (he.ext hM hA hat)).1
  have hg := (hty u X e _ hu he).1
  have hi := idt_hom hM he.1
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hb (he.ext hM hA hat)
    (pair_hom hM hi hg) (envEq_precomp_extEnv hM he.1 hA (fun p hp ↦ (he.2 p hp).1)
      (pair_hom hM hi hg) (fst_pair hM hi hg) (snd_pair hM hi hg)
      (envEq_precomp_idt hM fun p hp ↦ (he.2 p hp).1))
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds b X ((g, a) :: e) r₁ h₁ e (instVar u) he
    fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (g, a) = p := by simpa using hp
        exact ⟨(g, a), hu, ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
  exact ⟨r₂, h₂, (show ResEq M ρ (comp (ev a B') (pair (curry X a T) g), B')
      (comp T (pair (idt X) g), B') from
    ⟨rfl, (ev_pair_curry hM he.1 hA hT hg).symm⟩).trans (hr₁.trans hr₂)⟩

/-- The first component of a pair is its first term. -/
theorem fstPair_sound (Γ : List Tree) (a b : Term) :
    RwSound M ρ G n Γ (Term.fst (Term.pair a b)) a := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨p, f, A, B, hp, hc, rfl⟩ := compile_fst_iff.mp h
  simp only [List.cons.injEq, and_true] at hp
  subst hp
  obtain ⟨a', b', fa, A', fb, B', hab, ha, hb, hpair⟩ := compile_pair_iff.mp hc
  simp only [List.cons.injEq, and_true] at hab
  obtain ⟨rfl, rfl⟩ := hab
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, hAB⟩ := hpair
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  exact ⟨_, ha, rfl, (fst_pair hM (hty _ _ _ _ ha he).1 (hty _ _ _ _ hb he).1).symm⟩

/-- The second component of a pair is its second term. -/
theorem sndPair_sound (Γ : List Tree) (a b : Term) :
    RwSound M ρ G n Γ (Term.snd (Term.pair a b)) b := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨p, f, A, B, hp, hc, rfl⟩ := compile_snd_iff.mp h
  simp only [List.cons.injEq, and_true] at hp
  subst hp
  obtain ⟨a', b', fa, A', fb, B', hab, ha, hb, hpair⟩ := compile_pair_iff.mp hc
  simp only [List.cons.injEq, and_true] at hab
  obtain ⟨rfl, rfl⟩ := hab
  simp only [Prod.mk.injEq] at hpair
  obtain ⟨rfl, hAB⟩ := hpair
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  exact ⟨_, hb, rfl, (snd_pair hM (hty _ _ _ _ ha he).1 (hty _ _ _ _ hb he).1).symm⟩

/-- The pair of a term's components is the term. -/
theorem pairEta_sound (Γ : List Tree) (p : Term) :
    RwSound M ρ G n Γ (Term.pair (Term.fst p) (Term.snd p)) p := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨x, y, f₁, A, f₂, B, hxy, hx, hy, rfl⟩ := compile_pair_iff.mp h
  simp only [List.cons.injEq, and_true] at hxy
  obtain ⟨rfl, rfl⟩ := hxy
  obtain ⟨p₁, f, A₁, B₁, hp₁, hf, hr₁⟩ := compile_fst_iff.mp hx
  obtain ⟨p₂, f', A₂, B₂, hp₂, hf', hr₂⟩ := compile_snd_iff.mp hy
  simp only [List.cons.injEq, and_true] at hp₁ hp₂
  subst hp₁ hp₂
  rw [hf] at hf'
  simp only [Option.some.injEq, Prod.mk.injEq] at hf' hr₁ hr₂
  obtain ⟨rfl, hAB⟩ := hf'
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  obtain ⟨rfl, rfl⟩ := hr₁
  obtain ⟨rfl, rfl⟩ := hr₂
  obtain ⟨hfh, hPt⟩ := hty _ _ _ _ hf he
  simp only [isTy_prod, Bool.and_eq_true] at hPt
  exact ⟨_, hf, rfl, (pair_eta hM (isObj_of_isTy hM hρ _ hPt.1) (isObj_of_isTy hM hρ _ hPt.2)
    hfh).symm⟩

/-- A term of the terminal type is its element. -/
theorem unitEta_sound {Γ : List Tree} {t : Term} (h₁ : typeIn G n Γ t = some one) :
    RwSound M ρ G n Γ t Term.star := by
  intro X e he hΓ r h
  obtain ⟨⟨f₀, A₀⟩, hstd, rfl⟩ := Option.map_eq_some_iff.mp h₁
  obtain ⟨f, hf⟩ := compile_retype t _ _ _ hstd X e (hΓ.trans (map_snd_stdEnv Γ).symm)
  obtain rfl := Option.some_inj.mp (h.symm.trans hf)
  exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl,
    (bang_unique hM (compile_hom hM hG hρ hps hds t X e _ hf he).1).symm⟩

/-- The unfolding of a definition is sound: its application is its body at the objects and the
arguments. -/
theorem delta_sound (hδ : DefnsOk M G) {k : ℕ} {d : Defn} (hd : G.defs[k]? = some d)
    (Γ θ : List Tree) (args : List Term) :
    RwSound M ρ G n Γ (Term.defn k θ args)
      (Term.subst (Term.osubst θ d.body) (Term.substList args)) := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨d', rs, hd', hrs, hl, hθ, hsnd, rfl⟩ := compile_defn_iff.mp h
  obtain rfl : d' = d := Option.some_inj.mp (hd'.symm.trans hd)
  obtain ⟨F, hF, hop⟩ := hδ k d' hd
  have hF' := compile_osubst hG hl hθ d'.body _ _ _ hF
  rw [subst_ctxObj, map_substPair_stdEnv] at hF'
  have hrs' : EnvHom M ρ n X rs := ⟨he.1, fun q hq ↦ by
    obtain ⟨c, -, hcq⟩ := exists_of_mapM hrs hq
    exact hty c X e q hcq he⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_of_stdEnv hM hG hρ hps hds hF' hrs' hsnd
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds _ X rs r₁ h₁ e (Term.substList args) he
    fun i p hp ↦ by
      obtain ⟨c, hc, hcp⟩ := getElem?_of_mapM_eq hrs hp
      exact ⟨p, by simpa [Term.substList, hc] using hcp, ResEq.refl p⟩
  exact ⟨r₂, h₂, (show ResEq M ρ
      (comp (op (G.base + k) θ) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d'.type)
      (comp (PartialHorn.subst θ F) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d'.type) from
    ⟨rfl, eval_op₂_congr 3 (hop n ρ θ hρ hl hθ).symm rfl⟩).trans (hr₁.trans hr₂)⟩

/-- The fold of zero is the start. -/
theorem natZero_sound {kz : ℕ} (hk : G.prims[kz]? = some zeroPrim) (Γ : List Tree)
    (z s : Term) : RwSound M ρ G n Γ (Term.natRec z s (Term.arr kz [] Term.star)) z := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, z', C, hzc, s', hsc, m', hm, rfl⟩ := compile_natRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = zeroPrim := Option.some_inj.mp (hp.symm.trans hk)
  obtain ⟨-, hgb⟩ := compile_star_iff.mp hg
  simp only [Prod.mk.injEq] at hgb hm'
  obtain ⟨rfl, -⟩ := hgb
  obtain ⟨rfl, -⟩ := hm'
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hρ C hCt
  have hs' := (hty _ _ _ _ hsc ⟨hC, by simpa using ⟨idt_hom hM hC, hCt⟩⟩).1
  obtain ⟨r', h', hr'⟩ := compile_closed hM hG hρ hps hds hzc he
  refine ⟨r', h', (show ResEq M ρ
      (comp (natRec z' s') (comp (PartialHorn.subst [] zeroN) (bang X)), C)
      (comp z' (bang X), C) from ⟨rfl, ?_⟩).trans hr'⟩
  rw [show PartialHorn.subst [] zeroN = zeroN from subst_const [] 30]
  exact (eval_op₂_congr 3 (natRec_zero hM hz' hs') rfl).symm.trans
    (comp_assoc hM (bang_hom hM he.1) (zeroN_hom hM) (natRec_hom hM hz' hs')).symm

/-- The fold of a successor is the step at the fold. -/
theorem natSucc_sound {ks : ℕ} (hk : G.prims[ks]? = some succPrim) (Γ : List Tree)
    (z s c : Term) :
    RwSound M ρ G n Γ (Term.natRec z s (Term.arr ks [] c))
      (Term.subst s (instVar (Term.natRec z s c))) := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, z', C, hzc, s', hsc, m', hm, rfl⟩ := compile_natRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = succPrim := Option.some_inj.mp (hp.symm.trans hk)
  simp only [Prod.mk.injEq] at hm'
  obtain ⟨rfl, -⟩ := hm'
  rw [show PartialHorn.subst [] succPrim.dom = nat from subst_nat []] at hg
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hρ C hCt
  have hCe : EnvHom M ρ n C [(idt C, C)] := ⟨hC, by simpa using ⟨idt_hom hM hC, hCt⟩⟩
  have hs' := (hty _ _ _ _ hsc hCe).1
  have hg' := (hty _ _ _ _ hg he).1
  have hrec := natRec_hom hM hz' hs'
  have hq := comp_hom hM hg' hrec
  have hN : compile G n (Term.natRec z s c) X e = some (comp (natRec z' s') g, C) :=
    compile_natRec_iff.mpr ⟨z, s, c, rfl, z', C, hzc, s', hsc, g, hg, rfl⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hsc hCe hq
    (e' := [(comp (natRec z' s') g, C)]) fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (idt C) (comp (natRec z' s') g), C) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (idt_comp hM hq).symm⟩
      · simp [precomp] at hp
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds s X _ r₁ h₁ e
    (instVar (Term.natRec z s c)) he fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (natRec z' s') g, C) = p := by simpa using hp
        exact ⟨_, hN, ResEq.refl _⟩
      · simp at hp
  refine ⟨r₂, h₂, (show ResEq M ρ
      (comp (natRec z' s') (comp (PartialHorn.subst [] succ) g), C)
      (comp s' (comp (natRec z' s') g), C) from ⟨rfl, ?_⟩).trans (hr₁.trans hr₂)⟩
  rw [show PartialHorn.subst [] succ = succ from subst_const [] 31]
  exact Eq.symm ((comp_assoc hM hg' (succ_hom hM) hrec).trans
    ((eval_op₂_congr 3 (natRec_succ hM hz' hs') rfl).trans (comp_assoc hM hg' hrec hs').symm))

/-- The fold of the empty list is the start. -/
theorem listNil_sound {kn : ℕ} (hk : G.prims[kn]? = some nilPrim) (Γ : List Tree)
    (z s : Term) (a₀ : Tree) :
    RwSound M ρ G n Γ (Term.listRec z s (Term.arr kn [a₀] Term.star)) z := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, m', A, hm, z', C, hzc, s', hsc, rfl⟩ := compile_listRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨hmh, hLt⟩ := hty _ _ _ _ hm he
  rw [isTy_list] at hLt
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = nilPrim := Option.some_inj.mp (hp.symm.trans hk)
  obtain ⟨-, hgb⟩ := compile_star_iff.mp hg
  simp only [Prod.mk.injEq] at hgb hm'
  obtain ⟨rfl, -⟩ := hgb
  obtain ⟨rfl, hA⟩ := hm'
  obtain rfl : a₀ = A := list_inj ((subst_list_x a₀).symm.trans hA)
  have hA := isObj_of_isTy hM hρ a₀ hLt
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hρ C hCt
  have hs' := (hty _ _ _ _ hsc ⟨isObj_prod hM hA hC, by
    simpa using ⟨⟨snd_hom hM hA hC, hCt⟩, fst_hom hM hA hC, hLt⟩⟩).1
  obtain ⟨r', h', hr'⟩ := compile_closed hM hG hρ hps hds hzc he
  refine ⟨r', h', (show ResEq M ρ
      (comp (listRec a₀ z' s') (comp (PartialHorn.subst [a₀] (nil (x 0))) (bang X)), C)
      (comp z' (bang X), C) from ⟨rfl, ?_⟩).trans hr'⟩
  rw [subst_nil_x]
  exact (eval_op₂_congr 3 (listRec_nil hM hA hz' hs') rfl).symm.trans
    (comp_assoc hM (bang_hom hM he.1) (nil_hom hM hA) (listRec_hom hM hA hz' hs')).symm

/-- The fold of a construction is the step at the element and the fold of the tail. -/
theorem listCons_sound {kc : ℕ} (hk : G.prims[kc]? = some consPrim) (Γ : List Tree)
    (z s : Term) (a₀ : Tree) (hd tl : Term) :
    RwSound M ρ G n Γ (Term.listRec z s (Term.arr kc [a₀] (Term.pair hd tl)))
      (Term.subst s (Term.substList [Term.listRec z s tl, hd])) := by
  intro X e he _ r h
  have hty := compile_hom hM hG hρ hps hds
  obtain ⟨z₁, s₁, m, hcs, m', A, hm, z', C, hzc, s', hsc, rfl⟩ := compile_listRec_iff.mp h
  simp only [List.cons.injEq, and_true] at hcs
  obtain ⟨rfl, rfl, rfl⟩ := hcs
  obtain ⟨-, hLt⟩ := hty _ _ _ _ hm he
  rw [isTy_list] at hLt
  obtain ⟨t₀, ht₀, p, hp, g, hg, -, -, hm'⟩ := compile_arr_iff.mp hm
  simp only [List.cons.injEq, and_true] at ht₀
  subst ht₀
  obtain rfl : p = consPrim := Option.some_inj.mp (hp.symm.trans hk)
  simp only [Prod.mk.injEq] at hm'
  obtain ⟨rfl, hA⟩ := hm'
  obtain rfl : a₀ = A := list_inj ((subst_list_x a₀).symm.trans hA)
  rw [show PartialHorn.subst [a₀] consPrim.dom = prod a₀ (list a₀) from subst_prod_list_x a₀]
    at hg
  obtain ⟨hd', tl', gh, A₁, gt, B₁, hht, hh, htl, hgp⟩ := compile_pair_iff.mp hg
  simp only [List.cons.injEq, and_true] at hht
  obtain ⟨rfl, rfl⟩ := hht
  simp only [Prod.mk.injEq] at hgp
  obtain ⟨rfl, hAB⟩ := hgp
  obtain ⟨rfl, rfl⟩ := prod_inj hAB
  have hA := isObj_of_isTy hM hρ A₁ hLt
  obtain ⟨hz', hCt⟩ := hty _ _ _ _ hzc ⟨isObj_one hM, by simp⟩
  have hC := isObj_of_isTy hM hρ C hCt
  have hse : EnvHom M ρ n (prod A₁ C) [(snd A₁ C, C), (fst A₁ C, A₁)] :=
    ⟨isObj_prod hM hA hC, by simpa using ⟨⟨snd_hom hM hA hC, hCt⟩, fst_hom hM hA hC, hLt⟩⟩
  have hs' := (hty _ _ _ _ hsc hse).1
  have hgh := (hty _ _ _ _ hh he).1
  have hgt := (hty _ _ _ _ htl he).1
  have hlr := listRec_hom hM hA hz' hs'
  have hq := comp_hom hM hgt hlr
  have hk' := pair_hom hM hgh hq
  have hL : compile G n (Term.listRec z s tl) X e = some (comp (listRec A₁ z' s') gt, C) :=
    compile_listRec_iff.mpr ⟨z, s, tl, rfl, gt, A₁, htl, z', C, hzc, s', hsc, rfl⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_precomp hM hG hρ hps hds hsc hse hk'
    (e' := [(comp (listRec A₁ z' s') gt, C), (gh, A₁)]) fun i p hp ↦ by
      rcases i with _ | _ | j
      · obtain rfl : (comp (snd A₁ C) (pair gh (comp (listRec A₁ z' s') gt)), C) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (snd_pair hM hgh hq).symm⟩
      · obtain rfl : (comp (fst A₁ C) (pair gh (comp (listRec A₁ z' s') gt)), A₁) = p := by
          simpa [precomp] using hp
        exact ⟨_, rfl, rfl, (fst_pair hM hgh hq).symm⟩
      · simp [precomp] at hp
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds s X _ r₁ h₁ e
    (Term.substList [Term.listRec z s tl, hd]) he fun i p hp ↦ by
      rcases i with _ | _ | j
      · obtain rfl : (comp (listRec A₁ z' s') gt, C) = p := by simpa using hp
        exact ⟨_, by simpa [Term.substList] using hL, ResEq.refl _⟩
      · obtain rfl : (gh, A₁) = p := by simpa using hp
        exact ⟨_, by simpa [Term.substList] using hh, ResEq.refl _⟩
      · simp at hp
  refine ⟨r₂, h₂, (show ResEq M ρ
      (comp (listRec A₁ z' s') (comp (PartialHorn.subst [A₁] (cons (x 0))) (pair gh gt)), C)
      (comp s' (pair gh (comp (listRec A₁ z' s') gt)), C) from ⟨rfl, ?_⟩).trans
    (hr₁.trans hr₂)⟩
  rw [subst_cons_x]
  have hL' := isObj_list hM hA
  have hpg := pair_hom hM hgh hgt
  have hpm := pair_hom hM (fst_hom hM hA hL') (comp_hom hM (snd_hom hM hA hL') hlr)
  refine Eq.symm ((comp_assoc hM hpg (cons_hom hM hA) hlr).trans
    ((eval_op₂_congr 3 (listRec_cons hM hA hz' hs') rfl).trans
      ((comp_assoc hM hpg hpm hs').symm.trans (eval_op₂_congr 3 rfl ?_))))
  exact (pair_comp hM (fst_hom hM hA hL') (comp_hom hM (snd_hom hM hA hL') hlr) hpg).trans
    (eval_op₂_congr 9 (fst_pair hM hgh hgt) ((comp_assoc hM hpg (snd_hom hM hA hL') hlr).symm.trans
      (eval_op₂_congr 3 rfl (snd_pair hM hgh hgt))))

/-- A side of a theorem, at objects and at terms of the instances of its context's types,
compiles to its arrow's instance after the terms' tuple. -/
theorem compile_thm_side {m : ℕ} {Δ : List Tree} {s : Term} {F A : Tree}
    (hs : compile G m s (ctxObj Δ) (stdEnv Δ) = some (F, A)) {θ : List Tree}
    (hl : θ.length = m) (hθ : θ.all (IsTy n) = true) {σ : List Term} {X : Tree}
    {e rs : List (Tree × Tree)} (he : EnvHom M ρ n X e)
    (hrs : σ.mapM (fun u ↦ compile G n u X e) = some rs)
    (hsnd : rs.map Prod.snd = Δ.map (PartialHorn.subst θ)) :
    ∃ r', compile G n (Term.subst (Term.osubst θ s) (Term.substList σ)) X e = some r' ∧
      ResEq M ρ (comp (PartialHorn.subst θ F) (tuple X (rs.map Prod.fst)),
        PartialHorn.subst θ A) r' := by
  have hty := compile_hom hM hG hρ hps hds
  have hs' := compile_osubst hG hl hθ s _ _ _ hs
  rw [subst_ctxObj, map_substPair_stdEnv] at hs'
  have hrs' : EnvHom M ρ n X rs := ⟨he.1, fun q hq ↦ by
    obtain ⟨c, -, hcq⟩ := exists_of_mapM hrs hq
    exact hty c X e q hcq he⟩
  obtain ⟨r₁, h₁, hr₁⟩ := compile_of_stdEnv hM hG hρ hps hds hs' hrs' hsnd
  obtain ⟨r₂, h₂, hr₂⟩ := compile_subst hM hG hρ hps hds _ X rs r₁ h₁ e (Term.substList σ) he
    fun i p hp ↦ by
      obtain ⟨c, hc, hcp⟩ := getElem?_of_mapM_eq hrs hp
      exact ⟨p, by simpa [Term.substList, hc] using hcp, ResEq.refl p⟩
  exact ⟨r₂, h₂, hr₁.trans hr₂⟩

omit hG hps hds in
/-- The instances at types of a valid theorem's arrows have one value. -/
theorem Thm.Valid.eval_subst {a : Thm} (ha : a.Valid M G) {f g A : Tree}
    (hf : compile G a.arity a.lhs (ctxObj a.ctx) (stdEnv a.ctx) = some (f, A))
    (hg : compile G a.arity a.rhs (ctxObj a.ctx) (stdEnv a.ctx) = some (g, A))
    {θ : List Tree} (hl : θ.length = a.arity) (hθ : θ.all (IsTy n) = true) :
    eval M ρ (PartialHorn.subst θ f) = eval M ρ (PartialHorn.subst θ g) := by
  obtain ⟨-, f', g', A', hf', hg', hv⟩ := ha
  rw [hf] at hf'
  rw [hg] at hg'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hf')
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some_inj.mp hg')
  obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hρ θ hθ
  rw [hl] at hws
  obtain ⟨hfh, hfg⟩ := hv ws hws
  obtain ⟨w, hw, -⟩ := hfh.exists_eval
  have hlen : ws.length = θ.length := by simpa [hl] using congrArg List.length hws
  have hsf := scoped_of_eval f hw
  have hsg := scoped_of_eval g (hfg ▸ hw)
  rw [hlen] at hsf hsg
  rw [PartialHorn.eval_subst hθw f hsf, PartialHorn.eval_subst hθw g hsg, hfg]


/-- An instance of a valid theorem, from either side to the other, is sound: its sides at objects
and at terms of the instances of its context's types. -/
theorem thm_inst_sound {a : Thm} (ha : a.Valid M G) {Γ θ : List Tree} {σ : List Term}
    (hl : θ.length = a.arity) (hθ : θ.all (IsTy n) = true) (hσl : σ.length = a.ctx.length)
    (hall : (σ.zip (a.ctx.map (PartialHorn.subst θ))).all
      (fun x ↦ decide (typeIn G n Γ x.1 = some x.2)) = true)
    {s s' : Term} (hs : s = a.lhs ∧ s' = a.rhs ∨ s = a.rhs ∧ s' = a.lhs) :
    RwSound M ρ G n Γ (Term.subst (Term.osubst θ s) (Term.substList σ))
      (Term.subst (Term.osubst θ s') (Term.substList σ)) := by
  intro X e he hΓ r h
  obtain ⟨-, f, g, A, hf, hg, -⟩ := id ha
  obtain ⟨rs, hrs, hsnd⟩ := mapM_compile_of_typeIn hΓ σ _ (by simp [hσl]) hall
  obtain ⟨r₁, h₁, hr₁⟩ := compile_thm_side hM hG hρ hps hds hf hl hθ he hrs hsnd
  obtain ⟨r₂, h₂, hr₂⟩ := compile_thm_side hM hG hρ hps hds hg hl hθ he hrs hsnd
  have hPQ : ResEq M ρ (comp (PartialHorn.subst θ f) (tuple X (rs.map Prod.fst)),
      PartialHorn.subst θ A) (comp (PartialHorn.subst θ g) (tuple X (rs.map Prod.fst)),
      PartialHorn.subst θ A) :=
    ⟨rfl, eval_op₂_congr 3 (Thm.Valid.eval_subst hM hρ ha hf hg hl hθ).symm rfl⟩
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain rfl := Option.some_inj.mp (h.symm.trans h₁)
    exact ⟨r₂, h₂, hr₁.symm.trans (hPQ.trans hr₂)⟩
  · obtain rfl := Option.some_inj.mp (h.symm.trans h₂)
    exact ⟨r₁, h₁, hr₂.symm.trans (hPQ.symm.trans hr₁)⟩

/-- Each equation of the language applied at a term's root is sound, with sound unfoldings and
valid earlier theorems. -/
theorem rootStep_sound (hδ : DefnsOk M G) {E : Array Thm}
    (hE : ∀ (j : ℕ) (a : Thm), E[j]? = some a → a.Valid M G) {Γ : List Tree} {l : Rule}
    {t t' : Term}
    (h : rootStep G E n Γ l t = some t') : RwSound M ρ G n Γ t t' := by
  obtain ⟨l₀, cs, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
    ⟨_, _, (RoseTree.node_label_children t).symm⟩
  cases l with
  | beta =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨f, _ | ⟨u, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, f = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children f).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨b, _ | ⟨w, cs⟩⟩ <;> simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact beta_sound hM hG hρ hps hds Γ _ b u
  | fstPair =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨p, _ | ⟨w, cs⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨a, _ | ⟨b, _ | ⟨w, cs⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact fstPair_sound hM hG hρ hps hds Γ _ b
  | sndPair =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨p, _ | ⟨w, cs⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨a, _ | ⟨b, _ | ⟨w, cs⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.some.injEq] at h
    subst h
    exact sndPair_sound hM hG hρ hps hds Γ a _
  | pairEta =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨x₁, _ | ⟨y₁, _ | ⟨w, cs⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, x₁ = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children x₁).symm⟩
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, y₁ = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children y₁).symm⟩
    cases l₁ <;> cases l₂ <;>
      simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;> rcases cs₂ with _ | ⟨q, _ | ⟨w', cs₂⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact pairEta_sound hM hG hρ hps hds Γ p
  | unitEta =>
    simp only [rootStep] at h
    split_ifs at h with h₁
    obtain rfl := Option.some_inj.mp h
    exact unitEta_sound hM hG hρ hps hds h₁
  | delta =>
    cases l₀ <;> simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq,
      Option.map_eq_some_iff] at h
    obtain ⟨d, hd, rfl⟩ := h
    exact delta_sound hM hG hρ hps hds hδ hd Γ _ cs
  | natZero kz =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, θ⟩ <;> rcases cs₁ with _ | ⟨c, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk, rfl⟩, rfl⟩ := h
    exact natZero_sound hM hG hρ hps hds hk Γ z s
  | natSucc ks =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, θ⟩ <;> rcases cs₁ with _ | ⟨c, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk⟩, rfl⟩ := h
    exact natSucc_sound hM hG hρ hps hds hk Γ z s c
  | listNil kn =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, _ | ⟨b, θ⟩⟩ <;> rcases cs₁ with _ | ⟨c, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk, rfl⟩, rfl⟩ := h
    exact listNil_sound hM hG hρ hps hds hk Γ z s a
  | listCons kc =>
    cases l₀ <;>
      simp only [rootStep, RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨w, cs⟩⟩⟩⟩ <;> simp only [reduceCtorEq] at h
    obtain ⟨l₁, cs₁, rfl⟩ : ∃ l cs, m = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children m).symm⟩
    cases l₁ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rename_i k θ
    rcases θ with _ | ⟨a, _ | ⟨b, θ⟩⟩ <;> rcases cs₁ with _ | ⟨p, _ | ⟨w, cs₁⟩⟩ <;>
      simp only [reduceCtorEq] at h
    obtain ⟨l₂, cs₂, rfl⟩ : ∃ l cs, p = RoseTree.node l cs :=
      ⟨_, _, (RoseTree.node_label_children p).symm⟩
    cases l₂ <;> simp only [RoseTree.label_node, RoseTree.children_node, reduceCtorEq] at h
    rcases cs₂ with _ | ⟨hd, _ | ⟨tl, _ | ⟨w, cs₂⟩⟩⟩ <;>
      simp only [reduceCtorEq, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨⟨rfl, hk⟩, rfl⟩ := h
    exact listCons_sound hM hG hρ hps hds hk Γ z s a hd tl
  | thm j θ σ flip =>
    cases flip <;> simp only [rootStep, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h <;> obtain ⟨a, ha, h⟩ := h <;> split_ifs at h with hc <;>
      obtain ⟨hl, hθ, hσl, hall, ht⟩ := hc <;> obtain rfl := Option.some_inj.mp h <;> rw [ht]
    · exact thm_inst_sound hM hG hρ hps hds (hE j a ha) hl hθ hσl hall (.inl ⟨rfl, rfl⟩)
    · exact thm_inst_sound hM hG hρ hps hds (hE j a ha) hl hθ hσl hall (.inr ⟨rfl, rfl⟩)
  | refl | trans | cong | join | natInd | listInd => simp only [rootStep, reduceCtorEq] at h


/-- Congruence is sound: a node whose children rewrite soundly, each in its own context,
rewrites soundly to the node of their rewrites. -/
theorem cong_sound {l : Label} {ts ts' : List Term} {Γ : List Tree} {Γs : List (List Tree)}
    (hΓs : childCtxs G n l ts Γ = some Γs)
    (hR : List.Forall₂ (fun (p : List Tree × Term) u ↦ RwSound M ρ G n p.1 p.2 u)
      (Γs.zip ts) ts') :
    RwSound M ρ G n Γ (RoseTree.node l ts) (RoseTree.node l ts') := by
  intro X e he hΓ r h
  have hty := compile_hom hM hG hρ hps hds
  have hobj := isObj_of_isTy hM hρ
  have he₁ : EnvHom M ρ n one [] := ⟨isObj_one hM, by simp⟩
  cases l with
  | var i =>
    obtain ⟨rfl, -⟩ := compile_var_iff.mp h
    obtain rfl : ts' = [] := by simpa using hR
    exact ⟨r, h, ResEq.refl r⟩
  | star =>
    obtain ⟨rfl, -⟩ := compile_star_iff.mp h
    obtain rfl : ts' = [] := by simpa using hR
    exact ⟨r, h, ResEq.refl r⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    obtain rfl : Γs = [Γ, Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := h₁ X e he hΓ _ ht
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := h₂ X e he hΓ _ hu
    exact ⟨_, compile_pair_iff.mpr ⟨_, _, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      eval_op₂_congr 9 hf hg⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    obtain rfl : Γs = [Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := h₁ X e he hΓ _ ht
    exact ⟨_, compile_fst_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    obtain rfl : Γs = [Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := h₁ X e he hΓ _ ht
    exact ⟨_, compile_snd_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | lam a =>
    obtain ⟨b, f, B, rfl, hat, hb, rfl⟩ := compile_lam_iff.mp h
    obtain rfl : Γs = [a :: Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨f', B'⟩, hb', rfl, hf⟩ := h₁ _ _ (he.ext hM (hobj a hat) hat)
      (by simp [extEnv, hΓ, Function.comp_def]) _ hb
    exact ⟨_, compile_lam_iff.mpr ⟨_, f', B', rfl, hat, hb', rfl⟩, rfl,
      eval_op₃_congr 24 rfl rfl hf⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    obtain rfl : Γs = [Γ, Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := h₁ X e he hΓ _ ht
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := h₂ X e he hΓ _ hu
    exact ⟨_, compile_app_iff.mpr ⟨_, _, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    obtain rfl : Γs = [Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | _⟩
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := h₁ X e he hΓ _ ht
    exact ⟨_, compile_arr_iff.mpr ⟨_, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hg⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    have hc : typeIn G n [] z = some c := by
      change (compile G n z one []).map Prod.snd = some c
      rw [hz]
      rfl
    obtain rfl : Γs = [[], [c], Γ] := by
      change (typeIn G n [] z).bind (fun c ↦ some [[], [c], Γ]) = some Γs at hΓs
      rw [hc, Option.bind_some] at hΓs
      exact (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
    obtain ⟨hz'h, hct⟩ := hty _ _ _ _ hz he₁
    have hC := hobj c hct
    obtain ⟨⟨z'', c'⟩, hz', hzc, hzv⟩ := h₁ one [] he₁ rfl _ hz
    obtain rfl : c = c' := hzc.symm
    obtain ⟨⟨s'', c''⟩, hs', hsc, hsv⟩ := h₂ c [(idt c, c)]
      ⟨hC, by simpa using ⟨idt_hom hM hC, hct⟩⟩ rfl _ hs
    obtain rfl : c = c'' := hsc.symm
    obtain ⟨⟨m'', N⟩, hm', rfl, hmv⟩ := h₃ X e he hΓ _ hm
    exact ⟨_, compile_natRec_iff.mpr ⟨_, _, _, rfl, z'', c, hz', s'', hs', m'', hm', rfl⟩, rfl,
      eval_op₂_congr 3 (eval_op₂_congr 32 hzv hsv) hmv⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', A, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    have hc : typeIn G n [] z = some c := by
      change (compile G n z one []).map Prod.snd = some c
      rw [hz]
      rfl
    obtain ⟨f₀, hf₀⟩ := compile_retype m X e _ hm (ctxObj Γ) (stdEnv Γ)
      (by rw [map_snd_stdEnv, hΓ])
    have hmt : typeIn G n Γ m = some (list A) := by
      change (compile G n m (ctxObj Γ) (stdEnv Γ)).map Prod.snd = some (list A)
      rw [hf₀]
      rfl
    obtain rfl : Γs = [[], [c, A], Γ] := by
      change (typeIn G n [] z).bind (fun c ↦ ((typeIn G n Γ m).bind listPart).bind
        fun a ↦ some [[], [c, a], Γ]) = some Γs at hΓs
      rw [hc, Option.bind_some, hmt, Option.bind_some, listPart_eq_some.mpr rfl,
        Option.bind_some] at hΓs
      exact (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | ⟨h₃, _ | _⟩⟩⟩
    obtain ⟨-, hLt⟩ := hty _ _ _ _ hm he
    rw [isTy_list] at hLt
    obtain ⟨-, hct⟩ := hty _ _ _ _ hz he₁
    have hA := hobj A hLt
    have hC := hobj c hct
    obtain ⟨⟨z'', c'⟩, hz', hzc, hzv⟩ := h₁ one [] he₁ rfl _ hz
    obtain rfl : c = c' := hzc.symm
    obtain ⟨⟨s'', c''⟩, hs', hsc, hsv⟩ := h₂ (prod A c) [(snd A c, c), (fst A c, A)]
      ⟨isObj_prod hM hA hC, by simpa using ⟨⟨snd_hom hM hA hC, hct⟩, fst_hom hM hA hC, hLt⟩⟩
      rfl _ hs
    obtain rfl : c = c'' := hsc.symm
    obtain ⟨⟨m'', N⟩, hm', hmN, hmv⟩ := h₃ X e he hΓ _ hm
    obtain rfl : list A = N := hmN.symm
    exact ⟨_, compile_listRec_iff.mpr ⟨_, _, _, rfl, m'', A, hm', z'', c, hz', s'', hs', rfl⟩,
      rfl, eval_op₂_congr 3 (eval_op₃_congr 36 rfl hzv hsv) hmv⟩
  | roseRec c =>
    obtain ⟨s, m, s', m', rfl, hct, hs, hm, rfl⟩ := compile_roseRec_iff.mp h
    obtain rfl : Γs = [[prod nat (list c)], Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    have hPt : IsTy n (prod nat (list c)) = true := by simp [isTy_prod, isTy_list, isTy_nat, hct]
    have hP := hobj _ hPt
    obtain ⟨⟨s'', c'⟩, hs', rfl, hsv⟩ := h₁ _ [(idt (prod nat (list c)), prod nat (list c))]
      ⟨hP, by simpa using ⟨idt_hom hM hP, hPt⟩⟩ rfl _ hs
    obtain ⟨⟨m'', N⟩, hm', rfl, hmv⟩ := h₂ X e he hΓ _ hm
    exact ⟨_, compile_roseRec_iff.mpr ⟨_, _, s'', m'', rfl, hct, hs', hm', rfl⟩, rfl,
      eval_op₂_congr 3 (eval_op₁_congr 39 hsv) hmv⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    obtain rfl : Γs = [Γ, Γ] := (Option.some_inj.mp hΓs).symm
    rcases hR with _ | ⟨h₁, _ | ⟨h₂, _ | _⟩⟩
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := h₁ X e he hΓ _ ht
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := h₂ X e he hΓ _ hu
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hsnd, rfl⟩ := compile_defn_iff.mp h
    obtain rfl : Γs = ts.map fun _ ↦ Γ := (Option.some_inj.mp hΓs).symm
    obtain ⟨rs', hrs', hRR⟩ := mapM_forall₂ (R := ResEq M ρ)
      (fun _ _ r h₁ hr ↦ h₁ X e he hΓ r hr) (forall₂_zip_const ts hR) hrs
    exact ⟨_, compile_defn_iff.mpr ⟨d, rs', hd, hrs', hl, hθ,
      (map_snd_of_forall₂ hRR).trans hsnd, rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_tuple_of_forall₂ X hRR)⟩


/-- Induction on the natural numbers is sound: an equation, in a context of a natural number
variable, whose sides agree at zero and are each, at a successor, a step of their type applied to
their value, holds. -/
theorem natInd_sound {kz ks : ℕ} (hkz : G.prims[kz]? = some zeroPrim)
    (hks : G.prims[ks]? = some succPrim) {Γ' : List Tree} {t u s : Term} {C : Tree}
    (htC : typeIn G n (nat :: Γ') t = some C) (hsC : typeIn G n (C :: Γ') s = some C)
    (p₀ : EqSound M ρ G n Γ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star))))
    (p₁ : EqSound M ρ G n (nat :: Γ') (natSuccAt ks t) (Term.subst s (atVar0 t)))
    (p₂ : EqSound M ρ G n (nat :: Γ') (natSuccAt ks u) (Term.subst s (atVar0 u))) :
    EqSound M ρ G n (nat :: Γ') t u := by
  intro X e he hΓ r r' ht hu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  have he'h : ∀ p ∈ e', Hom M ρ p.1 X p.2 := fun p hp ↦ (he'.2 p hp).1
  have hx₀ : Hom M ρ x₀ X nat := (he.2 _ List.mem_cons_self).1
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he.1
  -- the generic environment, over the product with the natural numbers object
  have hê : EnvHom M ρ n (prod X nat) (extEnv X nat e') := he'.ext hM hN isTy_nat
  have hêΓ : (extEnv X nat e').map Prod.snd = nat :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  -- the sides' type, and their arrows in the generic environment
  obtain ⟨⟨f₀, C₀⟩, htstd, rfl⟩ := Option.map_eq_some_iff.mp htC
  obtain ⟨f₁, hf₁⟩ := compile_retype t _ _ _ htstd X ((x₀, nat) :: e')
    (by simp [map_snd_stdEnv, hΓ'])
  obtain rfl := Option.some_inj.mp (ht.symm.trans hf₁)
  obtain ⟨F, hF⟩ := compile_retype t X _ _ ht (prod X nat) (extEnv X nat e') (by simp [hêΓ, hΓ'])
  obtain ⟨⟨g₁, D⟩, rfl⟩ : ∃ q, r' = q := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ := compile_retype u X _ _ hu (prod X nat) (extEnv X nat e')
    (by simp [hêΓ, hΓ'])
  have hFh := (hty _ _ _ _ hF hê).1
  have hGh := (hty _ _ _ _ hG' hê).1
  obtain ⟨hCt⟩ : IsTy n C₀ = true ∧ True := ⟨(hty _ _ _ _ hF hê).2, trivial⟩
  have hC := isObj_of_isTy hM hρ C₀ hCt
  -- an arrow of the generic environment at an element of the natural numbers object
  have hat : ∀ {h x : Tree} {e'' : List (Tree × Tree)}, Hom M ρ x X nat →
      EnvEq M ρ (precomp (idt X) e') e'' → h = pair (idt X) x →
      EnvEq M ρ (precomp h (extEnv X nat e')) ((x, nat) :: e'') := fun hx he'' hh ↦ by
    subst hh
    exact envEq_precomp_extEnv hM hX hN he'h (pair_hom hM (idt_hom hM hX) hx)
      (fst_pair hM (idt_hom hM hX) hx) (snd_pair hM (idt_hom hM hX) hx) he''
  -- the sides are their generic arrows at the variable
  have hh₀ := pair_hom hM (idt_hom hM hX) hx₀
  obtain ⟨q, hq, hrq⟩ := compile_precomp hM hG hρ hps hds hF hê hh₀
    (hat hx₀ (envEq_precomp_idt hM he'h) rfl)
  obtain rfl := Option.some_inj.mp (hq.symm.trans ht)
  obtain ⟨q', hq', hrq'⟩ := compile_precomp hM hG hρ hps hds hG' hê hh₀
    (hat hx₀ (envEq_precomp_idt hM he'h) rfl)
  obtain rfl := Option.some_inj.mp (hq'.symm.trans hu)
  -- at zero
  have hzb := comp_hom hM (bang_hom hM hX) (zeroN_hom hM)
  have hhz := pair_hom hM (idt_hom hM hX) hzb
  have zero : ∀ {w : Term} {W A : Tree}, compile G n w (prod X nat) (extEnv X nat e') =
      some (W, A) → ∃ q, compile G n (Term.subst w (instVar (Term.arr kz [] Term.star))) X e' =
        some q ∧ ResEq M ρ (comp W (pair (idt X) (comp zeroN (bang X))), A) q := by
    intro w W A hw
    obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw hê hhz
      (hat hzb (envEq_precomp_idt hM he'h) rfl)
    obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w X _ q₀ hq₀ e'
      (instVar (Term.arr kz [] Term.star)) he' fun i p hp ↦ by
        rcases i with _ | j
        · obtain rfl : (comp zeroN (bang X), nat) = p := by simpa using hp
          exact ⟨_, compile_zeroT hkz X e', ResEq.refl _⟩
        · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
    exact ⟨q₁, hq₁, hr₀.trans hr₁⟩
  obtain ⟨z₁, hz₁, hrz₁⟩ := zero hF
  obtain ⟨z₂, hz₂, hrz₂⟩ := zero hG'
  have h₀ := p₀ X e' he' hΓ' z₁ z₂ hz₁ hz₂
  obtain rfl : C₀ = D := (hrz₂.trans (h₀.symm.trans hrz₁.symm)).1
  -- the step, in the generic environment of its own context
  have hCt : IsTy n C₀ = true := (hty _ _ _ _ hF hê).2
  have hC := isObj_of_isTy hM hρ C₀ hCt
  obtain ⟨⟨s₀, C₁⟩, hsstd, hC₁⟩ := Option.map_eq_some_iff.mp hsC
  obtain rfl : C₀ = C₁ := hC₁.symm
  have hês : EnvHom M ρ n (prod X C₀) (extEnv X C₀ e') := he'.ext hM hC hCt
  obtain ⟨S, hS⟩ := compile_retype s _ _ _ hsstd (prod X C₀) (extEnv X C₀ e')
    (by simp [extEnv, hΓ', map_snd_stdEnv, Function.comp_def])
  have hSh := (hty _ _ _ _ hS hês).1
  -- at a successor, each side is the step after the parameters paired with its value
  have hfst := fst_hom hM hX hN
  have hsnd := snd_hom hM hX hN
  have hsc := comp_hom hM hsnd (succ_hom hM)
  have hk₁ := pair_hom hM hfst hsc
  have succStep : ∀ {w : Term} {W : Tree},
      compile G n w (prod X nat) (extEnv X nat e') = some (W, C₀) →
      EqSound M ρ G n (nat :: Γ') (natSuccAt ks w) (Term.subst s (atVar0 w)) →
      eval M ρ (comp W (pair (fst X nat) (comp succ (snd X nat)))) =
        eval M ρ (comp S (pair (fst X nat) W)) := by
    intro w W hw pw
    have hWh := (hty _ _ _ _ hw hê).1
    obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw hê hk₁
      (e' := (comp succ (snd X nat), nat) :: precomp (fst X nat) e')
      (envEq_precomp_extEnv hM hX hN he'h hk₁ (fst_pair hM hfst hsc) (snd_pair hM hfst hsc)
        (envEq_refl _))
    obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w _ _ q₀ hq₀ (extEnv X nat e')
      (atVar0 (Term.arr ks [] (Term.var 0))) hê fun i p hp ↦ by
        rcases i with _ | j
        · obtain rfl : (comp succ (snd X nat), nat) = p := by simpa using hp
          exact ⟨_, compile_succT hks (compile_var_iff.mpr ⟨rfl, rfl⟩), ResEq.refl _⟩
        · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
            ResEq.refl p⟩
    have hk₂ := pair_hom hM hfst hWh
    obtain ⟨q₂, hq₂, hr₂⟩ := compile_precomp hM hG hρ hps hds hS hês hk₂
      (e' := (W, C₀) :: precomp (fst X nat) e')
      (envEq_precomp_extEnv hM hX hC he'h hk₂ (fst_pair hM hfst hWh) (snd_pair hM hfst hWh)
        (envEq_refl _))
    obtain ⟨q₃, hq₃, hr₃⟩ := compile_subst hM hG hρ hps hds s _ _ q₂ hq₂ (extEnv X nat e')
      (atVar0 w) hê fun i p hp ↦ by
        rcases i with _ | j
        · obtain rfl : (W, C₀) = p := by simpa using hp
          exact ⟨_, hw, ResEq.refl _⟩
        · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
            ResEq.refl p⟩
    exact ((hr₀.trans (hr₁.trans (pw _ _ hê hêΓ q₁ q₃ hq₁ hq₃))).trans
      (hr₂.trans hr₃).symm).2.symm
  have hFG := natRec_param_unique hM hX hFh hGh hSh
    (hrz₁.trans (h₀.trans hrz₂.symm)).2.symm (succStep hF p₁) (succStep hG' p₂)
  exact hrq.symm.trans ((show ResEq M ρ (comp F (pair (idt X) x₀), C₀)
      (comp G' (pair (idt X) x₀), C₀) from ⟨rfl, eval_op₂_congr 3 hFG.symm rfl⟩).trans hrq')


/-- Induction on a list type is sound: an equation, in a context of a list variable, whose sides
agree at the empty list and are each, at a construction, a step of their type applied to the
element and their value at the tail, holds. -/
theorem listInd_sound {kn kc : ℕ} (hkn : G.prims[kn]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {Γ' : List Tree} {a : Tree} {t u s : Term} {C : Tree}
    (htC : typeIn G n (list a :: Γ') t = some C) (hsC : typeIn G n (C :: a :: Γ') s = some C)
    (p₀ : EqSound M ρ G n Γ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star))))
    (p₁ : EqSound M ρ G n (list a :: a :: Γ') (listConsAt kc a t)
      (Term.subst s (atVar0 (weakenElem t))))
    (p₂ : EqSound M ρ G n (list a :: a :: Γ') (listConsAt kc a u)
      (Term.subst s (atVar0 (weakenElem u)))) :
    EqSound M ρ G n (list a :: Γ') t u := by
  intro X e he hΓ r r' ht hu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  have he'h : ∀ p ∈ e', Hom M ρ p.1 X p.2 := fun p hp ↦ (he'.2 p hp).1
  obtain ⟨hx₀, hLt⟩ := he.2 _ List.mem_cons_self
  have hat : IsTy n a = true := by simpa [isTy_list] using hLt
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hX := he.1
  -- the generic environment, over the product with the list object
  have hê : EnvHom M ρ n (prod X (list a)) (extEnv X (list a) e') := he'.ext hM hL hLt
  have hêΓ : (extEnv X (list a) e').map Prod.snd = list a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  -- the sides' type, and their arrows in the generic environment
  obtain ⟨⟨f₀, C₀⟩, htstd, rfl⟩ := Option.map_eq_some_iff.mp htC
  obtain ⟨f₁, hf₁⟩ := compile_retype t _ _ _ htstd X ((x₀, list a) :: e')
    (by simp [map_snd_stdEnv, hΓ'])
  obtain rfl := Option.some_inj.mp (ht.symm.trans hf₁)
  obtain ⟨F, hF⟩ := compile_retype t X _ _ ht (prod X (list a)) (extEnv X (list a) e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨⟨g₁, D⟩, rfl⟩ : ∃ q, r' = q := ⟨_, rfl⟩
  obtain ⟨G', hG'⟩ := compile_retype u X _ _ hu (prod X (list a)) (extEnv X (list a) e')
    (by simp [hêΓ, hΓ'])
  have hFh := (hty _ _ _ _ hF hê).1
  have hGh := (hty _ _ _ _ hG' hê).1
  -- an arrow of the generic environment at an element of the list object
  have hel : ∀ {x : Tree}, Hom M ρ x X (list a) →
      EnvEq M ρ (precomp (pair (idt X) x) (extEnv X (list a) e')) ((x, list a) :: e') :=
    fun hx ↦ envEq_precomp_extEnv hM hX hL he'h (pair_hom hM (idt_hom hM hX) hx)
      (fst_pair hM (idt_hom hM hX) hx) (snd_pair hM (idt_hom hM hX) hx)
      (envEq_precomp_idt hM he'h)
  -- the sides are their generic arrows at the variable
  have hh₀ := pair_hom hM (idt_hom hM hX) hx₀
  obtain ⟨q, hq, hrq⟩ := compile_precomp hM hG hρ hps hds hF hê hh₀ (hel hx₀)
  obtain rfl := Option.some_inj.mp (hq.symm.trans ht)
  obtain ⟨q', hq', hrq'⟩ := compile_precomp hM hG hρ hps hds hG' hê hh₀ (hel hx₀)
  obtain rfl := Option.some_inj.mp (hq'.symm.trans hu)
  -- at the empty list
  have hnb := comp_hom hM (bang_hom hM hX) (nil_hom hM hA)
  have hhn := pair_hom hM (idt_hom hM hX) hnb
  have empty : ∀ {w : Term} {W B : Tree},
      compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B) →
      ∃ q, compile G n (Term.subst w (instVar (Term.arr kn [a] Term.star))) X e' = some q ∧
        ResEq M ρ (comp W (pair (idt X) (comp (nil a) (bang X))), B) q := by
    intro w W B hw
    obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw hê hhn (hel hnb)
    obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w X _ q₀ hq₀ e'
      (instVar (Term.arr kn [a] Term.star)) he' fun i p hp ↦ by
        rcases i with _ | j
        · obtain rfl : (comp (nil a) (bang X), list a) = p := by simpa using hp
          exact ⟨_, compile_nilT hkn hat X e', ResEq.refl _⟩
        · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
    exact ⟨q₁, hq₁, hr₀.trans hr₁⟩
  obtain ⟨z₁, hz₁, hrz₁⟩ := empty hF
  obtain ⟨z₂, hz₂, hrz₂⟩ := empty hG'
  have h₀ := p₀ X e' he' hΓ' z₁ z₂ hz₁ hz₂
  obtain rfl : C₀ = D := (hrz₂.trans (h₀.symm.trans hrz₁.symm)).1
  -- the step, in the generic environment of its own context
  have hCt : IsTy n C₀ = true := (hty _ _ _ _ hF hê).2
  have hC := isObj_of_isTy hM hρ C₀ hCt
  obtain ⟨⟨s₀, C₁⟩, hsstd, hC₁⟩ := Option.map_eq_some_iff.mp hsC
  obtain rfl : C₀ = C₁ := hC₁.symm
  have hea : EnvHom M ρ n (prod X a) (extEnv X a e') := he'.ext hM hA hat
  have hXa := hea.1
  have hês : EnvHom M ρ n (prod (prod X a) C₀) (extEnv (prod X a) C₀ (extEnv X a e')) :=
    hea.ext hM hC hCt
  obtain ⟨S, hS⟩ := compile_retype s _ _ _ hsstd (prod (prod X a) C₀)
    (extEnv (prod X a) C₀ (extEnv X a e'))
    (by simp [extEnv, hΓ', map_snd_stdEnv, Function.comp_def])
  have hSh := (hty _ _ _ _ hS hês).1
  -- the generic environment of the step's premises
  have hê₁ : EnvHom M ρ n (prod (prod X a) (list a)) (extEnv (prod X a) (list a) (extEnv X a e')) :=
    hea.ext hM hL hLt
  have hê₁Γ : (extEnv (prod X a) (list a) (extEnv X a e')).map Prod.snd = list a :: a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hfXa := fst_hom hM hX hA
  have hsXa := snd_hom hM hX hA
  have hff := comp_hom hM hfQ hfXa
  have hsf := comp_hom hM hfQ hsXa
  have hel₁ := pair_hom hM hsf hsQ
  have hcel := comp_hom hM hel₁ (cons_hom hM hA)
  have hk₁ := pair_hom hM hff hcel
  have hk₂ := pair_hom hM hff hsQ
  -- at a construction, each side is the step after the parameters, the element and its value
  -- at the tail
  have consStep : ∀ {w : Term} {W : Tree},
      compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, C₀) →
      EqSound M ρ G n (list a :: a :: Γ') (listConsAt kc a w)
        (Term.subst s (atVar0 (weakenElem w))) →
      eval M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
          (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a)))))) =
        eval M ρ (comp S (pair (fst (prod X a) (list a))
          (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a)))))) := by
    intro w W hw pw
    have hWh := (hty _ _ _ _ hw hê).1
    -- the left side
    obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw hê hk₁
      (e' := (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
        (snd (prod X a) (list a))), list a) ::
        precomp (comp (fst X a) (fst (prod X a) (list a))) e')
      (envEq_precomp_extEnv hM hX hL he'h hk₁ (fst_pair hM hff hcel) (snd_pair hM hff hcel)
        (envEq_refl _))
    obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w _ _ q₀ hq₀
      (extEnv (prod X a) (list a) (extEnv X a e'))
      (fun i ↦ match i with
        | 0 => Term.arr kc [a] (Term.pair (Term.var 1) (Term.var 0))
        | j + 1 => Term.var (j + 2)) hê₁ fun i p hp ↦ by
        rcases i with _ | j
        · obtain rfl : (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
              (snd (prod X a) (list a))), list a) = p := by simpa using hp
          exact ⟨_, compile_consT hkc hat (compile_pair_iff.mpr ⟨_, _, _, a, _, list a, rfl,
            compile_var_iff.mpr ⟨rfl, rfl⟩, compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩),
            ResEq.refl _⟩
        · simp only [precomp, List.getElem?_cons_succ, List.getElem?_map,
            Option.map_eq_some_iff] at hp
          obtain ⟨p₀, hp₀, rfl⟩ := hp
          exact ⟨(comp (comp p₀.1 (fst X a)) (fst (prod X a) (list a)), p₀.2),
            compile_var_iff.mpr ⟨rfl, by simp [extEnv, hp₀]⟩, rfl,
            (comp_assoc hM hfQ hfXa (he'h p₀ (List.mem_of_getElem? hp₀))).symm⟩
    -- the right side: the side at the tail, weakened past the element
    obtain ⟨q₂, hq₂, hr₂⟩ := compile_precomp hM hG hρ hps hds hw hê hk₂
      (e' := (snd (prod X a) (list a), list a) ::
        precomp (fst (prod X a) (list a)) (precomp (fst X a) e'))
      (envEq_precomp_extEnv hM hX hL he'h hk₂ (fst_pair hM hff hsQ) (snd_pair hM hff hsQ)
        (envEq_precomp_comp hM he'h hfXa hfQ))
    have hwk := compile_rename w _ (extEnv (prod X a) (list a) (extEnv X a e')) _
      (fun i ↦ match i with
        | 0 => 0
        | j + 1 => j + 2) q₂ hq₂ fun i _ ↦ by
        rcases i with _ | j
        · rfl
        · simp [extEnv, precomp]
    obtain ⟨q₃, hq₃, hr₃⟩ := compile_precomp hM hG hρ hps hds hS hês
      (pair_hom hM hfQ (comp_hom hM hk₂ hWh))
      (e' := (comp W (pair (comp (fst X a) (fst (prod X a) (list a))) (snd (prod X a) (list a))),
        C₀) :: precomp (fst (prod X a) (list a)) (extEnv X a e'))
      (envEq_precomp_extEnv hM hXa hC (fun p hp ↦ (hea.2 p hp).1)
        (pair_hom hM hfQ (comp_hom hM hk₂ hWh)) (fst_pair hM hfQ (comp_hom hM hk₂ hWh))
        (snd_pair hM hfQ (comp_hom hM hk₂ hWh)) (envEq_refl _))
    obtain ⟨q₄, hq₄, hr₄⟩ := compile_subst hM hG hρ hps hds s _ _ q₃ hq₃
      (extEnv (prod X a) (list a) (extEnv X a e')) (atVar0 (weakenElem w)) hê₁ fun i p hp ↦ by
        rcases i with _ | j
        · obtain rfl : (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
              (snd (prod X a) (list a))), C₀) = p := by simpa using hp
          exact ⟨_, hwk, hr₂⟩
        · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
            ResEq.refl p⟩
    exact ((hr₀.trans (hr₁.trans (pw _ _ hê₁ hê₁Γ q₁ q₄ hq₁ hq₄))).trans
      (hr₃.trans hr₄).symm).2.symm
  have hFG := listRec_param_unique hM hX hA hFh hGh hSh
    (hrz₁.trans (h₀.trans hrz₂.symm)).2.symm (consStep hF p₁) (consStep hG' p₂)
  exact hrq.symm.trans ((show ResEq M ρ (comp F (pair (idt X) x₀), C₀)
      (comp G' (pair (idt X) x₀), C₀) from ⟨rfl, eval_op₂_congr 3 hFG.symm rfl⟩).trans hrq')


/-- The checker is sound: every rewriting a derivation performs is sound, and every equation it
proves holds, with sound unfoldings and valid earlier theorems. -/
theorem check_sound (hδ : DefnsOk M G) {E : Array Thm}
    (hE : ∀ (j : ℕ) (a : Thm), E[j]? = some a → a.Valid M G) :
    ∀ d : Deriv, (∀ Γ t t', (check G E n d).1 Γ t = some t' → RwSound M ρ G n Γ t t') ∧
      (∀ Γ t u, (check G E n d).2 Γ t u = true → EqSound M ρ G n Γ t u) := by
  refine RoseTree.ind fun l cs ih ↦ ⟨fun Γ t t' h ↦ ?_, fun Γ t u h ↦ ?_⟩
  · rw [check_node] at h
    cases l
    case refl =>
      rcases cs with _ | ⟨c, cs⟩
      · obtain rfl : t = t' := Option.some_inj.mp h
        exact RwSound.refl Γ t
      · simp [checkStep] at h
    case trans =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep, rootStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        obtain ⟨v, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
        exact ((ih c₁ (by simp)).1 _ _ _ h₁).trans ((ih c₂ (by simp)).1 _ _ _ h₂)
      · simp [checkStep] at h
    case cong =>
      obtain ⟨l₀, ts, rfl⟩ : ∃ l cs, t = RoseTree.node l cs :=
        ⟨_, _, (RoseTree.node_label_children t).symm⟩
      simp only [checkStep, RoseTree.label_node, RoseTree.children_node] at h
      obtain ⟨Γs, hΓs, h⟩ := Option.bind_eq_some_iff.mp h
      split_ifs at h with hlen
      obtain ⟨ts', hts', h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some_inj.mp h
      refine cong_sound hM hG hρ hps hds hΓs ?_
      refine forall₂_zip_imp
        (P := fun x : Deriv × Checks ↦ ∀ Γ t t', x.2.1 Γ t = some t' → RwSound M ρ G n Γ t t')
        (R := fun x r ↦ x.1.2.1 x.2.1 x.2.2 = some r)
        (fun _ _ _ hx hR ↦ hx _ _ _ hR) _ _ _ (by simp [hlen.1, hlen.2])
        (fun x hx ↦ ?_) (forall₂_of_mapM _ hts')
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact (ih c hc).1
    all_goals
      rcases cs with _ | ⟨c, cs⟩
      · exact rootStep_sound hM hG hρ hps hds hδ hE (by simpa [checkStep] using h)
      · simp [checkStep] at h
  · rw [check_node] at h
    cases l
    case join =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i v v' h₁ h₂
          obtain rfl := of_decide_eq_true h
          exact EqSound.of_join ((ih c₁ (by simp)).1 _ _ _ h₁) ((ih c₂ (by simp)).1 _ _ _ h₂)
        · simp at h
      · simp [checkStep] at h
    case natInd kz ks s =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i c Γ' C htC
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨⟨rfl, hkz, hks, hsC⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
          exact natInd_sound hM hG hρ hps hds hkz hks htC hsC ((ih c₀ (by simp)).2 _ _ _ hp₀)
            ((ih c₁ (by simp)).2 _ _ _ hp₁) ((ih c₂ (by simp)).2 _ _ _ hp₂)
        · simp at h
      · simp [checkStep] at h
    case listInd kn kc s =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i c Γ' C htC
          split at h
          · rename_i a ha
            obtain rfl := listPart_eq_some.mp ha
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨hkn, hkc, hsC⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
            exact listInd_sound hM hG hρ hps hds hkn hkc htC hsC ((ih c₀ (by simp)).2 _ _ _ hp₀)
              ((ih c₁ (by simp)).2 _ _ _ hp₁) ((ih c₂ (by simp)).2 _ _ _ hp₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    all_goals simp [checkStep] at h


end Rewriting

section Theorems

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}
  (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF)
  (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
  (hds : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → DefsHom M ρ G m)
  (hδ : DefnsOk M G)
include hM hG hps hds hδ

/-- A theorem a derivation proves with valid earlier theorems is valid. -/
theorem Thm.valid_of_checks {E : Array Thm}
    (hE : ∀ (j : ℕ) (a : Thm), E[j]? = some a → a.Valid M G) {a : Thm} {d : Deriv}
    (h : a.checks G E d = true) : a.Valid M G := by
  simp only [Thm.checks, Bool.and_eq_true] at h
  obtain ⟨⟨hctx, hty⟩, hd⟩ := h
  split at hty
  · rename_i A B hA hB
    obtain rfl := of_decide_eq_true hty
    obtain ⟨⟨f, A'⟩, hf, rfl⟩ := Option.map_eq_some_iff.mp hA
    obtain ⟨⟨g, B'⟩, hg, rfl⟩ := Option.map_eq_some_iff.mp hB
    refine ⟨hctx, f, g, _, hf, hg, fun ρ hρ ↦ ?_⟩
    have hstd := stdEnv_hom hM hρ a.ctx hctx
    exact ⟨(compile_hom hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) _ _ _ _ hf hstd).1,
      ((check_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE d).2 _ _ _ hd _ _ hstd
        (map_snd_stdEnv _) _ _ hf hg).2.symm⟩
  · simp at hty

/-- Every theorem of a development that checks, with valid earlier theorems, is valid. -/
theorem valid_of_checkThms :
    ∀ (ds : List (Thm × Deriv)) (E : Array Thm),
      (∀ (j : ℕ) (a : Thm), E[j]? = some a → a.Valid M G) → checkThms G ds E = true →
      ∀ p ∈ ds, p.1.Valid M G :=
  List.rec (fun _ _ _ _ hp ↦ by simp at hp) fun e ds ih E hE h p hp ↦ by
    change (e.1.checks G E e.2 && checkThms G ds (E.push e.1)) = true at h
    rw [Bool.and_eq_true] at h
    have he := Thm.valid_of_checks hM hG hps hds hδ hE h.1
    rcases List.mem_cons.mp hp with rfl | hp
    · exact he
    · refine ih (E.push e.1) (fun j a hj ↦ ?_) h.2 p hp
      rcases Nat.lt_trichotomy j E.size with hlt | rfl | hgt
      · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at hj
        exact hE j a hj
      · rw [Array.getElem?_push_size] at hj
        obtain rfl := Option.some_inj.mp hj
        exact he
      · rw [Array.getElem?_eq_none (by rw [Array.size_push]; omega)] at hj
        cases hj

end Theorems

/-- The soundness of the internal language's derivations: in every model of the theory extended
by the combinators' definitions and those the definitions compile to, every theorem of a
development that checks is valid, when the check accepts the constants. -/
theorem valid_of_checkThms_ok {pre cds : List PartialHorn.Defn}
    {M : Model.{v} (ext (pre ++ cds)).sig} (hM : IsModel (ext (pre ++ cds)) M) {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) {ds : List (Thm × Deriv)} (h : checkThms G ds #[] = true) :
    ∀ p ∈ ds, p.1.Valid M G := by
  have hG := Globals.wf_of_ok hok
  have hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
      PrimsHom M ρ G m := fun _ _ hρ ↦ primsHom_of_ok hM hok hρ
  obtain ⟨hds, -⟩ := defsInv hM hbase hG hc hps G.defs.length le_rfl
  simp only [List.take_length] at hds
  exact valid_of_checkThms hM hG hps hds (fun _ _ hd ↦ defn_body hM hbase hG hc hps hd) ds #[]
    (fun _ _ hj ↦ by simp at hj) h

/-- The soundness of the internal language's derivations for the theory itself: each theorem of
a development that checks has sides that compile in its context to arrows of one type, whose
equation, with every definition unfolded, holds in every model of the theory, when the check
accepts the constants and their definitions are well formed. -/
theorem valid_unfoldAll_of_checkThms {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds))
    {ds : List (Thm × Deriv)} (h : checkThms G ds #[] = true) (p : Thm × Deriv) (hp : p ∈ ds) :
    ∃ f g A, compile G p.1.arity p.1.lhs (ctxObj p.1.ctx) (stdEnv p.1.ctx) = some (f, A) ∧
      compile G p.1.arity p.1.rhs (ctxObj p.1.ctx) (stdEnv p.1.ctx) = some (g, A) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ cds)
          ⟨List.replicate p.1.arity obj, [], ⟨f, g⟩⟩).Valid M := by
  have hM₀ : IsModel (ext (pre ++ cds)) (PartialHorn.pointModel (ext (pre ++ cds)).sig) :=
    PartialHorn.isModel_point
      (PartialHorn.sidesSorted_extendAll (pre ++ cds) theory theory_sidesSorted hwf)
  obtain ⟨hctx, f, g, A, hf, hg, -⟩ := valid_of_checkThms_ok hM₀ hbase hok hc h p hp
  refine ⟨f, g, A, hf, hg, fun M hM ↦ ?_⟩
  have hG := Globals.wf_of_ok hok
  have hsrt := fun {s : Term} {r : Tree × Tree}
      (hs : compile G p.1.arity s (ctxObj p.1.ctx) (stdEnv p.1.ctx) = some r) ↦
    compile_sortOf (defs := pre ++ cds) hG (fun k p hp ↦ sortOf_prims_of_ok hok hp)
      (fun k d hd ↦ getElem?_sig_compileDefs hbase hc hd) s _ _ r hs (sortOf_ctxObj _ hctx)
      (sortOf_stdEnv _ hctx)
  refine PartialHorn.valid_unfoldAll (pre ++ cds) theory M hM theory_ofSig hwf _ ?_ ?_
  · intro q hq
    obtain rfl : q = ⟨f, g⟩ := by simpa using hq
    exact ⟨⟨arr, (hsrt hf).1⟩, ⟨arr, (hsrt hg).1⟩⟩
  · intro N hN ρ hρ _
    obtain ⟨-, f', g', A', hf', hg', hv⟩ := valid_of_checkThms_ok hN hbase hok hc h p hp
    rw [hf] at hf'
    rw [hg] at hg'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some_inj.mp hf')
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some_inj.mp hg')
    obtain ⟨hfh, heq⟩ := hv ρ hρ
    obtain ⟨w, hw, -⟩ := hfh.exists_eval
    exact ⟨w, hw, heq.symm.trans hw⟩

end Geb.FreeTopos.Internal

end
