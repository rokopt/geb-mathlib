/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Soundness
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of the internal language's proofs

The checker {name}`Geb.FreeTopos.Internal.check` is sound ({lit}`check_sound`): every rewriting a
derivation performs is sound, and every formula it proves is sound, in the sense of
{name}`Geb.FreeTopos.Internal.FmSound`. In every model of the theory extended by the combinators'
definitions and those the language's definitions compile to, every theorem of a development that
checks is valid ({lit}`valid_of_checkThms_ok`). With every definition unfolded, the equation of a
theorem without hypotheses holds in every model of the theory itself
({lit}`valid_unfoldAll_of_checkThms`), as does the truth of its formula
({lit}`valid_unfoldAll_holds_of_checkThms`).

The rules of proof are sound by the universal properties of the subobject classifier and of the
exponential. An equation whose sides rewrite to one term holds; a cut, and a formula rewritten
before or after its proof, are sound by the soundness of the rewriting and of the formula cut in.
Propositional extensionality is sound by the uniqueness of characteristic maps
({name}`Geb.FreeTopos.omega_ext`), each formula being true on the other's pullback of truth;
function extensionality by the η of the exponential, the applications compared in the
environment extended by a variable; and the application of an earlier theorem by its validity at
the instance. Induction in the form of the uniqueness of recursion is sound by the uniqueness of
the folds with a parameter ({name}`Geb.FreeTopos.natRec_param_unique`,
{name}`Geb.FreeTopos.listRec_param_unique`), and induction with the induction hypothesis by
induction on subobjects ({name}`Geb.FreeTopos.truth_of_natInd`,
{name}`Geb.FreeTopos.truth_of_listInd`), the step proved on the formula's pullback of truth. Each
induction is applied in the environment that extends the other variables' environment by the
induction variable, in which the hypotheses, which do not mention it, still hold, and is carried
to the given environment by the arrow of the variable. Case analysis on a coproduct is applied in
the same way, and is sound because an arrow from the product of an object and a coproduct is
determined by its composites with the products of the object and the injections
({name}`Geb.FreeTopos.prod_coprod_ext`); a formula in a context with a variable of the initial
type holds because an object with an arrow to the initial object is initial
({name}`Geb.FreeTopos.eq_of_hom_zero`).

## Main statements

* {lit}`join_sound`, {lit}`cut_sound`, {lit}`conv_sound`, {lit}`convFrom_sound`,
  {lit}`propExt_sound`, {lit}`funExt_sound`, {lit}`apply_sound` — the logical rules are sound.
* {lit}`natInd_sound`, {lit}`listInd_sound`, {lit}`natIndHyp_sound`, {lit}`listIndHyp_sound` —
  induction is sound.
* {lit}`coprodInd_sound`, {lit}`zeroInd_sound` — case analysis on a coproduct, and a context
  with a variable of the initial type, are sound.
* {lit}`check_sound` — the checker is sound.
* {lit}`valid_of_checkThms_ok`, {lit}`valid_unfoldAll_of_checkThms`,
  {lit}`valid_unfoldAll_holds_of_checkThms` — the theorems of a development that checks are
  valid, in the extension and in the theory.

## Tags

internal language, soundness, proof checker, induction, subobject classifier
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

section Proofs

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig} {ρ : List M.Val}
  (hM : IsModel (ext defs) M) {G : Globals} (hG : G.WF) {n : ℕ}
  (hρ : ρ.map Sigma.fst = List.replicate n obj) (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n)
include hM hG hρ hps hds

omit hM hG hρ hps hds in
/-- A term's result related to another has the other's type. -/
theorem compile_resEq {s : Term} {X : Tree} {e : List (Tree × Tree)} {q r : Tree × Tree}
    (hq : compile G n s X e = some q) (hr : ResEq M ρ r q) :
    compile G n s X e = some (q.1, r.2) :=
  hq.trans (congrArg some (Prod.ext rfl hr.1))

omit hM hG hρ hps hds in
/-- A formula of a context compiles, to the subobject classifier's type, in every environment of
the context's types. -/
theorem compile_of_typeIn {Γ : List Tree} {φ : Term} {A : Tree} (hφ : typeIn G n Γ φ = some A)
    {X : Tree} {e : List (Tree × Tree)} (hΓ : e.map Prod.snd = Γ) :
    ∃ f, compile G n φ X e = some (f, A) := by
  obtain ⟨⟨f₀, A₀⟩, hstd, rfl⟩ := Option.map_eq_some_iff.mp hφ
  exact compile_retype φ _ _ _ hstd X e (hΓ.trans (map_snd_stdEnv Γ).symm)

/-- An equation whose sides rewrite soundly to one term holds. -/
theorem join_sound {Γ : List Tree} {Φ : List Term} {t u v : Term}
    (h₁ : RwSound M ρ G n Γ Φ t v) (h₂ : RwSound M ρ G n Γ Φ u v) :
    FmSound M ρ G n Γ Φ (Term.eq t u) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  obtain ⟨q, hq, -, hq₁⟩ := h₁ X e he hΓ hΦ _ ht
  obtain ⟨q', hq', -, hq'₁⟩ := h₂ X e he hΓ hΦ _ hu
  obtain rfl : q = q' := Option.some_inj.mp (hq.symm.trans hq')
  exact (holds_eq_iff hM hG hρ hps hds he ht hu).mpr (hq₁.symm.trans hq'₁)

omit hM hG hρ hps hds in
/-- A hypothesis holds. -/
theorem hyp_sound {Γ : List Tree} {Φ : List Term} {i : ℕ} {φ : Term} (h : Φ[i]? = some φ) :
    FmSound M ρ G n Γ Φ φ := fun X e _ _ hΦ r hr ↦ by
  obtain ⟨q, hq, hH⟩ := hΦ φ (List.mem_of_getElem? h)
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact hH

omit hM hG hρ hps hds in
/-- A formula that holds under a formula proved first holds. -/
theorem cut_sound {Γ : List Tree} {Φ : List Term} {ψ φ : Term}
    (hψ : typeIn G n Γ ψ = some omega) (p : FmSound M ρ G n Γ Φ ψ)
    (q : FmSound M ρ G n Γ (Φ ++ [ψ]) φ) : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ hΦ r hr
  obtain ⟨f, hf⟩ := compile_of_typeIn hψ (X := X) hΓ
  exact q X e he hΓ ((hypsHold_append M ρ).mpr ⟨hΦ, _, hf, p X e he hΓ hΦ _ hf⟩) r hr

omit hM hG hρ hps hds in
/-- A formula that a sound rewriting takes to one that holds holds. -/
theorem conv_sound {Γ : List Tree} {Φ : List Term} {φ φ' : Term}
    (d : RwSound M ρ G n Γ Φ φ φ') (p : FmSound M ρ G n Γ Φ φ') : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ hΦ r hr
  obtain ⟨r', hr', hr'₂, hr'₁⟩ := d X e he hΓ hΦ r hr
  obtain ⟨h₂, h₁⟩ := p X e he hΓ hΦ r' hr'
  exact ⟨hr'₂.symm.trans h₂, hr'₁.symm.trans h₁⟩

omit hM hG hρ hps hds in
/-- A formula to which a formula that holds rewrites soundly holds. -/
theorem convFrom_sound {Γ : List Tree} {Φ : List Term} {φ φ' : Term}
    (hφ' : typeIn G n Γ φ' = some omega) (d : RwSound M ρ G n Γ Φ φ' φ)
    (p : FmSound M ρ G n Γ Φ φ') : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ hΦ r hr
  obtain ⟨f, hf⟩ := compile_of_typeIn hφ' (X := X) hΓ
  obtain ⟨r', hr', hr'₂, hr'₁⟩ := d X e he hΓ hΦ _ hf
  obtain rfl := Option.some_inj.mp (hr.symm.trans hr')
  obtain ⟨h₂, h₁⟩ := p X e he hΓ hΦ _ hf
  exact ⟨hr'₂.trans h₂, hr'₁.trans h₁⟩

/-- Two formulas, each of which holds under the other, are equal. -/
theorem propExt_sound {Γ : List Tree} {Φ : List Term} {α β : Term}
    (hα : typeIn G n Γ α = some omega)
    (p : FmSound M ρ G n Γ (Φ ++ [α]) β) (q : FmSound M ρ G n Γ (Φ ++ [β]) α) :
    FmSound M ρ G n Γ Φ (Term.eq α β) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨α', β', hαβ, F, A, hF, P, hP, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at hαβ
  obtain ⟨rfl, rfl⟩ := hαβ
  obtain ⟨F', hF'⟩ := compile_of_typeIn hα (X := X) hΓ
  obtain rfl : A = omega := (Prod.mk.inj (Option.some_inj.mp (hF.symm.trans hF'))).2
  have hFh : Hom M ρ F X omega := (compile_hom hM hG hρ hps hds _ X e _ hF he).1
  have hPh : Hom M ρ P X omega := (compile_hom hM hG hρ hps hds _ X e _ hP he).1
  -- each holds on the other's pullback of truth
  have key : ∀ {γ δ : Term} {C D : Tree}, Hom M ρ C X omega → Hom M ρ D X omega →
      compile G n γ X e = some (C, omega) → compile G n δ X e = some (D, omega) →
      FmSound M ρ G n Γ (Φ ++ [γ]) δ →
      eval M ρ (comp D (truthIncl C)) = eval M ρ (comp tru (bang (truthEq C))) := by
    intro γ δ C D hC hD hγ hδ pγ
    obtain ⟨hi, hCi⟩ := truthIncl_hom hM hC
    have he₁ := envHom_precomp hM he hi
    obtain ⟨r₁, hr₁, hr₁₂, hr₁₁⟩ := compile_precomp hM hG hρ hps hds hγ he hi (envEq_refl _)
    obtain ⟨r₂, hr₂, hr₂₂, hr₂₁⟩ := compile_precomp hM hG hρ hps hds hδ he hi (envEq_refl _)
    have hH := pγ _ _ he₁ (by simp [precomp, Function.comp_def, hΓ])
      ((hypsHold_append M ρ).mpr ⟨hypsHold_precomp hM hG hρ hps hds hΦ he hi (envEq_refl _),
        r₁, hr₁, hr₁₂, hr₁₁.trans hCi⟩) r₂ hr₂
    exact hr₂₁.symm.trans hH.2
  have hFP := omega_ext hM hFh hPh (key hFh hPh hF hP p) (key hPh hFh hP hF q)
  exact (holds_eq_iff hM hG hρ hps hds he hF hP).mpr hFP

/-- Two functions whose applications to a new variable are equal are equal. -/
theorem funExt_sound {Γ : List Tree} {Φ : List Term} {f g : Term} {a b : Tree}
    (hf : (typeIn G n Γ f).bind expParts = some (a, b))
    (p : FmSound M ρ G n (a :: Γ) (Φ.map weaken1)
      (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0)))) :
    FmSound M ρ G n Γ Φ (Term.eq f g) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨f', g', hfg, F, A, hF, G', hG', rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at hfg
  obtain ⟨rfl, rfl⟩ := hfg
  obtain ⟨T, hT, hTab⟩ := Option.bind_eq_some_iff.mp hf
  obtain rfl := expParts_eq_some.mp hTab
  obtain ⟨F', hF'⟩ := compile_of_typeIn hT (X := X) hΓ
  obtain rfl : A = exp a b := (Prod.mk.inj (Option.some_inj.mp (hF.symm.trans hF'))).2
  obtain ⟨hFh, hABt⟩ := compile_hom hM hG hρ hps hds _ X e _ hF he
  have hGh : Hom M ρ G' X (exp a b) := (compile_hom hM hG hρ hps hds _ X e _ hG' he).1
  simp only [isTy_exp, Bool.and_eq_true] at hABt
  have hA := isObj_of_isTy hM hρ a hABt.1
  have hB := isObj_of_isTy hM hρ b hABt.2
  have hX := he.1
  -- the applications to the new variable, in the extended environment
  have app : ∀ {w : Term} {W : Tree}, compile G n w X e = some (W, exp a b) →
      ∃ W', compile G n (Term.app (weaken1 w) (Term.var 0)) (prod X a) (extEnv X a e) =
        some (comp (ev a b) (pair W' (snd X a)), b) ∧
        eval M ρ W' = eval M ρ (comp W (fst X a)) := fun {w W} hw ↦ by
    obtain ⟨⟨W', B'⟩, hr₁, hr₁₂, hr₁₁⟩ := compile_precomp hM hG hρ hps hds hw he
      (fst_hom hM hX hA) (envEq_refl _)
    obtain rfl : B' = exp a b := hr₁₂
    have hw' := compile_rename w (prod X a) (extEnv X a e) (precomp (fst X a) e) (· + 1) _ hr₁
      fun i hi ↦ by simp [extEnv, precomp]
    exact ⟨W', compile_app_iff.mpr ⟨_, _, rfl, W', a, b, hw', snd X a,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl⟩, hr₁₁⟩
  obtain ⟨F₁, hF₁, hF₁v⟩ := app hF
  obtain ⟨G₁, hG₁, hG₁v⟩ := app hG'
  have hext := he.ext hM hA hABt.1
  have hH := p _ _ hext (by simp [extEnv, hΓ, Function.comp_def])
    (hypsHold_weaken1 hM hG hρ hps hds hΦ he hA) _
    (compile_eq_iff.mpr ⟨_, _, rfl, _, b, hF₁, _, hG₁, rfl⟩)
  have heq := (holds_eq_iff hM hG hρ hps hds hext hF₁ hG₁).mp hH
  -- each function is the currying of its evaluation at the new variable
  have hcur : ∀ {W W₁ : Tree}, Hom M ρ W X (exp a b) → eval M ρ W₁ = eval M ρ (comp W (fst X a)) →
      eval M ρ W = eval M ρ (curry X a (comp (ev a b) (pair W₁ (snd X a)))) :=
    fun hW hW₁ ↦ (curry_eta hM hA hB hW).symm.trans
      (eval_op₃_congr 24 rfl rfl (eval_op₂_congr 3 rfl (eval_op₂_congr 9 hW₁.symm rfl)))
  exact (holds_eq_iff hM hG hρ hps hds he hF hG').mpr ((hcur hFh hF₁v).trans
    ((eval_op₃_congr 24 rfl rfl heq).trans (hcur hGh hG₁v).symm))

/-- An instance of a valid theorem, the instances of whose hypotheses hold, holds. -/
theorem apply_sound {E : Array Thm} (hE : ∀ (j : ℕ) (a : Thm), E[j]? = some a → a.Valid M G)
    {Γ : List Tree} {Φ : List Term} {j : ℕ} {a : Thm} (ha : E[j]? = some a) {θ : List Tree}
    {σ : List Term} (hok : instOk G n Γ a θ σ = true)
    (hs : ∀ h ∈ a.hyps, FmSound M ρ G n Γ Φ (instTerm θ σ h)) :
    FmSound M ρ G n Γ Φ (instTerm θ σ a.concl) := by
  intro X e he hΓ hΦ r hr
  simp only [instOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨hl, hθ⟩, hσl⟩, hall⟩ := hok
  obtain ⟨rs, hrs, hsnd⟩ := mapM_compile_of_typeIn hΓ σ _ (by simp [hσl]) hall
  have hv := hE j a ha
  refine Thm.Valid.inst hM hG hρ hps hds hv hl hθ he hrs hsnd (fun ψ hψ ↦ ?_) r hr
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hψ
  obtain ⟨⟨fh, Ah⟩, hstd, -⟩ := Option.map_eq_some_iff.mp (hv.2.1 h hh)
  obtain ⟨r', hr', -⟩ := compile_thm_side hM hG hρ hps hds hstd hl hθ he hrs hsnd
  exact ⟨r', hr', hs h hh X e he hΓ hΦ r' hr'⟩

omit hM hG hρ hps hds in
/-- Hypotheses that hold in an environment extended by a variable none of them mentions hold,
lowered, in the environment. -/
theorem hypsHold_lower {Γ' : List Tree} {Φ Φ' : List Term} (hlow : lowerHyps G n Γ' Φ = some Φ')
    {X x B : Tree} {e' : List (Tree × Tree)} (hΓ' : e'.map Prod.snd = Γ')
    (hΦ : HypsHold M ρ G n Φ X ((x, B) :: e')) : HypsHold M ρ G n Φ' X e' := by
  obtain ⟨hΦeq, hty⟩ := lowerHyps_spec hlow
  intro ψ hψ
  obtain ⟨f, hf⟩ := compile_of_typeIn (hty ψ hψ) (X := X) hΓ'
  obtain ⟨r, hr, hH⟩ := hΦ (weaken1 ψ) (by rw [hΦeq]; exact List.mem_map_of_mem hψ)
  have hw := compile_rename ψ X ((x, B) :: e') e' (· + 1) _ hf fun i _ ↦ by simp
  obtain rfl := Option.some_inj.mp (hr.symm.trans hw)
  exact ⟨_, hf, hH⟩

/-- A term in the environment extended by a natural number variable, at an element of the
natural numbers object, is its arrow there after the pairing of the identity with the
element. -/
theorem natAt {X x W B : Tree} {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ n X e')
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, B)) (hx : Hom M ρ x X nat) :
    ∃ q, compile G n w X ((x, nat) :: e') = some q ∧
      ResEq M ρ (comp W (pair (idt X) x), B) q :=
  compile_at hM hG hρ hps hds he' isTy_nat hw hx

/-- A term in the environment extended by a natural number variable, at zero, is its arrow there
after the pairing of the identity with zero. -/
theorem natZeroAt {kz : ℕ} (hkz : G.prims[kz]? = some zeroPrim) {X W B : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ n X e')
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, B)) :
    ∃ q, compile G n (Term.subst w (instVar (Term.arr kz [] Term.star))) X e' = some q ∧
      ResEq M ρ (comp W (pair (idt X) (comp zeroN (bang X))), B) q := by
  obtain ⟨q₀, hq₀, hr₀⟩ := natAt hM hG hρ hps hds he' hw
    (comp_hom hM (bang_hom hM he'.1) (zeroN_hom hM))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w X _ q₀ hq₀ e'
    (instVar (Term.arr kz [] Term.star)) he' fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp zeroN (bang X), nat) = p := by simpa using hp
        exact ⟨_, compile_zeroT hkz X e', ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a variable of type {lit}`D`, at a term that compiles in
the environment extended instead by a variable of type {lit}`A` to an arrow {lit}`i` from
{lit}`A` to {lit}`D` after the variable, is its arrow after the product of the environment's
object with {lit}`i`. -/
theorem atVar0_compile {X W B A D i : Tree} {e' : List (Tree × Tree)} {w u : Term}
    (he' : EnvHom M ρ n X e') (hAt : IsTy n A = true) (hDt : IsTy n D = true)
    (hi : Hom M ρ i A D) (hw : compile G n w (prod X D) (extEnv X D e') = some (W, B))
    (hu : compile G n u (prod X A) (extEnv X A e') = some (comp i (snd X A), D)) :
    ∃ q, compile G n (Term.subst w (atVar0 u)) (prod X A) (extEnv X A e') = some q ∧
      ResEq M ρ (comp W (pair (fst X A) (comp i (snd X A))), B) q := by
  have hA := hi.isObj_dom
  have hD := hi.isObj_cod
  have hX := he'.1
  have hfst := fst_hom hM hX hA
  have hsc := comp_hom hM (snd_hom hM hX hA) hi
  have hk₁ := pair_hom hM hfst hsc
  obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw (he'.ext hM hD hDt) hk₁
    (e' := (comp i (snd X A), D) :: precomp (fst X A) e')
    (envEq_precomp_extEnv hM hX hD (fun p hp ↦ (he'.2 p hp).1) hk₁ (fst_pair hM hfst hsc)
      (snd_pair hM hfst hsc) (envEq_refl _))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w _ _ q₀ hq₀ (extEnv X A e')
    (atVar0 u) (he'.ext hM hA hAt) fun j p hp ↦ by
      rcases j with _ | j
      · obtain rfl : (comp i (snd X A), D) = p := by simpa using hp
        exact ⟨_, hu, ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
          ResEq.refl p⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a natural number variable, at the variable's
successor, is its arrow after the successor on the variable. -/
theorem natSuccAt_compile {ks : ℕ} (hks : G.prims[ks]? = some succPrim) {X W B : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ n X e')
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, B)) :
    ∃ q, compile G n (natSuccAt ks w) (prod X nat) (extEnv X nat e') = some q ∧
      ResEq M ρ (comp W (pair (fst X nat) (comp succ (snd X nat))), B) q :=
  atVar0_compile hM hG hρ hps hds he' isTy_nat isTy_nat (succ_hom hM) hw
    (compile_succT hks (compile_var_iff.mpr ⟨rfl, rfl⟩))

/-- An induction's step at a term's value, in the environment extended by a natural number
variable, is the step's arrow after the parameters paired with the term's arrow. -/
theorem natStepAt {X W S C : Tree} {e' : List (Tree × Tree)} {w s : Term}
    (he' : EnvHom M ρ n X e') (hCt : IsTy n C = true)
    (hS : compile G n s (prod X C) (extEnv X C e') = some (S, C))
    (hw : compile G n w (prod X nat) (extEnv X nat e') = some (W, C)) :
    ∃ q, compile G n (Term.subst s (atVar0 w)) (prod X nat) (extEnv X nat e') = some q ∧
      ResEq M ρ (comp S (pair (fst X nat) W), C) q := by
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he'.1
  have hC := isObj_of_isTy hM hρ C hCt
  have hê := he'.ext hM hN isTy_nat
  have hfst := fst_hom hM hX hN
  have hWh : Hom M ρ W (prod X nat) C := (compile_hom hM hG hρ hps hds _ _ _ _ hw hê).1
  have hk₂ := pair_hom hM hfst hWh
  obtain ⟨q₂, hq₂, hr₂⟩ := compile_precomp hM hG hρ hps hds hS (he'.ext hM hC hCt) hk₂
    (e' := (W, C) :: precomp (fst X nat) e')
    (envEq_precomp_extEnv hM hX hC (fun p hp ↦ (he'.2 p hp).1) hk₂ (fst_pair hM hfst hWh)
      (snd_pair hM hfst hWh) (envEq_refl _))
  obtain ⟨q₃, hq₃, hr₃⟩ := compile_subst hM hG hρ hps hds s _ _ q₂ hq₂ (extEnv X nat e')
    (atVar0 w) hê fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (W, C) = p := by simpa using hp
        exact ⟨_, hw, ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
          ResEq.refl p⟩
  exact ⟨q₃, hq₃, hr₂.trans hr₃⟩

/-- Induction on the natural numbers, in the form of the uniqueness of recursion, is sound: an
equation, in a context of a natural number variable, whose sides agree at zero and are each, at
a successor, a step of their type applied to their value, holds, under hypotheses that do not
mention the variable. -/
theorem natInd_sound {kz ks : ℕ} (hkz : G.prims[kz]? = some zeroPrim)
    (hks : G.prims[ks]? = some succPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {t u s : Term} {C : Tree}
    (htC : typeIn G n (nat :: Γ') t = some C) (hsC : typeIn G n (C :: Γ') s = some C)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))))
    (p₁ : FmSound M ρ G n (nat :: Γ') Φ (Term.eq (natSuccAt ks t) (Term.subst s (atVar0 t))))
    (p₂ : FmSound M ρ G n (nat :: Γ') Φ (Term.eq (natSuccAt ks u) (Term.subst s (atVar0 u)))) :
    FmSound M ρ G n (nat :: Γ') Φ (Term.eq t u) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  have hx₀ : Hom M ρ x₀ X nat := (he.2 _ List.mem_cons_self).1
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he.1
  have hê : EnvHom M ρ n (prod X nat) (extEnv X nat e') := he'.ext hM hN isTy_nat
  have hêΓ : (extEnv X nat e').map Prod.snd = nat :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hΦê : HypsHold M ρ G n Φ (prod X nat) (extEnv X nat e') := by
    rw [(lowerHyps_spec hlow).1]
    exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hN
  -- the sides' type, and their arrows in the generic environment
  obtain ⟨f₀, hf₀⟩ := compile_of_typeIn htC (X := X) (e := (x₀, nat) :: e') (by simp [hΓ'])
  obtain rfl : A = C := (Prod.mk.inj (Option.some_inj.mp (ht.symm.trans hf₀))).2
  obtain ⟨F, hF⟩ := compile_retype t X _ _ ht (prod X nat) (extEnv X nat e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨G', hG'⟩ := compile_retype u X _ _ hu (prod X nat) (extEnv X nat e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨hFh, hCt⟩ := hty _ _ _ _ hF hê
  have hGh := (hty _ _ _ _ hG' hê).1
  -- the sides are their generic arrows at the variable
  obtain ⟨q, hq, hrq⟩ := natAt hM hG hρ hps hds he' hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans ht)
  obtain ⟨q', hq', hrq'⟩ := natAt hM hG hρ hps hds he' hG' hx₀
  obtain rfl := Option.some_inj.mp (hq'.symm.trans hu)
  -- at zero
  obtain ⟨z₁, hz₁, hrz₁⟩ := natZeroAt hM hG hρ hps hds hkz he' hF
  obtain ⟨z₂, hz₂, hrz₂⟩ := natZeroAt hM hG hρ hps hds hkz he' hG'
  have hz₁' := compile_resEq hz₁ hrz₁
  have hz₂' := compile_resEq hz₂ hrz₂
  have h₀ := (holds_eq_iff hM hG hρ hps hds he' hz₁' hz₂').mp
    (p₀ X e' he' hΓ' hΦ' _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hz₁', _, hz₂', rfl⟩))
  -- at a successor
  obtain ⟨S, hS⟩ := compile_of_typeIn hsC (X := prod X A) (e := extEnv X A e')
    (by simp [extEnv, hΓ', Function.comp_def])
  have hSh : Hom M ρ S (prod X A) A :=
    (hty _ _ _ _ hS (he'.ext hM (isObj_of_isTy hM hρ A hCt) hCt)).1
  have step : ∀ {w : Term} {W : Tree},
      compile G n w (prod X nat) (extEnv X nat e') = some (W, A) →
      FmSound M ρ G n (nat :: Γ') Φ (Term.eq (natSuccAt ks w) (Term.subst s (atVar0 w))) →
      eval M ρ (comp W (pair (fst X nat) (comp succ (snd X nat)))) =
        eval M ρ (comp S (pair (fst X nat) W)) := fun {w W} hw pw ↦ by
    obtain ⟨q₁, hq₁, hr₁⟩ := natSuccAt_compile hM hG hρ hps hds hks he' hw
    obtain ⟨q₃, hq₃, hr₃⟩ := natStepAt hM hG hρ hps hds he' hCt hS hw
    have hq₁' := compile_resEq hq₁ hr₁
    have hq₃' := compile_resEq hq₃ hr₃
    exact hr₁.2.symm.trans (((holds_eq_iff hM hG hρ hps hds hê hq₁' hq₃').mp
      (pw _ _ hê hêΓ hΦê _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hq₁', _, hq₃', rfl⟩))).trans
      hr₃.2)
  have hFG := natRec_param_unique hM hX hFh hGh hSh (hrz₁.2.symm.trans (h₀.trans hrz₂.2))
    (step hF p₁) (step hG' p₂)
  exact (holds_eq_iff hM hG hρ hps hds he hq hq').mpr
    (hrq.2.trans ((eval_op₂_congr 3 hFG rfl).trans hrq'.2.symm))

/-- Induction on the natural numbers with an induction hypothesis is sound: a formula, in a
context of a natural number variable, that holds at zero and, where it holds, at the successor,
holds, under hypotheses that do not mention the variable. -/
theorem natIndHyp_sound {kz ks : ℕ} (hkz : G.prims[kz]? = some zeroPrim)
    (hks : G.prims[ks]? = some succPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {φ : Term}
    (hφ : typeIn G n (nat :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))))
    (p₁ : FmSound M ρ G n (nat :: Γ') (Φ ++ [φ]) (natSuccAt ks φ)) :
    FmSound M ρ G n (nat :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  have hx₀ : Hom M ρ x₀ X nat := (he.2 _ List.mem_cons_self).1
  have hN := isObj_nat (ρ := ρ) hM
  have hX := he.1
  have hê : EnvHom M ρ n (prod X nat) (extEnv X nat e') := he'.ext hM hN isTy_nat
  have hêΓ : (extEnv X nat e').map Prod.snd = nat :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hΦê : HypsHold M ρ G n Φ (prod X nat) (extEnv X nat e') := by
    rw [(lowerHyps_spec hlow).1]
    exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hN
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X nat) hêΓ
  have hFh : Hom M ρ F (prod X nat) omega := (compile_hom hM hG hρ hps hds _ _ _ _ hF hê).1
  -- at zero
  obtain ⟨z, hz, hrz⟩ := natZeroAt hM hG hρ hps hds hkz he' hF
  have h₀ := hrz.2.symm.trans (p₀ X e' he' hΓ' hΦ' _ hz).2
  -- at the successor, on the pullback of truth along the formula
  obtain ⟨hi, hFi⟩ := truthIncl_hom hM hFh
  have hE₁ := envHom_precomp hM hê hi
  have hE₁Γ : (precomp (truthIncl F) (extEnv X nat e')).map Prod.snd = nat :: Γ' := by
    simp [precomp, Function.comp_def, ← hêΓ]
  obtain ⟨r₁, hr₁, hr₁₂, hr₁₁⟩ := compile_precomp hM hG hρ hps hds hF hê hi (envEq_refl _)
  have hH₁ : HypsHold M ρ G n (Φ ++ [φ]) (truthEq F)
      (precomp (truthIncl F) (extEnv X nat e')) :=
    (hypsHold_append M ρ).mpr ⟨hypsHold_precomp hM hG hρ hps hds hΦê hê hi (envEq_refl _),
      r₁, hr₁, hr₁₂, hr₁₁.trans hFi⟩
  obtain ⟨q₁, hq₁, hrq₁⟩ := natSuccAt_compile hM hG hρ hps hds hks he' hF
  obtain ⟨q₂, hq₂, -, hq₂₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hq₁ hrq₁) hê hi (envEq_refl _)
  have h₁ := (eval_op₂_congr 3 hrq₁.2.symm rfl).trans
    (hq₂₁.symm.trans (p₁ _ _ hE₁ hE₁Γ hH₁ q₂ hq₂).2)
  have hFtrue := truth_of_natInd hM hX hFh h₀ h₁
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := natAt hM hG hρ hps hds he' hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 hFtrue rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

/-- Case analysis on a coproduct is sound: a formula, in a context of a variable of a coproduct
type, that holds at the left injection of a variable of the first summand and at the right
injection of a variable of the second holds, under hypotheses that do not mention the
variable. -/
theorem coprodInd_sound {kl kr : ℕ} (hkl : G.prims[kl]? = some inlPrim)
    (hkr : G.prims[kr]? = some inrPrim) {a b : Tree} {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {φ : Term}
    (hφ : typeIn G n (coprod a b :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n (a :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kl [a, b] (Term.var 0)))))
    (p₁ : FmSound M ρ G n (b :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kr [a, b] (Term.var 0))))) :
    FmSound M ρ G n (coprod a b :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, D⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hDt⟩ := he.2 _ List.mem_cons_self
  have hab := hDt
  rw [isTy_coprod, Bool.and_eq_true] at hab
  obtain ⟨hat, hbt⟩ := hab
  have hA := isObj_of_isTy hM hρ a hat
  have hB := isObj_of_isTy hM hρ b hbt
  have hX := he.1
  have hP := isObj_prod hM hX (isObj_coprod hM hA hB)
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X (coprod a b))
    (by simp [extEnv, hΓ', Function.comp_def] : (extEnv X (coprod a b) e').map Prod.snd = _)
  have hFh : Hom M ρ F (prod X (coprod a b)) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hF (he'.ext hM (isObj_coprod hM hA hB) hDt)).1
  -- the formula holds at each injection, where it is its arrow after the product of the
  -- environment's object with the injection
  have side : ∀ {k c i}, IsTy n c = true → Hom M ρ i c (coprod a b) →
      compile G n (Term.arr k [a, b] (Term.var 0)) (prod X c) (extEnv X c e') =
        some (comp i (snd X c), coprod a b) →
      FmSound M ρ G n (c :: Γ') Φ (Term.subst φ (atVar0 (Term.arr k [a, b] (Term.var 0)))) →
      eval M ρ (comp F (pair (fst X c) (comp i (snd X c)))) =
        eval M ρ (comp (comp tru (bang (prod X (coprod a b))))
          (pair (fst X c) (comp i (snd X c)))) := by
    intro k c i hct hi hu p
    have hC := hi.isObj_dom
    obtain ⟨q, hq, hrq⟩ := atVar0_compile hM hG hρ hps hds he' hct hDt hi hF hu
    have hΦc : HypsHold M ρ G n Φ (prod X c) (extEnv X c e') := by
      rw [(lowerHyps_spec hlow).1]
      exact hypsHold_weaken1 hM hG hρ hps hds hΦ' he' hC
    have hH := p _ _ (he'.ext hM hC hct) (by simp [extEnv, hΓ', Function.comp_def]) hΦc q hq
    exact hrq.2.symm.trans (hH.2.trans (truth_comp hM (pair_hom hM (fst_hom hM hX hC)
      (comp_hom hM (snd_hom hM hX hC) hi))).symm)
  have hθ : [a, b].all (IsTy n) = true := by simp [hat, hbt]
  have hFtrue := prod_coprod_ext hM hX hA hB hFh
    (comp_hom hM (bang_hom hM hP) (tru_hom hM))
    (side hat (inl_hom hM hA hB) (compile_arr_iff.mpr ⟨_, rfl, inlPrim, hkl, snd X a,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl, hθ, rfl⟩) p₀)
    (side hbt (inr_hom hM hA hB) (compile_arr_iff.mpr ⟨_, rfl, inrPrim, hkr, snd X b,
      compile_var_iff.mpr ⟨rfl, rfl⟩, rfl, hθ, rfl⟩) p₁)
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := compile_at hM hG hρ hps hds he' hDt hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 hFtrue rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

/-- A formula in a context with a variable of the initial type holds: the environment's object
has an arrow to the initial object, and is initial. -/
theorem zeroInd_sound {i : ℕ} {Γ : List Tree} {Φ : List Term} {φ : Term}
    (hi : Γ[i]? = some zero) (hφ : typeIn G n Γ φ = some omega) : FmSound M ρ G n Γ Φ φ := by
  intro X e he hΓ _ r hr
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := X) hΓ
  obtain rfl := Option.some_inj.mp (hF.symm.trans hr)
  rw [← hΓ, List.getElem?_map, Option.map_eq_some_iff] at hi
  obtain ⟨p, hp, hpz⟩ := hi
  exact ⟨rfl, eq_of_hom_zero hM (hpz ▸ (he.2 p (List.mem_of_getElem? hp)).1)
    (compile_hom hM hG hρ hps hds _ _ _ _ hF he).1 (comp_hom hM (bang_hom hM he.1) (tru_hom hM))⟩

/-- A term in the environment extended by a list variable, at an element of the list object, is
its arrow there after the pairing of the identity with the element. -/
theorem listAt {X x W B a : Tree} {e' : List (Tree × Tree)} {w : Term}
    (he' : EnvHom M ρ n X e') (hat : IsTy n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B))
    (hx : Hom M ρ x X (list a)) :
    ∃ q, compile G n w X ((x, list a) :: e') = some q ∧
      ResEq M ρ (comp W (pair (idt X) x), B) q :=
  compile_at hM hG hρ hps hds he' (by simpa [isTy_list] using hat) hw hx

/-- A term in the environment extended by a list variable, at the empty list, is its arrow there
after the pairing of the identity with the empty list. -/
theorem listNilAt {kn : ℕ} (hkn : G.prims[kn]? = some nilPrim) {X W B a : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ n X e') (hat : IsTy n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B)) :
    ∃ q, compile G n (Term.subst w (instVar (Term.arr kn [a] Term.star))) X e' = some q ∧
      ResEq M ρ (comp W (pair (idt X) (comp (nil a) (bang X))), B) q := by
  obtain ⟨q₀, hq₀, hr₀⟩ := listAt hM hG hρ hps hds he' hat hw
    (comp_hom hM (bang_hom hM he'.1) (nil_hom hM (isObj_of_isTy hM hρ a hat)))
  obtain ⟨q₁, hq₁, hr₁⟩ := compile_subst hM hG hρ hps hds w X _ q₀ hq₀ e'
    (instVar (Term.arr kn [a] Term.star)) he' fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp (nil a) (bang X), list a) = p := by simpa using hp
        exact ⟨_, compile_nilT hkn hat X e', ResEq.refl _⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa using hp⟩, ResEq.refl p⟩
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a list variable, at a construction of a new element
onto the variable, is its arrow after construction. -/
theorem listConsAt_compile {kc : ℕ} (hkc : G.prims[kc]? = some consPrim) {X W B a : Tree}
    {e' : List (Tree × Tree)} {w : Term} (he' : EnvHom M ρ n X e') (hat : IsTy n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B)) :
    ∃ q, compile G n (listConsAt kc a w) (prod (prod X a) (list a))
        (extEnv (prod X a) (list a) (extEnv X a e')) = some q ∧
      ResEq M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
        (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
          (snd (prod X a) (list a))))), B) q := by
  have hX := he'.1
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hLt : IsTy n (list a) = true := by simpa [isTy_list] using hat
  have hea := he'.ext hM hA hat
  have hXa := hea.1
  have hê₁ := hea.ext hM hL hLt
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hfXa := fst_hom hM hX hA
  have hff := comp_hom hM hfQ hfXa
  have hsf := comp_hom hM hfQ (snd_hom hM hX hA)
  have hcel := comp_hom hM (pair_hom hM hsf hsQ) (cons_hom hM hA)
  have hk₁ := pair_hom hM hff hcel
  have he'h : ∀ p ∈ e', Hom M ρ p.1 X p.2 := fun p hp ↦ (he'.2 p hp).1
  obtain ⟨q₀, hq₀, hr₀⟩ := compile_precomp hM hG hρ hps hds hw (he'.ext hM hL hLt) hk₁
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
  exact ⟨q₁, hq₁, hr₀.trans hr₁⟩

/-- A term in the environment extended by a list variable, weakened past a new element, is its
arrow after the pairing of the parameters with the tail. -/
theorem weakenElemAt {X W B a : Tree} {e' : List (Tree × Tree)} {w : Term}
    (he' : EnvHom M ρ n X e') (hat : IsTy n a = true)
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, B)) :
    ∃ q, compile G n (weakenElem w) (prod (prod X a) (list a))
        (extEnv (prod X a) (list a) (extEnv X a e')) = some q ∧
      ResEq M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
        (snd (prod X a) (list a))), B) q := by
  have hX := he'.1
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hLt : IsTy n (list a) = true := by simpa [isTy_list] using hat
  have hXa := (he'.ext hM hA hat).1
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hfXa := fst_hom hM hX hA
  have hff := comp_hom hM hfQ hfXa
  have hk₂ := pair_hom hM hff hsQ
  have he'h : ∀ p ∈ e', Hom M ρ p.1 X p.2 := fun p hp ↦ (he'.2 p hp).1
  obtain ⟨q₂, hq₂, hr₂⟩ := compile_precomp hM hG hρ hps hds hw (he'.ext hM hL hLt) hk₂
    (e' := (snd (prod X a) (list a), list a) ::
      precomp (fst (prod X a) (list a)) (precomp (fst X a) e'))
    (envEq_precomp_extEnv hM hX hL he'h hk₂ (fst_pair hM hff hsQ) (snd_pair hM hff hsQ)
      (envEq_precomp_comp hM he'h hfXa hfQ))
  exact ⟨q₂, compile_rename w _ (extEnv (prod X a) (list a) (extEnv X a e')) _
    (fun i ↦ match i with
      | 0 => 0
      | j + 1 => j + 2) q₂ hq₂ fun i _ ↦ by
      rcases i with _ | j
      · rfl
      · simp [extEnv, precomp], hr₂⟩

/-- An induction's step at the element and a term's value at the tail, in the environment
extended by a list variable and a new element, is the step's arrow after the parameters and
the element paired with the term's arrow at the tail. -/
theorem listStepAt {X W S C a : Tree} {e' : List (Tree × Tree)} {w s : Term}
    (he' : EnvHom M ρ n X e') (hat : IsTy n a = true) (hCt : IsTy n C = true)
    (hS : compile G n s (prod (prod X a) C) (extEnv (prod X a) C (extEnv X a e')) = some (S, C))
    (hw : compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, C)) :
    ∃ q, compile G n (Term.subst s (atVar0 (weakenElem w))) (prod (prod X a) (list a))
        (extEnv (prod X a) (list a) (extEnv X a e')) = some q ∧
      ResEq M ρ (comp S (pair (fst (prod X a) (list a)) (comp W
        (pair (comp (fst X a) (fst (prod X a) (list a))) (snd (prod X a) (list a))))), C) q := by
  have hX := he'.1
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hC := isObj_of_isTy hM hρ C hCt
  have hLt : IsTy n (list a) = true := by simpa [isTy_list] using hat
  have hea := he'.ext hM hA hat
  have hXa := hea.1
  have hê₁ := hea.ext hM hL hLt
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hk₂ := pair_hom hM (comp_hom hM hfQ (fst_hom hM hX hA)) hsQ
  have hWh : Hom M ρ W (prod X (list a)) C :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hw (he'.ext hM hL hLt)).1
  obtain ⟨q₂, hq₂, hr₂⟩ := weakenElemAt hM hG hρ hps hds he' hat hw
  have hk₃ := pair_hom hM hfQ (comp_hom hM hk₂ hWh)
  obtain ⟨q₃, hq₃, hr₃⟩ := compile_precomp hM hG hρ hps hds hS (hea.ext hM hC hCt) hk₃
    (e' := (comp W (pair (comp (fst X a) (fst (prod X a) (list a))) (snd (prod X a) (list a))),
      C) :: precomp (fst (prod X a) (list a)) (extEnv X a e'))
    (envEq_precomp_extEnv hM hXa hC (fun p hp ↦ (hea.2 p hp).1) hk₃
      (fst_pair hM hfQ (comp_hom hM hk₂ hWh)) (snd_pair hM hfQ (comp_hom hM hk₂ hWh))
      (envEq_refl _))
  obtain ⟨q₄, hq₄, hr₄⟩ := compile_subst hM hG hρ hps hds s _ _ q₃ hq₃
    (extEnv (prod X a) (list a) (extEnv X a e')) (atVar0 (weakenElem w)) hê₁ fun i p hp ↦ by
      rcases i with _ | j
      · obtain rfl : (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a))), C) = p := by simpa using hp
        exact ⟨_, hq₂, hr₂⟩
      · exact ⟨p, compile_var_iff.mpr ⟨rfl, by simpa [extEnv, precomp] using hp⟩,
          ResEq.refl p⟩
  exact ⟨q₄, hq₄, hr₃.trans hr₄⟩

/-- Hypotheses that hold in an environment hold, weakened past two variables, in its extension
by an element and a list. -/
theorem hypsHold_weaken2 {Φ : List Term} {X a : Tree} {e' : List (Tree × Tree)}
    (hΦ : HypsHold M ρ G n Φ X e') (he' : EnvHom M ρ n X e') (hat : IsTy n a = true) :
    HypsHold M ρ G n (Φ.map weaken2) (prod (prod X a) (list a))
      (extEnv (prod X a) (list a) (extEnv X a e')) := by
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hXa := (he'.ext hM hA hat).1
  have hfQ := fst_hom hM hXa hL
  have hfXa := fst_hom hM he'.1 hA
  exact hypsHold_rename hM hG hρ hps hds hΦ he' (comp_hom hM hfQ hfXa)
    (envEq_precomp_comp hM (fun p hp ↦ (he'.2 p hp).1) hfXa hfQ) fun i _ ↦ by
      simp [extEnv, precomp]

/-- Induction on a list type, in the form of the uniqueness of recursion, is sound: an equation,
in a context of a list variable, whose sides agree at the empty list and are each, at a
construction, a step of their type applied to the element and their value at the tail, holds,
under hypotheses that do not mention the variable. -/
theorem listInd_sound {kn kc : ℕ} (hkn : G.prims[kn]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {a : Tree} {t u s : Term} {C : Tree}
    (htC : typeIn G n (list a :: Γ') t = some C) (hsC : typeIn G n (C :: a :: Γ') s = some C)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))))
    (p₁ : FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2)
      (Term.eq (listConsAt kc a t) (Term.subst s (atVar0 (weakenElem t)))))
    (p₂ : FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2)
      (Term.eq (listConsAt kc a u) (Term.subst s (atVar0 (weakenElem u))))) :
    FmSound M ρ G n (list a :: Γ') Φ (Term.eq t u) := by
  intro X e he hΓ hΦ r hr
  obtain ⟨t', u', htu, f, A, ht, g, hu, rfl⟩ := compile_eq_iff.mp hr
  simp only [List.cons.injEq, and_true] at htu
  obtain ⟨rfl, rfl⟩ := htu
  have hty := compile_hom hM hG hρ hps hds
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hLt⟩ := he.2 _ List.mem_cons_self
  have hat : IsTy n a = true := by simpa [isTy_list] using hLt
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hX := he.1
  have hê : EnvHom M ρ n (prod X (list a)) (extEnv X (list a) e') := he'.ext hM hL hLt
  have hêΓ : (extEnv X (list a) e').map Prod.snd = list a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hê₁ := (he'.ext hM hA hat).ext hM hL hLt
  have hê₁Γ : (extEnv (prod X a) (list a) (extEnv X a e')).map Prod.snd = list a :: a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ₁ := hypsHold_weaken2 hM hG hρ hps hds hΦ' he' hat
  -- the sides' type, and their arrows in the generic environment
  obtain ⟨f₀, hf₀⟩ := compile_of_typeIn htC (X := X) (e := (x₀, list a) :: e') (by simp [hΓ'])
  obtain rfl : A = C := (Prod.mk.inj (Option.some_inj.mp (ht.symm.trans hf₀))).2
  obtain ⟨F, hF⟩ := compile_retype t X _ _ ht (prod X (list a)) (extEnv X (list a) e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨G', hG'⟩ := compile_retype u X _ _ hu (prod X (list a)) (extEnv X (list a) e')
    (by simp [hêΓ, hΓ'])
  obtain ⟨hFh, hCt⟩ := hty _ _ _ _ hF hê
  have hGh := (hty _ _ _ _ hG' hê).1
  -- the sides are their generic arrows at the variable
  obtain ⟨q, hq, hrq⟩ := listAt hM hG hρ hps hds he' hat hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans ht)
  obtain ⟨q', hq', hrq'⟩ := listAt hM hG hρ hps hds he' hat hG' hx₀
  obtain rfl := Option.some_inj.mp (hq'.symm.trans hu)
  -- at the empty list
  obtain ⟨z₁, hz₁, hrz₁⟩ := listNilAt hM hG hρ hps hds hkn he' hat hF
  obtain ⟨z₂, hz₂, hrz₂⟩ := listNilAt hM hG hρ hps hds hkn he' hat hG'
  have hz₁' := compile_resEq hz₁ hrz₁
  have hz₂' := compile_resEq hz₂ hrz₂
  have h₀ := (holds_eq_iff hM hG hρ hps hds he' hz₁' hz₂').mp
    (p₀ X e' he' hΓ' hΦ' _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hz₁', _, hz₂', rfl⟩))
  -- at a construction
  obtain ⟨S, hS⟩ := compile_of_typeIn hsC (X := prod (prod X a) A)
    (e := extEnv (prod X a) A (extEnv X a e')) (by simp [extEnv, hΓ', Function.comp_def])
  have hSh : Hom M ρ S (prod (prod X a) A) A :=
    (hty _ _ _ _ hS ((he'.ext hM hA hat).ext hM (isObj_of_isTy hM hρ A hCt) hCt)).1
  have step : ∀ {w : Term} {W : Tree},
      compile G n w (prod X (list a)) (extEnv X (list a) e') = some (W, A) →
      FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2)
        (Term.eq (listConsAt kc a w) (Term.subst s (atVar0 (weakenElem w)))) →
      eval M ρ (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
          (comp (cons a) (pair (comp (snd X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a)))))) =
        eval M ρ (comp S (pair (fst (prod X a) (list a))
          (comp W (pair (comp (fst X a) (fst (prod X a) (list a)))
            (snd (prod X a) (list a)))))) := fun {w W} hw pw ↦ by
    obtain ⟨q₁, hq₁, hr₁⟩ := listConsAt_compile hM hG hρ hps hds hkc he' hat hw
    obtain ⟨q₃, hq₃, hr₃⟩ := listStepAt hM hG hρ hps hds he' hat hCt hS hw
    have hq₁' := compile_resEq hq₁ hr₁
    have hq₃' := compile_resEq hq₃ hr₃
    exact hr₁.2.symm.trans (((holds_eq_iff hM hG hρ hps hds hê₁ hq₁' hq₃').mp
      (pw _ _ hê₁ hê₁Γ hΦ₁ _ (compile_eq_iff.mpr ⟨_, _, rfl, _, _, hq₁', _, hq₃', rfl⟩))).trans
      hr₃.2)
  have hFG := listRec_param_unique hM hX hA hFh hGh hSh (hrz₁.2.symm.trans (h₀.trans hrz₂.2))
    (step hF p₁) (step hG' p₂)
  exact (holds_eq_iff hM hG hρ hps hds he hq hq').mpr
    (hrq.2.trans ((eval_op₂_congr 3 hFG rfl).trans hrq'.2.symm))

/-- Induction on a list type with an induction hypothesis is sound: a formula, in a context of a
list variable, that holds at the empty list and, at a construction, where it holds at the tail,
holds, under hypotheses that do not mention the variable. -/
theorem listIndHyp_sound {kn kc : ℕ} (hkn : G.prims[kn]? = some nilPrim)
    (hkc : G.prims[kc]? = some consPrim) {Γ' : List Tree} {Φ Φ' : List Term}
    (hlow : lowerHyps G n Γ' Φ = some Φ') {a : Tree} {φ : Term}
    (hφ : typeIn G n (list a :: Γ') φ = some omega)
    (p₀ : FmSound M ρ G n Γ' Φ' (Term.subst φ (instVar (Term.arr kn [a] Term.star))))
    (p₁ : FmSound M ρ G n (list a :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem φ])
      (listConsAt kc a φ)) :
    FmSound M ρ G n (list a :: Γ') Φ φ := by
  intro X e he hΓ hΦ r hr
  rcases e with _ | ⟨⟨x₀, N⟩, e'⟩
  · simp at hΓ
  simp only [List.map_cons, List.cons.injEq] at hΓ
  obtain ⟨rfl, hΓ'⟩ := hΓ
  have he' : EnvHom M ρ n X e' := ⟨he.1, fun p hp ↦ he.2 p (List.mem_cons_of_mem _ hp)⟩
  obtain ⟨hx₀, hLt⟩ := he.2 _ List.mem_cons_self
  have hat : IsTy n a = true := by simpa [isTy_list] using hLt
  have hA := isObj_of_isTy hM hρ a hat
  have hL := isObj_list hM hA
  have hX := he.1
  have hê : EnvHom M ρ n (prod X (list a)) (extEnv X (list a) e') := he'.ext hM hL hLt
  have hêΓ : (extEnv X (list a) e').map Prod.snd = list a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ' := hypsHold_lower hlow hΓ' hΦ
  have hea := he'.ext hM hA hat
  have hê₁ := hea.ext hM hL hLt
  have hê₁Γ : (extEnv (prod X a) (list a) (extEnv X a e')).map Prod.snd = list a :: a :: Γ' := by
    simp [extEnv, hΓ', Function.comp_def]
  have hΦ₁ := hypsHold_weaken2 hM hG hρ hps hds hΦ' he' hat
  obtain ⟨F, hF⟩ := compile_of_typeIn hφ (X := prod X (list a)) hêΓ
  have hFh : Hom M ρ F (prod X (list a)) omega :=
    (compile_hom hM hG hρ hps hds _ _ _ _ hF hê).1
  -- at the empty list
  obtain ⟨z, hz, hrz⟩ := listNilAt hM hG hρ hps hds hkn he' hat hF
  have h₀ := hrz.2.symm.trans (p₀ X e' he' hΓ' hΦ' _ hz).2
  -- at a construction, on the pullback of truth along the formula at the tail
  have hXa := hea.1
  have hfQ := fst_hom hM hXa hL
  have hsQ := snd_hom hM hXa hL
  have hk₂ := pair_hom hM (comp_hom hM hfQ (fst_hom hM hX hA)) hsQ
  have hFk₂ := comp_hom hM hk₂ hFh
  obtain ⟨hi, hFk₂i⟩ := truthIncl_hom hM hFk₂
  have hE₁ := envHom_precomp hM hê₁ hi
  have hE₁Γ : (precomp (truthIncl (comp F (pair (comp (fst X a) (fst (prod X a) (list a)))
      (snd (prod X a) (list a))))) (extEnv (prod X a) (list a) (extEnv X a e'))).map
        Prod.snd = list a :: a :: Γ' := by
    simp [precomp, Function.comp_def, ← hê₁Γ]
  obtain ⟨qw, hqw, hrqw⟩ := weakenElemAt hM hG hρ hps hds he' hat hF
  obtain ⟨r₁, hr₁, hr₁₂, hr₁₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hqw hrqw) hê₁ hi (envEq_refl _)
  have hH₁ := (hypsHold_append M ρ).mpr ⟨hypsHold_precomp hM hG hρ hps hds hΦ₁ hê₁ hi
    (envEq_refl _), r₁, hr₁, hr₁₂, hr₁₁.trans ((eval_op₂_congr 3 hrqw.2 rfl).trans hFk₂i)⟩
  obtain ⟨qc, hqc, hrqc⟩ := listConsAt_compile hM hG hρ hps hds hkc he' hat hF
  obtain ⟨q₂, hq₂, -, hq₂₁⟩ :=
    compile_precomp hM hG hρ hps hds (compile_resEq hqc hrqc) hê₁ hi (envEq_refl _)
  have h₁ := (eval_op₂_congr 3 hrqc.2.symm rfl).trans
    (hq₂₁.symm.trans (p₁ _ _ hE₁ hE₁Γ hH₁ q₂ hq₂).2)
  have hFtrue := truth_of_listInd hM hX hA hFh h₀ h₁
  -- the formula at the variable
  obtain ⟨q, hq, hrq⟩ := listAt hM hG hρ hps hds he' hat hF hx₀
  obtain rfl := Option.some_inj.mp (hq.symm.trans hr)
  exact ⟨hrq.1, hrq.2.trans ((eval_op₂_congr 3 hFtrue rfl).trans
    (truth_comp hM (pair_hom hM (idt_hom hM hX) hx₀)))⟩

omit hM hG hρ hps hds in
/-- A property of each pair of a zip of lists of one length is a property of the second list's
elements with some element of the first. -/
theorem exists_of_all_zip {α β : Type} {p : α × β → Bool} :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length → (l₁.zip l₂).all p = true →
      ∀ y ∈ l₂, ∃ x ∈ l₁, p (x, y) = true := fun l₁ l₂ hl h y hy ↦ by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  have hi' : i < l₁.length := hl ▸ hi
  refine ⟨l₁[i], List.getElem_mem hi', List.all_eq_true.mp h _ ?_⟩
  rw [List.mem_iff_getElem]
  exact ⟨i, by simp [hi, hi'], by simp⟩

/-- The checker is sound: every rewriting a derivation performs is sound, and every formula it
proves holds, with sound unfoldings and valid earlier theorems. -/
theorem check_sound (hδ : DefnsOk M G) {E : Array Thm}
    (hE : ∀ (j : ℕ) (a : Thm), E[j]? = some a → a.Valid M G) :
    ∀ d : Deriv, (∀ Γ Φ t t', (check G E n d).1 Γ Φ t = some t' → RwSound M ρ G n Γ Φ t t') ∧
      (∀ Γ Φ φ, (check G E n d).2 Γ Φ φ = true → FmSound M ρ G n Γ Φ φ) := by
  refine RoseTree.ind fun l cs ih ↦ ⟨fun Γ Φ t t' h ↦ ?_, fun Γ Φ φ h ↦ ?_⟩
  · rw [check_node] at h
    cases l
    case refl =>
      rcases cs with _ | ⟨c, cs⟩
      · obtain rfl : t = t' := Option.some_inj.mp h
        exact RwSound.refl Γ Φ t
      · simp [checkStep] at h
    case trans =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep, rootStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        obtain ⟨v, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
        exact ((ih c₁ (by simp)).1 _ _ _ _ h₁).trans ((ih c₂ (by simp)).1 _ _ _ _ h₂)
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
        (P := fun x : Deriv × Checks ↦ ∀ Γ Φ t t', x.2.1 Γ Φ t = some t' →
          RwSound M ρ G n Γ Φ t t')
        (R := fun x r ↦ x.1.2.1 x.2.1.1 x.2.1.2 x.2.2 = some r)
        (fun _ _ _ hx hR ↦ hx _ _ _ _ hR) _ _ _ (by simp [hlen.1, hlen.2])
        (fun x hx ↦ ?_) (forall₂_of_mapM _ hts')
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact (ih c hc).1
    all_goals
      rcases cs with _ | ⟨c, cs⟩
      · exact rootStep_sound hM hG hρ hps hds hδ hE
          (by simpa only [checkStep, List.map_nil] using h)
      · nomatch h
  · rw [check_node] at h
    cases l
    case join =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i t u htu
          split at h
          · rename_i v v' h₁ h₂
            obtain rfl := of_decide_eq_true h
            rw [eqParts_eq_some htu]
            exact join_sound hM hG hρ hps hds ((ih c₁ (by simp)).1 _ _ _ _ h₁)
              ((ih c₂ (by simp)).1 _ _ _ _ h₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case hyp i =>
      rcases cs with _ | ⟨c, cs⟩
      · exact hyp_sound (of_decide_eq_true h)
      · simp [checkStep] at h
    case cut ψ =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨hψ, hp⟩, hq⟩ := h
        exact cut_sound hψ ((ih c₁ (by simp)).2 _ _ _ hp) ((ih c₂ (by simp)).2 _ _ _ hq)
      · simp [checkStep] at h
    case conv =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i φ' hd
          exact conv_sound ((ih c₁ (by simp)).1 _ _ _ _ hd) ((ih c₂ (by simp)).2 _ _ _ h)
        · simp at h
      · simp [checkStep] at h
    case convFrom ψ =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil, Bool.and_eq_true,
          decide_eq_true_eq] at h
        obtain ⟨⟨hψ, hd⟩, hp⟩ := h
        exact convFrom_sound hψ ((ih c₁ (by simp)).1 _ _ _ _ hd) ((ih c₂ (by simp)).2 _ _ _ hp)
      · simp [checkStep] at h
    case propExt =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i α β hαβ
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h
          obtain ⟨⟨⟨hα, -⟩, hp⟩, hq⟩ := h
          rw [eqParts_eq_some hαβ]
          exact propExt_sound hM hG hρ hps hds hα ((ih c₁ (by simp)).2 _ _ _ hp)
            ((ih c₂ (by simp)).2 _ _ _ hq)
        · simp at h
      · simp [checkStep] at h
    case funExt =>
      rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · rename_i f g hfg
          split at h
          · rename_i a b hab
            rw [eqParts_eq_some hfg]
            exact funExt_sound hM hG hρ hps hds hab ((ih c₁ (by simp)).2 _ _ _ h)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case natInd kz ks s =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i t u c Γ' htu _ _ C Φ' hC hlow
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨rfl, hkz, hks, -, hsC⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
            rw [eqParts_eq_some htu]
            exact natInd_sound hM hG hρ hps hds hkz hks hlow hC hsC
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
              ((ih c₂ (by simp)).2 _ _ _ hp₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case listInd kn kc s =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i t u c Γ' htu _ _ _ C a Φ' hC ha hlow
            obtain rfl := listPart_eq_some.mp ha
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨⟨hkn, hkc, -, hsC⟩, hp₀⟩, hp₁⟩, hp₂⟩ := h
            rw [eqParts_eq_some htu]
            exact listInd_sound hM hG hρ hps hds hkn hkc hlow hC hsC
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
              ((ih c₂ (by simp)).2 _ _ _ hp₂)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case apply j θ σ =>
      simp only [checkStep] at h
      split at h
      · rename_i a ha
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨⟨hok, rfl⟩, hlen⟩, hall⟩ := h
        refine apply_sound hM hG hρ hps hds hE ha hok fun h hh ↦ ?_
        obtain ⟨x, hx, hxh⟩ := exists_of_all_zip _ _ hlen hall h hh
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        exact (ih c hc).2 _ _ _ hxh
      · simp at h
    case natIndHyp kz ks =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i c Γ' _ Φ' hlow
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨rfl, hkz, hks, hφ⟩, hp₀⟩, hp₁⟩ := h
            exact natIndHyp_sound hM hG hρ hps hds hkz hks hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case listIndHyp kn kc =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i c Γ' _ _ a Φ' ha hlow
            obtain rfl := listPart_eq_some.mp ha
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hkn, hkc, hφ⟩, hp₀⟩, hp₁⟩ := h
            exact listIndHyp_sound hM hG hρ hps hds hkn hkc hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case coprodInd kl kr =>
      rcases cs with _ | ⟨c₀, _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩⟩
      · simp [checkStep] at h
      · simp [checkStep] at h
      · simp only [checkStep, List.map_cons, List.map_nil] at h
        split at h
        · split at h
          · rename_i c Γ' _ _ a b Φ' hab hlow
            obtain rfl := coprodParts_eq_some.mp hab
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h
            obtain ⟨⟨⟨hkl, hkr, hφ⟩, hp₀⟩, hp₁⟩ := h
            exact coprodInd_sound hM hG hρ hps hds hkl hkr hlow hφ
              ((ih c₀ (by simp)).2 _ _ _ hp₀) ((ih c₁ (by simp)).2 _ _ _ hp₁)
          · simp at h
        · simp at h
      · simp [checkStep] at h
    case zeroInd i =>
      rcases cs with _ | ⟨c₀, cs⟩
      · simp only [checkStep, List.map_nil, decide_eq_true_eq] at h
        exact zeroInd_sound hM hG hρ hps hds h.1 h.2
      · simp [checkStep] at h
    all_goals simp [checkStep] at h

end Proofs

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
  simp only [Thm.checks, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hctx, hhyps⟩, hconcl⟩, hd⟩ := h
  exact ⟨hctx, fun h hh ↦ of_decide_eq_true (List.all_eq_true.mp hhyps h hh), hconcl,
    fun ρ hρ ↦ ⟨hps _ ρ hρ, hds _ ρ hρ,
      (check_sound hM hG hρ (hps _ ρ hρ) (hds _ ρ hρ) hδ hE d).2 _ _ _ hd⟩⟩

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

/-- The one-point model is a model of every well-formed extension of the theory. -/
theorem isModel_point_ext {pre cds : List PartialHorn.Defn}
    (hwf : PartialHorn.DefnsWF sig (pre ++ cds)) :
    IsModel (ext (pre ++ cds)) (PartialHorn.pointModel (ext (pre ++ cds)).sig) :=
  PartialHorn.isModel_point
    (PartialHorn.sidesSorted_extendAll (pre ++ cds) theory theory_sidesSorted hwf)

/-- The soundness of the internal language's derivations for the theory itself, for
equations: each equation proved without hypotheses in a development that checks has sides that
compile in its context to arrows of one type, whose equation, with every definition unfolded,
holds in every model of the theory, when the check accepts the constants and their definitions
are well formed. -/
theorem valid_unfoldAll_of_checkThms {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds))
    {ds : List (Thm × Deriv)} (h : checkThms G ds #[] = true) (p : Thm × Deriv) (hp : p ∈ ds)
    (hnil : p.1.hyps = []) {l r : Term} (hlr : eqParts p.1.concl = some (l, r)) :
    ∃ f g A, compile G p.1.arity l (ctxObj p.1.ctx) (stdEnv p.1.ctx) = some (f, A) ∧
      compile G p.1.arity r (ctxObj p.1.ctx) (stdEnv p.1.ctx) = some (g, A) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ cds)
          ⟨List.replicate p.1.arity obj, [], ⟨f, g⟩⟩).Valid M := by
  obtain ⟨hctx, -, hcon, -⟩ := valid_of_checkThms_ok (isModel_point_ext hwf) hbase hok hc h p hp
  obtain ⟨⟨C, C'⟩, hC, -⟩ := Option.map_eq_some_iff.mp hcon
  rw [eqParts_eq_some hlr] at hC
  obtain ⟨l', r', hlr', f, A, hf, g, hg, -⟩ := compile_eq_iff.mp hC
  simp only [List.cons.injEq, and_true] at hlr'
  obtain ⟨rfl, rfl⟩ := hlr'
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
    obtain ⟨-, -, -, hv⟩ := valid_of_checkThms_ok hN hbase hok hc h p hp
    obtain ⟨hpsN, hdsN, hfN⟩ := hv ρ hρ
    have hstd := stdEnv_hom hN hρ _ hctx
    have hH := hfN _ _ hstd (map_snd_stdEnv _) (by rw [hnil]; exact fun _ h ↦ by simp at h) _
      (by rw [eqParts_eq_some hlr]; exact compile_eq_iff.mpr ⟨_, _, rfl, f, A, hf, g, hg, rfl⟩)
    have heq := (holds_eq_iff hN hG hρ hpsN hdsN hstd hf hg).mp hH
    obtain ⟨w, hw, -⟩ := (compile_hom hN hG hρ hpsN hdsN _ _ _ _ hf hstd).1.exists_eval
    exact ⟨w, hw, heq.symm.trans hw⟩

/-- The soundness of the internal language's derivations for the theory itself, for formulas:
each formula proved without hypotheses in a development that checks compiles in its context to
an arrow that, with every definition unfolded, is true in every model of the theory, when the
check accepts the constants and their definitions are well formed. -/
theorem valid_unfoldAll_holds_of_checkThms {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds))
    {ds : List (Thm × Deriv)} (h : checkThms G ds #[] = true) (p : Thm × Deriv) (hp : p ∈ ds)
    (hnil : p.1.hyps = []) :
    ∃ C, compile G p.1.arity p.1.concl (ctxObj p.1.ctx) (stdEnv p.1.ctx) = some (C, omega) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ cds)
          ⟨List.replicate p.1.arity obj, [], ⟨C, comp tru (bang (ctxObj p.1.ctx))⟩⟩).Valid M := by
  obtain ⟨hctx, -, hcon, -⟩ := valid_of_checkThms_ok (isModel_point_ext hwf) hbase hok hc h p hp
  obtain ⟨⟨C, C'⟩, hC, hC'⟩ := Option.map_eq_some_iff.mp hcon
  obtain rfl : C' = omega := hC'
  refine ⟨C, hC, fun M hM ↦ ?_⟩
  have hG := Globals.wf_of_ok hok
  have hsC := (compile_sortOf (defs := pre ++ cds) hG (fun k p hp ↦ sortOf_prims_of_ok hok hp)
    (fun k d hd ↦ getElem?_sig_compileDefs hbase hc hd) _ _ _ _ hC (sortOf_ctxObj _ hctx)
    (sortOf_stdEnv _ hctx)).1
  refine PartialHorn.valid_unfoldAll (pre ++ cds) theory M hM theory_ofSig hwf _ ?_ ?_
  · intro q hq
    obtain rfl : q = ⟨C, comp tru (bang (ctxObj p.1.ctx))⟩ := by simpa using hq
    exact ⟨⟨arr, hsC⟩, ⟨arr, sortOf_comp (sortOf_op rfl rfl)
      (sortOf_bang (sortOf_ctxObj _ hctx))⟩⟩
  · intro N hN ρ hρ _
    obtain ⟨-, -, -, hv⟩ := valid_of_checkThms_ok hN hbase hok hc h p hp
    obtain ⟨-, -, hfN⟩ := hv ρ hρ
    have hstd := stdEnv_hom hN hρ _ hctx
    have hH := hfN _ _ hstd (map_snd_stdEnv _) (by rw [hnil]; exact fun _ h ↦ by simp at h) _ hC
    obtain ⟨w, hw, -⟩ := (truth_hom hN hstd.1).exists_eval
    exact ⟨w, hH.2.trans hw, hw⟩

end Geb.FreeTopos.Internal

end
