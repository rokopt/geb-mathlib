/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Sorting
public import Geb.Prototypes.PartialHorn.Point
public import Geb.Prototypes.FreeTopos.Internal.Substitution
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Unfolding the definitions and the compilation

Compiling a term of the internal language, whose definitions compile to definitions of the
combinators, agrees with unfolding its definitions in the language and compiling the result: in
every model of the theory extended by the combinators' definitions, the unfolded term has the
term's type and an arrow of the same value ({lit}`compile_unfold`). The compiled arrows are well
sorted ({name}`Geb.FreeTopos.Internal.compile_sortOf`), so that by eliminability
({name}`Geb.PartialHorn.valid_unfoldAll`) the unfoldings of the combinators' definitions in the
two arrows have one value in every model of the theory ({lit}`valid_unfoldAll_compile`).

The two do not give one term. Unfolding in the language substitutes the arguments for the
definition's parameters, where the compiled application composes the definition's arrow with the
tuple of the arguments' arrows; the proof meets them by the substitution lemma
({name}`Geb.FreeTopos.Internal.compile_subst`), naturality along the tuple, and the projections
after a tuple ({lit}`proj_tuple`). It proceeds over the definitions in order
({lit}`defsInv`): the operation of each is an arrow, by the soundness of its compiled body's
typing, and its unfolded body compiles to the operation's value, by the square for the
definitions before it.

## Main definitions

* {lit}`UbsOk` — the unfolded bodies compile to the definitions' values.
* {lit}`DefsInv` — the invariant over an initial segment of the definitions.

## Main statements

* {lit}`compile_mono` — the compilation is monotone in the definitions.
* {lit}`compile_unfold_of` — the square, given the definitions' invariant.
* {lit}`compile_unfold`, {lit}`compile_unfold_of_ok` — the square.
* {lit}`compile_unfold_some` — the unfolding of a term that compiles compiles.
* {lit}`valid_unfoldAll_compile` — the square for the definition-free arrows, in every model of
  the theory.

## Tags

internal language, definition, unfolding, compilation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op eval Model IsModel)
open Sorts
open scoped FinEnum

universe v

/-- The constants of {lit}`G` are among those of {lit}`G'`: the same primitive arrows and base,
and the definitions an initial segment. -/
def Globals.Le (G G' : Globals) : Prop :=
  G.prims = G'.prims ∧ G.base = G'.base ∧ ∃ ds, G'.defs = G.defs ++ ds

/-- A term compiles to the same arrow and type with more definitions. -/
theorem compile_mono {G G' : Globals} (hle : G.Le G') {n : ℕ} (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      compile G' n s X e = some r := by
  obtain ⟨hp, hb, ds, hds⟩ := hle
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → compile G' n s X e = some r) (fun l cs ih ↦ ?_) s
  intro X e r h
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    exact compile_var_iff.mpr ⟨rfl, hi⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    exact compile_star_iff.mpr ⟨rfl, rfl⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    exact compile_pair_iff.mpr ⟨t, u, f, a, g, b, rfl, ih t (by simp) X e _ ht,
      ih u (by simp) X e _ hu, rfl⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    exact compile_fst_iff.mpr ⟨t, f, a, b, rfl, ih t (by simp) X e _ ht, rfl⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    exact compile_snd_iff.mpr ⟨t, f, a, b, rfl, ih t (by simp) X e _ ht, rfl⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    exact compile_lam_iff.mpr ⟨t, f, b, rfl, hat, ih t (by simp) _ _ _ ht, rfl⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    exact compile_app_iff.mpr ⟨t, u, rfl, f, a, b, ih t (by simp) X e _ ht, g,
      ih u (by simp) X e _ hu, rfl⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hpk, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    exact compile_arr_iff.mpr ⟨t, rfl, p, hp ▸ hpk, g, ih t (by simp) X e _ ht, hl, hθ, rfl⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    exact compile_natRec_iff.mpr ⟨z, s, m, rfl, z', c, ih z (by simp) _ _ _ hz, s',
      ih s (by simp) _ _ _ hs, m', ih m (by simp) X e _ hm, rfl⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    exact compile_listRec_iff.mpr ⟨z, s, m, rfl, m', a, ih m (by simp) X e _ hm, z', c,
      ih z (by simp) _ _ _ hz, s', ih s (by simp) _ _ _ hs, rfl⟩
  | roseRec c =>
    obtain ⟨s, m, s', m', rfl, hc, hs, hm, rfl⟩ := compile_roseRec_iff.mp h
    exact compile_roseRec_iff.mpr ⟨s, m, s', m', rfl, hc, ih s (by simp) _ _ _ hs,
      ih m (by simp) X e _ hm, rfl⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    exact compile_eq_iff.mpr ⟨t, u, rfl, f, a, ih t (by simp) X e _ ht, g,
      ih u (by simp) X e _ hu, rfl⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, hty, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (R := Eq) (g := fun c ↦ compile G' n c X e) cs hrs
      fun c hc r hr ↦ ⟨r, ih c hc X e r hr, rfl⟩
    rw [List.forall₂_eq_eq_eq] at hR
    subst hR
    have hd' : G'.defs[k]? = some d := by
      rw [hds, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hd).1]
      exact hd
    exact hb ▸ compile_defn_iff.mpr ⟨d, rs, hd', hrs', hl, hθ, hty, rfl⟩

/-- The unfolding of an application of a definition that has an unfolded body. -/
theorem unfold_defn {ubs : List Term} {k : ℕ} {θ : List Tree} {cs : List Term} {ub : Term}
    (hub : ubs[k]? = some ub) : unfold ubs (RoseTree.node (.defn k θ) cs) =
      Term.subst (Term.osubst θ ub) (Term.substList (cs.map (unfold ubs))) := by
  simp [unfold, RoseTree.elim_node, hub]

/-- The unfolding of a node of any other label unfolds its children. -/
theorem unfold_node {ubs : List Term} {l : Label} (hl : ∀ k θ, l ≠ .defn k θ)
    (cs : List Term) : unfold ubs (RoseTree.node l cs) = RoseTree.node l (cs.map (unfold ubs)) := by
  rw [unfold, RoseTree.elim_node]
  cases l <;> first | rfl | exact (hl _ _ rfl).elim

/-- A result of a partial function over a list is its value at the element of the same
position. -/
theorem getElem?_of_mapM {α β : Type} {f : α → Option β} {l : List α} {rs : List β}
    (h : l.mapM f = some rs) {i : ℕ} {a : α} (ha : l[i]? = some a) :
    ∃ r, rs[i]? = some r ∧ f a = some r := by
  rw [PartialHorn.mapM_eq_some_iff] at h
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map, ha, Option.map_some] at hi
  obtain ⟨r, hr, hfr⟩ := Option.map_eq_some_iff.mp hi.symm
  exact ⟨r, hr, hfr.symm⟩

section Square

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}

variable (M) in
/-- Each definition of {lit}`G` has an unfolded body in {lit}`ubs`, which compiles in its
parameters' environment to its value's type and an arrow that has, at types substituted for its
object parameters, the value of the definition's operation at them. -/
def UbsOk (G : Globals) (ubs : List Term) : Prop :=
  ∀ (k : ℕ) (d : Defn), G.defs[k]? = some d → ∃ ub, ubs[k]? = some ub ∧
    ∀ (m : ℕ) (ρ : List M.Val) (θ : List Tree), ρ.map Sigma.fst = List.replicate m obj →
      θ.length = d.arity → θ.all (IsTy m) = true →
      ∃ F, compile G d.arity ub (ctxObj d.params) (stdEnv d.params) = some (F, d.type) ∧
        eval M ρ (PartialHorn.subst θ F) = eval M ρ (op (G.base + k) θ)

variable (hM : IsModel (ext defs) M)
include hM

/-- A context's environment of projections is an environment of arrows. -/
theorem stdEnv_hom {ρ : List M.Val} {n : ℕ} (hρ : ρ.map Sigma.fst = List.replicate n obj) :
    ∀ Γ : List Tree, Γ.all (IsTy n) = true → EnvHom M ρ n (ctxObj Γ) (stdEnv Γ) :=
  List.rec (fun _ ↦ ⟨isObj_one hM, by simp [stdEnv]⟩) fun a Γ ih h ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hA := isObj_of_isTy hM hρ a h.1
    rcases Γ with _ | ⟨b, Γ⟩
    · exact ⟨hA, by simpa [stdEnv] using ⟨idt_hom hM hA, h.1⟩⟩
    · exact (ih h.2).ext hM hA h.1

/-- The projections of a context after a tuple of arrows of its types are the arrows. -/
theorem proj_tuple {ρ : List M.Val} {n : ℕ} (hρ : ρ.map Sigma.fst = List.replicate n obj)
    {X : Tree} (hX : IsObj M ρ X) :
    ∀ qs : List (Tree × Tree), (∀ q ∈ qs, Hom M ρ q.1 X q.2 ∧ IsTy n q.2 = true) →
      EnvEq M ρ (precomp (tuple X (qs.map Prod.fst)) (stdEnv (qs.map Prod.snd))) qs :=
  List.rec (fun _ i p hp ↦ by simp [precomp, stdEnv] at hp) fun q qs ih hqs i p hp ↦ by
    have hq := (hqs q List.mem_cons_self).1
    rcases qs with _ | ⟨q', qs⟩
    · -- a single arrow: the identity after it
      rcases i with _ | j
      · obtain rfl : (comp (idt q.2) q.1, q.2) = p := by simpa [precomp, stdEnv, tuple] using hp
        exact ⟨q, rfl, rfl, (idt_comp hM hq).symm⟩
      · simp [precomp, stdEnv] at hp
    have hqs' : ∀ r ∈ q' :: qs, Hom M ρ r.1 X r.2 ∧ IsTy n r.2 = true :=
      fun r hr ↦ hqs r (List.mem_cons_of_mem _ hr)
    have hT := tuple_hom hM hX (q' :: qs) fun r hr ↦ (hqs' r hr).1
    have hΓ : ((q' :: qs).map Prod.snd).all (IsTy n) = true := by
      rw [List.all_map, List.all_eq_true]
      exact fun r hr ↦ (hqs' r hr).2
    have hstd := stdEnv_hom hM hρ _ hΓ
    rcases i with _ | j
    · obtain rfl : (comp (snd (ctxObj ((q' :: qs).map Prod.snd)) q.2)
          (pair (tuple X ((q' :: qs).map Prod.fst)) q.1), q.2) = p := by
        simpa [precomp, stdEnv, extEnv, tuple] using hp
      exact ⟨q, rfl, rfl, (snd_pair hM hT hq).symm⟩
    · change (precomp (pair (tuple X ((q' :: qs).map Prod.fst)) q.1)
          (extEnv (ctxObj ((q' :: qs).map Prod.snd)) q.2
            (stdEnv ((q' :: qs).map Prod.snd))))[j + 1]? = some p at hp
      simp only [precomp, extEnv, List.map_cons, List.getElem?_cons_succ, List.map_map,
        List.getElem?_map, Option.map_eq_some_iff, Function.comp_apply] at hp
      obtain ⟨p₀, hp₀, rfl⟩ := hp
      obtain ⟨q₀, hq₀, h₂, h₁⟩ :=
        ih hqs' j (comp p₀.1 (tuple X ((q' :: qs).map Prod.fst)), p₀.2)
          (by simp only [precomp, List.map_cons] at hp₀ ⊢; simp [hp₀])
      have hp₀h := (hstd.2 p₀ (List.mem_of_getElem? hp₀)).1
      refine ⟨q₀, by simpa using hq₀, h₂, h₁.trans ?_⟩
      exact (eval_op₂_congr 3 rfl (fst_pair hM hT hq).symm).trans
        (comp_assoc hM (pair_hom hM hT hq) (fst_hom hM hT.isObj_cod hq.isObj_cod) hp₀h)

/-- The unfolding of a well-typed term's definitions, by unfolded bodies whose arrows have the
values of the definitions' operations, has the term's type and an arrow of the same value. -/
theorem compile_unfold_of {G : Globals} (hG : G.WF) {ubs : List Term} (hubs : UbsOk M G ubs)
    {n : ℕ} {ρ : List M.Val} (hρ : ρ.map Sigma.fst = List.replicate n obj)
    (hps : PrimsHom M ρ G n) (hds : DefsHom M ρ G n) (s : Term) :
    ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree), compile G n s X e = some r →
      EnvHom M ρ n X e →
      ∃ r', compile G n (unfold ubs s) X e = some r' ∧ ResEq M ρ r r' := by
  refine RoseTree.ind (P := fun s ↦ ∀ (X : Tree) (e : List (Tree × Tree)) (r : Tree × Tree),
    compile G n s X e = some r → EnvHom M ρ n X e →
      ∃ r', compile G n (unfold ubs s) X e = some r' ∧ ResEq M ρ r r')
    (fun l cs ih ↦ ?_) s
  intro X e r h he
  have hobj := isObj_of_isTy hM hρ
  have hty := compile_hom hM hG hρ hps hds
  cases l with
  | var i =>
    obtain ⟨rfl, hi⟩ := compile_var_iff.mp h
    rw [unfold_node (by simp)]
    exact ⟨r, compile_var_iff.mpr ⟨rfl, hi⟩, rfl, rfl⟩
  | star =>
    obtain ⟨rfl, rfl⟩ := compile_star_iff.mp h
    rw [unfold_node (by simp)]
    exact ⟨_, compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, rfl⟩
  | pair =>
    obtain ⟨t, u, f, a, g, b, rfl, ht, hu, rfl⟩ := compile_pair_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he
    exact ⟨_, compile_pair_iff.mpr ⟨_, _, f', a', g', b', rfl, ht', hu', rfl⟩, rfl,
      eval_op₂_congr 9 hf hg⟩
  | fst =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_fst_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he
    exact ⟨_, compile_fst_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | snd =>
    obtain ⟨t, f, a, b, rfl, ht, rfl⟩ := compile_snd_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he
    exact ⟨_, compile_snd_iff.mpr ⟨_, f', a, b, rfl, ht', rfl⟩, rfl, eval_op₂_congr 3 rfl hf⟩
  | lam a =>
    obtain ⟨t, f, b, rfl, hat, ht, rfl⟩ := compile_lam_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨f', b'⟩, ht', rfl, hf⟩ := ih t (by simp) _ _ _ ht (he.ext hM (hobj a hat) hat)
    exact ⟨_, compile_lam_iff.mpr ⟨_, f', b', rfl, hat, ht', rfl⟩, rfl,
      eval_op₃_congr 24 rfl rfl hf⟩
  | app =>
    obtain ⟨t, u, rfl, f, a, b, ht, g, hu, rfl⟩ := compile_app_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨f', p⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he
    obtain ⟨⟨g', a'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he
    exact ⟨_, compile_app_iff.mpr ⟨_, _, rfl, f', a', b, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | arr k θ =>
    obtain ⟨t, rfl, p, hp, g, ht, hl, hθ, rfl⟩ := compile_arr_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨g', d'⟩, ht', rfl, hg⟩ := ih t (by simp) X e _ ht he
    exact ⟨_, compile_arr_iff.mpr ⟨_, rfl, p, hp, g', ht', hl, hθ, rfl⟩, rfl,
      eval_op₂_congr 3 rfl hg⟩
  | natRec =>
    obtain ⟨z, s, m, rfl, z', c, hz, s', hs, m', hm, rfl⟩ := compile_natRec_iff.mp h
    rw [unfold_node (by simp)]
    have hz₀ : EnvHom M ρ n one [] := ⟨isObj_one hM, by simp⟩
    obtain ⟨-, hct⟩ := hty z _ _ _ hz hz₀
    have hC := hobj c hct
    obtain ⟨⟨z'', c'⟩, hz', rfl, hzv⟩ := ih z (by simp) _ _ _ hz hz₀
    obtain ⟨⟨s'', c''⟩, hs', rfl, hsv⟩ :=
      ih s (by simp) _ _ _ hs ⟨hC, by simpa using ⟨idt_hom hM hC, hct⟩⟩
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he
    exact ⟨_, compile_natRec_iff.mpr ⟨_, _, _, rfl, _, _, hz', _, hs', _, hm', rfl⟩, rfl,
      eval_op₂_congr 3 (eval_op₂_congr 32 hzv hsv) hmv⟩
  | listRec =>
    obtain ⟨z, s, m, rfl, m', a, hm, z', c, hz, s', hs, rfl⟩ := compile_listRec_iff.mp h
    rw [unfold_node (by simp)]
    have hz₀ : EnvHom M ρ n one [] := ⟨isObj_one hM, by simp⟩
    obtain ⟨-, hlt⟩ := hty m X e _ hm he
    rw [isTy_list] at hlt
    obtain ⟨-, hct⟩ := hty z _ _ _ hz hz₀
    have hA := hobj a hlt
    have hC := hobj c hct
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he
    obtain ⟨⟨z'', c'⟩, hz', rfl, hzv⟩ := ih z (by simp) _ _ _ hz hz₀
    obtain ⟨⟨s'', c''⟩, hs', rfl, hsv⟩ := ih s (by simp) _ _ _ hs ⟨isObj_prod hM hA hC, by
      simpa using ⟨⟨snd_hom hM hA hC, hct⟩, fst_hom hM hA hC, hlt⟩⟩
    exact ⟨_, compile_listRec_iff.mpr ⟨_, _, _, rfl, _, _, hm', _, _, hz', _, hs', rfl⟩, rfl,
      eval_op₂_congr 3 (eval_op₃_congr 36 rfl hzv hsv) hmv⟩
  | roseRec c =>
    obtain ⟨s, m, s', m', rfl, hct, hs, hm, rfl⟩ := compile_roseRec_iff.mp h
    rw [unfold_node (by simp)]
    have hPt : IsTy n (prod nat (list c)) = true := by simp [isTy_prod, isTy_list, isTy_nat, hct]
    have hP := hobj _ hPt
    obtain ⟨⟨s'', c'⟩, hs', rfl, hsv⟩ :=
      ih s (by simp) _ _ _ hs ⟨hP, by simpa using ⟨idt_hom hM hP, hPt⟩⟩
    obtain ⟨⟨m'', t⟩, hm', rfl, hmv⟩ := ih m (by simp) X e _ hm he
    exact ⟨_, compile_roseRec_iff.mpr ⟨_, _, _, _, rfl, hct, hs', hm', rfl⟩, rfl,
      eval_op₂_congr 3 (eval_op₁_congr 39 hsv) hmv⟩
  | eq =>
    obtain ⟨t, u, rfl, f, a, ht, g, hu, rfl⟩ := compile_eq_iff.mp h
    rw [unfold_node (by simp)]
    obtain ⟨⟨f', a'⟩, ht', rfl, hf⟩ := ih t (by simp) X e _ ht he
    obtain ⟨⟨g', b'⟩, hu', rfl, hg⟩ := ih u (by simp) X e _ hu he
    exact ⟨_, compile_eq_iff.mpr ⟨_, _, rfl, f', _, ht', g', hu', rfl⟩, rfl,
      eval_op₂_congr 3 rfl (eval_op₂_congr 9 hf hg)⟩
  | defn k θ =>
    obtain ⟨d, rs, hd, hrs, hl, hθ, htys, rfl⟩ := compile_defn_iff.mp h
    obtain ⟨ub, hub, hubF⟩ := hubs k d hd
    obtain ⟨F, hF, hFv⟩ := hubF n ρ θ hρ hl hθ
    rw [unfold_defn hub]
    -- the unfolded arguments compile to the arguments' types and values
    obtain ⟨rs', hrs', hR⟩ := mapM_lift (g := fun c ↦ compile G n (unfold ubs c) X e) cs hrs
      fun c hc r hr ↦ ih c hc X e r hr he
    have hq : ∀ q ∈ rs', Hom M ρ q.1 X q.2 ∧ IsTy n q.2 = true := fun q hq ↦ by
      obtain ⟨c, -, hcq⟩ := exists_of_mapM hrs' hq
      exact hty _ X e q hcq he
    have hsn : rs'.map Prod.snd = d.params.map (PartialHorn.subst θ) :=
      (map_snd_of_forall₂ hR).trans htys
    have hT := tuple_hom hM he.1 rs' fun q hq' ↦ (hq q hq').1
    have hPt : (rs'.map Prod.snd).all (IsTy n) = true := by
      rw [List.all_map, List.all_eq_true]
      exact fun q hq' ↦ (hq q hq').2
    -- the body at the objects, in its parameters' environment, precomposed with the arguments
    have hO := compile_osubst hG hl hθ ub _ _ _ hF
    rw [subst_ctxObj, map_substPair_stdEnv, ← hsn] at hO
    obtain ⟨r₁, hr₁, hr₁v⟩ :=
      compile_comp hM hG hρ hps hds _ _ _ _ hO (stdEnv_hom hM hρ _ hPt) X _ hT
    -- the substitution of the unfolded arguments
    have hlen : rs'.length = cs.length := by
      simpa using (congrArg List.length ((PartialHorn.mapM_eq_some_iff cs rs').mp hrs')).symm
    have hσ : SubstEq M ρ G n X e (Term.substList (cs.map (unfold ubs)))
        (precomp (tuple X (rs'.map Prod.fst)) (stdEnv (rs'.map Prod.snd))) := by
      intro i p hp
      obtain ⟨q, hq', hpq⟩ := proj_tuple hM hρ he.1 rs' hq i p hp
      have hi : i < cs.length := hlen ▸ (List.getElem?_eq_some_iff.mp hq').1
      obtain ⟨q', hq'', hcq⟩ := getElem?_of_mapM hrs' (List.getElem?_eq_getElem hi)
      obtain rfl : q = q' := Option.some_inj.mp (hq'.symm.trans hq'')
      refine ⟨q, ?_, hpq⟩
      simpa [Term.substList, hi] using hcq
    obtain ⟨r₂, hr₂, hr₂v⟩ := compile_subst hM hG hρ hps hds _ X _ r₁ hr₁ e _ he hσ
    exact ⟨r₂, hr₂, hr₂v.1.trans hr₁v.1,
      hr₂v.2.trans (hr₁v.2.trans (eval_op₂_congr 3 hFv (eval_tuple_of_forall₂ X hR)))⟩

end Square

/-- The definitions of the combinators that definitions compile to are their compilations over
the definitions before them. -/
theorem compileDefs_getElem? {G : Globals} {cds : List PartialHorn.Defn}
    (hc : compileDefs G = some cds) {k : ℕ} {d : Defn} (hd : G.defs[k]? = some d) :
    ∃ cd, cds[k]? = some cd ∧ d.compile { G with defs := G.defs.take k } = some cd := by
  obtain ⟨cd, hcd, h⟩ := getElem?_of_mapM hc (i := k) (a := (d, k))
    (by simp [List.getElem?_zipIdx, hd])
  exact ⟨cd, hcd, h⟩

/-- A definition compiles to the arrow its body compiles to, in its object parameters. -/
theorem Defn.compile_eq_some {G : Globals} {d : Defn} {cd : PartialHorn.Defn}
    (h : d.compile G = some cd) : ∃ cb,
      Internal.compile G d.arity d.body (ctxObj d.params) (stdEnv d.params) =
        some (cb, d.type) ∧ cd = ⟨List.replicate d.arity obj, arr, cb⟩ := by
  simp only [Defn.compile, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨cb, c⟩, hcb, h⟩ := h
  split_ifs at h with hok
  exact ⟨cb, hok.2 ▸ hcb, (Option.some_inj.mp h).symm⟩

/-- The unfolded bodies of one more definition. -/
theorem unfoldBodies_take_succ {ds : List Defn} {k : ℕ} {d : Defn} (hd : ds[k]? = some d) :
    unfoldBodies (ds.take (k + 1)) =
      unfoldBodies (ds.take k) ++ [unfold (unfoldBodies (ds.take k)) d.body] := by
  rw [List.take_add_one, hd, Option.toList_some, unfoldBodies, List.foldl_append]
  rfl

/-- There is one unfolded body for each definition. -/
theorem length_unfoldBodies (ds : List Defn) : (unfoldBodies ds).length = ds.length := by
  suffices h : ∀ acc : List Term, (ds.foldl (fun ubs d ↦ ubs ++ [unfold ubs d.body]) acc).length =
      acc.length + ds.length by simpa [unfoldBodies] using h []
  exact ds.rec (fun _ ↦ rfl) fun d ds ih acc ↦ by
    rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
    omega

/-- An element of an initial segment of a list is the list's element, at a position below the
segment's length. -/
theorem getElem?_of_take {α : Type} {l : List α} {i j : ℕ} {a : α}
    (h : (l.take i)[j]? = some a) : j < i ∧ l[j]? = some a := by
  rw [List.getElem?_take] at h
  split_ifs at h with hj
  exact ⟨hj, h⟩

/-- The constants of an initial segment of well-formed constants are well formed. -/
theorem Globals.WF.take {G : Globals} (hG : G.WF) (k : ℕ) :
    ({ G with defs := G.defs.take k } : Globals).WF :=
  ⟨hG.prims, fun j d hd ↦ hG.defs j d (getElem?_of_take hd).2⟩

/-- A type is a type of the product of a context of types. -/
theorem isTy_ctxObj {n : ℕ} : ∀ Γ : List Tree, Γ.all (IsTy n) = true → IsTy n (ctxObj Γ) = true :=
  List.rec (fun _ ↦ isTy_one) fun a Γ ih h ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases Γ with _ | ⟨b, Γ⟩
    · exact h.1
    · change IsTy n (prod (ctxObj (b :: Γ)) a) = true
      simp [isTy_prod, ih h.2, h.1]

section Values

variable {defs : List PartialHorn.Defn} {M : Model.{v} (ext defs).sig}

/-- A term with a value at an assignment is in the assignment's scope. -/
theorem scoped_of_eval {ρ : List M.Val} :
    ∀ t : Tree, ∀ {w : M.Val}, eval M ρ t = Part.some w → PartialHorn.Scoped ρ.length t = true :=
  RoseTree.ind fun l cs ih w h ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [eval] at h
      rotate_left
      · simp [eval] at h
      rw [PartialHorn.eval_node_zero] at h
      rw [PartialHorn.scoped_node_zero, decide_eq_true_eq]
      by_contra hi
      rw [List.getElem?_eq_none (by omega)] at h
      simp at h
    · rw [PartialHorn.scoped_node_succ, List.all_eq_true]
      intro c hc
      obtain ⟨v, hv⟩ := exists_eval_of_eval_op (k := k) h c hc
      exact ih c hc hv

/-- Types at an assignment of objects have values, objects. -/
theorem exists_vals_of_isTy (hM : IsModel (ext defs) M) {m : ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = List.replicate m obj) :
    ∀ θ : List Tree, θ.all (IsTy m) = true → ∃ ws : List M.Val,
      θ.map (eval M ρ) = ws.map Part.some ∧ ws.map Sigma.fst = List.replicate θ.length obj :=
  List.rec (fun _ ↦ ⟨[], rfl, rfl⟩) fun a θ ih h ↦ by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨w, hw, hws⟩ := isObj_of_isTy hM hρ a h.1
    obtain ⟨ws, h₁, h₂⟩ := ih h.2
    exact ⟨w :: ws, by simp [hw, h₁], by simp [hws, h₂, List.replicate_succ]⟩

/-- Unary applications of an operation to terms of one value at two assignments have one
value. -/
theorem eval_op₁_of_eq {ρ ρ' : List M.Val} {k : ℕ} {t t' : Tree}
    (h : eval M ρ t = eval M ρ' t') : eval M ρ (op k [t]) = eval M ρ' (op k [t']) := by
  rw [PartialHorn.eval_op, PartialHorn.eval_op]
  simp only [List.mapM_cons, List.mapM_nil, h]

end Values

section Definitions

variable {pre cds : List PartialHorn.Defn} {M : Model.{v} (ext (pre ++ cds)).sig}

/-- Constants the check accepts are well formed. -/
theorem Globals.wf_of_ok {E : ExtEnv} {G : Globals} (h : G.ok E = true) : G.WF := by
  simp only [Globals.ok, Bool.and_eq_true] at h
  refine ⟨fun k p hp ↦ ?_, fun k d hd ↦ ?_⟩
  · have hp' := List.all_eq_true.mp h.1 p (List.mem_of_getElem? hp)
    simp only [Prim.ok, Bool.and_eq_true] at hp'
    exact ⟨hp'.1.1.1.1, hp'.1.1.1.2, hp'.1.1.2⟩
  · have hd' := List.all_eq_true.mp h.2 d (List.mem_of_getElem? hd)
    simp only [Bool.and_eq_true] at hd'
    exact hd'

/-- The primitive arrows of constants the check accepts are arrows, at every assignment of
objects. -/
theorem primsHom_of_ok (hM : IsModel (ext (pre ++ cds)) M) {G : Globals}
    (h : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true) {m : ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = List.replicate m obj) : PrimsHom M ρ G m := by
  intro k p hp θ hl hθ
  have hpo : p.ok (ExtEnv.ofDefs (pre ++ cds)) = true := by
    simp only [Globals.ok, Bool.and_eq_true, List.all_eq_true] at h
    exact h.1 p (List.mem_of_getElem? hp)
  unfold Prim.ok at hpo
  simp only [Bool.and_eq_true] at hpo
  obtain ⟨⟨⟨⟨har, hdt⟩, hct⟩, -⟩, hinf⟩ := hpo
  split at hinf
  · rename_i a ha
    simp only [Bool.and_eq_true, beq_iff_eq] at hinf
    obtain ⟨⟨hs, hlo⟩, hhi⟩ := hinf
    obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hρ θ hθ
    rw [hl] at hws
    obtain ⟨w, hw, hwsrt, -, harr⟩ := (infers_sound (ExtEnv.wf_ofDefs (pre ++ cds)) hM hws
      (H := []) (by simp) inferFuel).2 _ a ha
    obtain ⟨⟨d, hd, hdl⟩, ⟨c, hc, hch⟩⟩ := harr hs
    have hsc : ∀ x : Tree, PartialHorn.Scoped p.arity x = true →
        eval M ρ (PartialHorn.subst θ x) = eval M ws x :=
      fun x hx ↦ PartialHorn.eval_subst hθw x (hl ▸ hx)
    have hw' := (hsc _ har).trans hw
    refine ⟨w, hw', hwsrt.trans hs, isObj_of_isTy hM hρ _ (isTy_subst hl hθ _ hdt),
      isObj_of_isTy hM hρ _ (isTy_subst hl hθ _ hct), ?_, ?_⟩
    · rw [hsc _ (scoped_of_isTy _ hdt), ← hlo]
      exact (eval_op₁_of_eq (hsc _ har)).trans (hd.trans hdl.symm)
    · rw [hsc _ (scoped_of_isTy _ hct), ← hhi]
      exact (eval_op₁_of_eq (hsc _ har)).trans (hc.trans hch.symm)
  · simp at hinf

variable (M) in
/-- The invariant of the definitions' compilation, over an initial segment of them: their
operations are arrows, and their unfolded bodies compile to the operations' values. -/
def DefsInv (G : Globals) (k : ℕ) : Prop :=
  (∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj →
    DefsHom M ρ { G with defs := G.defs.take k } m) ∧
  UbsOk M { G with defs := G.defs.take k } (unfoldBodies (G.defs.take k))

variable (hM : IsModel (ext (pre ++ cds)) M) {G : Globals}
  (hbase : G.base = sig.length + pre.length) (hG : G.WF) (hc : compileDefs G = some cds)
  (hps : ∀ (m : ℕ) (ρ : List M.Val), ρ.map Sigma.fst = List.replicate m obj → PrimsHom M ρ G m)
include hM hbase hG hc hps

/-- The invariant extends to one more definition. -/
theorem defsInv_succ {k : ℕ} (hk : k < G.defs.length) (h : DefsInv M G k) :
    DefsInv M G (k + 1) := by
  obtain ⟨d, hd⟩ : ∃ d, G.defs[k]? = some d := ⟨_, List.getElem?_eq_getElem hk⟩
  obtain ⟨cd, hcd, hdc⟩ := compileDefs_getElem? hc hd
  obtain ⟨cb, hcb, rfl⟩ := Defn.compile_eq_some hdc
  obtain ⟨hpt, htt⟩ := hG.defs k d hd
  have hGk := hG.take k
  have hle : Globals.Le { G with defs := G.defs.take k } { G with defs := G.defs.take (k + 1) } :=
    ⟨rfl, rfl, [d], by rw [List.take_add_one, hd]; rfl⟩
  -- the compiled body at an assignment of objects to the object parameters
  have hbody : ∀ (ws : List M.Val), ws.map Sigma.fst = List.replicate d.arity obj →
      Hom M ws cb (ctxObj d.params) d.type := fun ws hws ↦
    (compile_hom hM hGk hws (hps _ ws hws) (h.1 _ ws hws) _ _ _ _ hcb
      (stdEnv_hom hM hws _ hpt)).1
  -- the operation at types has the compiled body's value at their values
  have hop : ∀ (m : ℕ) (ρ : List M.Val) (θ : List Tree) (ws : List M.Val),
      θ.map (eval M ρ) = ws.map Part.some → ws.map Sigma.fst = List.replicate d.arity obj →
      eval M ρ (op (G.base + k) θ) = eval M ws cb := fun m ρ θ ws hθ hws ↦ by
    obtain ⟨v, hv, -⟩ := hbody ws hws
    rw [hv, hbase, Nat.add_assoc]
    exact eval_op_defn hM (i := pre.length + k) (d := ⟨List.replicate d.arity obj, arr, cb⟩)
      (by simp [List.getElem?_append_right, hcd]) hθ hws hv
  have hvals : ∀ (m : ℕ) (ρ : List M.Val) (θ : List Tree),
      ρ.map Sigma.fst = List.replicate m obj → θ.length = d.arity → θ.all (IsTy m) = true →
      ∃ ws : List M.Val, θ.map (eval M ρ) = ws.map Part.some ∧
        ws.map Sigma.fst = List.replicate d.arity obj := fun m ρ θ hρ hl hθ ↦ by
    obtain ⟨ws, h₁, h₂⟩ := exists_vals_of_isTy hM hρ θ hθ
    exact ⟨ws, h₁, hl ▸ h₂⟩
  refine ⟨fun m ρ hρ j d' hd' θ hl hθ ↦ ?_, fun j d' hd' ↦ ?_⟩
  · -- the operations are arrows
    rcases Nat.lt_or_ge j k with hj | hj
    · have hd'k : (G.defs.take k)[j]? = some d' := by
        rw [List.getElem?_take_of_lt hj]
        exact (getElem?_of_take hd').2
      exact h.1 m ρ hρ j d' hd'k θ hl hθ
    · have hjk : j = k := Nat.le_antisymm (Nat.le_of_lt_succ (getElem?_of_take hd').1) hj
      subst hjk
      obtain rfl : d' = d := Option.some_inj.mp ((getElem?_of_take hd').2.symm.trans hd)
      obtain ⟨ws, hθw, hws⟩ := hvals m ρ θ hρ hl hθ
      obtain ⟨v, hv, hvs, -, -, hdom, hcod⟩ := hbody ws hws
      have hsc : ∀ x : Tree, IsTy d'.arity x = true →
          eval M ρ (PartialHorn.subst θ x) = eval M ws x := fun x hx ↦
        PartialHorn.eval_subst hθw x (hl ▸ scoped_of_isTy x hx)
      have ho := hop m ρ θ ws hθw hws
      refine ⟨v, ho.trans hv, hvs,
        isObj_of_isTy hM hρ _ (isTy_ctxObj _ (by
          rw [List.all_map, List.all_eq_true]
          exact fun x hx ↦ isTy_subst hl hθ x (List.all_eq_true.mp hpt x hx))),
        isObj_of_isTy hM hρ _ (isTy_subst hl hθ _ htt), ?_, ?_⟩
      · rw [← subst_ctxObj, hsc _ (isTy_ctxObj _ hpt)]
        exact (eval_op₁_of_eq ho).trans hdom
      · rw [hsc _ htt]
        exact (eval_op₁_of_eq ho).trans hcod
  · -- the unfolded bodies compile to the operations' values
    have hlen : (unfoldBodies (G.defs.take k)).length = k := by
      rw [length_unfoldBodies, List.length_take, Nat.min_eq_left hk.le]
    rw [unfoldBodies_take_succ hd]
    rcases Nat.lt_or_ge j k with hj | hj
    · have hd'k : (G.defs.take k)[j]? = some d' := by
        rw [List.getElem?_take_of_lt hj]
        exact (getElem?_of_take hd').2
      obtain ⟨ub, hub, hF⟩ := h.2 j d' hd'k
      refine ⟨ub, by rw [List.getElem?_append_left (by rw [hlen]; exact hj)]; exact hub,
        fun m ρ θ hρ hl hθ ↦ ?_⟩
      obtain ⟨F, hFc, hFv⟩ := hF m ρ θ hρ hl hθ
      exact ⟨F, compile_mono hle _ _ _ _ hFc, hFv⟩
    · have hjk : j = k := Nat.le_antisymm (Nat.le_of_lt_succ (getElem?_of_take hd').1) hj
      subst hjk
      obtain rfl : d' = d := Option.some_inj.mp ((getElem?_of_take hd').2.symm.trans hd)
      refine ⟨_, by rw [List.getElem?_append_right hlen.le, hlen, Nat.sub_self]; rfl,
        fun m ρ θ hρ hl hθ ↦ ?_⟩
      obtain ⟨ws, hθw, hws⟩ := hvals m ρ θ hρ hl hθ
      obtain ⟨⟨F, ty⟩, hF, rfl, hFv⟩ := compile_unfold_of hM hGk h.2 hws (hps _ ws hws)
        (h.1 _ ws hws) _ _ _ _ hcb (stdEnv_hom hM hws _ hpt)
      obtain ⟨-, -, -, ⟨w, hw, -⟩, -⟩ := hbody ws hws
      obtain ⟨v, hv, -⟩ := hbody ws hws
      have hFw : eval M ws F = Part.some v := hFv.trans hv
      have hsF : PartialHorn.Scoped θ.length F = true := by
        have := scoped_of_eval F hFw
        rwa [show ws.length = θ.length by
          simpa [hl] using congrArg List.length hws] at this
      exact ⟨F, compile_mono hle _ _ _ _ hF,
        ((PartialHorn.eval_subst hθw F hsF).trans hFv).trans (hop m ρ θ ws hθw hws).symm⟩

/-- The invariant holds of every initial segment of the definitions. -/
theorem defsInv : ∀ k ≤ G.defs.length, DefsInv M G k :=
  Nat.rec (fun _ ↦ ⟨fun _ _ _ j d hd ↦ by simp at hd, fun j d hd ↦ by simp at hd⟩)
    fun k ih hk ↦ defsInv_succ hM hbase hG hc hps hk (ih (Nat.le_of_succ_le hk))

/-- A definition's body compiles in its parameters' environment to its value's type and an
arrow whose instance at types has the value of the definition's operation at them: the
definition's axiom. -/
theorem defn_body {k : ℕ} {d : Defn} (hd : G.defs[k]? = some d) :
    ∃ F, compile G d.arity d.body (ctxObj d.params) (stdEnv d.params) = some (F, d.type) ∧
      ∀ (m : ℕ) (ρ : List M.Val) (θ : List Tree), ρ.map Sigma.fst = List.replicate m obj →
        θ.length = d.arity → θ.all (IsTy m) = true →
        eval M ρ (op (G.base + k) θ) = eval M ρ (PartialHorn.subst θ F) := by
  obtain ⟨cd, hcd, hdc⟩ := compileDefs_getElem? hc hd
  obtain ⟨cb, hcb, rfl⟩ := Defn.compile_eq_some hdc
  have hk : k < G.defs.length := (List.getElem?_eq_some_iff.mp hd).1
  obtain ⟨hds, -⟩ := defsInv hM hbase hG hc hps k hk.le
  have hle : Globals.Le { G with defs := G.defs.take k } G :=
    ⟨rfl, rfl, G.defs.drop k, (List.take_append_drop k G.defs).symm⟩
  obtain ⟨hpt, -⟩ := hG.defs k d hd
  refine ⟨cb, compile_mono hle _ _ _ _ hcb, fun m ρ θ hρ hl hθ ↦ ?_⟩
  obtain ⟨ws, hθw, hws⟩ := exists_vals_of_isTy hM hρ θ hθ
  rw [hl] at hws
  obtain ⟨v, hv, -⟩ := (compile_hom hM (hG.take k) hws (hps _ ws hws) (hds _ ws hws) _ _ _ _ hcb
    (stdEnv_hom hM hws _ hpt)).1
  have hsc : PartialHorn.Scoped θ.length cb = true := by
    have := scoped_of_eval cb hv
    rwa [show ws.length = θ.length by simpa [hl] using congrArg List.length hws] at this
  rw [PartialHorn.eval_subst hθw cb hsc, hv, hbase, Nat.add_assoc]
  exact eval_op_defn hM (i := pre.length + k) (d := ⟨List.replicate d.arity obj, arr, cb⟩)
    (by simp [List.getElem?_append_right, hcd]) hθw hws hv

/-- The square of the compilation and the unfolding: in every model of the theory extended by
the combinators' definitions and those the definitions compile to, a term that compiles in an
environment of arrows has an arrow to its type, and, unfolded, its type and an arrow of the same
value. -/
theorem compile_unfold {n : ℕ} {ρ : List M.Val} (hρ : ρ.map Sigma.fst = List.replicate n obj)
    {s : Term} {X : Tree} {e : List (Tree × Tree)} {r : Tree × Tree}
    (h : compile G n s X e = some r) (he : EnvHom M ρ n X e) :
    Hom M ρ r.1 X r.2 ∧
      ∃ r', compile G n (unfold (unfoldBodies G.defs) s) X e = some r' ∧ ResEq M ρ r r' := by
  obtain ⟨hds, hubs⟩ := defsInv hM hbase hG hc hps G.defs.length le_rfl
  simp only [List.take_length] at hds hubs
  exact ⟨(compile_hom hM hG hρ (hps n ρ hρ) (hds n ρ hρ) s X e r h he).1,
    compile_unfold_of hM hG hubs hρ (hps n ρ hρ) (hds n ρ hρ) s X e r h he⟩

end Definitions

/-- The square of the compilation and the unfolding, for constants the check accepts: in every
model of the theory extended by the combinators' definitions {lit}`pre` and those the
definitions compile to, a term that compiles in an environment of arrows has, unfolded, its type
and an arrow of the same value. -/
theorem compile_unfold_of_ok {pre cds : List PartialHorn.Defn}
    {M : Model.{v} (ext (pre ++ cds)).sig} (hM : IsModel (ext (pre ++ cds)) M) {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) {n : ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = List.replicate n obj) {s : Term} {X : Tree}
    {e : List (Tree × Tree)} {r : Tree × Tree} (h : compile G n s X e = some r)
    (he : EnvHom M ρ n X e) :
    Hom M ρ r.1 X r.2 ∧
      ∃ r', compile G n (unfold (unfoldBodies G.defs) s) X e = some r' ∧ ResEq M ρ r r' :=
  compile_unfold hM hbase (Globals.wf_of_ok hok) hc (fun _ _ hρ' ↦ primsHom_of_ok hM hok hρ') hρ
    h he

/-- The definitions of the combinators that definitions compile to take objects to arrows. -/
theorem getElem?_sig_compileDefs {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hc : compileDefs G = some cds) {k : ℕ} {d : Defn}
    (hd : G.defs[k]? = some d) :
    (ext (pre ++ cds)).sig[G.base + k]? = some (List.replicate d.arity obj, arr) := by
  obtain ⟨cd, hcd, hdc⟩ := compileDefs_getElem? hc hd
  obtain ⟨cb, -, rfl⟩ := Defn.compile_eq_some hdc
  rw [PartialHorn.Theory.extendAll_sig, show theory.sig = sig from rfl, sig_extendAll_eq, hbase,
    Nat.add_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.map_append, List.getElem?_append_right (by simp), List.length_map,
    Nat.add_sub_cancel_left, List.getElem?_map, hcd]
  rfl

/-- The primitive arrows of constants the check accepts are arrows of the extended signature. -/
theorem sortOf_prims_of_ok {defs : List PartialHorn.Defn} {G : Globals}
    (hok : G.ok (ExtEnv.ofDefs defs) = true) {k : ℕ} {p : Prim} (hp : G.prims[k]? = some p) :
    PartialHorn.sortOf (ext defs).sig (List.replicate p.arity obj) p.arrow = some arr := by
  simp only [Globals.ok, Bool.and_eq_true] at hok
  have hpo := List.all_eq_true.mp hok.1 p (List.mem_of_getElem? hp)
  simp only [Prim.ok, Bool.and_eq_true, beq_iff_eq] at hpo
  simpa [ExtEnv.ofDefs] using hpo.1.2

/-- The square for the definition-free arrows, given the arrow the unfolding compiles to: in
every model of the theory, the unfoldings of the combinators' definitions in the arrow a term
compiles to in a context and in the arrow its unfolding compiles to have one value, when the
combinators' definitions are well formed. -/
theorem valid_unfoldAll_compile_of {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds)) {n : ℕ}
    {Γ : List Tree} (hΓ : Γ.all (IsTy n) = true) {s : Term} {f A f' A' : Tree}
    (h : compile G n s (ctxObj Γ) (stdEnv Γ) = some (f, A))
    (h' : compile G n (unfold (unfoldBodies G.defs) s) (ctxObj Γ) (stdEnv Γ) = some (f', A'))
    {M : Model.{v} theory.sig} (hM : IsModel theory M) :
    (PartialHorn.unfoldAll sig (pre ++ cds) ⟨List.replicate n obj, [], ⟨f, f'⟩⟩).Valid M := by
  have hG := Globals.wf_of_ok hok
  have hsrt := fun {s : Term} {r : Tree × Tree} (hs : compile G n s (ctxObj Γ) (stdEnv Γ) =
      some r) ↦ compile_sortOf (defs := pre ++ cds) hG (fun k p hp ↦ sortOf_prims_of_ok hok hp)
    (fun k d hd ↦ getElem?_sig_compileDefs hbase hc hd) s _ _ r hs (sortOf_ctxObj Γ hΓ)
    (sortOf_stdEnv Γ hΓ)
  refine PartialHorn.valid_unfoldAll (pre ++ cds) theory M hM theory_ofSig hwf _ ?_ ?_
  · intro q hq
    obtain rfl : q = ⟨f, f'⟩ := by simpa using hq
    exact ⟨⟨arr, (hsrt h).1⟩, ⟨arr, (hsrt h').1⟩⟩
  · intro N hN ρ hρ _
    obtain ⟨hf, r', hr', hR⟩ := compile_unfold_of_ok hN hbase hok hc hρ h (stdEnv_hom hN hρ Γ hΓ)
    rw [h'] at hr'
    obtain rfl := (Option.some_inj.mp hr').symm
    obtain ⟨w, hw, -⟩ := hf
    exact ⟨w, hw, hR.2.trans hw⟩

/-- The theory's axioms equate terms of one sort. -/
theorem theory_sidesSorted : ∀ a ∈ theory.axioms, PartialHorn.SidesSorted theory.sig a := by
  have h : axioms.all (fun a ↦ match PartialHorn.sortOf sig a.ctx a.concl.lhs with
      | some s => PartialHorn.sortOf sig a.ctx a.concl.rhs == some s
      | none => false) = true := by
    decide
  intro a ha
  have ha' := List.all_eq_true.mp h a ha
  split at ha'
  · rename_i s hs
    exact ⟨s, hs, beq_iff_eq.mp ha'⟩
  · simp at ha'

/-- The unfolding of a term that compiles in a context compiles there, to the term's type: the
square in the one-point model, a model of every well-formed extension of the theory. -/
theorem compile_unfold_some {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds)) {n : ℕ}
    {Γ : List Tree} (hΓ : Γ.all (IsTy n) = true) {s : Term} {r : Tree × Tree}
    (h : compile G n s (ctxObj Γ) (stdEnv Γ) = some r) :
    ∃ r', compile G n (unfold (unfoldBodies G.defs) s) (ctxObj Γ) (stdEnv Γ) = some r' ∧
      r'.2 = r.2 := by
  have hM : IsModel (ext (pre ++ cds)) (PartialHorn.pointModel (ext (pre ++ cds)).sig) :=
    PartialHorn.isModel_point
      (PartialHorn.sidesSorted_extendAll (pre ++ cds) theory theory_sidesSorted hwf)
  have hρ : (List.replicate n (⟨obj, ()⟩ :
      (PartialHorn.pointModel (ext (pre ++ cds)).sig).Val)).map Sigma.fst =
        List.replicate n obj := by
    simp
  obtain ⟨-, r', hr', hR⟩ := compile_unfold_of_ok hM hbase hok hc hρ h (stdEnv_hom hM hρ Γ hΓ)
  exact ⟨r', hr', hR.1⟩

/-- The square for the definition-free arrows: the unfolding of a term that compiles in a context
compiles there to its type, and in every model of the theory the unfoldings of the combinators'
definitions in the two arrows have one value, when the combinators' definitions are well
formed. -/
theorem valid_unfoldAll_compile {pre cds : List PartialHorn.Defn} {G : Globals}
    (hbase : G.base = sig.length + pre.length) (hok : G.ok (ExtEnv.ofDefs (pre ++ cds)) = true)
    (hc : compileDefs G = some cds) (hwf : PartialHorn.DefnsWF sig (pre ++ cds)) {n : ℕ}
    {Γ : List Tree} (hΓ : Γ.all (IsTy n) = true) {s : Term} {f A : Tree}
    (h : compile G n s (ctxObj Γ) (stdEnv Γ) = some (f, A)) :
    ∃ f', compile G n (unfold (unfoldBodies G.defs) s) (ctxObj Γ) (stdEnv Γ) = some (f', A) ∧
      ∀ (M : Model.{v} theory.sig), IsModel theory M →
        (PartialHorn.unfoldAll sig (pre ++ cds) ⟨List.replicate n obj, [], ⟨f, f'⟩⟩).Valid M := by
  obtain ⟨⟨f', A'⟩, h', hA⟩ := compile_unfold_some hbase hok hc hwf hΓ h
  obtain rfl : A' = A := hA
  exact ⟨f', h', fun M hM ↦ valid_unfoldAll_compile_of hbase hok hc hwf hΓ h h' hM⟩

end Geb.FreeTopos.Internal

end
