/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.ProofCheck
import Mathlib.Data.Nat.Cast.Order.Basic -- shake: keep
import Mathlib.Tactic.IntervalCases
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The soundness of the decoding of proofs

A canonical LF term of the family of proofs of a formula, in an LF context of term and proof
variables, decodes ({name}`Geb.LF.Topos.decPf`) to a derivation that the internal language's
checker accepts as a proof of the formula's decoding, in the internal context of the term
variables' types under the hypotheses of the proof variables' formulas.

## Main definitions

* {lit}`TmCtx` — an LF context of proofs matches an environment and an internal context at its
  term variables.
* {lit}`PfCtx` — it matches them at its proof variables, and hypotheses.

## Main statements

* {lit}`termOf_typed` — the adequacy of the representation of terms in an LF context of proofs.
* {lit}`pfSound`, {lit}`decPf_sound` — the soundness of the decoding of proofs.
* {lit}`decPf_checks` — a proof in a context of term variables decodes to a derivation of a
  theorem of the internal language.

## Implementation notes

The type of a rule instantiates along its arguments by hereditary substitution, which leaves the
instances of a motive, an LF abstraction, at its arguments: these are renamings of the motive's
body where the argument is a variable ({lit}`hsub_var_base`), substitutions into it that commute
with the surrounding renamings where it is a term ({lit}`hsub_hole`), and are left in place by the
substitution of a proof, whose variable they do not mention ({lit}`hsubWith_vacuous'`).

## References

* {cite}`HarperLicata2007`, Sections 3.2 and 3.4, for the adequacy of the representations of
  syntax and of judgments.

## Tags

logical framework, LF, adequacy, soundness, proof, derivation, internal language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open FreeTopos.Internal (Term Deriv Globals Entry check typeIn instVar weaken1 ctxObj stdEnv)

/-- An LF context of proofs matches an environment and an internal context at its term
variables: each declaration is of a family of terms or of proofs, each family of terms is of the
encoding of the type the environment's renaming of its variable indexes in the internal context,
and the internal context's types are encoded. -/
structure TmCtx (ΓLF : Ctx) (env : List (Option ℕ)) (Γ : List PartialHorn.Tree) : Prop where
  shape : ∀ a ∈ ΓLF, (∃ A, a = tm A) ∨ ∃ F, a = pf F
  tmVar : ∀ (i : ℕ) (A : Expr), ΓLF[i]? = some (tm A) →
    ∃ a, encTy a = some A ∧ Γ[tmIdx env i]? = some a
  enc : ∃ ΓT, encCtx Γ = some ΓT

variable {ΓLF : Ctx} {env : List (Option ℕ)} {Γ : List PartialHorn.Tree}

/-- The family of terms is injective. -/
theorem tm_inj {A B : Expr} (h : tm A = tm B) : A = B := by
  simpa only [tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] using h

/-- The family of proofs is injective. -/
theorem pf_inj {F F' : Expr} (h : pf F = pf F') : F = F' := by
  simpa only [pf, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] using h

/-- No family of proofs is a family of terms. -/
theorem pf_ne_tm {F A : Expr} : pf F ≠ tm A := fun h ↦ by
  have := congrArg RoseTree.label h
  simp only [pf, tm, Expr.const, Expr.app, RoseTree.label_node, Label.app.injEq,
    Head.const.injEq] at this
  exact absurd this (by decide)

/-- The declarations of a context matching an environment have the shape of types whose
products' domains are of terms. -/
theorem TmCtx.typeShape (hc : TmCtx ΓLF env Γ) :
    ∀ a ∈ ΓLF, Expr.TypeShape a = true ∧ Expr.DomsOK a = true := fun a ha ↦ by
  rcases hc.shape a ha with ⟨A, rfl⟩ | ⟨F, rfl⟩ <;>
    exact ⟨by simp only [tm, pf, Expr.const, Expr.app, typeShape_node]; rfl,
      by simp only [tm, pf, Expr.const, Expr.app, domsOK_node]; rfl⟩

/-- A context matching an environment, extended by the family of terms of an encoded type,
matches the environment extended by a term variable and the internal context extended by the
type. -/
theorem TmCtx.consTm (hc : TmCtx ΓLF env Γ) {a : PartialHorn.Tree} {A : Expr}
    (ha : encTy a = some A) : TmCtx (tm A :: ΓLF) (none :: env) (a :: Γ) where
  shape b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inl ⟨A, rfl⟩
    · exact hc.shape b hb
  tmVar i B hi := by
    rcases i with _ | i
    · obtain rfl : A = B := tm_inj (Option.some.inj hi)
      exact ⟨a, ha, rfl⟩
    · obtain ⟨b, hb, hΓ⟩ := hc.tmVar i B hi
      exact ⟨b, hb, hΓ⟩
  enc := by
    obtain ⟨ΓT, hΓ⟩ := hc.enc
    exact ⟨_, encCtx_cons ha hΓ⟩

variable {G : Globals} {kz ks ki : ℕ}

/-- The adequacy of the representation of terms in an LF context of proofs: a canonical term of
the family of terms of an encoded type, in a context matching an environment and an internal
context, decodes in the environment to a term of the type in the internal context. A term
mentions no proof variable, its type's products' domains being of terms, so that its renaming to
the internal context's variables checks in the context of the term variables alone. -/
theorem termOf_typed (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim)
    (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim)
    (hi : G.defs[ki]? = some (.language FreeTopos.Internal.iterDefn))
    (hc : TmCtx ΓLF env Γ) {a : PartialHorn.Tree} {A M : Expr} (ha : encTy a = some A)
    (hj : judge sig M ΓLF (.check (tm A)) = true) :
    ∃ s, termOf kz ks ki env M = some s ∧ typeIn G 0 Γ s = some a := by
  have hAc := tm_closed (encTy_closed a A ha)
  have ho := judge_occursOnly M ΓLF (tm A) hc.typeShape
    (by simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl) rfl
    (by simp only [tm, Expr.const, Expr.app, domsOK_node]; rfl) hj
  obtain ⟨ΓT, hΓT⟩ := hc.enc
  have hρ : CtxRenOn (fun i ↦ (varType ΓLF i).any TermHead) ΓLF ΓT (tmIdx env) := by
    intro i T hS hT
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hT
    rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F, rfl⟩
    · obtain ⟨c, hc', hΓ⟩ := hc.tmVar i B hb
      obtain ⟨B', hB', hv⟩ := varType_encCtx hΓT hΓ
      obtain rfl := Option.some.inj (hc'.symm.trans hB')
      have hBc := tm_closed (encTy_closed c B hc')
      rw [hv, rename_closed hBc, rename_closed hBc]
    · simp only [hT, Option.any_some, TermHead, headDepth_rename, pf, Expr.const, Expr.app,
        headDepth_node, headDepthStep] at hS
      exact absurd hS (by decide)
  have hj' := judge_renameOn (Sig.ok_closed sig_ok) M (.check (tm A)) hρ ho hj
  rw [Mode.rename, rename_closed hAc] at hj'
  obtain ⟨s, r, hd, hcomp, hr, -⟩ := (tmComplete hz hs hi (M.rename (tmIdx env))).1
    (ctxObj Γ) (stdEnv Γ) ΓT A (by rw [FreeTopos.Internal.map_snd_stdEnv]; exact hΓT) hj'
  refine ⟨s, hd, ?_⟩
  rw [typeIn, hcomp, Option.map_some, encTy_inj hr ha]

/-- A term weakened by a new innermost variable has, in the context extended by the variable's
type, the type it had. -/
theorem typeIn_weaken1 {s : Term} {C a : PartialHorn.Tree} (h : typeIn G 0 Γ s = some C) :
    typeIn G 0 (a :: Γ) (weaken1 s) = some C := by
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.mp h
  have hsnd : (stdEnv (a :: Γ)).tail.map Prod.snd = (stdEnv Γ).map Prod.snd := by
    rw [List.map_tail, FreeTopos.Internal.map_snd_stdEnv, FreeTopos.Internal.map_snd_stdEnv]
    rfl
  obtain ⟨f, hf⟩ := FreeTopos.Internal.compile_retype s _ _ r hr (ctxObj (a :: Γ)) _ hsnd
  rw [typeIn, weaken1, FreeTopos.Internal.compile_rename s _ _ _ (· + 1) _ hf
    (fun i _ ↦ List.getElem?_tail.symm) fun _ _ ↦ Nat.succ_lt_succ]
  rfl

/-- The renaming of a context extended by a term variable, after the weakening of an LF term, is
the weakening of the renaming of the context. -/
theorem tmIdx_none_succ (env : List (Option ℕ)) (i : ℕ) :
    tmIdx (none :: env) (i + 1) = tmIdx env i + 1 := rfl

/-- The renaming of a context extended by a proof variable skips it. -/
theorem tmIdx_some_succ (env : List (Option ℕ)) (h i : ℕ) :
    tmIdx (some h :: env) (i + 1) = tmIdx env i := rfl

/-- The decoding of an LF term weakened by a term variable, in the environment extended by it, is
the weakening of its decoding. -/
theorem termOf_consTm {F : Expr} {k : ℕ} {φ : MTerm}
    (h : termOf kz ks ki env (F.rename (· + k)) = some φ) :
    termOf kz ks ki (none :: env) (F.rename (· + (k + 1))) = some (weaken1 φ) := by
  have := dec_rename _ (· + 1) φ h
  rw [rename_rename, rename_rename] at this
  rw [termOf, rename_rename]
  exact this

/-- The decoding of an LF term weakened by a proof variable, in the environment extended by it,
is its decoding. -/
theorem termOf_consPf {F : Expr} {k h : ℕ} :
    termOf kz ks ki (some h :: env) (F.rename (· + (k + 1))) =
      termOf kz ks ki env (F.rename (· + k)) := by
  rw [termOf, termOf, rename_rename, rename_rename]
  rfl

/-- An LF context of proofs matches an environment, an internal context and hypotheses: it
matches the environment and the internal context at its term variables, each proof variable is
of the family of proofs of a formula that decodes to the hypothesis the environment indexes, and
the hypotheses are formulas. -/
structure PfCtx (G : Globals) (kz ks ki : ℕ) (ΓLF : Ctx) (env : List (Option ℕ))
    (Γ : List PartialHorn.Tree) (Φ : List Term) : Prop extends TmCtx ΓLF env Γ where
  pfVar : ∀ (i : ℕ) (F : Expr), ΓLF[i]? = some (pf F) →
    ∃ h φ, env[i]? = some (some h) ∧ termOf kz ks ki env (F.rename (· + (i + 1))) = some φ ∧
      Φ[h]? = some φ
  typed : ∀ φ ∈ Φ, typeIn G 0 Γ φ = some FreeTopos.omega

variable {Φ : List Term}

/-- A context matching an environment, an internal context and hypotheses, extended by the
family of terms of an encoded type, matches them extended by a term variable, the type, and the
hypotheses weakened. -/
theorem PfCtx.consTm (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {a : PartialHorn.Tree} {A : Expr}
    (ha : encTy a = some A) :
    PfCtx G kz ks ki (tm A :: ΓLF) (none :: env) (a :: Γ) (Φ.map weaken1) where
  toTmCtx := hc.toTmCtx.consTm ha
  pfVar i F hi := by
    rcases i with _ | i
    · exact absurd (Option.some.inj hi).symm pf_ne_tm
    · obtain ⟨h, φ, he, hφ, hΦ⟩ := hc.pfVar i F hi
      exact ⟨h, weaken1 φ, he, termOf_consTm hφ, by rw [List.getElem?_map, hΦ]; rfl⟩
  typed φ hφ := by
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
    exact typeIn_weaken1 (hc.typed ψ hψ)

/-- A context matching an environment, an internal context and hypotheses, extended by the
family of proofs of a formula that decodes to a formula, matches the environment extended by a
proof variable of the next hypothesis, the internal context, and the hypotheses extended by the
formula. -/
theorem PfCtx.consPf (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {F : Expr} {φ : MTerm}
    (hφ : termOf kz ks ki env F = some φ) (hφt : typeIn G 0 Γ φ = some FreeTopos.omega) :
    PfCtx G kz ks ki (pf F :: ΓLF) (some Φ.length :: env) Γ (Φ ++ [φ]) where
  shape b hb := by
    rcases List.mem_cons.mp hb with rfl | hb
    · exact .inr ⟨F, rfl⟩
    · exact hc.shape b hb
  tmVar i B hi := by
    rcases i with _ | i
    · exact absurd (Option.some.inj hi) pf_ne_tm
    · exact hc.tmVar i B hi
  enc := hc.enc
  pfVar i F' hi := by
    rcases i with _ | i
    · obtain rfl : F = F' := pf_inj (Option.some.inj hi)
      refine ⟨Φ.length, φ, rfl, ?_, by
        rw [List.getElem?_append_right (le_refl _), Nat.sub_self]; rfl⟩
      rw [termOf, rename_rename]
      exact hφ
    · obtain ⟨h, ψ, he, hψ, hΦ⟩ := hc.pfVar i F' hi
      refine ⟨h, ψ, he, by rw [termOf_consPf]; exact hψ, ?_⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hΦ).1, hΦ]
  typed ψ hψ := by
    rcases List.mem_append.mp hψ with hψ | hψ
    · exact hc.typed ψ hψ
    · obtain rfl := List.mem_singleton.mp hψ
      exact hφt

/-- A context matching an environment, an internal context and hypotheses matches them with a
further formula among the hypotheses. -/
theorem PfCtx.addHyp (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {ψ : Term}
    (hψ : typeIn G 0 Γ ψ = some FreeTopos.omega) : PfCtx G kz ks ki ΓLF env Γ (Φ ++ [ψ]) where
  toTmCtx := hc.toTmCtx
  pfVar i F hi := by
    obtain ⟨h, φ, he, hφ, hΦ⟩ := hc.pfVar i F hi
    exact ⟨h, φ, he, hφ, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hΦ).1,
      hΦ]⟩
  typed φ hφ := by
    rcases List.mem_append.mp hφ with hφ | hφ
    · exact hc.typed φ hφ
    · obtain rfl := List.mem_singleton.mp hφ
      exact hψ

/-- The declarations whose types end in {lit}`pf` are the rules, of indices from 18 to 29. -/
theorem sig_head_pf {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 17) :
    18 ≤ c ∧ c ≤ 29 := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 17) || (18 ≤ p.2 && p.2 ≤ 29)) =
      true := by decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact this

/-- The decoding of an LF abstraction of a proof is its body's. -/
theorem decPf_lam (body : Expr) (env : List (Option ℕ)) (m : ℕ) :
    decPf kz ks ki (Expr.lam body) env m = decPf kz ks ki body env m :=
  congrFun (congrFun (RoseTree.para_node _ _ _) env) m

variable (G) (E : Array Entry) (kz ks ki) in
/-- The soundness of the decoding of proofs at a term: in every context matching an environment,
an internal context and hypotheses, where the term checks against the family of proofs of a
formula that decodes, it decodes to a derivation that proves the decoding. -/
def PfSoundAt (M : Expr) : Prop :=
  ∀ (ΓLF : Ctx) (env : List (Option ℕ)) (Γ : List PartialHorn.Tree) (Φ : List Term) (F : Expr)
    (φ : MTerm), PfCtx G kz ks ki ΓLF env Γ Φ → judge sig M ΓLF (.check (pf F)) = true →
    termOf kz ks ki env F = some φ →
    ∃ D, decPf kz ks ki M env Φ.length = some D ∧ (check G E 0 D).2 Γ Φ φ = true

/-- A property of the bodies of a term where it checks against a product: the term is an
abstraction whose body checks against the codomain, and has the property. -/
def PfLam (Q : Expr → Prop) (M : Expr) : Prop :=
  ∀ (ΓLF : Ctx) (T P : Expr), judge sig M ΓLF (.check (Expr.pi T P)) = true →
    ∃ body, M = Expr.lam body ∧ judge sig body (T :: ΓLF) (.check P) = true ∧ Q body

variable (G) (E : Array Entry) (kz ks ki) in
/-- The soundness of the decoding of proofs at a term, and at the bodies of one and of two
abstractions it is: the premises of the rules bind at most two variables. -/
def PfSound (M : Expr) : Prop :=
  PfSoundAt G kz ks ki E M ∧
    PfLam (fun b ↦ PfSoundAt G kz ks ki E b ∧ PfLam (PfSoundAt G kz ks ki E) b) M

/-- Substitution into an expression weakened past the substituted variable gives it. -/
theorem hsubWith_shift (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red (e.rename Nat.succ) n 0 = some e :=
  hsubWith_vacuous red e n 0

/-- Substitution into an expression weakened past the substituted variable, under a binder, gives
it. -/
theorem hsubWith_shift₁ (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red (e.rename (liftR Nat.succ)) n 1 = some e :=
  hsubWith_vacuous red e n 1

/-- Substitution under a binder into an expression weakened twice gives it weakened once. -/
theorem hsubWith_shift_shift (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red ((e.rename Nat.succ).rename Nat.succ) n 1 = some (e.rename Nat.succ) := by
  rw [show (e.rename Nat.succ).rename Nat.succ = (e.rename Nat.succ).rename (liftR Nat.succ) by
    rw [rename_rename, rename_rename]; rfl]
  exact hsubWith_shift₁ red _ n

/-- Substitution under two binders into an expression weakened thrice gives it weakened twice. -/
theorem hsubWith_shift₃ (red : Expr → List Expr → Option Expr) (e n : Expr) :
    hsubWith red (((e.rename Nat.succ).rename Nat.succ).rename Nat.succ) n 2 =
      some ((e.rename Nat.succ).rename Nat.succ) := by
  rw [show ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ =
      ((e.rename Nat.succ).rename Nat.succ).rename (liftR^[2] Nat.succ) by
    rw [rename_rename, rename_rename, rename_rename, rename_rename]; rfl]
  exact hsubWith_vacuous red _ n 2

/-- In an expression judged with a family of terms innermost, the innermost variable occurs
unapplied, the family being of base type. -/
theorem appliedAt_of_judge_tm {E A : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ, Expr.TypeShape a = true)
    (hA : A.FreeBelow 0 = true) {md : Mode} (hmd : ModeShape md = true)
    (hj : judge sig E (tm A :: Γ) md = true) :
    Expr.AppliedAt (EtaLongSpine (RoseTree.node (SimpleLabel.base 6) [])) E 0 = true := by
  have hΓ' : ∀ a ∈ tm A :: Γ, Expr.TypeShape a = true := fun a ha ↦ by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓ a ha
  exact (judge_appliedAt sig_ok E (tm A :: Γ) md hΓ' hmd hj).1 0 (tm A)
    (by rw [varType, List.getElem?_cons_zero, Option.map_some, rename_closed (tm_closed hA)])

/-- Substituting the innermost variable of a family of terms for the variable it renames, in an
expression judged with it, gives the expression: its occurrences are unapplied, the family being
of base type. -/
theorem hsub_var0_self {E A : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ, Expr.TypeShape a = true)
    (hA : A.FreeBelow 0 = true) {md : Mode} (hmd : ModeShape md = true)
    (hj : judge sig E (tm A :: Γ) md = true) :
    hsubWith (reduceStep (SimpleLabel.base 6) []) (E.rename (liftR Nat.succ))
      (RoseTree.node (.app (.var 0)) []) 0 = some E := by
  have h := hsub_eta_identity (appliedAt_of_judge_tm hΓ hA hmd hj)
  rw [hsub_eq, show reduce (RoseTree.node (SimpleLabel.base 6) []) =
    reduceStep (SimpleLabel.base 6) [] from reduce_node _ _] at h
  exact h

/-- Substituting the innermost variable for itself in an expression weakened under it, where the
expression is judged with a family of terms innermost, gives the weakened expression. -/
theorem hsub_var0_self_weak {E A : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ, Expr.TypeShape a = true)
    (hA : A.FreeBelow 0 = true) {P : Expr} (hP : P.TypeShape = true)
    (hj : judge sig E (tm A :: Γ) (.check P) = true) :
    hsubWith (reduceStep (SimpleLabel.base 6) [])
      ((E.rename (liftR Nat.succ)).rename (liftR Nat.succ)) (RoseTree.node (.app (.var 0)) []) 0 =
        some (E.rename (liftR Nat.succ)) := by
  have hj' := judge_rename (Sig.ok_closed sig_ok) E (.check P)
    (CtxRen.lift (CtxRen.succ Γ (tm A)) (tm A)) hj
  rw [rename_closed (tm_closed hA)] at hj'
  refine hsub_var0_self (Γ := tm A :: Γ) (fun a ha ↦ ?_) hA ?_ hj'
  · rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓ a ha
  · simp only [Mode.rename, ModeShape, typeShape_rename, hP]

/-- Substitution at a base type into an expression whose occurrences of the substituted variable
are unapplied has a value: no reduction is needed. -/
theorem hsubWith_base_total (c : ℕ) :
    ∀ (e n : Expr) (j : ℕ),
      Expr.AppliedAt (EtaLongSpine (RoseTree.node (SimpleLabel.base c) [])) e j = true →
      ∃ e', hsubWith (reduceStep (SimpleLabel.base c) []) e n j = some e' :=
  RoseTree.ind fun l cs ih n j h ↦ by
    obtain ⟨hv, hcs⟩ := appliedAt_node_iff.mp h
    have hch : ∀ (m : Expr) (b : ℕ → ℕ), (∀ idx, b idx = l.binders idx) →
        ∃ ys, (cs.zipIdx.map fun p ↦ hsubWith (reduceStep (SimpleLabel.base c) []) p.1
          (Expr.shift^[b p.2] m) (j + b p.2)).mapM id = some ys := fun m b hb ↦
      exists_mapM_id _ fun k hk ↦ by
        simp only [List.length_map, List.length_zipIdx] at hk
        simp only [List.getElem_map, List.getElem_zipIdx, zero_add, hb]
        exact ih _ (List.getElem_mem hk) _ _ (hcs k hk)
    rcases l with _ | _ | _ | (i | c')
    rotate_left 3
    · obtain ⟨ys, hys⟩ := hch n (fun _ ↦ 0) fun _ ↦ rfl
      rw [hsubWith_var]
      have hys' : (cs.map fun x ↦ hsubWith (reduceStep (SimpleLabel.base c) []) x n j).mapM id =
          some ys := by
        rw [← hys]
        congr 1
        exact List.ext_getElem (by simp) fun k _ _ ↦ by simp
      rw [hys', Option.bind_some]
      by_cases hij : i = j
      · subst hij
        have hnil : cs = [] := by
          have := hv i rfl rfl
          simpa [EtaLongSpine, etaLong_node, etaLongStep] using this
        subst hnil
        obtain rfl : ys = [] := by simpa using hys'
        simp [reduceStep]
      · simp [hij]
    all_goals
      obtain ⟨ys, hys⟩ := hch n (fun idx ↦ Label.binders _ idx) fun _ ↦ rfl
      rw [hsubWith_node_of_ne _ _ (fun _ h ↦ by cases h)]
      exact ⟨_, by rw [hys]; rfl⟩

/-- Substituting a variable at a base type into a renaming of an expression whose occurrences of
the innermost variable are unapplied is a renaming of the expression: the one taking the
innermost variable to the substituted one. -/
theorem hsub_var_base {c : ℕ} {E : Expr}
    (hE : Expr.AppliedAt (EtaLongSpine (RoseTree.node (SimpleLabel.base c) [])) E 0 = true)
    (f ρ : ℕ → ℕ) (hf0 : f 0 = 0) (hf : ∀ i, f (i + 1) = ρ (i + 1) + 1) {k : ℕ} (hk : ρ 0 = k) :
    hsubWith (reduceStep (SimpleLabel.base c) []) (E.rename f) (Expr.var k []) 0 =
      some (E.rename ρ) := by
  have h := hsub_rename _ _ _ 0 ρ _ (hsub_eta_identity hE)
  rw [hsub_eq, show reduce (RoseTree.node (SimpleLabel.base c) []) =
    reduceStep (SimpleLabel.base c) [] from reduce_node _ _, rename_rename] at h
  rw [show f = liftR^[0 + 1] ρ ∘ liftR Nat.succ from funext fun i ↦ by
    rcases i with _ | i
    · exact hf0
    · exact hf i]
  rw [← hk]
  exact h

/-- Substitution into a renaming of an expression whose image skips the substituted variable
gives the renaming that lowers the variables above it. -/
theorem hsubWith_vacuous' (red : Expr → List Expr → Option Expr) (E n : Expr) {j : ℕ}
    {f g : ℕ → ℕ} (h : ∀ i, f i = (liftR^[j] Nat.succ) (g i)) :
    hsubWith red (E.rename f) n j = some (E.rename g) := by
  rw [show E.rename f = (E.rename g).rename (liftR^[j] Nat.succ) by
    rw [rename_rename]; exact congrArg _ (funext h)]
  exact hsubWith_vacuous red _ n j

/-- Substitution at a base type into a renaming of an expression, at the image of its innermost
variable, is the renaming of the substitution at the innermost variable, where the renaming
skips that image otherwise. -/
theorem hsub_hole {c : ℕ} {E n X : Expr}
    (hX : hsubWith (reduceStep (SimpleLabel.base c) []) E n 0 = some X) {τ σ : ℕ → ℕ} {j : ℕ}
    (hτ : τ 0 = j) (hσ : ∀ i, τ (i + 1) ≠ j ∧ renumber j (τ (i + 1)) = σ i) :
    hsubWith (reduceStep (SimpleLabel.base c) []) (E.rename τ) (n.rename σ) j =
      some (X.rename σ) := by
  have hred : RenameCompat (reduceStep (SimpleLabel.base c) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base c) []) =
      reduceStep (SimpleLabel.base c) [] from reduce_node _ _]
    exact reduce_rename _
  refine hsubWith_holeRen hred E n 0 j σ τ X ⟨hτ, fun i hi ↦ ?_⟩ hX
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  exact hσ i

/-- The computation of the instantiation of a declaration's type along a spine, in a
hypothesis. -/
local macro "lf_spine_at" h:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      hsubWith_shift, hsubWith_shift₁, hsubWith_shift_shift, hsubWith_shift₃, Expr.lam,
      $hs,*] at $h:ident))

/-- The variables of a context matching an environment are of no type ending in {lit}`tp`. -/
theorem TmCtx.heads₀ (hc : TmCtx ΓLF env Γ) :
    ∀ i t, varType ΓLF i = some t → t.TypeShape = true ∧ t.headDepth.1 ≠ some 0 := by
  intro i t ht
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp ht
  rw [typeShape_rename, headDepth_rename]
  rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F, rfl⟩ <;>
    exact ⟨by simp only [tm, pf, Expr.const, Expr.app, typeShape_node]; rfl,
      by simp only [tm, pf, Expr.const, Expr.app, headDepth_node, headDepthStep]; decide⟩

/-- The decoding of an application of a constant in an environment, from its arguments' renamings
and decodings. -/
theorem termOf_const (c : ℕ) (args : List Expr) :
    termOf kz ks ki env (Expr.const c args) =
      decStep kz ks ki (.app (.const c)) (args.map fun a ↦ (a.rename (tmIdx env),
        termOf kz ks ki env a)) := by
  rw [termOf, Expr.const, Expr.app, rename_app_node, dec_node, List.map_map]
  rfl

/-- The decoding of a proof that applies a constant, from its arguments' decodings. -/
theorem decPf_const (c : ℕ) (args : List Expr) (env : List (Option ℕ)) (m : ℕ) :
    decPf kz ks ki (Expr.const c args) env m =
      decPfStep kz ks ki (.app (.const c)) (args.map fun a ↦ (a, decPf kz ks ki a)) env m :=
  congrFun (congrFun (RoseTree.para_node _ _ _) env) m

/-- The decoding of an LF abstraction in an environment is the abstraction, over the placeholder
type, of its body's decoding in the environment extended by a term variable. -/
theorem termOf_lam (b : Expr) :
    termOf kz ks ki env (Expr.lam b) =
      (termOf kz ks ki (none :: env) b).map (Term.lam FreeTopos.one) := by
  rw [termOf, rename_lam, Expr.lam, dec_node]
  rfl

/-- The decoding of an expression into which a term of base type is substituted for the innermost
variable, in an environment, is the instantiation of the decoding of the expression, in the
environment extended by a term variable, at the decoding of the term. -/
theorem termOf_hsub₀ {e n e' : Expr} {s u : MTerm}
    (h : hsubWith (reduceStep (SimpleLabel.base 6) []) e n 0 = some e')
    (hs : termOf kz ks ki (none :: env) e = some s) (hu : termOf kz ks ki env n = some u) :
    termOf kz ks ki env e' = some (Term.subst s (instVar u)) := by
  rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) = reduceStep (SimpleLabel.base 6) []
    from reduce_node _ _] at h
  have h' := hsubWith_rename (reduce_rename _) e n 0 (tmIdx env) e' h
  rw [← substAt_zero]
  exact dec_hsub _ _ _ 0 _ s u hs hu h'

/-- A plain node is simple where its children are. -/
theorem simple_plain {l : FreeTopos.Internal.Label} {cs : List Term}
    (hl : ∀ a, l ≠ .lam a) (hn : l ≠ .natRec) (hli : l ≠ .listRec) (hr : ∀ c, l ≠ .roseRec c)
    (h : ∀ c ∈ cs, Term.Simple c = true) : Term.Simple (RoseTree.node l cs) = true := by
  rw [simple_node]
  have hall : (cs.map Term.Simple).all id = true := by
    rw [List.all_eq_true]
    intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact h c hc
  unfold simpleStep
  split
  · exact absurd rfl hn
  · exact absurd rfl hli
  · exact absurd rfl (hr _)
  · exact absurd rfl (hl _)
  · exact hall

/-- An abstraction is simple where its body is. -/
theorem simple_lam (a : PartialHorn.Tree) {b : Term} (h : Term.Simple b = true) :
    Term.Simple (Term.lam a b) = true := by
  rw [Term.lam, simple_node]
  simp only [List.map_cons, List.map_nil, simpleStep, List.length_cons, List.length_nil,
    zero_add, beq_self_eq_true, List.all_cons, List.all_nil, id, h, Bool.and_self]

/-- The decoded terms are simple. -/
theorem dec_simple : ∀ (e : Expr) (s : MTerm), dec kz ks ki e = some s → Term.Simple s = true :=
  RoseTree.ind fun l cs ih s h ↦ by
    rw [dec_node] at h
    unfold decStep at h
    have pl : ∀ {l : FreeTopos.Internal.Label} {ts : List Term}, (∀ a, l ≠ .lam a) →
        l ≠ .natRec → l ≠ .listRec → (∀ c, l ≠ .roseRec c) → (∀ c ∈ ts, Term.Simple c = true) →
        Term.Simple (RoseTree.node l ts) = true := fun h₁ h₂ h₃ h₄ h₅ ↦ simple_plain h₁ h₂ h₃ h₄ h₅
    split at h
    · obtain rfl := Option.some.inj h
      exact pl nofun nofun nofun nofun nofun
    · obtain rfl := Option.some.inj h
      exact pl nofun nofun nofun nofun nofun
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      have hu := ih u (by simp) su (hd (u, some su) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht, hu])
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht])
    · next _ _ p₁ p₂ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht])
    · next _ _ A dA p₂ f df heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      subst hsf
      have hf := ih f (by simp) sf (hd (f, some sf) (by simp))
      obtain ⟨a', b, rfl, rfl⟩ := relam_eq_some.mp h
      exact simple_lam a (simple_child (cs := [b]) hf (List.mem_singleton_self b))
    · next _ _ p₁ p₂ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      have hu := ih u (by simp) su (hd (u, some su) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht, hu])
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht])
    · next _ _ t dt heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hst
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht])
    · next _ _ A dA z dz f df m dm heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨c, hc, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sm, hsm, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sz, hsz, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨sf, hsf, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hsm hsz hsf
      have hz := ih z (by simp) sz (hd (z, some sz) (by simp))
      have hf := ih f (by simp) sf (hd (f, some sf) (by simp))
      have hm := ih m (by simp) sm (hd (m, some sm) (by simp))
      obtain ⟨a', b, rfl, rfl⟩ := relam_eq_some.mp hr
      have hr' := simple_lam c (simple_child (cs := [b]) hf (List.mem_singleton_self b))
      refine pl nofun nofun nofun nofun ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hm,
        true_and]
      exact pl nofun nofun nofun nofun (by simp [hz, hr'])
    · next _ _ p₁ t dt u du heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨st, hst, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨su, hsu, h⟩ := Option.bind_eq_some_iff.mp h
      obtain rfl := Option.some.inj h
      subst hst hsu
      have ht := ih t (by simp) st (hd (t, some st) (by simp))
      have hu := ih u (by simp) su (hd (u, some su) (by simp))
      exact pl nofun nofun nofun nofun (by simp [ht, hu])
    · next _ _ b db heq =>
      obtain ⟨rfl, hd⟩ := map_dec_eq heq
      obtain ⟨sb, hsb, rfl⟩ := Option.map_eq_some_iff.mp h
      subst hsb
      exact simple_lam _ (ih b (by simp) sb (hd (b, some sb) (by simp)))
    · exact absurd h (by simp)

/-- The decoding of an LF term weakened by a term variable, in the environment extended by it, is
the weakening of its decoding. -/
theorem termOf_shift {z : Expr} {sz : MTerm} (h : termOf kz ks ki env z = some sz) :
    termOf kz ks ki (none :: env) (z.rename Nat.succ) = some (weaken1 sz) := by
  have := dec_rename _ Nat.succ sz h
  rw [rename_rename] at this
  rw [termOf, rename_rename]
  exact this

/-- The decoding of an LF term weakened by a term variable under the innermost one, in the
environment extended by it under the innermost, is the weakening of its decoding under the
innermost variable. -/
theorem termOf_shift_lift {e : Expr} {x : MTerm} (h : termOf kz ks ki (none :: env) e = some x) :
    termOf kz ks ki (none :: none :: env) (e.rename (liftR Nat.succ)) =
      some (Term.rename x (liftR Nat.succ)) := by
  have := dec_rename _ (liftR Nat.succ) x h
  rw [rename_rename] at this
  rw [termOf, rename_rename, show tmIdx (none :: none :: env) ∘ liftR Nat.succ =
    liftR Nat.succ ∘ tmIdx (none :: env) from funext fun i ↦ by rcases i with _ | i <;> rfl]
  exact this

/-- The decoded terms in an environment are simple. -/
theorem termOf_simple {e : Expr} {s : MTerm} (h : termOf kz ks ki env e = some s) :
    Term.Simple s = true :=
  dec_simple _ s h

/-- A term weakened by a variable and instantiated at a term is itself. -/
theorem subst_weaken1_instVar {t : Term} (ht : Term.VarLeaves t = true) (u : Term) :
    Term.subst (weaken1 t) (instVar u) = t := by
  rw [weaken1, Term.subst_rename t (· + 1) _ Term.var fun _ ↦ rfl,
    Term.subst_id t ht _ fun _ ↦ rfl]

/-- A term weakened under the innermost variable and substituted at the lifted instantiation is
itself. -/
theorem subst_rename_liftR_liftS {t : Term} (ht : Term.VarLeaves t = true) (u : Term) :
    Term.subst (Term.rename t (liftR Nat.succ)) (Term.liftS (instVar u)) = t := by
  rw [Term.subst_rename t _ _ Term.var fun i ↦ by rcases i with _ | i <;> rfl,
    Term.subst_id t ht _ fun _ ↦ rfl]

/-- The decoding of the right side of the computation of the fold at a successor: the step at
the fold of the predecessor, the step instantiated at it after its substitution under the
predecessor's binder. -/
theorem natSucc_rhs (c : PartialHorn.Tree) {sz ssb sn : Term} (hz : Term.VarLeaves sz = true)
    (hb : Term.VarLeaves ssb = true) :
    Term.subst (Term.subst (Term.rename ssb (liftR Nat.succ)) (instVar (Term.defn ki [c]
        [Term.var 0, Term.pair (weaken1 sz) (Term.lam c (Term.rename ssb (liftR Nat.succ)))])))
      (instVar sn) =
    Term.subst ssb (instVar (Term.defn ki [c] [sn, Term.pair sz (Term.lam c ssb)])) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ssb _ _ _ fun i ↦ ?_
  rcases i with _ | i
  · change Term.subst (Term.defn ki [c] [Term.var 0, Term.pair (weaken1 sz)
      (Term.lam c (Term.rename ssb (liftR Nat.succ)))]) (instVar sn) = _
    rw [show Term.subst (Term.defn ki [c] [Term.var 0, Term.pair (weaken1 sz)
        (Term.lam c (Term.rename ssb (liftR Nat.succ)))]) (instVar sn) =
      Term.defn ki [c] [sn, Term.pair (Term.subst (weaken1 sz) (instVar sn))
        (Term.lam c (Term.subst (Term.rename ssb (liftR Nat.succ)) (Term.liftS (instVar sn))))]
      from rfl, subst_weaken1_instVar hz, subst_rename_liftR_liftS hb]
    rfl
  · rfl

/-- Iterated weakening of an application of a definition to two arguments. -/
theorem weaken1_iterate_defn (k₀ : ℕ) (θ : List PartialHorn.Tree) (a b : Term) :
    ∀ k : ℕ, weaken1^[k] (Term.defn k₀ θ [a, b]) =
      Term.defn k₀ θ [weaken1^[k] a, weaken1^[k] b] :=
  Nat.rec rfl fun k ih ↦ by
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    rfl

/-- Iterated weakening of an application of a fold whose start and step weakening leaves in
place. -/
theorem weaken1_iterate_app_natRec {Z S : Term} (hZ : Term.rename Z (· + 1) = Z)
    (hS : Term.rename S (Term.liftR (· + 1)) = S) (m p : Term) :
    ∀ k : ℕ, weaken1^[k] (Term.app (Term.natRec Z S m) p) =
      Term.app (Term.natRec Z S (weaken1^[k] m)) (weaken1^[k] p) :=
  Nat.rec rfl fun k ih ↦ by
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    simp only [weaken1, Term.app, Term.natRec, Term.rename_node, Term.renameStep, List.map_cons,
      List.map_nil, hZ, hS]

/-- The innermost term variable decodes to the innermost variable. -/
theorem termOf_var0 : termOf kz ks ki (none :: env) (Expr.var 0) = some (Term.var 0) := rfl

/-- The decoding of an LF term weakened by a proof variable, in the environment extended by it,
is its decoding. -/
theorem termOf_consPf_shift (F : Expr) (h : ℕ) :
    termOf kz ks ki (some h :: env) (F.rename Nat.succ) = termOf kz ks ki env F := by
  rw [termOf, termOf, rename_rename]
  rfl

variable (E : Array Entry) (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim)
  (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim)
  (hi : G.defs[ki]? = some (.language FreeTopos.Internal.iterDefn))

include hz hs hi in
/-- The soundness of the decoding of reflexivity. -/
theorem sound_refl (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (pf (eq (v 1) (v 0) (v 0)))))
      [(A, judge sig A), (t, judge sig t)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 18 [A, t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hA := spine_tp₁ hS
  obtain ⟨a, ha⟩ := tyComplete hc.heads₀ A hA
  have hAc := encTy_closed a A ha
  simp only [tm, tp, pf, eq, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc]
  obtain ⟨-, ht, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨u, hu, -⟩ := termOf_typed hz hs hi hc.toTmCtx ha ht
  rw [show RoseTree.node (.app (.const 16)) [A, t, t] = Expr.const 16 [A, t, t] from rfl,
    termOf_const] at hφ
  simp only [List.map_cons, List.map_nil, decStep, hu, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD reflD reflD, by rw [decPf_const]; rfl, check_join (check_refl _) (check_refl _)⟩

include hz hs hi in
/-- The soundness of the decoding of the computation of a pair's first component. -/
theorem sound_fstPair (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A B a b F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 1)) (Expr.pi (tm (v 1))
      (pf (eq (v 3) (fst (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 1)))))))
      [(A, judge sig A), (B, judge sig B), (a, judge sig a), (b, judge sig b)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 21 [A, B, a, b]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xb, hxb⟩ := tyComplete hc.heads₀ B hT.2
  have hAc := encTy_closed xa A hxa
  have hBc := encTy_closed xb B hxb
  simp only [tm, tp, pf, eq, fst, pair, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hBc, hsubWith_closed hBc]
  obtain ⟨-, -, ha, hb, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sa, hsa, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxb hb
  rw [show RoseTree.node (.app (.const 16)) [A, RoseTree.node (.app (.const 9))
      [A, B, RoseTree.node (.app (.const 8)) [A, B, a, b]], a] =
      Expr.const 16 [A, Expr.const 9 [A, B, Expr.const 8 [A, B, a, b]], a] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsa, hsb, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .fstPair) reflD, by rw [decPf_const]; rfl,
    check_join (check_fstPair _ _) (check_refl _)⟩


include hz hs hi in
/-- The soundness of the decoding of the computation of a pair's second component. -/
theorem sound_sndPair (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A B a b F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 1)) (Expr.pi (tm (v 1))
      (pf (eq (v 2) (snd (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 0)))))))
      [(A, judge sig A), (B, judge sig B), (a, judge sig a), (b, judge sig b)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 22 [A, B, a, b]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xb, hxb⟩ := tyComplete hc.heads₀ B hT.2
  have hAc := encTy_closed xa A hxa
  have hBc := encTy_closed xb B hxb
  simp only [tm, tp, pf, eq, snd, pair, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hBc, hsubWith_closed hBc]
  obtain ⟨-, -, ha, hb, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sa, hsa, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxb hb
  rw [show RoseTree.node (.app (.const 16)) [B, RoseTree.node (.app (.const 10))
      [A, B, RoseTree.node (.app (.const 8)) [A, B, a, b]], b] =
      Expr.const 16 [B, Expr.const 10 [A, B, Expr.const 8 [A, B, a, b]], b] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsa, hsb, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .sndPair) reflD, by rw [decPf_const]; rfl,
    check_join (check_sndPair _ _) (check_refl _)⟩

include hz hs hi in
/-- The soundness of the decoding of the η rule of pairs. -/
theorem sound_pairEta (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A B p F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (prod (v 1) (v 0)))
      (pf (eq (prod (v 2) (v 1))
        (pair (v 2) (v 1) (fst (v 2) (v 1) (v 0)) (snd (v 2) (v 1) (v 0))) (v 0))))))
      [(A, judge sig A), (B, judge sig B), (p, judge sig p)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 23 [A, B, p]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xb, hxb⟩ := tyComplete hc.heads₀ B hT.2
  have hAc := encTy_closed xa A hxa
  have hBc := encTy_closed xb B hxb
  simp only [tm, tp, pf, eq, prod, fst, snd, pair, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hBc, hsubWith_closed hBc]
  obtain ⟨-, -, hp, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  have hxab : encTy (FreeTopos.prod xa xb) = some (prod A B) := by
    rw [encTy_prod, hxa, hxb]; rfl
  obtain ⟨sp, hsp, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxab hp
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 2)) [A, B],
      RoseTree.node (.app (.const 8)) [A, B, RoseTree.node (.app (.const 9)) [A, B, p],
        RoseTree.node (.app (.const 10)) [A, B, p]], p] =
      Expr.const 16 [prod A B, Expr.const 8 [A, B, Expr.const 9 [A, B, p],
        Expr.const 10 [A, B, p]], p] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsp, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .pairEta) reflD, by rw [decPf_const]; rfl,
    check_join (check_pairEta _) (check_refl _)⟩

include hz hs hi in
/-- The soundness of the decoding of the η rule of the terminal object. -/
theorem sound_unitEta (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi (tm one) (pf (eq one (v 0) star))) [(t, judge sig t)] =
      some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 24 [t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, one, star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨ht, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨st, hst, hty⟩ := termOf_typed (a := FreeTopos.one) hz hs hi hc.toTmCtx rfl ht
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 1)) [], t,
      RoseTree.node (.app (.const 7)) []] = Expr.const 16 [one, t, Expr.const 7 []] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hst, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .unitEta) reflD, by rw [decPf_const]; rfl,
    check_join (check_unitEta hty) (check_refl _)⟩

include hz hs hi in
/-- The soundness of the decoding of β. -/
theorem sound_beta (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A B f a F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 0)))
      (Expr.pi (tm (v 2))
      (pf (eq (v 2) (app (v 3) (v 2) (lam (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0]))) (v 0))
        (Expr.var 1 [v 0])))))))
      [(A, judge sig A), (B, judge sig B), (f, judge sig f), (a, judge sig a)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 20 [A, B, f, a]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xb, hxb⟩ := tyComplete hc.heads₀ B hT.2
  have hAc := encTy_closed xa A hxa
  have hBc := encTy_closed xb B hxb
  simp only [tm, tp, pf, eq, app, lam, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hBc, hsubWith_closed hBc]
  obtain ⟨-, -, a₁, b, ⟨hf, h₁, h₂⟩, ha, a₂, h₃, b₁, h₄, hF⟩ := hS
  obtain ⟨fb, rfl, hfb⟩ := judge_check_pi_inv hf
  have hfbs : Expr.TypeShape (tm B) = true := by
    simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at h₁ h₂
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  rw [hsub_var0_self hΓs hAc (md := .check (tm B)) hfbs hfb, Option.some.injEq] at h₂
  rw [hsub_var0_self_weak hΓs hAc hfbs hfb, Option.some.injEq] at h₁
  subst h₁ h₂
  rw [hsubWith_shift₁, Option.some.injEq] at h₃
  subst h₃
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sa, hsa, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxa ha
  obtain ⟨sf, hsf, -⟩ := termOf_typed hz hs hi (hc.toTmCtx.consTm hxa) hxb hfb
  have hb₁ := termOf_hsub₀ h₄ hsf hsa
  rw [show RoseTree.node (.app (.const 16)) [B, RoseTree.node (.app (.const 12))
      [A, B, RoseTree.node (.app (.const 11)) [A, B, RoseTree.node .lam [fb]], a], b₁] =
      Expr.const 16 [B, Expr.const 12 [A, B, Expr.const 11 [A, B, Expr.lam fb], a], b₁]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsa, hsf, hb₁,
    rename_closed hAc, decTy_encTy xa A hxa, Option.map_some, relam_lam, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .beta) reflD, by rw [decPf_const]; rfl,
    check_join (check_beta _ _ _) (check_refl _)⟩

include hz hs hi in
/-- The soundness of the decoding of the computation of the fold at zero. -/
theorem sound_natZero (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {C z s F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 1)))
      (pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (Expr.var 1 [v 0])) zero) (v 1))))))
      [(C, judge sig C), (z, judge sig z), (s, judge sig s)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 25 [C, z, s]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨xc, hxc⟩ := tyComplete hc.heads₀ C (spine_tp₁ hS)
  have hCc := encTy_closed xc C hxc
  simp only [tm, tp, pf, eq, natRec, zero, zeroAt, star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hCc, hsubWith_closed hCc]
  obtain ⟨-, hz', hs', x, hx, hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hCs : Expr.TypeShape (tm C) = true := by
    simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at hx
  rw [hsub_var0_self (fun a ha ↦ (hc.typeShape a ha).1) hCc (md := .check (tm C)) hCs hsb,
    Option.some.injEq] at hx
  subst hx
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, -⟩ := termOf_typed hz hs hi (hc.toTmCtx.consTm hxc) hxc hsb
  rw [show RoseTree.node (.app (.const 16)) [C, RoseTree.node (.app (.const 15))
      [C, z, RoseTree.node .lam [sb], RoseTree.node (.app (.const 13))
        [RoseTree.node (.app (.const 7)) []]], z] =
      Expr.const 16 [C, Expr.const 15 [C, z, Expr.lam sb, Expr.const 13 [Expr.const 7 []]], z]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsz, hss,
    rename_closed hCc, decTy_encTy xc C hxc, Option.map_some, relam_lam, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (natZeroLhsD kz) reflD, by rw [decPf_const]; rfl,
    check_join (check_natZeroLhs hi hz _ _ _) (check_refl _)⟩

include hz hs hi in
/-- The soundness of the decoding of the computation of the fold at a successor. -/
theorem sound_natSucc (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {C z s n F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 1)))
      (Expr.pi (tm nat)
      (pf (eq (v 3) (natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (succ (v 0)))
        (Expr.var 1 [natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (v 0)])))))))
      [(C, judge sig C), (z, judge sig z), (s, judge sig s), (n, judge sig n)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 26 [C, z, s, n]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨xc, hxc⟩ := tyComplete hc.heads₀ C (spine_tp₁ hS)
  have hCc := encTy_closed xc C hxc
  simp only [tm, tp, pf, eq, natRec, succ, nat, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hCc, hsubWith_closed hCc]
  obtain ⟨-, hz', b₀, a₁, ⟨hs', h₂, b', h₂', h₃⟩, hn, b₁, h₅, a₃, h₆, hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hCs : Expr.TypeShape (tm C) = true := by
    simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at h₂ h₂' h₃
  rw [hsub_var0_self_weak hΓs hCc hCs hsb, Option.some.injEq] at h₂ h₂'
  subst h₂ h₂'
  rw [hsubWith_shift₁, Option.some.injEq] at h₅
  subst h₅
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, hzt⟩ := termOf_typed hz hs hi hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, hst⟩ := termOf_typed hz hs hi (hc.toTmCtx.consTm hxc) hxc hsb
  obtain ⟨sn, hsn, hnt⟩ := termOf_typed (a := FreeTopos.nat) hz hs hi hc.toTmCtx rfl hn
  have hR : termOf kz ks ki (none :: env) (Expr.const 15 [C, z.rename Nat.succ,
      Expr.lam (sb.rename (liftR Nat.succ)), Expr.var 0]) =
      some (Term.defn ki [xc] [Term.var 0, Term.pair (weaken1 sz)
        (Term.lam xc (Term.rename ss (liftR Nat.succ)))]) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep,
      termOf_shift hsz, termOf_shift_lift hss, rename_closed hCc, decTy_encTy xc C hxc,
      Option.map_some, relam_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have ha₁ := termOf_hsub₀ (env := none :: env) h₃ (termOf_shift_lift hss) hR
  have ha₃ := termOf_hsub₀ h₆ ha₁ hsn
  rw [natSucc_rhs xc (varLeaves_of_typeIn hzt) (varLeaves_of_typeIn hst)] at ha₃
  rw [show RoseTree.node (.app (.const 16)) [C, RoseTree.node (.app (.const 15))
      [C, z, RoseTree.node .lam [sb], RoseTree.node (.app (.const 14)) [n]], a₃] =
      Expr.const 16 [C, Expr.const 15 [C, z, Expr.lam sb, Expr.const 14 [n]], a₃]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsz, hss, hsn,
    ha₃, rename_closed hCc, decTy_encTy xc C hxc, Option.map_some, relam_lam,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_eq_map,
    Option.some.injEq] at hφ
  subst hφ
  refine ⟨joinD (natSuccLhsD ks) (congAlong (ruleD .delta) ss 0), ?_, ?_⟩
  · rw [decPf_const]
    simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hss, Option.map_some,
      Option.bind_eq_bind, Option.bind_some, lamBody, Term.lam, RoseTree.label_node,
      RoseTree.children_node, Option.pure_def]
  · have hd : ∀ (k : ℕ) (Δ : List PartialHorn.Tree),
        (check G E 0 (ruleD .delta)).1 Δ ((List.map weaken1)^[k] Φ)
          (weaken1^[k] (Term.defn ki [xc] [sn, Term.pair sz (Term.lam xc ss)])) =
        some (weaken1^[k] (Term.app (Term.natRec (iterStart xc) (iterStep xc) sn)
          (Term.pair sz (Term.lam xc ss)))) := fun k Δ ↦ by
      rw [weaken1_iterate_defn, weaken1_iterate_app_natRec rfl rfl]
      exact check_delta_iter hi _ _ _
    have := check_congAlong hd ss (termOf_simple hss) 0 Γ
    simp only [Function.iterate_zero, id, substAt_zero] at this
    exact check_join (check_natSuccLhs hi hs xc (varLeaves_of_typeIn hnt) sz ss) this

include hz hs hi in
/-- The soundness of the decoding of function extensionality. -/
theorem sound_funExt (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A B f g dH F : Expr} {φ : MTerm}
    (ihH : PfLam (PfSoundAt G kz ks ki E) dH)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (exp (v 1) (v 0)))
      (Expr.pi (tm (exp (v 2) (v 1)))
      (Expr.arrow (Expr.pi (tm (v 3))
          (pf (eq (v 3) (app (v 4) (v 3) (v 2) (v 0)) (app (v 4) (v 3) (v 1) (v 0)))))
        (pf (eq (exp (v 3) (v 2)) (v 1) (v 0))))))))
      [(A, judge sig A), (B, judge sig B), (f, judge sig f), (g, judge sig g),
        (dH, judge sig dH)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 27 [A, B, f, g, dH]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xb, hxb⟩ := tyComplete hc.heads₀ B hT.2
  have hAc := encTy_closed xa A hxa
  have hBc := encTy_closed xb B hxb
  simp only [tm, tp, pf, eq, exp, app, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hBc, hsubWith_closed hBc]
  obtain ⟨-, -, hf, hg, hdH, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  have hxab : encTy (FreeTopos.exp xa xb) = some (exp A B) := by
    rw [encTy_exp, hxa, hxb]; rfl
  obtain ⟨sf, hsf, hft⟩ := termOf_typed hz hs hi hc.toTmCtx hxab hf
  obtain ⟨sg, hsg, -⟩ := termOf_typed hz hs hi hc.toTmCtx hxab hg
  obtain ⟨body, rfl, hbody, hsound⟩ := ihH ΓLF _ _ hdH
  have hF' : termOf kz ks ki (none :: env) (Expr.const 16 [B,
      Expr.const 12 [A, B, f.rename Nat.succ, Expr.var 0],
      Expr.const 12 [A, B, g.rename Nat.succ, Expr.var 0]]) =
      some (Term.eq (Term.app (weaken1 sf) (Term.var 0)) (Term.app (weaken1 sg) (Term.var 0))) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, termOf_shift hsf,
      termOf_shift hsg, termOf_var0, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨D', hD', hcheck⟩ := hsound _ _ _ _ _ _ (hc.consTm hxa) hbody hF'
  rw [List.length_map] at hD'
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 3)) [A, B], f, g] =
      Expr.const 16 [Expr.const 3 [A, B], f, g] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsf, hsg, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  refine ⟨nd .funExt [D'], ?_, check_funExt hft hcheck⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, decPf_lam, hD', Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]

include hz hs hi in
/-- The soundness of the decoding of propositional extensionality. -/
theorem sound_propExt (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {P Q d₁ d₂ F : Expr} {φ : MTerm}
    (ih₁ : PfLam (PfSoundAt G kz ks ki E) d₁) (ih₂ : PfLam (PfSoundAt G kz ks ki E) d₂)
    (hS : spine ΓLF (Expr.pi (tm omega) (Expr.pi (tm omega)
      (Expr.arrow (Expr.arrow (pf (v 1)) (pf (v 0)))
        (Expr.arrow (Expr.arrow (pf (v 0)) (pf (v 1))) (pf (eq omega (v 1) (v 0)))))))
      [(P, judge sig P), (Q, judge sig Q), (d₁, judge sig d₁), (d₂, judge sig d₂)] =
        some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 28 [P, Q, d₁, d₂]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, omega, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨hP, hQ, hd₁, hd₂, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sP, hsP, hPt⟩ := termOf_typed (a := FreeTopos.omega) hz hs hi hc.toTmCtx rfl hP
  obtain ⟨sQ, hsQ, hQt⟩ := termOf_typed (a := FreeTopos.omega) hz hs hi hc.toTmCtx rfl hQ
  obtain ⟨b₁, rfl, hb₁, hsound₁⟩ := ih₁ ΓLF _ _ hd₁
  obtain ⟨b₂, rfl, hb₂, hsound₂⟩ := ih₂ ΓLF _ _ hd₂
  obtain ⟨D₁, hD₁, hc₁⟩ := hsound₁ _ _ _ _ _ _ (hc.consPf hsP hPt) hb₁
    (by rw [termOf_consPf_shift]; exact hsQ)
  obtain ⟨D₂, hD₂, hc₂⟩ := hsound₂ _ _ _ _ _ _ (hc.consPf hsQ hQt) hb₂
    (by rw [termOf_consPf_shift]; exact hsP)
  rw [List.length_append, List.length_singleton] at hD₁ hD₂
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 4)) [], P, Q] =
      Expr.const 16 [omega, P, Q] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsP, hsQ, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  refine ⟨nd .propExt [D₁, D₂], ?_, check_propExt hPt hQt hc₁ hc₂⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, decPf_lam, hD₁, hD₂, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def]

include hz hs hi in
/-- The soundness of the decoding of the substitution of equals. -/
theorem sound_leib (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {A P t u dh dp F : Expr} {φ : MTerm}
    (ihh : PfSoundAt G kz ks ki E dh) (ihp : PfSoundAt G kz ks ki E dp)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 0)) (tm omega))
      (Expr.pi (tm (v 1)) (Expr.pi (tm (v 2))
      (Expr.arrow (pf (eq (v 3) (v 1) (v 0)))
        (Expr.arrow (pf (Expr.var 2 [v 1])) (pf (Expr.var 2 [v 0]))))))))
      [(A, judge sig A), (P, judge sig P), (t, judge sig t), (u, judge sig u),
        (dh, judge sig dh), (dp, judge sig dp)] = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 19 [A, P, t, u, dh, dp]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A (spine_tp₁ hS)
  have hAc := encTy_closed xa A hxa
  simp only [tm, tp, pf, eq, omega, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc]
  obtain ⟨-, a, b, ⟨hP, ha, hb⟩, a₁, b₁, ⟨ht, ha₁, hb₁⟩, a', b', ⟨hu, ha', hb'⟩, a₂, a₃,
    ⟨hdh, ha₂, ha₃⟩, hdp, x, hx, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha hb
  rw [rename_rename, rename_rename] at ha
  rw [rename_rename, rename_rename, rename_rename] at hb
  rw [rename_rename] at ha₁ hb'
  rw [rename_rename, rename_rename] at hb₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm hΓs hAc hOs hPb
  obtain ⟨Xt, hXt⟩ := hsubWith_base_total 6 Pb t 0 hApp
  obtain ⟨Xu, hXu⟩ := hsubWith_base_total 6 Pb u 0 hApp
  have hσ₂ : ∀ i : ℕ, i + 1 + 2 ≠ 2 ∧ renumber 2 (i + 1 + 2) = (Nat.succ ∘ Nat.succ) i :=
    fun i ↦ ⟨by omega, by simp only [renumber, Function.comp_apply]; split_ifs <;> omega⟩
  -- the motive at `t`, the type of `dp`
  obtain rfl := Option.some.inj (ha.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ) (· + 2) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_hole hXt (τ := (· + 2)) rfl hσ₂))
  obtain rfl := Option.some.inj (ha'.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := Nat.succ) fun _ ↦ rfl))
  rw [hsubWith_shift, Option.some.injEq] at ha₂
  subst ha₂
  -- the motive at `u`, the conclusion
  obtain rfl := Option.some.inj (hb.symm.trans (hsub_var_base hApp
    (((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 2 | k + 1 => k + 4) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (hb₁.symm.trans (hsubWith_vacuous' _ _ _ (j := 3)
    (g := fun i ↦ match i with | 0 => 2 | k + 1 => k + 3) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (hb'.symm.trans (hsub_hole hXu
    (τ := fun i ↦ match i with | 0 => 2 | k + 1 => k + 3) rfl hσ₂))
  obtain rfl := Option.some.inj (ha₃.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := Nat.succ) fun _ ↦ rfl))
  rw [hsubWith_shift, Option.some.injEq] at hx
  subst hx
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨st, hst, htt⟩ := termOf_typed hz hs hi hc.toTmCtx hxa ht
  obtain ⟨su, hsu, hut⟩ := termOf_typed hz hs hi hc.toTmCtx hxa hu
  obtain ⟨sp, hsp, -⟩ := termOf_typed (a := FreeTopos.omega) hz hs hi (hc.toTmCtx.consTm hxa)
    rfl hPb
  have hXt' := termOf_hsub₀ hXt hsp hst
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ hXu hsp hsu))
  have heq : termOf kz ks ki env (Expr.const 16 [A, t, u]) = some (Term.eq st su) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, hst, hsu,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hψ := typeIn_eq htt hut
  obtain ⟨Dh, hDh, hch⟩ := ihh _ _ _ _ _ _ hc hdh heq
  obtain ⟨Dp, hDp, hcp⟩ := ihp _ _ _ _ _ _ (hc.addHyp hψ) hdp hXt'
  rw [List.length_append, List.length_singleton] at hDp
  refine ⟨leibD sp st su Φ.length Dh Dp, ?_, check_leibD (termOf_simple hsp) hψ hch hcp⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hst, hsu, hDh, hDp,
    Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody, Term.lam,
    RoseTree.label_node, RoseTree.children_node, Option.pure_def]

include hz hs hi in
/-- The soundness of the decoding of induction on the natural numbers. -/
theorem sound_natInd (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {P d₀ ds n F : Expr} {φ : MTerm}
    (ih₀ : PfSoundAt G kz ks ki E d₀)
    (ihs : PfLam (fun b ↦ PfLam (PfSoundAt G kz ks ki E) b) ds)
    (hS : spine ΓLF (Expr.pi (Expr.arrow (tm nat) (tm omega))
      (Expr.arrow (pf (Expr.var 0 [zero]))
        (Expr.arrow (Expr.pi (tm nat) (Expr.arrow (pf (Expr.var 1 [v 0]))
            (pf (Expr.var 1 [succ (v 0)]))))
          (Expr.pi (tm nat) (pf (Expr.var 1 [v 0]))))))
      [(P, judge sig P), (d₀, judge sig d₀), (ds, judge sig ds), (n, judge sig n)] =
        some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.const 29 [P, d₀, ds, n]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  simp only [tm, pf, nat, omega, zero, zeroAt, star, succ, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨a, a₁, b, a₂, ⟨hP, ha, ha₁, hb, ha₂⟩, a₃, b₁, a₄, ⟨hd₀, ha₃, hb₁, ha₄⟩, a', ⟨hds, ha'⟩,
    hn, a₅, ha₅, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha ha₁ hb ha₂
  rw [rename_rename] at ha₁ hb₁ ha₄
  rw [rename_rename, rename_rename] at hb ha₂
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hnatc : nat.FreeBelow 0 = true := rfl
  have hApp := appliedAt_of_judge_tm hΓs hnatc hOs hPb
  -- the motive at the step's variable, the type of the step's hypothesis
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_var_base hApp
    (liftR Nat.succ ∘ liftR Nat.succ) (liftR Nat.succ) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₃.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  -- the motive at the conclusion's variable
  obtain rfl := Option.some.inj (ha₂.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | k + 1 => k + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₄.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (ha'.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  -- the motive at the successor of the step's variable, the step's conclusion
  have hR2 : CtxRen ΓLF (tm nat :: tm nat :: ΓLF) (Nat.succ ∘ Nat.succ) := fun i T hT ↦ by
    have h₂ := CtxRen.succ (tm nat :: ΓLF) (tm nat) _ _ (CtxRen.succ ΓLF (tm nat) i T hT)
    rwa [rename_rename] at h₂
  have hPb2 := judge_rename (Sig.ok_closed sig_ok) Pb _ (CtxRen.lift hR2 (tm nat)) hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR (Nat.succ ∘ Nat.succ)) = tm omega from
      rename_closed (tm_closed rfl) _] at hPb2
  have hΓs2 : ∀ x ∈ tm nat :: tm nat :: ΓLF, Expr.TypeShape x = true := fun x hx ↦ by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs x hx
  have hApp2 := appliedAt_of_judge_tm hΓs2 hnatc hOs hPb2
  obtain ⟨Y, hY⟩ := hsubWith_base_total 6 _ (Expr.const 14 [Expr.var 1 []]) 0 hApp2
  have hred : RenameCompat (reduceStep (SimpleLabel.base 6) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) =
      reduceStep (SimpleLabel.base 6) [] from reduce_node _ _]
    exact reduce_rename _
  have hbY := hsubWith_rename hred _ _ 0 (liftR^[2] Nat.succ) Y hY
  rw [rename_rename, show liftR^[0 + 1] (liftR^[2] Nat.succ) ∘ liftR (Nat.succ ∘ Nat.succ) =
    (liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ from
      funext fun i ↦ by rcases i with _ | i <;> rfl] at hbY
  obtain rfl := Option.some.inj (hb.symm.trans hbY)
  rw [Function.iterate_zero_apply, hsubWith_vacuous, Option.some.injEq] at hb₁
  subst hb₁
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hz hs hi
    (hc.toTmCtx.consTm (a := FreeTopos.nat) rfl) rfl hPb
  obtain ⟨sn, hsn, hnt⟩ := termOf_typed (a := FreeTopos.nat) hz hs hi hc.toTmCtx rfl hn
  have hid : termOf kz ks ki (none :: env) (Pb.rename id) = some sp := by
    rw [termOf, rename_rename]
    exact hsp
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₅ hid hsn))
  have hzero : termOf kz ks ki env (Expr.const 13 [Expr.const 7 []]) =
      some (Term.arr kz [] Term.star) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, Option.map_eq_map,
      Option.map_some]
  have ha0 := termOf_hsub₀ ha hsp hzero
  have hlen : (Φ.map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_singleton]
  have hc₂ := ((hc.consTm (a := FreeTopos.nat) (A := nat) rfl).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.nat :: Γ))).consPf hid hpt
  rw [hlen] at hc₂
  have hY' : termOf kz ks ki (some (Φ.length + 1) :: none :: env) Y =
      some (FreeTopos.Internal.natSuccAt ks sp) := by
    have h₁ : termOf kz ks ki (none :: some (Φ.length + 1) :: none :: env)
        (Pb.rename (liftR (Nat.succ ∘ Nat.succ))) = some (Term.rename sp (liftR Nat.succ)) := by
      have := dec_rename _ (liftR Nat.succ) sp hsp
      rw [rename_rename] at this
      rw [termOf, rename_rename, show tmIdx (none :: some (Φ.length + 1) :: none :: env) ∘
        liftR (Nat.succ ∘ Nat.succ) = liftR Nat.succ ∘ tmIdx (none :: env) from
          funext fun i ↦ by rcases i with _ | i <;> rfl]
      exact this
    have h₂ : termOf kz ks ki (some (Φ.length + 1) :: none :: env)
        (Expr.const 14 [Expr.var 1 []]) = some (Term.arr ks [] (Term.var 0)) := rfl
    rw [termOf_hsub₀ hY h₁ h₂, FreeTopos.Internal.natSuccAt,
      Term.subst_rename sp _ _ (FreeTopos.Internal.atVar0 (Term.arr ks [] (Term.var 0)))
        fun i ↦ by rcases i with _ | i <;> rfl]
  obtain ⟨D₀, hD₀, hc₀⟩ := ih₀ _ _ _ _ _ _ (hc.addHyp typeIn_truth) hd₀ ha0
  rw [List.length_append, List.length_singleton] at hD₀
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hsound⟩ := hlam _ _ _ hb1
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb2 hY'
  have hDs' : decPf kz ks ki body₂ (some (Φ.length + 1) :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  refine ⟨natIndD kz ks sp sn Φ.length D₀ Ds, ?_, check_natIndD hz hs hpt hnt hc.typed hc₀ hcs⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hsn, hD₀, decPf_lam,
    hDs', Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody,
    Term.lam, RoseTree.label_node, RoseTree.children_node, Option.pure_def]

/-- The soundness of the decoding of a proof variable: the hypothesis the environment indexes. -/
theorem sound_hyp (hc : PfCtx G kz ks ki ΓLF env Γ Φ) {i : ℕ} {ms : List Expr} {C F : Expr}
    {φ : MTerm} (hC : classOf sig ΓLF (.var i) = some C)
    (hS : spine ΓLF C (ms.map fun m ↦ (m, judge sig m)) = some (pf F))
    (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki (Expr.app (.var i) ms) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp hC
  have hCs : Expr.TypeShape (b.rename (· + (i + 1))) = true := by
    rw [typeShape_rename]
    rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F', rfl⟩ <;>
      · simp only [tm, pf, Expr.const, Expr.app, typeShape_node]; rfl
  obtain ⟨h₁, h₂⟩ := spine_headDepth _ _ _ hCs hS
  rw [headDepth_rename] at h₁ h₂
  rcases hc.shape b (List.mem_of_getElem? hb) with ⟨B, rfl⟩ | ⟨F', rfl⟩
  · simp only [tm, pf, Expr.const, Expr.app, headDepth_node, headDepthStep] at h₁
    exact absurd h₁ (by decide)
  · simp only [pf, Expr.const, Expr.app, headDepth_node, headDepthStep, List.length_map] at h₂
    obtain rfl := List.length_eq_zero_iff.mp (by omega : ms.length = 0)
    simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq] at hS
    obtain ⟨h, φ', he, hφ', hΦ⟩ := hc.pfVar i F' hb
    rw [pf, Expr.const, Expr.app, rename_app_node] at hS
    simp only [Head.rename, List.map_cons, List.map_nil, pf, Expr.const, Expr.app, node_inj,
      List.cons.injEq, and_true, true_and] at hS
    subst hS
    obtain rfl := Option.some.inj (hφ'.symm.trans hφ)
    refine ⟨ruleD (.hyp h), ?_, check_hyp hΦ⟩
    rw [decPf, Expr.app, RoseTree.para_node]
    simp only [List.map_nil, decPfStep, he]

include hz hs hi in
/-- The soundness of the decoding of proofs: a canonical LF term of the family of proofs of a
formula, in a context matching an environment, an internal context and hypotheses, where the
formula decodes, decodes to a derivation that the internal language's checker accepts as a proof
of the formula's decoding; and likewise at the bodies of one and of two abstractions it is. -/
theorem pfSound : ∀ M : Expr, PfSound G kz ks ki E M :=
  RoseTree.ind fun l cs ih ↦ by
    have hlam : ∀ c ∈ cs, PfLam (PfSoundAt G kz ks ki E) c := fun c hc ΓLF T P hj ↦ by
      obtain ⟨b, h₁, h₂, h₃, -⟩ := (ih c hc).2 ΓLF T P hj
      exact ⟨b, h₁, h₂, h₃⟩
    have hlam₂ : ∀ c ∈ cs, PfLam (fun b ↦ PfLam (PfSoundAt G kz ks ki E) b) c :=
      fun c hc ΓLF T P hj ↦ by
        obtain ⟨b, h₁, h₂, -, h₄⟩ := (ih c hc).2 ΓLF T P hj
        exact ⟨b, h₁, h₂, h₄⟩
    refine ⟨fun ΓLF env Γ Φ F φ hc hj hφ ↦ ?_, fun ΓLF T P hj ↦ ?_⟩
    · obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hM
      obtain ⟨C, hC, hS⟩ := judge_app_inv hj
      rcases h with i | c
      · exact sound_hyp E hc hC hS hφ
      have hCs := Sig.ok_typeShape sig_ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C _ hCs hS
      obtain ⟨hc₁, hc₂⟩ := sig_head_pf hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (pf F).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      have mem : ∀ {x : Expr} {xs : List Expr}, x ∈ x :: xs := List.mem_cons_self
      have mem' : ∀ {x y : Expr} {xs : List Expr}, x ∈ xs → x ∈ y :: xs := List.mem_cons_of_mem _
      interval_cases c
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, t, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        exact sound_refl E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨P, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨t, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        obtain ⟨u, dh, dp, rfl⟩ := List.length_eq_three.mp (Nat.succ.inj (Nat.succ.inj
          (Nat.succ.inj (hlen : cs.length + 1 + 1 + 1 = 3 + 1 + 1 + 1))))
        exact sound_leib E hz hs hi hc (ih dh (mem' (mem' (mem' (mem' mem))))).1
          (ih dp (mem' (mem' (mem' (mem' (mem' mem)))))).1 hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, f, a, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_beta E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, a, b, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_fstPair E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, a, b, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_sndPair E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, B, p, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_pairEta E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        exact sound_unitEta E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', z, s', rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_natZero E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨z, s', n, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_natSucc E hz hs hi hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        obtain ⟨f, g, dH, rfl⟩ := List.length_eq_three.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 3 + 1 + 1)))
        exact sound_funExt E hz hs hi hc (hlam dH (mem' (mem' (mem' (mem' mem))))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨Q, d₁, d₂, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_propExt E hz hs hi hc (hlam d₁ (mem' (mem' mem)))
          (hlam d₂ (mem' (mem' (mem' mem)))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨d₀, ds, n, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_natInd E hz hs hi hc (ih d₀ (mem' mem)).1 (hlam₂ ds (mem' (mem' mem))) hS hφ
    · obtain ⟨body, hM, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hM
      exact ⟨body, rfl, hbJ, (ih body List.mem_cons_self).1, hlam body List.mem_cons_self⟩

include hz hs hi in
/-- The soundness of the decoding of proofs, at a proof in a context matching an environment, an
internal context and hypotheses. -/
theorem decPf_sound {ΓLF : Ctx} {env : List (Option ℕ)} {Γ : List PartialHorn.Tree}
    {Φ : List Term} {M F : Expr} {φ : MTerm} (hc : PfCtx G kz ks ki ΓLF env Γ Φ)
    (hj : judge sig M ΓLF (.check (pf F)) = true) (hφ : termOf kz ks ki env F = some φ) :
    ∃ D, decPf kz ks ki M env Φ.length = some D ∧ (check G E 0 D).2 Γ Φ φ = true :=
  (pfSound E hz hs hi M).1 _ _ _ _ _ _ hc hj hφ

/-- The renaming of a context of term variables alone is the identity. -/
theorem tmIdx_replicate (n : ℕ) : ∀ i, tmIdx (List.replicate n none) i = i :=
  Nat.rec (motive := fun n ↦ ∀ i, tmIdx (List.replicate n none) i = i) (fun _ ↦ rfl)
    (fun n ih i ↦ by
      rcases i with _ | i
      · rfl
      · exact congrArg (· + 1) (ih i)) n

/-- The declarations of an encoded context are the families of terms of the encodings of its
types. -/
theorem encCtx_getElem? {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) {i : ℕ} {b : Expr}
    (hb : ΓLF[i]? = some b) : ∃ a A, Γ[i]? = some a ∧ encTy a = some A ∧ b = tm A := by
  rw [encCtx, PartialHorn.mapM_eq_some_iff] at h
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map, hb, Option.map_some] at hi
  obtain ⟨a, ha, hat⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hat
  exact ⟨a, A, ha, hA, rfl⟩

/-- An encoded context matches the environment of as many term variables, the internal context,
and no hypotheses. -/
theorem PfCtx.ofEnc {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) :
    PfCtx G kz ks ki ΓLF (List.replicate Γ.length none) Γ [] where
  shape b hb := by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    obtain ⟨-, A, -, -, he⟩ := encCtx_getElem? h (List.getElem?_eq_getElem hi)
    exact .inl ⟨A, he⟩
  tmVar i A hi := by
    obtain ⟨a, A', ha, hA', he⟩ := encCtx_getElem? h hi
    obtain rfl : A = A' := by simpa [tm, Expr.const, Expr.app, node_inj] using he
    rw [tmIdx_replicate]
    exact ⟨a, hA', ha⟩
  enc := ⟨ΓLF, h⟩
  pfVar i F hi := by
    obtain ⟨_, _, _, _, he⟩ := encCtx_getElem? h hi
    simp [tm, pf, Expr.const, Expr.app, node_inj] at he
  typed φ hφ := nomatch hφ

include hz hs hi in
/-- The soundness of the decoding of proofs, at a proof of a formula in a context of term
variables of encoded types: the proof decodes to a derivation that proves, as a theorem of the
internal language without hypotheses, the formula's decoding. -/
theorem decPf_checks {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) {M F : Expr}
    (hF : judge sig F ΓLF (.check (tm omega)) = true)
    (hj : judge sig M ΓLF (.check (pf F)) = true) :
    ∃ D φ, decPf kz ks ki M (List.replicate Γ.length none) 0 = some D ∧
      termOf kz ks ki (List.replicate Γ.length none) F = some φ ∧
      FreeTopos.Internal.Thm.checks G E ⟨0, Γ, [], φ⟩ D = true := by
  have hc : PfCtx G kz ks ki ΓLF (List.replicate Γ.length none) Γ [] := PfCtx.ofEnc h
  obtain ⟨φ, hφ, hφt⟩ := termOf_typed (a := FreeTopos.omega) hz hs hi hc.toTmCtx rfl hF
  obtain ⟨D, hD, hch⟩ := decPf_sound E hz hs hi hc hj hφ
  refine ⟨D, φ, hD, hφ, ?_⟩
  simp only [FreeTopos.Internal.Thm.checks, List.all_nil, Bool.and_true, hφt, decide_true,
    hch, List.all_eq_true]
  intro a ha
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha
  obtain ⟨A, hA, -⟩ := varType_encCtx h (List.getElem?_eq_getElem hi')
  exact isTy_of_encTy G _ A hA

end Geb.LF.Topos

end
