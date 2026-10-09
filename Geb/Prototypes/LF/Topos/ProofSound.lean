/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Topos.ProofCheck
import Mathlib.Data.Nat.Cast.Order.Basic -- shake: keep
import Mathlib.Tactic.NormNum
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

variable {G : Globals} {k : PrimIdx}

/-- The adequacy of the representation of terms in an LF context of proofs: a canonical term of
the family of terms of an encoded type, in a context matching an environment and an internal
context, decodes in the environment to a term of the type in the internal context. A term
mentions no proof variable, its type's products' domains being of terms, so that its renaming to
the internal context's variables checks in the context of the term variables alone. -/
theorem termOf_typed (hk : k.Valid G)
    (hc : TmCtx ΓLF env Γ) {a : PartialHorn.Tree} {A M : Expr} (ha : encTy a = some A)
    (hj : judge sig M ΓLF (.check (tm A)) = true) :
    ∃ s, termOf k env M = some s ∧ typeIn G 0 Γ s = some a := by
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
  obtain ⟨s, r, hd, hcomp, hr, -⟩ := (tmComplete hk (M.rename (tmIdx env))).1
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
theorem termOf_consTm {F : Expr} {j : ℕ} {φ : MTerm}
    (h : termOf k env (F.rename (· + j)) = some φ) :
    termOf k (none :: env) (F.rename (· + (j + 1))) = some (weaken1 φ) := by
  have := dec_rename _ (· + 1) φ h
  rw [rename_rename, rename_rename] at this
  rw [termOf, rename_rename]
  exact this

/-- The decoding of an LF term weakened by a proof variable, in the environment extended by it,
is its decoding. -/
theorem termOf_consPf {F : Expr} {j h : ℕ} :
    termOf k (some h :: env) (F.rename (· + (j + 1))) =
      termOf k env (F.rename (· + j)) := by
  rw [termOf, termOf, rename_rename, rename_rename]
  rfl

/-- An LF context of proofs matches an environment, an internal context and hypotheses: it
matches the environment and the internal context at its term variables, each proof variable is
of the family of proofs of a formula that decodes to the hypothesis the environment indexes, and
the hypotheses are formulas. -/
structure PfCtx (G : Globals) (k : PrimIdx) (ΓLF : Ctx) (env : List (Option ℕ))
    (Γ : List PartialHorn.Tree) (Φ : List Term) : Prop extends TmCtx ΓLF env Γ where
  pfVar : ∀ (i : ℕ) (F : Expr), ΓLF[i]? = some (pf F) →
    ∃ h φ, env[i]? = some (some h) ∧ termOf k env (F.rename (· + (i + 1))) = some φ ∧
      Φ[h]? = some φ
  typed : ∀ φ ∈ Φ, typeIn G 0 Γ φ = some FreeTopos.omega

variable {Φ : List Term}

/-- A context matching an environment, an internal context and hypotheses, extended by the
family of terms of an encoded type, matches them extended by a term variable, the type, and the
hypotheses weakened. -/
theorem PfCtx.consTm (hc : PfCtx G k ΓLF env Γ Φ) {a : PartialHorn.Tree} {A : Expr}
    (ha : encTy a = some A) :
    PfCtx G k (tm A :: ΓLF) (none :: env) (a :: Γ) (Φ.map weaken1) where
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
theorem PfCtx.consPf (hc : PfCtx G k ΓLF env Γ Φ) {F : Expr} {φ : MTerm}
    (hφ : termOf k env F = some φ) (hφt : typeIn G 0 Γ φ = some FreeTopos.omega) :
    PfCtx G k (pf F :: ΓLF) (some Φ.length :: env) Γ (Φ ++ [φ]) where
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
theorem PfCtx.addHyp (hc : PfCtx G k ΓLF env Γ Φ) {ψ : Term}
    (hψ : typeIn G 0 Γ ψ = some FreeTopos.omega) : PfCtx G k ΓLF env Γ (Φ ++ [ψ]) where
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

/-- The declarations whose types end in {lit}`pf` are the rules, of indices from 18 to 29, from
34 to 36, 40 and 41, and 45 and 46. -/
theorem sig_head_pf {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 17) :
    c ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 34, 35, 36, 40, 41, 45, 46] := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 17) ||
      decide (p.2 ∈ [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 34, 35, 36, 40, 41, 45, 46])) =
        true := by
    decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- The decoding of an LF abstraction of a proof is its body's. -/
theorem decPf_lam (body : Expr) (env : List (Option ℕ)) (m : ℕ) :
    decPf k (Expr.lam body) env m = decPf k body env m :=
  congrFun (congrFun (RoseTree.para_node _ _ _) env) m

variable (G) (E : Array Entry) (k) in
/-- The soundness of the decoding of proofs at a term: in every context matching an environment,
an internal context and hypotheses, where the term checks against the family of proofs of a
formula that decodes, it decodes to a derivation that proves the decoding. -/
def PfSoundAt (M : Expr) : Prop :=
  ∀ (ΓLF : Ctx) (env : List (Option ℕ)) (Γ : List PartialHorn.Tree) (Φ : List Term) (F : Expr)
    (φ : MTerm), PfCtx G k ΓLF env Γ Φ → judge sig M ΓLF (.check (pf F)) = true →
    termOf k env F = some φ →
    ∃ D, decPf k M env Φ.length = some D ∧ (check G E 0 D).2 Γ Φ φ = true

/-- A property of the bodies of a term where it checks against a product: the term is an
abstraction whose body checks against the codomain, and has the property. -/
def PfLam (Q : Expr → Prop) (M : Expr) : Prop :=
  ∀ (ΓLF : Ctx) (T P : Expr), judge sig M ΓLF (.check (Expr.pi T P)) = true →
    ∃ body, M = Expr.lam body ∧ judge sig body (T :: ΓLF) (.check P) = true ∧ Q body

variable (G) (E : Array Entry) (k) in
/-- The soundness of the decoding of proofs at a term, and at the bodies of one, of two and of
three abstractions it is: the premises of the rules bind at most three variables. -/
def PfSound (M : Expr) : Prop :=
  PfSoundAt G k E M ∧
    PfLam (fun b ↦ PfSoundAt G k E b ∧
      PfLam (fun b' ↦ PfSoundAt G k E b' ∧ PfLam (PfSoundAt G k E) b') b) M

/-- A property of the bodies of a term follows from a stronger one. -/
theorem PfLam.mono {Q Q' : Expr → Prop} {M : Expr} (h : PfLam Q M) (hQ : ∀ b, Q b → Q' b) :
    PfLam Q' M := fun ΓLF T P hj ↦ by
  obtain ⟨b, h₁, h₂, h₃⟩ := h ΓLF T P hj
  exact ⟨b, h₁, h₂, hQ b h₃⟩

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

/-- The application of a two-place LF abstraction, weakened past two variables, to the outer of
them, by hereditary substitution at a base type: the abstraction of its body with the bound
variable it replaces made the next. -/
theorem hsub_lam_var₁ {sb A C : Expr} {Γ : Ctx} (hΓ : ∀ a ∈ Γ, Expr.TypeShape a = true)
    (hA : A.FreeBelow 0 = true) (hj : judge sig sb (tm C :: tm A :: Γ) (.check (tm C)) = true) :
    hsubWith (reduceStep (SimpleLabel.base 6) [])
      ((Expr.lam sb).rename (liftR (Nat.succ ∘ Nat.succ)))
      (RoseTree.node (Label.app (Head.var 1)) []) 0 =
        some (Expr.lam (sb.rename (liftR Nat.succ))) := by
  have hP : ModeShape (.check (Expr.pi (tm C) (tm C))) = true := by
    simp only [ModeShape, Expr.pi, tm, Expr.const, Expr.app, typeShape_node]; rfl
  rw [show (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] from rfl,
    hsub_var_base (appliedAt_of_judge_tm hΓ hA hP (judge_lam hj)) (liftR (Nat.succ ∘ Nat.succ))
      (fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) rfl (fun _ ↦ rfl) rfl, rename_lam,
    show liftR (fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) = liftR Nat.succ from
      funext fun i ↦ by rcases i with _ | _ | i <;> rfl]

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
    termOf k env (Expr.const c args) =
      decStep k (.app (.const c)) (args.map fun a ↦ (a.rename (tmIdx env),
        termOf k env a)) := by
  rw [termOf, Expr.const, Expr.app, rename_app_node, dec_node, List.map_map]
  rfl

/-- The decoding of a proof that applies a constant, from its arguments' decodings. -/
theorem decPf_const (c : ℕ) (args : List Expr) (env : List (Option ℕ)) (m : ℕ) :
    decPf k (Expr.const c args) env m =
      decPfStep k (.app (.const c)) (args.map fun a ↦ (a, decPf k a)) env m :=
  congrFun (congrFun (RoseTree.para_node _ _ _) env) m

/-- The decoding of an LF abstraction in an environment is the abstraction, over the placeholder
type, of its body's decoding in the environment extended by a term variable. -/
theorem termOf_lam (b : Expr) :
    termOf k env (Expr.lam b) =
      (termOf k (none :: env) b).map (Term.lam FreeTopos.one) := by
  rw [termOf, rename_lam, Expr.lam, dec_node]
  rfl

/-- The decoding of an expression into which a term of base type is substituted for the innermost
variable, in an environment, is the instantiation of the decoding of the expression, in the
environment extended by a term variable, at the decoding of the term. -/
theorem termOf_hsub₀ {e n e' : Expr} {s u : MTerm}
    (h : hsubWith (reduceStep (SimpleLabel.base 6) []) e n 0 = some e')
    (hs : termOf k (none :: env) e = some s) (hu : termOf k env n = some u) :
    termOf k env e' = some (Term.subst s (instVar u)) := by
  rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) = reduceStep (SimpleLabel.base 6) []
    from reduce_node _ _] at h
  have h' := hsubWith_rename (reduce_rename _) e n 0 (tmIdx env) e' h
  rw [← substAt_zero]
  exact dec_hsub _ _ _ 0 _ s u hs hu h'

/-- The decoding of an LF term weakened by a term variable, in the environment extended by it, is
the weakening of its decoding. -/
theorem termOf_shift {z : Expr} {sz : MTerm} (h : termOf k env z = some sz) :
    termOf k (none :: env) (z.rename Nat.succ) = some (weaken1 sz) := by
  have := dec_rename _ Nat.succ sz h
  rw [rename_rename] at this
  rw [termOf, rename_rename]
  exact this

/-- The decoding of an LF term weakened by a term variable under the innermost one, in the
environment extended by it under the innermost, is the weakening of its decoding under the
innermost variable. -/
theorem termOf_shift_lift {e : Expr} {x : MTerm} (h : termOf k (none :: env) e = some x) :
    termOf k (none :: none :: env) (e.rename (liftR Nat.succ)) =
      some (Term.rename x (liftR Nat.succ)) := by
  have := dec_rename _ (liftR Nat.succ) x h
  rw [rename_rename] at this
  rw [termOf, rename_rename, show tmIdx (none :: none :: env) ∘ liftR Nat.succ =
    liftR Nat.succ ∘ tmIdx (none :: env) from funext fun i ↦ by rcases i with _ | i <;> rfl]
  exact this

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

/-- An expression weakened twice is weakened by two. -/
theorem rename_succ_two (e : Expr) : (e.rename Nat.succ).rename Nat.succ = e.rename (· + 2) := by
  rw [rename_rename]
  rfl

/-- An expression weakened four times is weakened by four. -/
theorem rename_succ_four (e : Expr) :
    (((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 4) := by
  rw [rename_rename, rename_rename, rename_rename]
  rfl

/-- The decoding of a renamed LF term, in an environment whose renaming of term variables agrees
with the renaming's: the decoding renamed. -/
theorem termOf_rename {env' : List (Option ℕ)} {e : Expr} {x : MTerm} (f g : ℕ → ℕ)
    (h : termOf k env e = some x) (hfg : ∀ i, tmIdx env' (f i) = g (tmIdx env i)) :
    termOf k env' (e.rename f) = some (Term.rename x g) := by
  have := dec_rename _ g x h
  rw [rename_rename] at this
  rw [termOf, rename_rename, show tmIdx env' ∘ f = g ∘ tmIdx env from funext hfg]
  exact this

/-- The decoding of an expression into which a term of base type is substituted for the variable
of index one, in an environment, is the substitution into the decoding of the expression, in the
environment extended by two term variables, of the decoding of the term, in the environment
extended by one. -/
theorem termOf_hsub₁ {e n e' : Expr} {s u : MTerm}
    (h : hsubWith (reduceStep (SimpleLabel.base 6) []) e n 1 = some e')
    (hs : termOf k (none :: none :: env) e = some s) (hu : termOf k (none :: env) n = some u) :
    termOf k (none :: env) e' = some (Term.subst s (substAt 1 u)) := by
  rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) = reduceStep (SimpleLabel.base 6) []
    from reduce_node _ _] at h
  exact dec_hsub _ _ _ 1 _ s u hs hu (hsubWith_rename (reduce_rename _) e n 1 (tmIdx env) e' h)

/-- The decoding of the right side of the computation of the fold at a successor: the step at
the fold of the predecessor, the step instantiated at it after its substitution under the
predecessor's binder. -/
theorem natSucc_rhs {sz ssb sn : Term} (hz : Term.VarLeaves sz = true)
    (hb : Term.VarLeaves ssb = true) :
    Term.subst (Term.subst (Term.rename ssb (liftR Nat.succ)) (instVar (Term.natRec (weaken1 sz)
        (Term.rename ssb (liftR Nat.succ)) (Term.var 0)))) (instVar sn) =
    Term.subst ssb (instVar (Term.natRec sz ssb sn)) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ssb _ _ _ fun i ↦ ?_
  rcases i with _ | i
  · change Term.subst (Term.natRec (weaken1 sz) (Term.rename ssb (liftR Nat.succ)) (Term.var 0))
      (instVar sn) = _
    rw [show Term.subst (Term.natRec (weaken1 sz) (Term.rename ssb (liftR Nat.succ)) (Term.var 0))
        (instVar sn) = Term.natRec (Term.subst (weaken1 sz) (instVar sn))
          (Term.subst (Term.rename ssb (liftR Nat.succ)) (Term.liftS (instVar sn))) sn from rfl,
      subst_weaken1_instVar hz, subst_rename_liftR_liftS hb]
    rfl
  · rfl

/-- The decoding of the right side of the computation of the fold of a list at a construction:
the step at the element and the fold of the rest, the step's two variables substituted in turn,
under the weakening past the element and the rest, and then the element and the rest. -/
theorem listCons_rhs {sz ss sh st : Term} (hz : Term.VarLeaves sz = true)
    (hs : Term.VarLeaves ss = true) (hh : Term.VarLeaves sh = true) :
    Term.subst (Term.subst (Term.subst
        (Term.rename ss (liftR fun i ↦ match i with | 0 => 1 | i + 1 => i + 2))
        (instVar (Term.listRec (weaken1 (weaken1 sz)) (Term.rename ss (liftR (liftR (· + 2))))
          (Term.var 0))))
        (substAt 1 (weaken1 sh))) (instVar st) =
      Term.subst ss (FreeTopos.Internal.instVar2 (Term.listRec sz ss st) sh) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl, Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ss _ _ _ fun i ↦ ?_
  rcases i with _ | _ | i
  · set ρ : ℕ → Term := fun i ↦ Term.subst (substAt 1 (weaken1 sh) i) (instVar st) with hρ
    change Term.subst (Term.listRec (weaken1 (weaken1 sz))
      (Term.rename ss (liftR (liftR (· + 2)))) (Term.var 0)) ρ = Term.listRec sz ss st
    have h₁ : Term.subst (weaken1 (weaken1 sz)) ρ = sz := by
      rw [weaken1, weaken1, Term.subst_rename _ _ _ _ fun _ ↦ rfl,
        Term.subst_rename _ _ _ _ fun _ ↦ rfl]
      exact Term.subst_id sz hz _ fun _ ↦ rfl
    have h₂ : Term.subst (Term.rename ss (liftR (liftR (· + 2)))) (Term.liftS (Term.liftS ρ)) =
        ss := by
      rw [Term.subst_rename _ _ _ _ fun _ ↦ rfl]
      refine Term.subst_id ss hs _ fun j ↦ ?_
      rcases j with _ | _ | j
      · rfl
      · rfl
      · rfl
    rw [Term.listRec, Term.subst_node]
    simp only [Term.substStep, List.map_cons, List.map_nil, h₁, h₂]
    rfl
  · change Term.subst (weaken1 sh) (instVar st) = sh
    exact subst_weaken1_instVar hh st
  · rfl

/-- The decoding of the right side of the computation of the fold of a rose tree at a
construction: the step at the pair of the label and the fold of the children's list by the
construction of a list from the fold of each child, the step under the weakening past the label
and the children, and then the label and the children substituted in turn. -/
theorem roseNode_rhs {kn kc : ℕ} {c : PartialHorn.Tree} (ss : Term) {sl : Term}
    (hl : Term.VarLeaves sl = true) (scs : Term) :
    Term.subst (Term.subst (Term.subst (Term.rename ss (liftR (· + 2)))
        (instVar (Term.pair (Term.var 1) (Term.listRec (Term.arr kn [c] Term.star)
          (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.rename ss (liftR (· + 4)))
            (Term.var 1)) (Term.var 0))) (Term.var 0)))))
        (substAt 1 (weaken1 sl))) (instVar scs) =
      Term.subst ss (instVar (Term.pair sl (Term.listRec (Term.arr kn [c] Term.star)
        (Term.arr kc [c] (Term.pair (Term.roseRec c (FreeTopos.Internal.weakenStep2 ss)
          (Term.var 1)) (Term.var 0))) scs))) := by
  rw [Term.subst_subst _ _ _ _ fun _ ↦ rfl, Term.subst_subst _ _ _ _ fun _ ↦ rfl]
  refine Term.subst_rename ss _ _ _ fun i ↦ ?_
  rcases i with _ | i
  · set ρ : ℕ → Term := fun i ↦ Term.subst (substAt 1 (weaken1 sl) i) (instVar scs) with hρ
    have h₁ : ρ 1 = sl := subst_weaken1_instVar hl scs
    have h₂ : Term.subst (Term.rename ss (liftR (· + 4)))
        (Term.liftS (Term.liftS (Term.liftS ρ))) = FreeTopos.Internal.weakenStep2 ss := by
      rw [Term.subst_rename _ _ _ _ fun _ ↦ rfl, FreeTopos.Internal.weakenStep2,
        Term.rename_eq_subst ss _ _ fun _ ↦ rfl]
      exact congrArg _ (funext fun j ↦ by rcases j with _ | j <;> rfl)
    change Term.subst (Term.pair (Term.var 1) (Term.listRec (Term.arr kn [c] Term.star)
      (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.rename ss (liftR (· + 4)))
        (Term.var 1)) (Term.var 0))) (Term.var 0))) ρ = _
    rw [show Term.subst (Term.pair (Term.var 1) (Term.listRec (Term.arr kn [c] Term.star)
        (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.rename ss (liftR (· + 4)))
          (Term.var 1)) (Term.var 0))) (Term.var 0))) ρ =
        Term.pair (ρ 1) (Term.listRec (Term.arr kn [c] Term.star)
          (Term.arr kc [c] (Term.pair (Term.roseRec c (Term.subst (Term.rename ss (liftR (· + 4)))
            (Term.liftS (Term.liftS (Term.liftS ρ)))) (Term.var 1)) (Term.var 0))) (ρ 0)) from rfl,
      h₁, h₂]
    rfl
  · rfl

/-- The innermost term variable decodes to the innermost variable. -/
theorem termOf_var0 : termOf k (none :: env) (Expr.var 0) = some (Term.var 0) := rfl

/-- The decoding of an LF term weakened by a proof variable, in the environment extended by it,
is its decoding. -/
theorem termOf_consPf_shift (F : Expr) (h : ℕ) :
    termOf k (some h :: env) (F.rename Nat.succ) = termOf k env F := by
  rw [termOf, termOf, rename_rename]
  rfl

variable (E : Array Entry) (hk : k.Valid G)

include hk in
/-- The soundness of the decoding of reflexivity. -/
theorem sound_refl (hc : PfCtx G k ΓLF env Γ Φ) {A t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (pf (eq (v 1) (v 0) (v 0)))))
      [(A, judge sig A), (t, judge sig t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 18 [A, t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hA := spine_tp₁ hS
  obtain ⟨a, ha⟩ := tyComplete hc.heads₀ A hA
  have hAc := encTy_closed a A ha
  simp only [tm, tp, pf, eq, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc]
  obtain ⟨-, ht, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨u, hu, -⟩ := termOf_typed hk hc.toTmCtx ha ht
  rw [show RoseTree.node (.app (.const 16)) [A, t, t] = Expr.const 16 [A, t, t] from rfl,
    termOf_const] at hφ
  simp only [List.map_cons, List.map_nil, decStep, hu, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD reflD reflD, by rw [decPf_const]; rfl, check_join (check_refl _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the computation of a pair's first component. -/
theorem sound_fstPair (hc : PfCtx G k ΓLF env Γ Φ) {A B a b F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 1)) (Expr.pi (tm (v 1))
      (pf (eq (v 3) (fst (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 1)))))))
      [(A, judge sig A), (B, judge sig B), (a, judge sig a), (b, judge sig b)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 21 [A, B, a, b]) env Φ.length = some D ∧
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
  obtain ⟨sa, hsa, -⟩ := termOf_typed hk hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, -⟩ := termOf_typed hk hc.toTmCtx hxb hb
  rw [show RoseTree.node (.app (.const 16)) [A, RoseTree.node (.app (.const 9))
      [A, B, RoseTree.node (.app (.const 8)) [A, B, a, b]], a] =
      Expr.const 16 [A, Expr.const 9 [A, B, Expr.const 8 [A, B, a, b]], a] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsa, hsb, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .fstPair) reflD, by rw [decPf_const]; rfl,
    check_join (check_fstPair _ _) (check_refl _)⟩


include hk in
/-- The soundness of the decoding of the computation of a pair's second component. -/
theorem sound_sndPair (hc : PfCtx G k ΓLF env Γ Φ) {A B a b F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 1)) (Expr.pi (tm (v 1))
      (pf (eq (v 2) (snd (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))) (v 0)))))))
      [(A, judge sig A), (B, judge sig B), (a, judge sig a), (b, judge sig b)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 22 [A, B, a, b]) env Φ.length = some D ∧
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
  obtain ⟨sa, hsa, -⟩ := termOf_typed hk hc.toTmCtx hxa ha
  obtain ⟨sb, hsb, -⟩ := termOf_typed hk hc.toTmCtx hxb hb
  rw [show RoseTree.node (.app (.const 16)) [B, RoseTree.node (.app (.const 10))
      [A, B, RoseTree.node (.app (.const 8)) [A, B, a, b]], b] =
      Expr.const 16 [B, Expr.const 10 [A, B, Expr.const 8 [A, B, a, b]], b] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hsa, hsb, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.map_eq_map, Option.map_some,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .sndPair) reflD, by rw [decPf_const]; rfl,
    check_join (check_sndPair _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the η rule of pairs. -/
theorem sound_pairEta (hc : PfCtx G k ΓLF env Γ Φ) {A B p F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (prod (v 1) (v 0)))
      (pf (eq (prod (v 2) (v 1))
        (pair (v 2) (v 1) (fst (v 2) (v 1) (v 0)) (snd (v 2) (v 1) (v 0))) (v 0))))))
      [(A, judge sig A), (B, judge sig B), (p, judge sig p)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 23 [A, B, p]) env Φ.length = some D ∧
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
  obtain ⟨sp, hsp, -⟩ := termOf_typed hk hc.toTmCtx hxab hp
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

include hk in
/-- The soundness of the decoding of the η rule of the terminal object. -/
theorem sound_unitEta (hc : PfCtx G k ΓLF env Γ Φ) {t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi (tm one) (pf (eq one (v 0) star))) [(t, judge sig t)] =
      some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 24 [t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, one, star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨ht, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨st, hst, hty⟩ := termOf_typed (a := FreeTopos.one) hk hc.toTmCtx rfl ht
  rw [show RoseTree.node (.app (.const 16)) [RoseTree.node (.app (.const 1)) [], t,
      RoseTree.node (.app (.const 7)) []] = Expr.const 16 [one, t, Expr.const 7 []] from rfl] at hφ
  simp only [termOf_const, List.map_cons, List.map_nil, decStep, hst, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD .unitEta) reflD, by rw [decPf_const]; rfl,
    check_join (check_unitEta hty) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of β. -/
theorem sound_beta (hc : PfCtx G k ΓLF env Γ Φ) {A B f a F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 0)))
      (Expr.pi (tm (v 2))
      (pf (eq (v 2) (app (v 3) (v 2) (lam (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0]))) (v 0))
        (Expr.var 1 [v 0])))))))
      [(A, judge sig A), (B, judge sig B), (f, judge sig f), (a, judge sig a)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 20 [A, B, f, a]) env Φ.length = some D ∧
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
  obtain ⟨sa, hsa, -⟩ := termOf_typed hk hc.toTmCtx hxa ha
  obtain ⟨sf, hsf, -⟩ := termOf_typed hk (hc.toTmCtx.consTm hxa) hxb hfb
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

include hk in
/-- The soundness of the decoding of the computation of the fold at zero. -/
theorem sound_natZero (hc : PfCtx G k ΓLF env Γ Φ) {C z s F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 1)))
      (pf (eq (v 2) (natRec (v 2) (v 1) (Expr.lam (Expr.var 1 [v 0])) zero) (v 1))))))
      [(C, judge sig C), (z, judge sig z), (s, judge sig s)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 25 [C, z, s]) env Φ.length = some D ∧
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
  obtain ⟨sz, hsz, -⟩ := termOf_typed hk hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, -⟩ := termOf_typed hk (hc.toTmCtx.consTm hxc) hxc hsb
  rw [show RoseTree.node (.app (.const 16)) [C, RoseTree.node (.app (.const 15))
      [C, z, RoseTree.node .lam [sb], RoseTree.node (.app (.const 13))
        [RoseTree.node (.app (.const 7)) []]], z] =
      Expr.const 16 [C, Expr.const 15 [C, z, Expr.lam sb, Expr.const 13 [Expr.const 7 []]], z]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsz, hss,
    Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.map_eq_map, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.natZero k.zero)) reflD, by rw [decPf_const]; rfl,
    check_join (check_natZero hk.zero _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the computation of the fold at a successor. -/
theorem sound_natSucc (hc : PfCtx G k ΓLF env Γ Φ) {C z s n F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (tm (v 0)) (Expr.pi (Expr.arrow (tm (v 1)) (tm (v 1)))
      (Expr.pi (tm nat)
      (pf (eq (v 3) (natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (succ (v 0)))
        (Expr.var 1 [natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (v 0)])))))))
      [(C, judge sig C), (z, judge sig z), (s, judge sig s), (n, judge sig n)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 26 [C, z, s, n]) env Φ.length = some D ∧
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
  obtain ⟨sz, hsz, hzt⟩ := termOf_typed hk hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk (hc.toTmCtx.consTm hxc) hxc hsb
  obtain ⟨sn, hsn, hnt⟩ := termOf_typed (a := FreeTopos.nat) hk hc.toTmCtx rfl hn
  have hR : termOf k (none :: env) (Expr.const 15 [C, z.rename Nat.succ,
      Expr.lam (sb.rename (liftR Nat.succ)), Expr.var 0]) =
      some (Term.natRec (weaken1 sz) (Term.rename ss (liftR Nat.succ)) (Term.var 0)) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep,
      termOf_shift hsz, termOf_shift_lift hss, Option.map_some, lamBody_lam,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have ha₁ := termOf_hsub₀ (env := none :: env) h₃ (termOf_shift_lift hss) hR
  have ha₃ := termOf_hsub₀ h₆ ha₁ hsn
  rw [natSucc_rhs (varLeaves_of_typeIn hzt) (varLeaves_of_typeIn hst)] at ha₃
  rw [show RoseTree.node (.app (.const 16)) [C, RoseTree.node (.app (.const 15))
      [C, z, RoseTree.node .lam [sb], RoseTree.node (.app (.const 14)) [n]], a₃] =
      Expr.const 16 [C, Expr.const 15 [C, z, Expr.lam sb, Expr.const 14 [n]], a₃]
      from rfl] at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsz, hss, hsn,
    ha₃, Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.map_eq_map, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.natSucc k.succ)) reflD, by rw [decPf_const]; rfl,
    check_join (check_natSucc hk.succ _ _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the computation of the fold of a list at the empty list. -/
theorem sound_listNil (hc : PfCtx G k ΓLF env Γ Φ) {A C z s F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 0))
      (Expr.pi (Expr.arrow (tm (v 2)) (Expr.arrow (tm (v 1)) (tm (v 1))))
        (pf (eq (v 2) (listRec (v 3) (v 2) (v 1) (Expr.lam (Expr.lam (Expr.var 2 [v 1, v 0])))
          (nil (v 3))) (v 1)))))))
      [(A, judge sig A), (C, judge sig C), (z, judge sig z), (s, judge sig s)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 34 [A, C, z, s]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xc, hxc⟩ := tyComplete hc.heads₀ C hT.2
  have hAc := encTy_closed xa A hxa
  have hCc := encTy_closed xc C hxc
  simp only [tm, tp, pf, eq, listRec, nil, nilAt, star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hCc, hsubWith_closed hCc]
  obtain ⟨-, -, hz', hs', x, hx, hF⟩ := hS
  obtain ⟨sb₁, rfl, hsb₁⟩ := judge_check_pi_inv hs'
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hsb₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hΓA : ∀ a ∈ tm A :: ΓLF, Expr.TypeShape a = true := fun a ha ↦ by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs a ha
  rw [rename_rename, rename_lam] at hx
  simp only [show ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam from fun _ ↦ rfl,
    show ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] from fun _ ↦ rfl] at hx
  rw [hsub_lam_var₁ hΓs hAc hsb, Option.bind_some] at hx
  simp only [show ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam from fun _ ↦ rfl,
    show ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] from fun _ ↦ rfl] at hx
  have hCs : ModeShape (.check (tm C)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  rw [hsub_var0_self hΓA hCc hCs hsb, Option.some.injEq] at hx
  subst hx
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sz, hsz, -⟩ := termOf_typed hk hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, -⟩ := termOf_typed hk ((hc.toTmCtx.consTm hxa).consTm hxc) hxc hsb
  change termOf k env (Expr.const 16 [C, Expr.const 33 [A, C, z, Expr.lam (Expr.lam sb),
    Expr.const 31 [A, Expr.const 7 []]], z]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsz, hss,
    rename_closed hAc, decTy_encTy xa A hxa, Option.map_some, lamBody_lam, Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.listNil k.nil)) reflD, by rw [decPf_const]; rfl,
    check_join (check_listNil hk.nil _ _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the computation of the fold of a list at a construction. -/
theorem sound_listCons (hc : PfCtx G k ΓLF env Γ Φ) {A C z s h t F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (v 0))
      (Expr.pi (Expr.arrow (tm (v 2)) (Expr.arrow (tm (v 1)) (tm (v 1))))
        (Expr.pi (tm (v 3)) (Expr.pi (tm (list (v 4)))
          (pf (eq (v 4)
            (listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (Expr.var 4 [v 1, v 0])))
              (cons (v 5) (pair (v 5) (list (v 5)) (v 1) (v 0))))
            (Expr.var 2 [v 1,
              listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (Expr.var 4 [v 1, v 0])))
                (v 0)])))))))))
      [(A, judge sig A), (C, judge sig C), (z, judge sig z), (s, judge sig s), (h, judge sig h),
        (t, judge sig t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 35 [A, C, z, s, h, t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xc, hxc⟩ := tyComplete hc.heads₀ C hT.2
  have hAc := encTy_closed xa A hxa
  have hCc := encTy_closed xc C hxc
  simp only [tm, tp, pf, eq, listRec, cons, pair, list, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hCc, hsubWith_closed hCc]
  obtain ⟨-, -, hz', a₀, b, ⟨hs', ha₀, a', ha', hb⟩, a₁, b₁, ⟨hh, ha₁, hb₁⟩, ht, a₂, ha₂, b₂,
    hb₂, hF⟩ := hS
  obtain ⟨sb₁, rfl, hsb₁⟩ := judge_check_pi_inv hs'
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hsb₁
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hΓA : ∀ a ∈ tm A :: ΓLF, Expr.TypeShape a = true := fun a ha ↦ by
    rcases List.mem_cons.mp ha with rfl | ha
    · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
    · exact hΓs a ha
  have hCs : ModeShape (.check (tm C)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hP : ModeShape (.check (Expr.pi (tm C) (tm C))) = true := by
    simp only [ModeShape, Expr.pi, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hE := appliedAt_of_judge_tm hΓs hAc hP (judge_lam hsb)
  have hE₀ := appliedAt_of_judge_tm hΓA hCc hCs hsb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₁ : (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] := rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  -- the step at the two innermost variables, under the weakening past the element and the rest
  rw [rename_succ_four, rename_lam] at ha₀ ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₁, hsub_var_base hE (liftR (· + 4)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) rfl
    (fun _ ↦ rfl) rfl, Option.bind_some, rename_lam] at ha₀ ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₀, hsub_var_base hE₀ _ (liftR (liftR (· + 2))) rfl
    (fun i ↦ by rcases i with _ | i <;> rfl) (k := 0) rfl, Option.some.injEq] at ha₀ ha'
  subst ha₀ ha'
  -- the step applied to the element, under the weakening past the element and the rest
  rw [rename_succ_two, rename_lam] at hb
  simp only [lamL, lamC] at hb
  rw [v₁, hsub_var_base hE (liftR (· + 2)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 2) rfl
    (fun _ ↦ rfl) rfl, Option.bind_some, rename_lam] at hb
  simp only [lamL, lamC] at hb
  -- the element and the rest substituted into the start's step, which mentions neither
  rw [show sb.rename (liftR (liftR (· + 2))) =
      (sb.rename (liftR (liftR Nat.succ))).rename (liftR^[3] Nat.succ) by
    rw [rename_rename]
    exact congrArg _ (funext fun i ↦ by rcases i with _ | _ | i <;> rfl),
    hsubWith_vacuous, Option.some.injEq] at ha₁
  subst ha₁
  rw [show sb.rename (liftR (liftR Nat.succ)) = sb.rename (liftR^[2] Nat.succ) from rfl,
    hsubWith_vacuous, Option.some.injEq] at ha₂
  subst ha₂
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sz, hsz, hzt⟩ := termOf_typed hk hc.toTmCtx hxc hz'
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk ((hc.toTmCtx.consTm hxa).consTm hxc) hxc hsb
  obtain ⟨sh, hsh, hht⟩ := termOf_typed hk hc.toTmCtx hxa hh
  obtain ⟨st, hst', -⟩ := termOf_typed (a := FreeTopos.list xa) hk hc.toTmCtx
    (by rw [encTy_list, hxa]; rfl) ht
  have hS₂ : termOf k (none :: none :: none :: none :: env) (sb.rename (liftR (liftR (· + 2)))) =
      some (Term.rename ss (liftR (liftR (· + 2)))) :=
    termOf_rename _ _ hss fun i ↦ by rcases i with _ | _ | i <;> rfl
  have hS₁ : termOf k (none :: none :: none :: env)
      (sb.rename (liftR fun i ↦ match i with | 0 => 1 | i + 1 => i + 2)) =
      some (Term.rename ss (liftR fun i ↦ match i with | 0 => 1 | i + 1 => i + 2)) :=
    termOf_rename _ _ hss fun i ↦ by rcases i with _ | _ | i <;> rfl
  have hR : termOf k (none :: none :: env) (Expr.const 33 [A, C,
      (z.rename Nat.succ).rename Nat.succ,
      Expr.lam (Expr.lam (sb.rename (liftR (liftR (· + 2))))), Expr.var 0 []]) =
      some (Term.listRec (weaken1 (weaken1 sz)) (Term.rename ss (liftR (liftR (· + 2))))
        (Term.var 0)) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep,
      termOf_shift (termOf_shift hsz), hS₂, Option.map_some, lamBody_lam, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  have hb' := termOf_hsub₀ (env := none :: none :: env) hb hS₁ hR
  have hb₁' := termOf_hsub₁ hb₁ hb' (termOf_shift hsh)
  have hb₂' := termOf_hsub₀ hb₂ hb₁' hst'
  rw [listCons_rhs (varLeaves_of_typeIn hzt) (varLeaves_of_typeIn hst)
    (varLeaves_of_typeIn hht)] at hb₂'
  change termOf k env (Expr.const 16 [C, Expr.const 33 [A, C, z, Expr.lam (Expr.lam sb),
    Expr.const 32 [A, Expr.const 8 [A, Expr.const 30 [A], h, t]]], b₂]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hsz, hss, hsh,
    hst', hb₂', rename_closed hAc, decTy_encTy xa A hxa, Option.map_some, lamBody_lam,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.listCons k.cons)) reflD, by rw [decPf_const]; rfl,
    check_join (check_listCons hk.cons _ _ _ _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the computation of the fold of a rose tree at a
construction. -/
theorem sound_roseNode (hc : PfCtx G k ΓLF env Γ Φ) {C s l cs F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0)))
      (Expr.pi (tm nat) (Expr.pi (tm (list rose))
        (pf (eq (v 3) (roseRec (v 3) (Expr.lam (Expr.var 3 [v 0]))
            (node (pair nat (list rose) (v 1) (v 0))))
          (Expr.var 2 [pair nat (list (v 3)) (v 1) (listRec rose (list (v 3)) (nil (v 3))
            (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
              (roseRec (v 5) (Expr.lam (Expr.var 5 [v 0])) (v 1)) (v 0))))) (v 0))])))))))
      [(C, judge sig C), (s, judge sig s), (l, judge sig l), (cs, judge sig cs)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 40 [C, s, l, cs]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨xc, hxc⟩ := tyComplete hc.heads₀ C (spine_tp₁ hS)
  have hCc := encTy_closed xc C hxc
  have hpc : encTy (FreeTopos.prod FreeTopos.nat (FreeTopos.list xc)) =
      some (prod nat (list C)) := by rw [encTy_prod, encTy_list, hxc]; rfl
  have hPc := encTy_closed _ _ hpc
  simp only [tm, tp, pf, eq, roseRec, node, listRec, nil, nilAt, cons, pair, list, prod, nat,
    rose, star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hCc, hsubWith_closed hCc]
  obtain ⟨-, a₀, b, ⟨hs', ha₀, a', ha', hb⟩, a₁, b₁, ⟨hl, ha₁, hb₁⟩, hcs, a₂, ha₂, b₂, hb₂,
    hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hCs : ModeShape (.check (tm C)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hE := appliedAt_of_judge_tm (A := prod nat (list C)) hΓs hPc hCs hsb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  have r5 : ∀ e : Expr, ((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
      Nat.succ).rename Nat.succ = e.rename (· + 5) :=
    fun e ↦ by rw [rename_rename, rename_rename, rename_rename, rename_rename]; rfl
  -- the step at the innermost variable, under the weakening past the label and the children
  rw [r3, rename_lam] at ha₀
  rw [r5, rename_lam] at ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₀, hsub_var_base hE (liftR (· + 3)) (liftR (· + 2)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₀
  rw [v₀, hsub_var_base hE (liftR (· + 5)) (liftR (· + 4)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha'
  subst ha₀ ha'
  -- the label and the children substituted into the outer step, which mentions neither
  rw [hsubWith_vacuous' _ _ _ (g := liftR (· + 1)) fun i ↦ by rcases i with _ | i <;> rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  -- the step applied to the pair, under the weakening past the label and the children
  rw [rename_succ_two, rename_lam] at hb
  simp only [lamL, lamC] at hb
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk (hc.toTmCtx.consTm hpc) hxc hsb
  obtain ⟨sl, hsl, hlt⟩ := termOf_typed (a := FreeTopos.nat) hk hc.toTmCtx rfl hl
  obtain ⟨scs, hscs, -⟩ := termOf_typed (a := FreeTopos.list FreeTopos.rose) hk hc.toTmCtx rfl
    hcs
  have hS₂ : termOf k (none :: none :: none :: env) (sb.rename (liftR (· + 2))) =
      some (Term.rename ss (liftR (· + 2))) :=
    termOf_rename _ _ hss fun i ↦ by rcases i with _ | i <;> rfl
  have hS₄ : termOf k (none :: none :: none :: none :: none :: env) (sb.rename (liftR (· + 4))) =
      some (Term.rename ss (liftR (· + 4))) :=
    termOf_rename _ _ hss fun i ↦ by rcases i with _ | i <;> rfl
  have hP : termOf k (none :: none :: env) (Expr.const 8 [Expr.const 5 [], Expr.const 30 [C],
      Expr.var 1 [], Expr.const 33 [Expr.const 37 [], Expr.const 30 [C],
        Expr.const 31 [C, Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [C, Expr.const 8 [C, Expr.const 30 [C],
          Expr.const 39 [C, Expr.lam (sb.rename (liftR (· + 4))), Expr.var 1 []],
          Expr.var 0 []]])), Expr.var 0 []]]) =
      some (Term.pair (Term.var 1) (Term.listRec (Term.arr k.nil [xc] Term.star)
        (Term.arr k.cons [xc] (Term.pair (Term.roseRec xc (Term.rename ss (liftR (· + 4)))
          (Term.var 1)) (Term.var 0))) (Term.var 0))) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hS₄,
      rename_closed hCc, decTy_encTy xc C hxc, Option.map_some, lamBody_lam, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  have hb' := termOf_hsub₀ (env := none :: none :: env) hb hS₂ hP
  have hb₁' := termOf_hsub₁ hb₁ hb' (termOf_shift hsl)
  have hb₂' := termOf_hsub₀ hb₂ hb₁' hscs
  rw [roseNode_rhs ss (varLeaves_of_typeIn hlt)] at hb₂'
  change termOf k env (Expr.const 16 [C, Expr.const 39 [C, Expr.lam sb,
    Expr.const 38 [Expr.const 8 [Expr.const 5 [], Expr.const 30 [Expr.const 37 []], l, cs]]],
    b₂]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hss, hsl, hscs,
    hb₂', rename_closed hCc, decTy_encTy xc C hxc, Option.map_eq_map, Option.map_some,
    lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.roseNode k.node k.nil k.cons)) reflD, by rw [decPf_const]; rfl,
    check_join (check_roseNode (.inl hk.node) hk.nil hk.cons _ _ _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of the computation of the fold of a rose tree of labels of a type
at a construction. -/
theorem sound_lroseNode (hc : PfCtx G k ΓLF env Γ Φ) {A C s l cs F : Expr} {φ : MTerm}
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp
      (Expr.pi (Expr.arrow (tm (prod (v 1) (list (v 0)))) (tm (v 0))) (Expr.pi (tm (v 2))
        (Expr.pi (tm (list (lrose (v 3))))
          (pf (eq (v 3) (lroseRec (v 4) (v 3) (Expr.lam (Expr.var 3 [v 0]))
              (lnode (v 4) (pair (v 4) (list (lrose (v 4))) (v 1) (v 0))))
            (Expr.var 2 [pair (v 4) (list (v 3)) (v 1) (listRec (lrose (v 4)) (list (v 3))
              (nil (v 3)) (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
                (lroseRec (v 6) (v 5) (Expr.lam (Expr.var 5 [v 0])) (v 1)) (v 0))))) (v 0))]))))))))
      [(A, judge sig A), (C, judge sig C), (s, judge sig s), (l, judge sig l),
        (cs, judge sig cs)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 45 [A, C, s, l, cs]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  have hT := spine_tp₂ hS
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A hT.1
  obtain ⟨xc, hxc⟩ := tyComplete hc.heads₀ C hT.2
  have hAc := encTy_closed xa A hxa
  have hCc := encTy_closed xc C hxc
  have hpc : encTy (FreeTopos.prod xa (FreeTopos.list xc)) = some (prod A (list C)) := by
    rw [encTy_prod, encTy_list, hxa, hxc]; rfl
  have hPc := encTy_closed _ _ hpc
  simp only [tm, tp, pf, eq, lroseRec, lnode, listRec, nil, nilAt, cons, pair, list, prod, lrose,
    star, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc,
    rename_closed hCc, hsubWith_closed hCc]
  obtain ⟨-, -, a₀, b, ⟨hs', ha₀, a', ha', hb⟩, a₁, b₁, ⟨hl, ha₁, hb₁⟩, hcs, a₂, ha₂, b₂, hb₂,
    hF⟩ := hS
  obtain ⟨sb, rfl, hsb⟩ := judge_check_pi_inv hs'
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hCs : ModeShape (.check (tm C)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hE := appliedAt_of_judge_tm (A := prod A (list C)) hΓs hPc hCs hsb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  have r5 : ∀ e : Expr, ((((e.rename Nat.succ).rename Nat.succ).rename Nat.succ).rename
      Nat.succ).rename Nat.succ = e.rename (· + 5) :=
    fun e ↦ by rw [rename_rename, rename_rename, rename_rename, rename_rename]; rfl
  -- the step at the innermost variable, under the weakening past the label and the children
  rw [r3, rename_lam] at ha₀
  rw [r5, rename_lam] at ha'
  simp only [lamL, lamC] at ha₀ ha'
  rw [v₀, hsub_var_base hE (liftR (· + 3)) (liftR (· + 2)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₀
  rw [v₀, hsub_var_base hE (liftR (· + 5)) (liftR (· + 4)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha'
  subst ha₀ ha'
  -- the label and the children substituted into the outer step, which mentions neither
  rw [hsubWith_vacuous' _ _ _ (g := liftR (· + 1)) fun i ↦ by rcases i with _ | i <;> rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  -- the step applied to the pair, under the weakening past the label and the children
  rw [rename_succ_two, rename_lam] at hb
  simp only [lamL, lamC] at hb
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨ss, hss, hst⟩ := termOf_typed hk (hc.toTmCtx.consTm hpc) hxc hsb
  obtain ⟨sl, hsl, hlt⟩ := termOf_typed hk hc.toTmCtx hxa hl
  obtain ⟨scs, hscs, -⟩ := termOf_typed (a := FreeTopos.list (FreeTopos.lrose xa)) hk hc.toTmCtx
    (by rw [encTy_list, encTy_lrose, hxa]; rfl) hcs
  have hS₂ : termOf k (none :: none :: none :: env) (sb.rename (liftR (· + 2))) =
      some (Term.rename ss (liftR (· + 2))) :=
    termOf_rename _ _ hss fun i ↦ by rcases i with _ | i <;> rfl
  have hS₄ : termOf k (none :: none :: none :: none :: none :: env) (sb.rename (liftR (· + 4))) =
      some (Term.rename ss (liftR (· + 4))) :=
    termOf_rename _ _ hss fun i ↦ by rcases i with _ | i <;> rfl
  have hP : termOf k (none :: none :: env) (Expr.const 8 [A, Expr.const 30 [C],
      Expr.var 1 [], Expr.const 33 [Expr.const 42 [A], Expr.const 30 [C],
        Expr.const 31 [C, Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [C, Expr.const 8 [C, Expr.const 30 [C],
          Expr.const 44 [A, C, Expr.lam (sb.rename (liftR (· + 4))), Expr.var 1 []],
          Expr.var 0 []]])), Expr.var 0 []]]) =
      some (Term.pair (Term.var 1) (Term.listRec (Term.arr k.nil [xc] Term.star)
        (Term.arr k.cons [xc] (Term.pair (Term.roseRec xc (Term.rename ss (liftR (· + 4)))
          (Term.var 1)) (Term.var 0))) (Term.var 0))) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hS₄,
      rename_closed hCc, decTy_encTy xc C hxc, Option.map_some, lamBody_lam, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    rfl
  have hb' := termOf_hsub₀ (env := none :: none :: env) hb hS₂ hP
  have hb₁' := termOf_hsub₁ hb₁ hb' (termOf_shift hsl)
  have hb₂' := termOf_hsub₀ hb₂ hb₁' hscs
  rw [roseNode_rhs ss (varLeaves_of_typeIn hlt)] at hb₂'
  change termOf k env (Expr.const 16 [C, Expr.const 44 [A, C, Expr.lam sb,
    Expr.const 43 [A, Expr.const 8 [A, Expr.const 30 [Expr.const 42 [A]], l, cs]]],
    b₂]) = some φ at hφ
  simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hss, hsl, hscs,
    hb₂', rename_closed hAc, rename_closed hCc, decTy_encTy xa A hxa, decTy_encTy xc C hxc,
    Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
    Option.some.injEq] at hφ
  subst hφ
  exact ⟨joinD (ruleD (.roseNode k.lnode k.nil k.cons)) reflD, by rw [decPf_const]; rfl,
    check_join (check_roseNode (.inr hk.lnode) hk.nil hk.cons _ _ _ _) (check_refl _)⟩

include hk in
/-- The soundness of the decoding of function extensionality. -/
theorem sound_funExt (hc : PfCtx G k ΓLF env Γ Φ) {A B f g dH F : Expr} {φ : MTerm}
    (ihH : PfLam (PfSoundAt G k E) dH)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi tp (Expr.pi (tm (exp (v 1) (v 0)))
      (Expr.pi (tm (exp (v 2) (v 1)))
      (Expr.arrow (Expr.pi (tm (v 3))
          (pf (eq (v 3) (app (v 4) (v 3) (v 2) (v 0)) (app (v 4) (v 3) (v 1) (v 0)))))
        (pf (eq (exp (v 3) (v 2)) (v 1) (v 0))))))))
      [(A, judge sig A), (B, judge sig B), (f, judge sig f), (g, judge sig g),
        (dH, judge sig dH)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 27 [A, B, f, g, dH]) env Φ.length = some D ∧
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
  obtain ⟨sf, hsf, hft⟩ := termOf_typed hk hc.toTmCtx hxab hf
  obtain ⟨sg, hsg, -⟩ := termOf_typed hk hc.toTmCtx hxab hg
  obtain ⟨body, rfl, hbody, hsound⟩ := ihH ΓLF _ _ hdH
  have hF' : termOf k (none :: env) (Expr.const 16 [B,
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

include hk in
/-- The soundness of the decoding of propositional extensionality. -/
theorem sound_propExt (hc : PfCtx G k ΓLF env Γ Φ) {P Q d₁ d₂ F : Expr} {φ : MTerm}
    (ih₁ : PfLam (PfSoundAt G k E) d₁) (ih₂ : PfLam (PfSoundAt G k E) d₂)
    (hS : spine ΓLF (Expr.pi (tm omega) (Expr.pi (tm omega)
      (Expr.arrow (Expr.arrow (pf (v 1)) (pf (v 0)))
        (Expr.arrow (Expr.arrow (pf (v 0)) (pf (v 1))) (pf (eq omega (v 1) (v 0)))))))
      [(P, judge sig P), (Q, judge sig Q), (d₁, judge sig d₁), (d₂, judge sig d₂)] =
        some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 28 [P, Q, d₁, d₂]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, omega, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨hP, hQ, hd₁, hd₂, hF⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  obtain ⟨sP, hsP, hPt⟩ := termOf_typed (a := FreeTopos.omega) hk hc.toTmCtx rfl hP
  obtain ⟨sQ, hsQ, hQt⟩ := termOf_typed (a := FreeTopos.omega) hk hc.toTmCtx rfl hQ
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

include hk in
/-- The soundness of the decoding of the substitution of equals. -/
theorem sound_leib (hc : PfCtx G k ΓLF env Γ Φ) {A P t u dh dp F : Expr} {φ : MTerm}
    (ihh : PfSoundAt G k E dh) (ihp : PfSoundAt G k E dp)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (v 0)) (tm omega))
      (Expr.pi (tm (v 1)) (Expr.pi (tm (v 2))
      (Expr.arrow (pf (eq (v 3) (v 1) (v 0)))
        (Expr.arrow (pf (Expr.var 2 [v 1])) (pf (Expr.var 2 [v 0]))))))))
      [(A, judge sig A), (P, judge sig P), (t, judge sig t), (u, judge sig u),
        (dh, judge sig dh), (dp, judge sig dp)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 19 [A, P, t, u, dh, dp]) env Φ.length = some D ∧
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
  obtain ⟨st, hst, htt⟩ := termOf_typed hk hc.toTmCtx hxa ht
  obtain ⟨su, hsu, hut⟩ := termOf_typed hk hc.toTmCtx hxa hu
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk (hc.toTmCtx.consTm hxa)
    rfl hPb
  have hXt' := termOf_hsub₀ hXt hsp hst
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ hXu hsp hsu))
  have heq : termOf k env (Expr.const 16 [A, t, u]) = some (Term.eq st su) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, hst, hsu,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have hψ := typeIn_eq htt hut
  obtain ⟨Dh, hDh, hch⟩ := ihh _ _ _ _ _ _ hc hdh heq
  obtain ⟨Dp, hDp, hcp⟩ := ihp _ _ _ _ _ _ (hc.addHyp hψ) hdp hXt'
  rw [List.length_append, List.length_singleton] at hDp
  refine ⟨leibD xa sp st su Φ.length Dh Dp, ?_,
    check_leibD (isTy_of_encTy G xa A hxa) hpt htt hut hch hcp⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hst, hsu, hDh, hDp,
    decTy_encTy xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

include hk in
/-- The soundness of the decoding of induction on the natural numbers. -/
theorem sound_natInd (hc : PfCtx G k ΓLF env Γ Φ) {P d₀ ds n F : Expr} {φ : MTerm}
    (ih₀ : PfSoundAt G k E d₀)
    (ihs : PfLam (fun b ↦ PfLam (PfSoundAt G k E) b) ds)
    (hS : spine ΓLF (Expr.pi (Expr.arrow (tm nat) (tm omega))
      (Expr.arrow (pf (Expr.var 0 [zero]))
        (Expr.arrow (Expr.pi (tm nat) (Expr.arrow (pf (Expr.var 1 [v 0]))
            (pf (Expr.var 1 [succ (v 0)]))))
          (Expr.pi (tm nat) (pf (Expr.var 1 [v 0]))))))
      [(P, judge sig P), (d₀, judge sig d₀), (ds, judge sig ds), (n, judge sig n)] =
        some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 29 [P, d₀, ds, n]) env Φ.length = some D ∧
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
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk
    (hc.toTmCtx.consTm (a := FreeTopos.nat) rfl) rfl hPb
  obtain ⟨sn, hsn, hnt⟩ := termOf_typed (a := FreeTopos.nat) hk hc.toTmCtx rfl hn
  have hid : termOf k (none :: env) (Pb.rename id) = some sp := by
    rw [termOf, rename_rename]
    exact hsp
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₅ hid hsn))
  have hzero : termOf k env (Expr.const 13 [Expr.const 7 []]) =
      some (Term.arr k.zero [] Term.star) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, Option.map_eq_map,
      Option.map_some]
  have ha0 := termOf_hsub₀ ha hsp hzero
  have hlen : (Φ.map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_singleton]
  have hc₂ := ((hc.consTm (a := FreeTopos.nat) (A := nat) rfl).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.nat :: Γ))).consPf hid hpt
  rw [hlen] at hc₂
  have hY' : termOf k (some (Φ.length + 1) :: none :: env) Y =
      some (FreeTopos.Internal.natSuccAt k.succ sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: env)
        (Pb.rename (liftR (Nat.succ ∘ Nat.succ))) = some (Term.rename sp (liftR Nat.succ)) := by
      have := dec_rename _ (liftR Nat.succ) sp hsp
      rw [rename_rename] at this
      rw [termOf, rename_rename, show tmIdx (none :: some (Φ.length + 1) :: none :: env) ∘
        liftR (Nat.succ ∘ Nat.succ) = liftR Nat.succ ∘ tmIdx (none :: env) from
          funext fun i ↦ by rcases i with _ | i <;> rfl]
      exact this
    have h₂ : termOf k (some (Φ.length + 1) :: none :: env)
        (Expr.const 14 [Expr.var 1 []]) = some (Term.arr k.succ [] (Term.var 0)) := rfl
    rw [termOf_hsub₀ hY h₁ h₂, FreeTopos.Internal.natSuccAt,
      Term.subst_rename sp _ _ (FreeTopos.Internal.atVar0 (Term.arr k.succ [] (Term.var 0)))
        fun i ↦ by rcases i with _ | i <;> rfl]
  obtain ⟨D₀, hD₀, hc₀⟩ := ih₀ _ _ _ _ _ _ (hc.addHyp typeIn_truth) hd₀ ha0
  rw [List.length_append, List.length_singleton] at hD₀
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hsound⟩ := hlam _ _ _ hb1
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb2 hY'
  have hDs' : decPf k body₂ (some (Φ.length + 1) :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  refine ⟨indD FreeTopos.nat (.natIndHyp k.zero k.succ) sp sn Φ.length [D₀, Ds], ?_,
    check_natIndD hk.zero hk.succ hpt hnt hc.typed hc₀ hcs⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hsn, hD₀, decPf_lam,
    hDs', Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody,
    Term.lam, RoseTree.label_node, RoseTree.children_node, Option.pure_def]

include hk in
/-- The soundness of the decoding of induction on lists. -/
theorem sound_listInd (hc : PfCtx G k ΓLF env Γ Φ) {A P d₀ ds l F : Expr} {φ : MTerm}
    (ih₀ : PfSoundAt G k E d₀)
    (ihs : PfLam (fun b ↦ PfLam (fun b' ↦ PfLam (PfSoundAt G k E) b') b) ds)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (list (v 0))) (tm omega))
      (Expr.arrow (pf (Expr.var 0 [nil (v 1)]))
        (Expr.arrow (Expr.pi (tm (v 1)) (Expr.pi (tm (list (v 2)))
            (Expr.arrow (pf (Expr.var 2 [v 0]))
              (pf (Expr.var 2 [cons (v 3) (pair (v 3) (list (v 3)) (v 1) (v 0))])))))
          (Expr.pi (tm (list (v 1))) (pf (Expr.var 1 [v 0])))))))
      [(A, judge sig A), (P, judge sig P), (d₀, judge sig d₀), (ds, judge sig ds),
        (l, judge sig l)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 36 [A, P, d₀, ds, l]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A (spine_tp₁ hS)
  have hAc := encTy_closed xa A hxa
  simp only [tm, tp, pf, list, omega, nil, nilAt, star, cons, pair, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc]
  obtain ⟨-, a, a₁, b, a₂, ⟨hP, ha, ha₁, hb, ha₂⟩, a₃, b₁, a₄, ⟨hd₀, ha₃, hb₁, ha₄⟩, a', ⟨hds, ha'⟩,
    hl, a₅, ha₅, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  simp only [Expr.lam, rename_node, RoseTree.label_node, RoseTree.children_node, List.zipIdx,
    List.map_cons, List.map_nil, Label.binders, Function.iterate_one, Label.rename] at ha ha₁ hb ha₂
  rw [rename_rename, rename_rename] at ha₁ ha₂
  rw [rename_rename, rename_rename, rename_rename] at hb
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hla : encTy (FreeTopos.list xa) = some (list A) := by rw [encTy_list, hxa]; rfl
  have hLc := encTy_closed _ _ hla
  have hApp := appliedAt_of_judge_tm hΓs hLc hOs hPb
  -- the motive at the step's rest, the type of the step's hypothesis
  obtain rfl := Option.some.inj (ha₁.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | i + 1 => i + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₃.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  -- the motive at the conclusion's variable
  obtain rfl := Option.some.inj (ha₂.symm.trans (hsub_var_base hApp
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ)
    (fun i ↦ match i with | 0 => 0 | i + 1 => i + 3) rfl (fun _ ↦ rfl) rfl))
  obtain rfl := Option.some.inj (ha₄.symm.trans (hsubWith_vacuous' _ _ _ (j := 2)
    (g := liftR Nat.succ) fun i ↦ by rcases i with _ | i <;> rfl))
  obtain rfl := Option.some.inj (ha'.symm.trans
    (hsubWith_vacuous' _ _ _ (j := 1) (g := id) fun _ ↦ rfl))
  -- the motive at the construction of the step's element and rest, the step's conclusion
  have hR3 : CtxRen ΓLF (tm (list A) :: tm (list A) :: tm (list A) :: ΓLF)
      (Nat.succ ∘ Nat.succ ∘ Nat.succ) := fun i T hT ↦ by
    have h₁ := CtxRen.succ ΓLF (tm (list A)) i T hT
    have h₂ := CtxRen.succ (tm (list A) :: ΓLF) (tm (list A)) _ _ h₁
    have h₃ := CtxRen.succ (tm (list A) :: tm (list A) :: ΓLF) (tm (list A)) _ _ h₂
    rwa [rename_rename, rename_rename] at h₃
  have hPb3 := judge_rename (Sig.ok_closed sig_ok) Pb _ (CtxRen.lift hR3 (tm (list A))) hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR (Nat.succ ∘ Nat.succ ∘ Nat.succ)) = tm omega from
      rename_closed (tm_closed rfl) _, rename_closed (tm_closed hLc)] at hPb3
  have hΓs3 : ∀ x ∈ tm (list A) :: tm (list A) :: tm (list A) :: ΓLF, Expr.TypeShape x = true :=
    fun x hx ↦ by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | hx
      · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
      · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
      · simp only [tm, Expr.const, Expr.app, typeShape_node]; rfl
      · exact hΓs x hx
  have hApp3 := appliedAt_of_judge_tm hΓs3 hLc hOs hPb3
  obtain ⟨Y, hY⟩ := hsubWith_base_total 6 _
    (Expr.const 32 [A, Expr.const 8 [A, Expr.const 30 [A], Expr.var 2 [], Expr.var 1 []]]) 0 hApp3
  have hred : RenameCompat (reduceStep (SimpleLabel.base 6) []) := by
    rw [← show reduce (RoseTree.node (SimpleLabel.base 6) []) =
      reduceStep (SimpleLabel.base 6) [] from reduce_node _ _]
    exact reduce_rename _
  have hbY := hsubWith_rename hred _ _ 0 (liftR^[3] Nat.succ) Y hY
  rw [rename_rename, show liftR^[0 + 1] (liftR^[3] Nat.succ) ∘
      liftR (Nat.succ ∘ Nat.succ ∘ Nat.succ) =
    ((liftR Nat.succ ∘ liftR Nat.succ) ∘ liftR Nat.succ) ∘ liftR Nat.succ from
      funext fun i ↦ by rcases i with _ | i <;> rfl] at hbY
  have hn3 : (Expr.const 32 [A, Expr.const 8 [A, Expr.const 30 [A], Expr.var 2 [],
      Expr.var 1 []]]).rename (liftR^[0] (liftR^[3] Nat.succ)) =
      Expr.const 32 [A, Expr.const 8 [A, Expr.const 30 [A], Expr.var 2 [], Expr.var 1 []]] := by
    simp only [Function.iterate_zero, id, Expr.const, Expr.var, Expr.app, rename_app_node,
      List.map_cons, List.map_nil, rename_closed hAc, Head.rename]
    rfl
  rw [hn3] at hbY
  obtain rfl := Option.some.inj (hb.symm.trans hbY)
  rw [Function.iterate_zero_apply, hsubWith_vacuous, Option.some.injEq] at hb₁
  subst hb₁
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk (hc.toTmCtx.consTm hla) rfl hPb
  obtain ⟨sl, hsl, hlt⟩ := termOf_typed hk hc.toTmCtx hla hl
  have hid : termOf k (none :: env) (Pb.rename id) = some sp := by
    rw [termOf, rename_rename]
    exact hsp
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₅ hid hsl))
  have hnil : termOf k env (Expr.const 31 [A, Expr.const 7 []]) =
      some (Term.arr k.nil [xa] Term.star) := by
    simp only [termOf_const, List.map_cons, List.map_nil, decStep, rename_closed hAc,
      decTy_encTy xa A hxa, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  have ha0 := termOf_hsub₀ ha hsp hnil
  -- the motive at the rest, under the element: the motive weakened past the element
  have hR1 : CtxRen (tm (list A) :: ΓLF) (tm (list A) :: tm A :: ΓLF) (liftR Nat.succ) := by
    have h := CtxRen.lift (CtxRen.succ ΓLF (tm A)) (tm (list A))
    rwa [rename_closed (tm_closed hLc)] at h
  have hPb1 := judge_rename (Sig.ok_closed sig_ok) Pb _ hR1 hPb
  rw [Mode.rename, show Expr.rename (RoseTree.node (.app (.const 6))
    [RoseTree.node (.app (.const 4)) []]) (liftR Nat.succ) = tm omega from
      rename_closed (tm_closed rfl) _] at hPb1
  obtain ⟨sq, hsq, hqt⟩ := termOf_typed (a := FreeTopos.omega) hk
    ((hc.toTmCtx.consTm hxa).consTm hla) rfl hPb1
  have hsq' : termOf k (none :: none :: env) (Pb.rename (liftR Nat.succ)) =
      some (FreeTopos.Internal.weakenElem sp) :=
    termOf_rename _ _ hsp fun i ↦ by rcases i with _ | i <;> rfl
  obtain rfl := Option.some.inj (hsq.symm.trans hsq')
  have hc₂ := (((hc.consTm hxa).consTm hla).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.list xa :: xa :: Γ))).consPf hsq' hqt
  have hlen : ((Φ.map weaken1).map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_map, List.length_singleton]
  rw [hlen] at hc₂
  -- the motive at the construction, the step's conclusion
  have hY' : termOf k (some (Φ.length + 1) :: none :: none :: env) Y =
      some (FreeTopos.Internal.listConsAt k.cons xa sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: none :: env)
        (Pb.rename (liftR (Nat.succ ∘ Nat.succ ∘ Nat.succ))) =
        some (Term.rename sp (liftR (· + 2))) :=
      termOf_rename _ _ hsp fun i ↦ by rcases i with _ | i <;> rfl
    have h₂ : termOf k (some (Φ.length + 1) :: none :: none :: env)
        (Expr.const 32 [A, Expr.const 8 [A, Expr.const 30 [A], Expr.var 2 [], Expr.var 1 []]]) =
        some (Term.arr k.cons [xa] (Term.pair (Term.var 1) (Term.var 0))) := by
      simp only [termOf_const, List.map_cons, List.map_nil, decStep, rename_closed hAc,
        decTy_encTy xa A hxa, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    rw [termOf_hsub₀ hY h₁ h₂]
    exact congrArg some (Term.subst_rename sp _ _ _ fun i ↦ by rcases i with _ | i <;> rfl)
  obtain ⟨D₀, hD₀, hc₀⟩ := ih₀ _ _ _ _ _ _ (hc.addHyp typeIn_truth) hd₀ ha0
  rw [List.length_append, List.length_singleton] at hD₀
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hlam'⟩ := hlam _ _ _ hb1
  obtain ⟨body₃, rfl, hb3, hsound⟩ := hlam' _ _ _ hb2
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb3 hY'
  have hDs' : decPf k body₃ (some (Φ.length + 1) :: none :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  have hw : (Φ ++ [truth]).map FreeTopos.Internal.weaken2 =
      (Φ.map weaken1).map weaken1 ++ [truth] := by
    rw [List.map_append, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun φ _ ↦ ?_) rfl
    exact (Term.rename_rename φ _ _ _ fun _ ↦ rfl).symm
  have hIs := isTy_of_encTy G (FreeTopos.list xa) (list A) hla
  refine ⟨indD (FreeTopos.list xa) (.listIndHyp k.nil k.cons) sp sl Φ.length [D₀, Ds], ?_,
    check_listIndD hk.nil hk.cons hIs hpt hlt hc.typed hc₀ (by rw [hw]; exact hcs)⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hsl, hD₀, decPf_lam, hDs',
    decTy_encTy xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

include hk in
/-- The soundness of the decoding of induction on rose trees. -/
theorem sound_roseInd (hc : PfCtx G k ΓLF env Γ Φ) {P ds t F : Expr} {φ : MTerm}
    (ihs : PfLam (fun b ↦ PfLam (fun b' ↦ PfLam (PfSoundAt G k E) b') b) ds)
    (hS : spine ΓLF (Expr.pi (Expr.arrow (tm rose) (tm omega))
      (Expr.arrow (Expr.pi (tm nat) (Expr.pi (tm (list rose))
          (Expr.arrow (pf (eq (list omega)
              (listRec rose (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (Expr.var 4 [v 1]) (v 0))))) (v 0))
              (listRec rose (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (eq one star star) (v 0))))) (v 0))))
            (pf (Expr.var 2 [node (pair nat (list rose) (v 1) (v 0))])))))
        (Expr.pi (tm rose) (pf (Expr.var 1 [v 0])))))
      [(P, judge sig P), (ds, judge sig ds), (t, judge sig t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 41 [P, ds, t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  simp only [tm, pf, eq, listRec, nil, nilAt, cons, pair, list, nat, rose, omega, one, star, node,
    Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff]
  obtain ⟨a, b, a₁, ⟨hP, ha, hb, ha₁⟩, a₂, ⟨hds, ha₂⟩, ht, a₃, ha₃, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := rose) hΓs rfl hOs hPb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₁ : (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] := rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  rw [rename_succ_four, rename_lam] at ha
  rw [r3, rename_lam] at hb
  rw [rename_succ_two, rename_lam] at ha₁
  simp only [lamL, lamC] at ha hb ha₁
  -- the motive at each child, in the hypothesis
  rw [v₁, hsub_var_base hApp (liftR (· + 4)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) rfl
    (fun _ ↦ rfl) rfl, Option.some.injEq] at ha
  subst ha
  -- the motive at the conclusion's variable
  rw [v₀, hsub_var_base hApp (liftR (· + 2)) (liftR (· + 1)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk
    (hc.toTmCtx.consTm (a := FreeTopos.rose) rfl) rfl hPb
  obtain ⟨st, hst, htt⟩ := termOf_typed (a := FreeTopos.rose) hk hc.toTmCtx rfl ht
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₃ hsp hst))
  -- the hypothesis that the motive holds at each child
  have hS₄ : termOf k (none :: none :: none :: none :: env)
      (Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) =
      some (Term.rename sp fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) :=
    termOf_rename _ _ hsp fun i ↦ by rcases i with _ | i <;> rfl
  have hH : termOf k (none :: none :: env) (Expr.const 16 [Expr.const 30 [Expr.const 4 []],
      Expr.const 33 [Expr.const 37 [], Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []], Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4,
          Expr.var 0 []]])), Expr.var 0 []],
      Expr.const 33 [Expr.const 37 [], Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []],
          Expr.const 16 [Expr.const 1 [], Expr.const 7 [], Expr.const 7 []], Expr.var 0 []]])),
        Expr.var 0 []]]) =
      some (FreeTopos.Internal.roseHyp k.nil k.cons sp) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hS₄,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have hc₂ := (((hc.consTm (a := FreeTopos.nat) (A := nat) rfl).consTm
    (a := FreeTopos.list FreeTopos.rose) (A := list rose) rfl).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.list FreeTopos.rose :: FreeTopos.nat :: Γ))).consPf
    hH (typeIn_roseHyp hk.nil hk.cons hpt)
  have hlen : ((Φ.map weaken1).map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_map, List.length_singleton]
  rw [hlen] at hc₂
  -- the motive at the construction, the step's conclusion
  have hY' : termOf k (some (Φ.length + 1) :: none :: none :: env) b =
      some (FreeTopos.Internal.roseNodeAt k.node FreeTopos.rose FreeTopos.nat sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: none :: env)
        (Pb.rename (liftR (· + 3))) = some (Term.rename sp (liftR (· + 2))) :=
      termOf_rename _ _ hsp fun i ↦ by rcases i with _ | i <;> rfl
    have h₂ : termOf k (some (Φ.length + 1) :: none :: none :: env)
        (Expr.const 38 [Expr.const 8 [Expr.const 5 [], Expr.const 30 [Expr.const 37 []],
          Expr.var 2 [], Expr.var 1 []]]) =
        some (Term.arr k.node [] (Term.pair (Term.var 1) (Term.var 0))) := rfl
    rw [termOf_hsub₀ hb h₁ h₂]
    refine congrArg some (Term.subst_rename sp _ _ _ fun i ↦ ?_)
    rcases i with _ | i
    · exact congrArg (Term.arr k.node · _) (ite_eq_left rfl).symm
    · rfl
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hlam'⟩ := hlam _ _ _ hb1
  obtain ⟨body₃, rfl, hb3, hsound⟩ := hlam' _ _ _ hb2
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb3 hY'
  have hDs' : decPf k body₃ (some (Φ.length + 1) :: none :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  have hw : (Φ ++ [truth]).map FreeTopos.Internal.weaken2 =
      (Φ.map weaken1).map weaken1 ++ [truth] := by
    rw [List.map_append, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun φ _ ↦ ?_) rfl
    exact (Term.rename_rename φ _ _ _ fun _ ↦ rfl).symm
  refine ⟨indD FreeTopos.rose (.roseIndHyp k.node k.nil k.cons) sp st Φ.length [Ds], ?_,
    check_roseIndD roseParts_rose (.inl ⟨hk.node, rfl⟩) hk.nil hk.cons
      (isTy_of_encTy G FreeTopos.rose rose rfl) hpt htt hc.typed (by rw [hw]; exact hcs)⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hst, decPf_lam, hDs',
    Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam, Option.pure_def]

include hk in
/-- The soundness of the decoding of induction on rose trees of labels of a type. -/
theorem sound_lroseInd (hc : PfCtx G k ΓLF env Γ Φ) {A P ds t F : Expr} {φ : MTerm}
    (ihs : PfLam (fun b ↦ PfLam (fun b' ↦ PfLam (PfSoundAt G k E) b') b) ds)
    (hS : spine ΓLF (Expr.pi tp (Expr.pi (Expr.arrow (tm (lrose (v 0))) (tm omega))
      (Expr.arrow (Expr.pi (tm (v 1)) (Expr.pi (tm (list (lrose (v 2))))
          (Expr.arrow (pf (eq (list omega)
              (listRec (lrose (v 3)) (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (Expr.var 4 [v 1]) (v 0))))) (v 0))
              (listRec (lrose (v 3)) (list omega) (nil omega) (Expr.lam (Expr.lam (cons omega
                (pair omega (list omega) (eq one star star) (v 0))))) (v 0))))
            (pf (Expr.var 2 [lnode (v 3) (pair (v 3) (list (lrose (v 3))) (v 1) (v 0))])))))
        (Expr.pi (tm (lrose (v 1))) (pf (Expr.var 1 [v 0]))))))
      [(A, judge sig A), (P, judge sig P), (ds, judge sig ds), (t, judge sig t)] = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.const 46 [A, P, ds, t]) env Φ.length = some D ∧
      (check G E 0 D).2 Γ Φ φ = true := by
  obtain ⟨xa, hxa⟩ := tyComplete hc.heads₀ A (spine_tp₁ hS)
  have hAc := encTy_closed xa A hxa
  have hra : encTy (FreeTopos.lrose xa) = some (lrose A) := by rw [encTy_lrose, hxa]; rfl
  have hRc := encTy_closed _ _ hra
  simp only [tm, tp, pf, eq, listRec, nil, nilAt, cons, pair, list, lrose, omega, one, star, lnode,
    Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, rename_closed hAc, hsubWith_closed hAc]
  obtain ⟨-, a, b, a₁, ⟨hP, ha, hb, ha₁⟩, a₂, ⟨hds, ha₂⟩, ht, a₃, ha₃, hF⟩ := hS
  obtain ⟨Pb, rfl, hPb⟩ := judge_check_pi_inv hP
  have hΓs := fun a ha ↦ (hc.typeShape a ha).1
  have hOs : ModeShape (.check (tm omega)) = true := by
    simp only [ModeShape, tm, Expr.const, Expr.app, typeShape_node]; rfl
  have hApp := appliedAt_of_judge_tm (A := lrose A) hΓs hRc hOs hPb
  have lamL : ∀ X : Expr, RoseTree.label (Expr.lam X) = Label.lam := fun _ ↦ rfl
  have lamC : ∀ X : Expr, RoseTree.children (Expr.lam X) = [X] := fun _ ↦ rfl
  have v₁ : (RoseTree.node (Label.app (Head.var 1)) [] : Expr) = Expr.var 1 [] := rfl
  have v₀ : (RoseTree.node (Label.app (Head.var 0)) [] : Expr) = Expr.var 0 [] := rfl
  have r3 : ∀ e : Expr, ((e.rename Nat.succ).rename Nat.succ).rename Nat.succ = e.rename (· + 3) :=
    fun e ↦ by rw [rename_rename, rename_rename]; rfl
  rw [rename_succ_four, rename_lam] at ha
  rw [r3, rename_lam] at hb
  rw [rename_succ_two, rename_lam] at ha₁
  simp only [lamL, lamC] at ha hb ha₁
  -- the motive at each child, in the hypothesis
  rw [v₁, hsub_var_base hApp (liftR (· + 4)) (fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) rfl
    (fun _ ↦ rfl) rfl, Option.some.injEq] at ha
  subst ha
  -- the motive at the conclusion's variable
  rw [v₀, hsub_var_base hApp (liftR (· + 2)) (liftR (· + 1)) rfl (fun _ ↦ rfl) (k := 0) rfl,
    Option.some.injEq] at ha₁
  subst ha₁
  rw [hsubWith_vacuous' _ _ _ (g := id) fun i ↦ by rcases i with _ | i <;> rfl, rename_id,
    Option.some.injEq] at ha₂
  subst ha₂
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hF
  subst hF
  -- the decodings
  obtain ⟨sp, hsp, hpt⟩ := termOf_typed (a := FreeTopos.omega) hk (hc.toTmCtx.consTm hra) rfl hPb
  obtain ⟨st, hst, htt⟩ := termOf_typed hk hc.toTmCtx hra ht
  obtain rfl := Option.some.inj (hφ.symm.trans (termOf_hsub₀ ha₃ hsp hst))
  -- the hypothesis that the motive holds at each child
  have hS₄ : termOf k (none :: none :: none :: none :: env)
      (Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) =
      some (Term.rename sp fun i ↦ match i with | 0 => 1 | i + 1 => i + 4) :=
    termOf_rename _ _ hsp fun i ↦ by rcases i with _ | i <;> rfl
  have hH : termOf k (none :: none :: env) (Expr.const 16 [Expr.const 30 [Expr.const 4 []],
      Expr.const 33 [Expr.const 42 [A], Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []], Pb.rename fun i ↦ match i with | 0 => 1 | i + 1 => i + 4,
          Expr.var 0 []]])), Expr.var 0 []],
      Expr.const 33 [Expr.const 42 [A], Expr.const 30 [Expr.const 4 []],
        Expr.const 31 [Expr.const 4 [], Expr.const 7 []],
        Expr.lam (Expr.lam (Expr.const 32 [Expr.const 4 [], Expr.const 8 [Expr.const 4 [],
          Expr.const 30 [Expr.const 4 []],
          Expr.const 16 [Expr.const 1 [], Expr.const 7 [], Expr.const 7 []], Expr.var 0 []]])),
        Expr.var 0 []]]) =
      some (FreeTopos.Internal.roseHyp k.nil k.cons sp) := by
    simp only [termOf_const, termOf_lam, List.map_cons, List.map_nil, decStep, hS₄,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
    rfl
  have hc₂ := (((hc.consTm hxa).consTm (a := FreeTopos.list (FreeTopos.lrose xa))
    (A := list (lrose A)) (by rw [encTy_list, hra]; rfl)).addHyp
    (typeIn_truth (G := G) (Γ := FreeTopos.list (FreeTopos.lrose xa) :: xa :: Γ))).consPf
    hH (typeIn_roseHyp hk.nil hk.cons hpt)
  have hlen : ((Φ.map weaken1).map weaken1 ++ [truth]).length = Φ.length + 1 := by
    rw [List.length_append, List.length_map, List.length_map, List.length_singleton]
  rw [hlen] at hc₂
  -- the motive at the construction, the step's conclusion
  have hY' : termOf k (some (Φ.length + 1) :: none :: none :: env) b =
      some (FreeTopos.Internal.roseNodeAt k.lnode (FreeTopos.lrose xa) xa sp) := by
    have h₁ : termOf k (none :: some (Φ.length + 1) :: none :: none :: env)
        (Pb.rename (liftR (· + 3))) = some (Term.rename sp (liftR (· + 2))) :=
      termOf_rename _ _ hsp fun i ↦ by rcases i with _ | i <;> rfl
    have h₂ : termOf k (some (Φ.length + 1) :: none :: none :: env)
        (Expr.const 43 [A, Expr.const 8 [A, Expr.const 30 [Expr.const 42 [A]],
          Expr.var 2 [], Expr.var 1 []]]) =
        some (Term.arr k.lnode [xa] (Term.pair (Term.var 1) (Term.var 0))) := by
      simp only [termOf_const, List.map_cons, List.map_nil, decStep, rename_closed hAc,
        decTy_encTy xa A hxa, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl
    rw [termOf_hsub₀ hb h₁ h₂]
    refine congrArg some (Term.subst_rename sp _ _ _ fun i ↦ ?_)
    rcases i with _ | i
    · exact congrArg (Term.arr k.lnode · _) (ite_eq_right (lrose_ne_rose xa)).symm
    · rfl
  obtain ⟨body₁, rfl, hb1, hlam⟩ := ihs ΓLF _ _ hds
  obtain ⟨body₂, rfl, hb2, hlam'⟩ := hlam _ _ _ hb1
  obtain ⟨body₃, rfl, hb3, hsound⟩ := hlam' _ _ _ hb2
  obtain ⟨Ds, hDs, hcs⟩ := hsound _ _ _ _ _ _ hc₂ hb3 hY'
  have hDs' : decPf k body₃ (some (Φ.length + 1) :: none :: none :: env) (Φ.length + 2) =
      some Ds := by
    rw [List.length_append, hlen, List.length_singleton] at hDs
    exact hDs
  have hw : (Φ ++ [truth]).map FreeTopos.Internal.weaken2 =
      (Φ.map weaken1).map weaken1 ++ [truth] := by
    rw [List.map_append, List.map_map]
    refine congrArg₂ _ (List.map_congr_left fun φ _ ↦ ?_) rfl
    exact (Term.rename_rename φ _ _ _ fun _ ↦ rfl).symm
  refine ⟨indD (FreeTopos.lrose xa) (.roseIndHyp k.lnode k.nil k.cons) sp st Φ.length [Ds], ?_,
    check_roseIndD (roseParts_lrose xa) (.inr ⟨hk.lnode, rfl⟩) hk.nil hk.cons
      (isTy_of_encTy G _ _ hra) hpt htt hc.typed (by rw [hw]; exact hcs)⟩
  rw [decPf_const]
  simp only [List.map_cons, List.map_nil, decPfStep, termOf_lam, hsp, hst, decPf_lam, hDs',
    decTy_encTy xa A hxa, Option.map_some, Option.bind_eq_bind, Option.bind_some, lamBody_lam,
    Option.pure_def]

/-- The soundness of the decoding of a proof variable: the hypothesis the environment indexes. -/
theorem sound_hyp (hc : PfCtx G k ΓLF env Γ Φ) {i : ℕ} {ms : List Expr} {C F : Expr}
    {φ : MTerm} (hC : classOf sig ΓLF (.var i) = some C)
    (hS : spine ΓLF C (ms.map fun m ↦ (m, judge sig m)) = some (pf F))
    (hφ : termOf k env F = some φ) :
    ∃ D, decPf k (Expr.app (.var i) ms) env Φ.length = some D ∧
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

include hk in
/-- The soundness of the decoding of proofs: a canonical LF term of the family of proofs of a
formula, in a context matching an environment, an internal context and hypotheses, where the
formula decodes, decodes to a derivation that the internal language's checker accepts as a proof
of the formula's decoding; and likewise at the bodies of one and of two abstractions it is. -/
theorem pfSound : ∀ M : Expr, PfSound G k E M :=
  RoseTree.ind fun l cs ih ↦ by
    have hlam : ∀ c ∈ cs, PfLam (PfSoundAt G k E) c := fun c hc ↦ (ih c hc).2.mono fun _ h ↦ h.1
    have hlam₂ : ∀ c ∈ cs, PfLam (fun b ↦ PfLam (PfSoundAt G k E) b) c := fun c hc ↦
      (ih c hc).2.mono fun _ h ↦ h.2.mono fun _ h' ↦ h'.1
    have hlam₃ : ∀ c ∈ cs, PfLam (fun b ↦ PfLam (fun b' ↦ PfLam (PfSoundAt G k E) b') b) c :=
      fun c hc ↦ (ih c hc).2.mono fun _ h ↦ h.2.mono fun _ h' ↦ h'.2
    refine ⟨fun ΓLF env Γ Φ F φ hc hj hφ ↦ ?_, fun ΓLF T P hj ↦ ?_⟩
    · obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hM
      obtain ⟨C, hC, hS⟩ := judge_app_inv hj
      rcases h with i | c
      · exact sound_hyp E hc hC hS hφ
      have hCs := Sig.ok_typeShape sig_ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C _ hCs hS
      have hc' := sig_head_pf hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (pf F).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      have mem : ∀ {x : Expr} {xs : List Expr}, x ∈ x :: xs := List.mem_cons_self
      have mem' : ∀ {x y : Expr} {xs : List Expr}, x ∈ xs → x ∈ y :: xs := List.mem_cons_of_mem _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, t, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        exact sound_refl E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨P, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨t, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        obtain ⟨u, dh, dp, rfl⟩ := List.length_eq_three.mp (Nat.succ.inj (Nat.succ.inj
          (Nat.succ.inj (hlen : cs.length + 1 + 1 + 1 = 3 + 1 + 1 + 1))))
        exact sound_leib E hk hc (ih dh (mem' (mem' (mem' (mem' mem))))).1
          (ih dp (mem' (mem' (mem' (mem' (mem' mem)))))).1 hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, f, a, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_beta E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, a, b, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_fstPair E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B, a, b, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_sndPair E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, B, p, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_pairEta E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        exact sound_unitEta E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', z, s', rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_natZero E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨z, s', n, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_natSucc E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨B, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        obtain ⟨f, g, dH, rfl⟩ := List.length_eq_three.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 3 + 1 + 1)))
        exact sound_funExt E hk hc (hlam dH (mem' (mem' (mem' (mem' mem))))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨Q, d₁, d₂, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_propExt E hk hc (hlam d₁ (mem' (mem' mem)))
          (hlam d₂ (mem' (mem' (mem' mem)))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨d₀, ds, n, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        exact sound_natInd E hk hc (ih d₀ (mem' mem)).1 (hlam₂ ds (mem' (mem' mem))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, C', z, s', rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        exact sound_listNil E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 5 + 1)
        obtain ⟨C', cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 5 + 1))
        obtain ⟨z, s', h, t, rfl⟩ := List.length_eq_four.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1 + 1)))
        exact sound_listCons E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨P, d₀, ds, l, rfl⟩ :=
          List.length_eq_four.mp (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        exact sound_listInd E hk hc (ih d₀ (mem' (mem' mem))).1
          (hlam₃ ds (mem' (mem' (mem' mem)))) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨C', s', l, t, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        exact sound_roseNode E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨P, ds, t, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        exact sound_roseInd E hk hc (hlam₃ ds (mem' mem)) hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, cs, rfl⟩ := List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨C', s', l, t, rfl⟩ :=
          List.length_eq_four.mp (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        exact sound_lroseNode E hk hc hS hφ
      · obtain rfl : C = _ := Option.some.inj (hC.symm.trans rfl)
        obtain ⟨A, P, ds, t, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        exact sound_lroseInd E hk hc (hlam₃ ds (mem' (mem' mem))) hS hφ
    · obtain ⟨body, hM, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hM
      exact ⟨body, rfl, hbJ, (ih body List.mem_cons_self).1,
        (ih body List.mem_cons_self).2.mono fun _ h ↦ ⟨h.1, h.2.mono fun _ h' ↦ h'.1⟩⟩

include hk in
/-- The soundness of the decoding of proofs, at a proof in a context matching an environment, an
internal context and hypotheses. -/
theorem decPf_sound {ΓLF : Ctx} {env : List (Option ℕ)} {Γ : List PartialHorn.Tree}
    {Φ : List Term} {M F : Expr} {φ : MTerm} (hc : PfCtx G k ΓLF env Γ Φ)
    (hj : judge sig M ΓLF (.check (pf F)) = true) (hφ : termOf k env F = some φ) :
    ∃ D, decPf k M env Φ.length = some D ∧ (check G E 0 D).2 Γ Φ φ = true :=
  (pfSound E hk M).1 _ _ _ _ _ _ hc hj hφ

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
    PfCtx G k ΓLF (List.replicate Γ.length none) Γ [] where
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

include hk in
/-- The soundness of the decoding of proofs, at a proof of a formula in a context of term
variables of encoded types: the proof decodes to a derivation that proves, as a theorem of the
internal language without hypotheses, the formula's decoding. -/
theorem decPf_checks {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) {M F : Expr}
    (hF : judge sig F ΓLF (.check (tm omega)) = true)
    (hj : judge sig M ΓLF (.check (pf F)) = true) :
    ∃ D φ, decPf k M (List.replicate Γ.length none) 0 = some D ∧
      termOf k (List.replicate Γ.length none) F = some φ ∧
      FreeTopos.Internal.Thm.checks G E ⟨0, Γ, [], φ⟩ D = true := by
  have hc : PfCtx G k ΓLF (List.replicate Γ.length none) Γ [] := PfCtx.ofEnc h
  obtain ⟨φ, hφ, hφt⟩ := termOf_typed (a := FreeTopos.omega) hk hc.toTmCtx rfl hF
  obtain ⟨D, hD, hch⟩ := decPf_sound E hk hc hj hφ
  refine ⟨D, φ, hD, hφ, ?_⟩
  simp only [FreeTopos.Internal.Thm.checks, List.all_nil, Bool.and_true, hφt, decide_true,
    hch, List.all_eq_true]
  intro a ha
  obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem ha
  obtain ⟨A, hA, -⟩ := varType_encCtx h (List.getElem?_eq_getElem hi')
  exact isTy_of_encTy G _ A hA

end Geb.LF.Topos

end
