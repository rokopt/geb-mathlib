/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Substitution
public import Geb.Prototypes.LF.Metatheory.Substitution
public import Geb.Prototypes.LF.Topos.Signature
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The adequacy of the representation of the internal language

The representation of a fragment of the internal language by the signature
{name}`Geb.LF.Topos.sig` is adequate ({cite}`HarperLicata2007`, Section 3.2): the encoding of a
term of the language, typed by {lit}`Geb.FreeTopos.Internal.compile`, is a canonical LF term of
{lit}`tm A` for the encoding {lit}`A` of its type in the encoding of its context; decoding inverts
encoding; and every canonical LF term of {lit}`tm A` in such a context whose folds' starts and
steps mention no variable around them decodes to a term of the language of the type that
{lit}`A` encodes, whose encoding it is. The fragment's types are those built from the terminal
object, binary products, exponentials, the subobject classifier and the natural numbers object,
and its terms the variables, the element of the terminal object, pairs and their components,
abstraction and application, zero and the successor, the fold of the natural numbers and
equality.

This file encodes the types ({lit}`encTy`) and decodes them ({lit}`decTy`).

## Main definitions

* {lit}`encTy`, {lit}`decTy` — the encoding of the fragment's types, and its inverse.

## Main statements

* {lit}`decTy_encTy` — decoding inverts the encoding of types.
* {lit}`encTy_closed`, {lit}`encTy_checks` — encoded types are closed canonical terms of
  {lit}`tp`.

## References

* {cite}`HarperLicata2007`, Section 3.2, for adequacy.

## Tags

logical framework, LF, adequacy, Mitchell–Bénabou language
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

/-- One step of the encoding of a type of the fragment, at a node of an operation's label, from
its children's encodings: the terminal object, a product, an exponential, the subobject
classifier and the natural numbers object, the operations of indices 4, 6, 22, 25 and 29 of the
combinators, are the constants of the same names. -/
def encTyStep (l : ℕ) (cs : List (Option Expr)) : Option Expr :=
  match l, cs with
    | 5, [] => some one
    | 7, [a, b] => do pure (prod (← a) (← b))
    | 23, [a, b] => do pure (exp (← a) (← b))
    | 26, [] => some omega
    | 30, [] => some nat
    | _, _ => none

/-- The encoding of a type of the fragment as a canonical term of {lit}`tp`. -/
def encTy : PartialHorn.Tree → Option Expr := RoseTree.elim encTyStep

/-- One step of the decoding of a canonical term of {lit}`tp`, at a node of a label, from its
children's decodings. -/
def decTyStep (l : Label) (cs : List (Option PartialHorn.Tree)) : Option PartialHorn.Tree :=
  match l, cs with
    | .app (.const 1), [] => some FreeTopos.one
    | .app (.const 2), [a, b] => do pure (FreeTopos.prod (← a) (← b))
    | .app (.const 3), [a, b] => do pure (FreeTopos.exp (← a) (← b))
    | .app (.const 4), [] => some FreeTopos.omega
    | .app (.const 5), [] => some FreeTopos.nat
    | _, _ => none

/-- The decoding of a canonical term of {lit}`tp` as a type of the fragment. -/
def decTy : Expr → Option PartialHorn.Tree := RoseTree.elim decTyStep

/-- The encodings of the fragment's types, one constructor at a time. -/
theorem encTy_node (l : ℕ) (cs : List PartialHorn.Tree) :
    encTy (RoseTree.node l cs) = encTyStep l (cs.map encTy) :=
  RoseTree.elim_node _ l cs

/-- The steps of the encoding that have a value. -/
theorem encTyStep_eq_some {l : ℕ} {cs : List (Option Expr)} {A : Expr}
    (h : encTyStep l cs = some A) :
    (l = 5 ∧ cs = [] ∧ A = one) ∨
      (l = 7 ∧ ∃ a b, cs = [some a, some b] ∧ A = prod a b) ∨
      (l = 23 ∧ ∃ a b, cs = [some a, some b] ∧ A = exp a b) ∨
      (l = 26 ∧ cs = [] ∧ A = omega) ∨ (l = 30 ∧ cs = [] ∧ A = nat) := by
  unfold encTyStep at h
  split at h
  · exact .inl ⟨rfl, rfl, (Option.some.inj h).symm⟩
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inl ⟨rfl, a, b, by rw [ha, hb], (Option.some.inj h).symm⟩)
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inl ⟨rfl, a, b, by rw [ha, hb], (Option.some.inj h).symm⟩))
  · exact .inr (.inr (.inr (.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩)))
  · exact .inr (.inr (.inr (.inr ⟨rfl, rfl, (Option.some.inj h).symm⟩)))
  · exact absurd h (by simp)

/-- The decoding of a node of a canonical term of {lit}`tp`. -/
theorem decTy_node (l : Label) (cs : List Expr) :
    decTy (RoseTree.node l cs) = decTyStep l (cs.map decTy) :=
  RoseTree.elim_node _ l cs

/-- Decoding inverts the encoding of types. -/
theorem decTy_encTy : ∀ (a : PartialHorn.Tree) (A : Expr), encTy a = some A → decTy A = some a :=
  RoseTree.ind fun l cs ih A h ↦ by
    rw [encTy_node] at h
    rcases encTyStep_eq_some h with ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        rw [prod, Expr.const, Expr.app, decTy_node]
        simp only [List.map_cons, List.map_nil, decTyStep, ih c₁ (by simp) a hcs.1,
          ih c₂ (by simp) b hcs.2]
        rfl
      · simp at hcs
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        rw [exp, Expr.const, Expr.app, decTy_node]
        simp only [List.map_cons, List.map_nil, decTyStep, ih c₁ (by simp) a hcs.1,
          ih c₂ (by simp) b hcs.2]
        rfl
      · simp at hcs
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl

/-- The encoding of a type is closed. -/
theorem encTy_closed :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy a = some A → A.FreeBelow 0 = true :=
  RoseTree.ind fun l cs ih A h ↦ by
    rw [encTy_node] at h
    rcases encTyStep_eq_some h with ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩
    · rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        refine freeBelow_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
        rcases idx with _ | _ | idx
        · exact ih c₁ (by simp) a hcs.1
        · exact ih c₂ (by simp) b hcs.2
        · exact absurd hidx (by simp)
      · simp at hcs
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        refine freeBelow_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
        rcases idx with _ | _ | idx
        · exact ih c₁ (by simp) a hcs.1
        · exact ih c₂ (by simp) b hcs.2
        · exact absurd hidx (by simp)
      · simp at hcs
    · rfl
    · rfl

/-- The computation of the instantiation of a declaration's type along a spine of symbolic
arguments: the hereditary substitutions unfolded node by node, with the given facts about the
arguments, their checks and their closedness among them. The set of lemmas is shared by every
declaration, and a given computation uses only some of them. -/
local macro "lf_spine" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, $hs,*]))

/-- An application of a constant checks against an atomic type that its type instantiates to
along its spine. -/
theorem judge_const {Γ : Ctx} {c : ℕ} {ms : List Expr} {T P : Expr} (hc : sig[c]? = some T)
    (hs : spine Γ T (ms.map fun m ↦ (m, judge sig m)) = some P) (hP : IsApp P = true) :
    judge sig (Expr.const c ms) Γ (.check P) = true := by
  rw [judge, Expr.const, Expr.app, judgeWith_node]
  simp only [judgeStep, hP, Bool.true_and, classOf, hc, Option.bind_some]
  rw [show spine Γ T (ms.map fun c ↦ (c, judgeWith (· == ·) sig c)) = some P from hs]
  exact beq_self_eq_true P

/-- The encoding of a type is a canonical term of {lit}`tp`, in every context. -/
theorem encTy_checks :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy a = some A → ∀ Γ : Ctx,
      judge sig A Γ (.check tp) = true :=
  RoseTree.ind fun l cs ih A h Γ ↦ by
    have hclosed := encTy_closed _ A h
    rw [encTy_node] at h
    rcases encTyStep_eq_some h with ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩
    · exact judge_const (T := tp) rfl rfl rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have ha := ih c₁ (by simp) a hcs.1 Γ
        have hb := ih c₂ (by simp) b hcs.2 Γ
        have hac := encTy_closed c₁ a hcs.1
        have hbc := encTy_closed c₂ b hcs.2
        refine judge_const (T := Expr.arrow tp (Expr.arrow tp tp)) rfl ?_ rfl
        simp only [tp, Expr.const, Expr.app] at ha hb ⊢
        lf_spine [ha, hb, rename_closed hac, rename_closed hbc, hsubWith_closed hac,
          hsubWith_closed hbc]
      · simp at hcs
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have ha := ih c₁ (by simp) a hcs.1 Γ
        have hb := ih c₂ (by simp) b hcs.2 Γ
        have hac := encTy_closed c₁ a hcs.1
        have hbc := encTy_closed c₂ b hcs.2
        refine judge_const (T := Expr.arrow tp (Expr.arrow tp tp)) rfl ?_ rfl
        simp only [tp, Expr.const, Expr.app] at ha hb ⊢
        lf_spine [ha, hb, rename_closed hac, rename_closed hbc, hsubWith_closed hac,
          hsubWith_closed hbc]
      · simp at hcs
    · exact judge_const (T := tp) rfl rfl rfl
    · exact judge_const (T := tp) rfl rfl rfl

/-- The encoding of a context of the fragment's types: each type {lit}`a` is the type
{lit}`tm A` of an LF variable, {lit}`A` the encoding of {lit}`a`. -/
def encCtx (Γ : List PartialHorn.Tree) : Option Ctx := Γ.mapM fun a ↦ (encTy a).map tm

/-- A term of the internal language. -/
abbrev MTerm : Type := FreeTopos.Internal.Term

/-- An environment of the compilation of the internal language: an arrow and a type for each
variable. -/
abbrev MEnv : Type := List (PartialHorn.Tree × PartialHorn.Tree)

section Encoding

variable (G : FreeTopos.Internal.Globals) (kz ks : ℕ)

open FreeTopos.Internal in
/-- One step of the encoding of a term of the internal language, at a node of a label, from its
children's encodings, in an environment over {lit}`X`: each constructor of the fragment is the
constant of the same name, applied to the encodings of the types of its children, which the
compilation computes, and of the children; an abstraction's body and a fold's step are LF
abstractions; zero and the successor are the primitive arrows of indices {lit}`kz` and
{lit}`ks`. A term outside the fragment, or with a type outside it, has no encoding. -/
def encStep (l : FreeTopos.Internal.Label)
    (cs : List (MTerm × (PartialHorn.Tree → MEnv → Option Expr)))
    (X : PartialHorn.Tree) (e : MEnv) : Option Expr :=
  match l, cs with
    | .var i, [] => some (Expr.var i)
    | .star, [] => some star
    | .pair, [(t, et), (u, eu)] => do
      let (_, a) ← compile G 0 t X e
      let (_, b) ← compile G 0 u X e
      pure (pair (← encTy a) (← encTy b) (← et X e) (← eu X e))
    | .fst, [(t, et)] => do
      let (_, p) ← compile G 0 t X e
      let (a, b) ← prodParts p
      pure (fst (← encTy a) (← encTy b) (← et X e))
    | .snd, [(t, et)] => do
      let (_, p) ← compile G 0 t X e
      let (a, b) ← prodParts p
      pure (snd (← encTy a) (← encTy b) (← et X e))
    | .lam a, [(t, et)] => do
      let (_, b) ← compile G 0 t (FreeTopos.prod X a) (extEnv X a e)
      pure (lam (← encTy a) (← encTy b) (Expr.lam (← et (FreeTopos.prod X a) (extEnv X a e))))
    | .app, [(t, et), (_, eu)] => do
      let (_, p) ← compile G 0 t X e
      let (a, b) ← expParts p
      pure (app (← encTy a) (← encTy b) (← et X e) (← eu X e))
    | .arr k [], [(_, et)] =>
      if k = kz then zeroAt <$> et X e else if k = ks then succ <$> et X e else none
    | .natRec, [(z, ez), (_, es), (_, em)] => do
      let (_, c) ← compile G 0 z FreeTopos.one []
      pure (natRec (← encTy c) (← ez FreeTopos.one [])
        (Expr.lam (← es c [(FreeTopos.idt c, c)])) (← em X e))
    | .eq, [(t, et), (_, eu)] => do
      let (_, a) ← compile G 0 t X e
      pure (eq (← encTy a) (← et X e) (← eu X e))
    | _, _ => none

/-- The encoding of a term of the internal language in an environment. -/
def enc : MTerm → PartialHorn.Tree → MEnv → Option Expr := RoseTree.para (encStep G kz ks)

/-- The computation rule of the encoding of terms. -/
theorem enc_node (l : FreeTopos.Internal.Label) (cs : List MTerm) :
    enc G kz ks (RoseTree.node l cs) = encStep G kz ks l (cs.map fun c ↦ (c, enc G kz ks c)) :=
  RoseTree.para_node _ l cs

end Encoding

/-- The family of terms of a closed type is closed. -/
theorem tm_closed {A : Expr} (h : A.FreeBelow 0 = true) : (tm A).FreeBelow 0 = true :=
  freeBelow_node_iff.mpr ⟨(fun _ h ↦ nomatch h), fun idx hidx ↦ by
    rcases idx with _ | idx
    · exact h
    · exact absurd hidx (by simp)⟩

/-- The type of a variable of an encoded context is the encoding of its type. -/
theorem varType_encCtx {Γ : List PartialHorn.Tree} {ΓLF : Ctx} (h : encCtx Γ = some ΓLF)
    {i : ℕ} {a : PartialHorn.Tree} (ha : Γ[i]? = some a) :
    ∃ A, encTy a = some A ∧ varType ΓLF i = some (tm A) := by
  rw [encCtx, PartialHorn.mapM_eq_some_iff] at h
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map, ha, Option.map_some] at hi
  obtain ⟨T, hT, hTe⟩ : ∃ T, ΓLF[i]? = some T ∧ (encTy a).map tm = some T := by
    cases hΓ : ΓLF[i]? with
    | none => rw [hΓ] at hi; simp at hi
    | some T => rw [hΓ] at hi; exact ⟨T, rfl, Option.some.inj hi⟩
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hTe
  refine ⟨A, hA, ?_⟩
  simp only [varType, hT, Option.map_some, rename_closed (tm_closed (encTy_closed a A hA))]

/-- A variable of a type checks against it. -/
theorem judge_var {Γ : Ctx} {i : ℕ} {A : Expr} (hA : IsApp A = true) (h : varType Γ i = some A) :
    judge sig (Expr.var i) Γ (.check A) = true := by
  rw [judge, Expr.var, Expr.app, judgeWith_node]
  simp only [judgeStep, hA, Bool.true_and, List.map_nil]
  rw [show classOf sig Γ (.var i) = some A from h, Option.bind_some]
  exact beq_self_eq_true A

/-- The encoding of a context extended by a type. -/
theorem encCtx_cons {a : PartialHorn.Tree} {A : Expr} (ha : encTy a = some A)
    {Γ : List PartialHorn.Tree} {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) :
    encCtx (a :: Γ) = some (tm A :: ΓLF) := by
  rw [encCtx, List.mapM_cons, ha, ← encCtx, h]
  rfl

/-- The encoding of a product type. -/
theorem encTy_prod (a b : PartialHorn.Tree) :
    encTy (FreeTopos.prod a b) = (encTy a).bind fun A ↦ (encTy b).map fun B ↦ prod A B := by
  rw [FreeTopos.prod, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy a <;> cases encTy b <;> rfl

/-- The encoding of an exponential type. -/
theorem encTy_exp (a b : PartialHorn.Tree) :
    encTy (FreeTopos.exp a b) = (encTy a).bind fun A ↦ (encTy b).map fun B ↦ exp A B := by
  rw [FreeTopos.exp, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy a <;> cases encTy b <;> rfl

/-- An abstraction checks against a product when its body checks against the codomain in the
context extended by the domain. -/
theorem judge_lam {Γ : Ctx} {body a b : Expr} (h : judge sig body (a :: Γ) (.check b) = true) :
    judge sig (Expr.lam body) Γ (.check (Expr.pi a b)) = true := by
  rw [judge, Expr.lam, judgeWith_node]
  simp only [judgeStep, List.map_cons, List.map_nil, Expr.pi, RoseTree.label_node,
    RoseTree.children_node]
  exact h

/-- A term judged in the empty context, closed, is judged so in every context. -/
theorem judge_of_nil {M : Expr} {md : Mode} (h : judge sig M [] md = true) (Γ : Ctx) :
    judge sig M Γ md = true := by
  rw [← h]
  exact judgeWith_congr_ctx M Γ [] 0 md (fun _ hi ↦ absurd hi (Nat.not_lt_zero _))
    (judgeWith_freeBelow M [] md h)

/-- A term judged in a context of one type is judged so in every context extending it by that
type. -/
theorem judge_of_single {M a : Expr} {md : Mode} (h : judge sig M [a] md = true) (Γ : Ctx) :
    judge sig M (a :: Γ) md = true := by
  rw [← h]
  refine judgeWith_congr_ctx M (a :: Γ) [a] 1 md (fun i hi ↦ ?_)
    (judgeWith_freeBelow M [a] md h)
  rcases i with _ | i
  · rfl
  · exact absurd hi (by omega)

section Soundness

variable {G : FreeTopos.Internal.Globals} {kz ks : ℕ}

/-- Encoding is sound: the encoding of a term of the fragment, in an environment whose types are
encoded, is a canonical LF term of the family of terms of the encoding of its type. -/
theorem enc_checks (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim)
    (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim) :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (M : Expr)
      (r : PartialHorn.Tree × PartialHorn.Tree),
      encCtx (e.map Prod.snd) = some ΓLF → enc G kz ks s X e = some M →
      FreeTopos.Internal.compile G 0 s X e = some r →
      ∃ A, encTy r.2 = some A ∧ judge sig M ΓLF (.check (tm A)) = true :=
  RoseTree.ind fun l cs ih X e ΓLF M r hΓ henc hcomp ↦ by
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨k, θ⟩ | _ | _ | c | ⟨k, θ⟩ | _
    · obtain ⟨rfl, hi⟩ := FreeTopos.Internal.compile_var_iff.mp hcomp
      simp only [encStep, List.map_nil, Option.some.injEq] at henc
      subst henc
      have hi' : (e.map Prod.snd)[i]? = some r.2 := by simp [hi]
      obtain ⟨A, hA, hv⟩ := varType_encCtx hΓ hi'
      exact ⟨A, hA, judge_var rfl hv⟩
    · obtain ⟨rfl, rfl⟩ := FreeTopos.Internal.compile_star_iff.mp hcomp
      simp only [encStep, List.map_nil, Option.some.injEq] at henc
      subst henc
      exact ⟨one, rfl, judge_const (T := tm one) rfl rfl rfl⟩
    · obtain ⟨t, u, f, a, g, b, rfl, hct, hcu, rfl⟩ :=
        FreeTopos.Internal.compile_pair_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, hcu, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨A', hA', hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
      obtain ⟨B', hB', hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ hΓ hMu hcu
      simp only [hA, Option.some.injEq] at hA'
      simp only [hB, Option.some.injEq] at hB'
      subst hA' hB'
      refine ⟨prod A B, by simp [encTy_prod, hA, hB], judge_const
        (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0))
          (tm (prod (v 1) (v 0))))))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hBt := encTy_checks b B hB ΓLF
      have hAc := encTy_closed a A hA
      have hBc := encTy_closed b B hB
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ hMuJ ⊢
      lf_spine [hAt, hBt, hMtJ, hMuJ, rename_closed hAc, rename_closed hBc, hsubWith_closed hAc,
        hsubWith_closed hBc]
    · obtain ⟨t, f, a, b, rfl, hct, rfl⟩ := FreeTopos.Internal.compile_fst_iff.mp hcomp
      have hp : FreeTopos.Internal.prodParts (FreeTopos.prod a b) = some (a, b) :=
        FreeTopos.Internal.prodParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
      obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
      simp only [encTy_prod, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      subst hP
      refine ⟨A, hA, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0)))
        (tm (v 1))))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hBt := encTy_checks b B hB ΓLF
      have hAc := encTy_closed a A hA
      have hBc := encTy_closed b B hB
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
      lf_spine [hAt, hBt, hMtJ, rename_closed hAc, rename_closed hBc, hsubWith_closed hAc,
        hsubWith_closed hBc]
    · obtain ⟨t, f, a, b, rfl, hct, rfl⟩ := FreeTopos.Internal.compile_snd_iff.mp hcomp
      have hp : FreeTopos.Internal.prodParts (FreeTopos.prod a b) = some (a, b) :=
        FreeTopos.Internal.prodParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, rfl⟩ := henc
      obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
      simp only [encTy_prod, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      subst hP
      refine ⟨B, hB, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0)))
        (tm (v 0))))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hBt := encTy_checks b B hB ΓLF
      have hAc := encTy_closed a A hA
      have hBc := encTy_closed b B hB
      simp only [tm, tp, prod, Expr.const, Expr.app] at hAt hBt hMtJ ⊢
      lf_spine [hAt, hBt, hMtJ, rename_closed hAc, rename_closed hBc, hsubWith_closed hAc,
        hsubWith_closed hBc]
    · obtain ⟨t, f, b, rfl, -, hct, rfl⟩ := FreeTopos.Internal.compile_lam_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mb, hMb, rfl⟩ := henc
      have hΓ' : encCtx ((FreeTopos.Internal.extEnv X a e).map Prod.snd) = some (tm A :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons hA (by simpa [Function.comp_def] using hΓ)
      obtain ⟨B', hB', hMbJ⟩ := ih t (by simp) _ _ _ Mb _ hΓ' hMb hct
      simp only [hB, Option.some.injEq] at hB'
      subst hB'
      have hAc := encTy_closed a A hA
      have hBc := encTy_closed b B hB
      have hlam : judge sig (Expr.lam Mb) ΓLF (.check (Expr.pi (tm A) (tm B))) = true :=
        judge_lam hMbJ
      refine ⟨exp A B, by simp [encTy_exp, hA, hB], judge_const
        (T := Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0)))
          (tm (exp (v 1) (v 0)))))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hBt := encTy_checks b B hB ΓLF
      simp only [tm, tp, exp, Expr.const, Expr.app, Expr.pi] at hAt hBt hlam ⊢
      lf_spine [hAt, hBt, hlam, rename_closed hAc, rename_closed hBc, hsubWith_closed hAc,
        hsubWith_closed hBc]
    · obtain ⟨t, u, rfl, f, a, b, hct, g, hcu, rfl⟩ := FreeTopos.Internal.compile_app_iff.mp hcomp
      have hp : FreeTopos.Internal.expParts (FreeTopos.exp a b) = some (a, b) :=
        FreeTopos.Internal.expParts_eq_some.mpr rfl
      simp only [encStep, List.map_cons, List.map_nil, hct, hp, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, B, hB, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
      obtain ⟨A', hA', hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ hΓ hMu hcu
      simp only [encTy_exp, hA, hB, Option.bind_some, Option.map_some, Option.some.injEq] at hP
      simp only [hA, Option.some.injEq] at hA'
      subst hP hA'
      refine ⟨B, hB, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (exp (v 1) (v 0)))
        (Expr.arrow (tm (v 1)) (tm (v 0)))))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hBt := encTy_checks b B hB ΓLF
      have hAc := encTy_closed a A hA
      have hBc := encTy_closed b B hB
      simp only [tm, tp, exp, Expr.const, Expr.app] at hAt hBt hMtJ hMuJ ⊢
      lf_spine [hAt, hBt, hMtJ, hMuJ, rename_closed hAc, rename_closed hBc, hsubWith_closed hAc,
        hsubWith_closed hBc]
    · obtain ⟨t, rfl, p, hp, g, hct, hl, -, rfl⟩ := FreeTopos.Internal.compile_arr_iff.mp hcomp
      rcases θ with _ | ⟨θ₀, θ⟩
      · by_cases hkz : k = kz
        · subst hkz
          rw [hz, Option.some.injEq] at hp
          subst hp
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.map_eq_map,
            Option.map_eq_some_iff] at henc
          obtain ⟨Mt, hMt, rfl⟩ := henc
          obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
          simp only [FreeTopos.Internal.zeroPrim, PartialHorn.subst_nil] at hP ⊢
          rw [show encTy FreeTopos.one = some one from rfl, Option.some.injEq] at hP
          subst hP
          refine ⟨nat, rfl, judge_const (T := Expr.arrow (tm one) (tm nat)) rfl ?_ rfl⟩
          simp only [tm, one, nat, Expr.const, Expr.app] at hMtJ ⊢
          lf_spine [hMtJ]
        · by_cases hks : k = ks
          · subst hks
            rw [hs, Option.some.injEq] at hp
            subst hp
            simp only [encStep, List.map_cons, List.map_nil, hkz, ↓reduceIte, Option.map_eq_map,
              Option.map_eq_some_iff] at henc
            obtain ⟨Mt, hMt, rfl⟩ := henc
            obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
            simp only [FreeTopos.Internal.succPrim, PartialHorn.subst_nil] at hP ⊢
            rw [show encTy FreeTopos.nat = some nat from rfl, Option.some.injEq] at hP
            subst hP
            refine ⟨nat, rfl, judge_const (T := Expr.arrow (tm nat) (tm nat)) rfl ?_ rfl⟩
            simp only [tm, nat, Expr.const, Expr.app] at hMtJ ⊢
            lf_spine [hMtJ]
          · simp [encStep, hkz, hks] at henc
      · simp [encStep] at henc
    · obtain ⟨z, sₛ, m, rfl, z', c, hcz, s', hcs, m', hcm, rfl⟩ :=
        FreeTopos.Internal.compile_natRec_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      obtain ⟨C₁, hC₁, hMzJ⟩ := ih z (by simp) _ [] [] Mz _ rfl hMz hcz
      obtain ⟨C₂, hC₂, hMsJ⟩ := ih sₛ (by simp) _ _ [tm C] Ms _
        (by simpa using encCtx_cons hC (Γ := []) rfl) hMs hcs
      obtain ⟨N, hN, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ hΓ hMm hcm
      simp only [hC, Option.some.injEq] at hC₁ hC₂
      rw [show encTy FreeTopos.nat = some nat from rfl, Option.some.injEq] at hN
      subst hC₁ hC₂ hN
      have hCc := encTy_closed c C hC
      have hMzJ' := judge_of_nil hMzJ ΓLF
      have hlam : judge sig (Expr.lam Ms) ΓLF (.check (Expr.pi (tm C) (tm C))) = true :=
        judge_lam (judge_of_single hMsJ ΓLF)
      refine ⟨C, hC, judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0))) (Expr.arrow (tm nat) (tm (v 0)))))) rfl ?_
        rfl⟩
      have hCt := encTy_checks c C hC ΓLF
      simp only [tm, tp, nat, Expr.const, Expr.app, Expr.pi] at hCt hMzJ' hlam hMmJ ⊢
      lf_spine [hCt, hMzJ', hlam, hMmJ, rename_closed hCc, hsubWith_closed hCc]
    · simp [encStep] at henc
    · simp [encStep] at henc
    · simp [encStep] at henc
    · obtain ⟨t, u, rfl, f, a, hct, g, hcu, rfl⟩ := FreeTopos.Internal.compile_eq_iff.mp hcomp
      simp only [encStep, List.map_cons, List.map_nil, hct, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, Mt, hMt, Mu, hMu, rfl⟩ := henc
      obtain ⟨A₁, hA₁, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
      obtain ⟨A₂, hA₂, hMuJ⟩ := ih u (by simp) X e ΓLF Mu _ hΓ hMu hcu
      simp only [hA, Option.some.injEq] at hA₁ hA₂
      subst hA₁ hA₂
      refine ⟨omega, rfl, judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (tm (v 0)) (tm omega)))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hAc := encTy_closed a A hA
      simp only [tm, tp, omega, Expr.const, Expr.app] at hAt hMtJ hMuJ ⊢
      lf_spine [hAt, hMtJ, hMuJ, rename_closed hAc, hsubWith_closed hAc]

end Soundness

section Decoding

variable (kz ks : ℕ)

/-- One step of the decoding of a canonical LF term of the fragment, at a node of a label, from
its children, each paired with its decoding: each constant is the constructor of the same name,
its type arguments dropped but for an abstraction's domain, which is decoded as a type; an LF
abstraction is its body, the body of an abstraction or the step of a fold; zero and the successor
are the primitive arrows of indices {lit}`kz` and {lit}`ks`. -/
def decStep (l : Label) (cs : List (Expr × Option MTerm)) : Option MTerm :=
  match l, cs with
    | .app (.var i), [] => some (FreeTopos.Internal.Term.var i)
    | .app (.const 7), [] => some FreeTopos.Internal.Term.star
    | .app (.const 8), [_, _, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.pair (← t) (← u))
    | .app (.const 9), [_, _, (_, t)] => FreeTopos.Internal.Term.fst <$> t
    | .app (.const 10), [_, _, (_, t)] => FreeTopos.Internal.Term.snd <$> t
    | .app (.const 11), [(A, _), _, (f, t)] =>
      if f.label = .lam then do pure (FreeTopos.Internal.Term.lam (← decTy A) (← t)) else none
    | .app (.const 12), [_, _, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.app (← t) (← u))
    | .app (.const 13), [(_, t)] => FreeTopos.Internal.Term.arr kz [] <$> t
    | .app (.const 14), [(_, t)] => FreeTopos.Internal.Term.arr ks [] <$> t
    | .app (.const 15), [_, (_, z), (f, s), (_, m)] =>
      if f.label = .lam then do pure (FreeTopos.Internal.Term.natRec (← z) (← s) (← m))
      else none
    | .app (.const 16), [_, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.eq (← t) (← u))
    | .lam, [(_, b)] => b
    | _, _ => none

/-- The decoding of a canonical LF term of the fragment as a term of the internal language. -/
def dec : Expr → Option MTerm := RoseTree.para (decStep kz ks)

/-- The computation rule of the decoding. -/
theorem dec_node (l : Label) (cs : List Expr) :
    dec kz ks (RoseTree.node l cs) = decStep kz ks l (cs.map fun c ↦ (c, dec kz ks c)) :=
  RoseTree.para_node _ l cs

end Decoding

/-- Decoding inverts encoding. -/
theorem dec_enc {G : FreeTopos.Internal.Globals} {kz ks : ℕ} :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (M : Expr), enc G kz ks s X e = some M →
      dec kz ks M = some s :=
  RoseTree.ind fun l cs ih X e M henc ↦ by
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨k, θ⟩ | _ | _ | c | ⟨k, θ⟩ | _
    · rcases cs with _ | ⟨d, cs⟩
      · simp only [encStep, List.map_nil, Option.some.injEq] at henc
        subst henc
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨d, cs⟩
      · simp only [encStep, List.map_nil, Option.some.injEq] at henc
        subst henc
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, a, -, -, b, -, A, -, B, -, Mt, hMt, Mu, hMu, rfl⟩ := henc
        rw [pair, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
          ih u (by simp) X e Mu hMu]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, p, -, a, b, -, A, -, B, -, Mt, hMt, rfl⟩ := henc
        rw [fst, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, p, -, a, b, -, A, -, B, -, Mt, hMt, rfl⟩ := henc
        rw [snd, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, b, -, A, hA, B, -, Mb, hMb, rfl⟩ := henc
        rw [lam, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, RoseTree.label_node,
          ↓reduceIte, dec_node, ih t (by simp) _ _ Mb hMb, decTy_encTy a A hA]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, p, -, a, b, -, A, -, B, -, Mt, hMt, Mu, hMu, rfl⟩ := henc
        rw [app, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
          ih u (by simp) X e Mu hMu]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨d, cs⟩⟩
      · simp [encStep] at henc
      · rcases θ with _ | ⟨θ₀, θ⟩
        · by_cases hkz : k = kz
          · subst hkz
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.map_eq_map,
              Option.map_eq_some_iff] at henc
            obtain ⟨Mt, hMt, rfl⟩ := henc
            rw [zeroAt, Expr.const, Expr.app, dec_node]
            simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
            rfl
          · by_cases hks : k = ks
            · subst hks
              simp only [encStep, List.map_cons, List.map_nil, hkz, ↓reduceIte,
                Option.map_eq_map, Option.map_eq_some_iff] at henc
              obtain ⟨Mt, hMt, rfl⟩ := henc
              rw [succ, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
              rfl
            · simp [encStep, hkz, hks] at henc
        · simp [encStep] at henc
      · simp [encStep] at henc
    · rcases cs with _ | ⟨z, _ | ⟨sₛ, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, c, -, C, -, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
        rw [natRec, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, RoseTree.label_node,
          ↓reduceIte, dec_node, ih z (by simp) _ _ Mz hMz, ih sₛ (by simp) _ _ Ms hMs,
          ih m (by simp) X e Mm hMm]
        rfl
      · simp [encStep] at henc
    · simp [encStep] at henc
    · simp [encStep] at henc
    · simp [encStep] at henc
    · rcases cs with _ | ⟨t, _ | ⟨u, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, a, -, A, -, Mt, hMt, Mu, hMu, rfl⟩ := henc
        rw [eq, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
          ih u (by simp) X e Mu hMu]
        rfl
      · simp [encStep] at henc

end Geb.LF.Topos

end
