/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.LF.Metatheory.Substitution
public import Geb.Prototypes.LF.Topos.Signature
import Mathlib.Tactic.IntervalCases
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

The encoding of terms ({lit}`enc`) is computed from the compilation, which supplies the types
that the constants of the signature take as arguments; decoding ({lit}`dec`) forgets them. The
completeness of the encoding requires the condition {lit}`Expr.FoldsClosed`, since the folds of
the internal language compile their start in the empty environment and their step in the
environment of the recursion's value alone, while LF admits a start and a step that mention the
variables around the fold.

## Main definitions

* {lit}`encTy`, {lit}`decTy` — the encoding of the fragment's types, and its inverse.
* {lit}`enc`, {lit}`dec` — the encoding of the fragment's terms, and its inverse.
* {lit}`Expr.FoldsClosed` — the condition that a term's folds have closed starts and steps.

## Main statements

* {lit}`decTy_encTy` — decoding inverts the encoding of types.
* {lit}`encTy_closed`, {lit}`encTy_checks` — encoded types are closed canonical terms of
  {lit}`tp`.
* {lit}`tyComplete` — every canonical term of {lit}`tp` is an encoded type.
* {lit}`enc_checks` — the encoding of a compiled term checks against the family of terms of its
  encoded type.
* {lit}`dec_enc` — decoding inverts the encoding of terms.
* {lit}`tmComplete` — every canonical term of a family of terms, in an encoded context, whose
  folds are closed, is the encoding of a compiled term of the type the family's index encodes.

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
        · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
      · simp at hcs
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        refine freeBelow_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
        rcases idx with _ | _ | idx
        · exact ih c₁ (by simp) a hcs.1
        · exact ih c₂ (by simp) b hcs.2
        · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
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
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      $hs,*]))

/-- The computation of the instantiation of a declaration's type along a spine, in a
hypothesis. -/
local macro "lf_spine_at" h:ident "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (set_option linter.unusedSimpArgs false in
    simp [spine, Expr.arrow, Expr.pi, Expr.shift, Expr.var, Expr.app, rename_node, Label.rename,
      Head.rename, liftR, hsub_eq, hsubWith_node, hsubStep, Label.binders, reduce_node,
      reduceStep, Expr.erase, eraseStep, renumber, -Nat.not_ofNat_lt_one, -Nat.add_eq_right,
      $hs,*] at $h:ident))

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
    · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)⟩

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

/-- Two nodes are equal exactly when their labels and children are. -/
theorem node_inj {l l' : Label} {cs cs' : List Expr} :
    (RoseTree.node l cs : Expr) = RoseTree.node l' cs' ↔ l = l' ∧ cs = cs' := by
  rw [RoseTree.node_eq_iff, RoseTree.label_node, RoseTree.children_node]

/-- The signature is formed. -/
theorem sig_ok : sig.ok = true := by decide +kernel

/-- The declarations whose types end in {lit}`tp` are the object types, of indices 1 to 5. -/
theorem sig_head_tp {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 0) :
    1 ≤ c ∧ c ≤ 5 := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 0) || (1 ≤ p.2 && p.2 ≤ 5)) =
      true := by decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact this

/-- The declarations whose types end in {lit}`tm` are the term constructors, of indices from 7
to 16. -/
theorem sig_head_tm {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 6) :
    7 ≤ c ∧ c ≤ 16 := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 6) || (7 ≤ p.2 && p.2 ≤ 16)) =
      true := by decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.and_eq_true,
    decide_eq_true_eq] at this
  exact this

/-- The inversion of the check of an application against an atomic type: the head's classifier
instantiates along the spine to it. -/
theorem judge_app_inv {Γ : Ctx} {h : Head} {ms : List Expr} {P : Expr}
    (hj : judge sig (Expr.app h ms) Γ (.check P) = true) :
    ∃ C, classOf sig Γ h = some C ∧ spine Γ C (ms.map fun m ↦ (m, judge sig m)) = some P := by
  rw [judge, Expr.app, judgeWith_node] at hj
  simp only [judgeStep, Bool.and_eq_true] at hj
  obtain ⟨-, hm⟩ := hj
  rcases hC : classOf sig Γ h with _ | C
  · rw [hC] at hm
    simp at hm
  · rw [hC, Option.bind_some] at hm
    rcases hS : spine Γ C (ms.map fun c ↦ (c, judgeWith (· == ·) sig c)) with _ | P'
    · rw [hS] at hm
      simp at hm
    · rw [hS] at hm
      simp only [beq_iff_eq] at hm
      subst hm
      exact ⟨C, rfl, hS⟩

/-- The checks against atomic types are of applications. -/
theorem judge_atomic_app {Γ : Ctx} {M P : Expr} (hP : IsApp P = true)
    (hj : judge sig M Γ (.check P) = true) : ∃ h ms, M = Expr.app h ms := by
  obtain ⟨l, cs, rfl⟩ := exists_node M
  rw [judge, judgeWith_node] at hj
  rcases l with _ | _ | _ | h
  · simp [judgeStep] at hj
  · simp [judgeStep] at hj
  · obtain ⟨pl, pcs, rfl⟩ := exists_node P
    rcases pl with _ | _ | _ | _ <;> simp [IsApp] at hP
    rcases cs with _ | ⟨m, _ | ⟨d, cs⟩⟩ <;> simp [judgeStep] at hj
  · exact ⟨h, cs, rfl⟩

/-- Every canonical term of {lit}`tp`, in a context whose variables' types end in {lit}`tm`, is
the encoding of a type. -/
theorem tyComplete {Γ : Ctx}
    (hΓ : ∀ i t, varType Γ i = some t → t.TypeShape = true ∧ t.headDepth.1 = some 6) :
    ∀ A : Expr, judge sig A Γ (.check tp) = true → ∃ a, encTy a = some A :=
  RoseTree.ind fun l cs ih hj ↦ by
    obtain ⟨h, ms, hA⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hA
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    rcases h with i | c
    · obtain ⟨hCs, hCh⟩ := hΓ i C hC
      have := (spine_headDepth _ C tp hCs hS).1
      rw [hCh] at this
      exact absurd this (by decide)
    · have hCs := Sig.ok_typeShape sig_ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C tp hCs hS
      obtain ⟨hc₁, hc₂⟩ := sig_head_tp hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show tp.headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      interval_cases c
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.one, rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl :
          some C = some (Expr.arrow tp (Expr.arrow tp tp)))
        obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha⟩ := ih x (by simp) hS.1
        obtain ⟨b, hb⟩ := ih y (by simp) hS.2
        exact ⟨FreeTopos.prod a b, by rw [encTy_prod, ha, hb]; rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl :
          some C = some (Expr.arrow tp (Expr.arrow tp tp)))
        obtain ⟨x, y, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha⟩ := ih x (by simp) hS.1
        obtain ⟨b, hb⟩ := ih y (by simp) hS.2
        exact ⟨FreeTopos.exp a b, by rw [encTy_exp, ha, hb]; rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.omega, rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.nat, rfl⟩

/-- The encoding of types is injective. -/
theorem encTy_inj {a b : PartialHorn.Tree} {A : Expr} (ha : encTy a = some A)
    (hb : encTy b = some A) : a = b :=
  Option.some.inj ((decTy_encTy a A ha).symm.trans (decTy_encTy b A hb))

/-- Whether a node, if a fold, has a start that mentions no variable and a step that is an
abstraction whose body mentions none but its own. -/
def foldClosedHere (l : Label) (cs : List Expr) : Bool :=
  match l, cs with
    | .app (.const 15), [_, z, f, _] =>
      Expr.FreeBelow z 0 && match f.label, f.children with
        | .lam, [b] => Expr.FreeBelow b 1
        | _, _ => false
    | _, _ => true

/-- One step of whether the folds of a term have closed starts and steps: the node's, and every
child's. -/
def foldsClosedStep (l : Label) (cs : List (Expr × Bool)) : Bool :=
  cs.all (·.2) && foldClosedHere l (cs.map Prod.fst)

/-- Whether the folds of a canonical LF term of the fragment have closed starts and steps, as the
folds of the internal language do: a start in the empty context, a step in the context of the
recursion's value. -/
def Expr.FoldsClosed : Expr → Bool := RoseTree.para foldsClosedStep

/-- The computation rule of the closedness of folds. -/
theorem foldsClosed_node (l : Label) (cs : List Expr) :
    Expr.FoldsClosed (RoseTree.node l cs) =
      foldsClosedStep l (cs.map fun c ↦ (c, Expr.FoldsClosed c)) :=
  RoseTree.para_node _ l cs

/-- The children of a term whose folds are closed have closed folds. -/
theorem foldsClosed_child {l : Label} {cs : List Expr}
    (h : Expr.FoldsClosed (RoseTree.node l cs) = true) {c : Expr} (hc : c ∈ cs) :
    Expr.FoldsClosed c = true := by
  rw [foldsClosed_node, foldsClosedStep, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 (c, Expr.FoldsClosed c) (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- A fold whose folds are closed has a closed start and a step whose body mentions only its own
variable. -/
theorem foldsClosed_natRec {C z f m : Expr}
    (h : Expr.FoldsClosed (Expr.const 15 [C, z, f, m]) = true) :
    Expr.FreeBelow z 0 = true ∧ ∃ b, f = Expr.lam b ∧ Expr.FreeBelow b 1 = true := by
  rw [Expr.const, Expr.app, foldsClosed_node, foldsClosedStep, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  simp only [List.map_cons, List.map_nil, foldClosedHere, Bool.and_eq_true] at h
  obtain ⟨hz, hf⟩ := h
  refine ⟨hz, ?_⟩
  obtain ⟨fl, fcs, rfl⟩ := exists_node f
  rw [RoseTree.label_node, RoseTree.children_node] at hf
  rcases fl with _ | _ | _ | _
  · simp at hf
  · simp at hf
  · rcases fcs with _ | ⟨b, _ | ⟨d, fcs⟩⟩
    · simp at hf
    · exact ⟨b, rfl, hf⟩
    · simp at hf
  · simp at hf

/-- The first step of a spine whose classifier is a product: the first argument checks against
the domain, and the rest instantiates the substituted codomain. -/
theorem spine_cons_inv {Γ : Ctx} {a b m : Expr} {J : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi a b) ((m, J) :: ms) = some P) :
    J Γ (.check a) = true ∧ ∃ b', hsub (Expr.erase a) m b 0 = some b' ∧ spine Γ b' ms = some P := by
  simp only [spine, List.foldlM_cons] at h
  obtain ⟨b', hb', hr⟩ := Option.bind_eq_some_iff.mp h
  rw [Expr.pi, RoseTree.label_node, RoseTree.children_node] at hb'
  simp only at hb'
  split_ifs at hb' with hJ
  exact ⟨hJ, b', hb', hr⟩

/-- The leading arguments of a spine of a classifier that begins with two products over
{lit}`tp` check against {lit}`tp`. -/
theorem spine_tp₂ {Γ : Ctx} {X A B : Expr} {JA JB : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi tp (Expr.pi tp X)) ((A, JA) :: (B, JB) :: ms) = some P) :
    JA Γ (.check tp) = true ∧ JB Γ (.check tp) = true := by
  obtain ⟨hA, b', hb', h⟩ := spine_cons_inv h
  obtain ⟨tp', X', htp, -, rfl⟩ := hsub_pi _ _ _ _ _ _ hb'
  rw [hsub_eq, hsubWith_closed (show tp.FreeBelow 0 = true from rfl), Option.some.injEq] at htp
  subst htp
  exact ⟨hA, (spine_cons_inv h).1⟩

/-- The leading argument of a spine of a classifier that begins with a product over {lit}`tp`
checks against {lit}`tp`. -/
theorem spine_tp₁ {Γ : Ctx} {X A : Expr} {JA : Ctx → Mode → Bool}
    {ms : List (Expr × (Ctx → Mode → Bool))} {P : Expr}
    (h : spine Γ (Expr.pi tp X) ((A, JA) :: ms) = some P) : JA Γ (.check tp) = true :=
  (spine_cons_inv h).1

/-- A variable of an encoded environment's type has an arrow and that type. -/
theorem env_of_map_snd {e : MEnv} {i : ℕ} {a : PartialHorn.Tree}
    (h : (e.map Prod.snd)[i]? = some a) : ∃ f, e[i]? = some (f, a) := by
  rw [List.getElem?_map, Option.map_eq_some_iff] at h
  obtain ⟨⟨f, a'⟩, hf, rfl⟩ := h
  exact ⟨f, hf⟩

/-- The types of the variables of an encoded context are the encodings' families of terms. -/
theorem varType_encCtx_inv {Γ : List PartialHorn.Tree} {ΓLF : Ctx} (h : encCtx Γ = some ΓLF)
    {i : ℕ} {t : Expr} (ht : varType ΓLF i = some t) :
    ∃ a A, Γ[i]? = some a ∧ encTy a = some A ∧ t = tm A := by
  obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
  rw [encCtx, PartialHorn.mapM_eq_some_iff] at h
  have hi := congrArg (·[i]?) h
  simp only [List.getElem?_map, ht', Option.map_some] at hi
  obtain ⟨a, ha, hat⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hat
  exact ⟨a, A, ha, hA, rename_closed (tm_closed (encTy_closed a A hA)) _⟩

/-- The families of terms of encoded types have the shape of types and end in {lit}`tm`. -/
theorem encCtx_heads {Γ : List PartialHorn.Tree} {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) :
    ∀ i t, varType ΓLF i = some t → t.TypeShape = true ∧ t.headDepth.1 = some 6 := by
  intro i t ht
  obtain ⟨a, A, -, -, rfl⟩ := varType_encCtx_inv h ht
  exact ⟨rfl, rfl⟩

/-- The encoded types are types of the internal language, built from operations of
{name}`Geb.FreeTopos.Internal.tyOps`. -/
theorem isTy_of_encTy (G : FreeTopos.Internal.Globals) :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy a = some A → FreeTopos.Internal.IsTy G 0 a = true :=
  RoseTree.ind fun l cs ih A h ↦ by
    rw [encTy_node] at h
    unfold FreeTopos.Internal.IsTy
    rw [RoseTree.para_node]
    rcases encTyStep_eq_some h with ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have h₁ := ih c₁ (by simp) a hcs.1
        have h₂ := ih c₂ (by simp) b hcs.2
        unfold FreeTopos.Internal.IsTy at h₁ h₂
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.all_cons,
          List.all_nil, h₁, h₂, Bool.and_true]
        rfl
      · simp at hcs
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, _ | ⟨c₃, cs⟩⟩⟩
      · simp at hcs
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have h₁ := ih c₁ (by simp) a hcs.1
        have h₂ := ih c₂ (by simp) b hcs.2
        unfold FreeTopos.Internal.IsTy at h₁ h₂
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.all_cons,
          List.all_nil, h₁, h₂, Bool.and_true]
        rfl
      · simp at hcs
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl

section Completeness

variable {G : FreeTopos.Internal.Globals} {kz ks : ℕ}

/-- The conclusion of the completeness of the encoding at a term, an environment and a type: the
term decodes to a term of the internal language that compiles in the environment to a type that
the type encodes, and whose encoding it is. -/
def TmConcl (G : FreeTopos.Internal.Globals) (kz ks : ℕ) (M : Expr) (X : PartialHorn.Tree)
    (e : MEnv) (A : Expr) : Prop :=
  ∃ s r, dec kz ks M = some s ∧ FreeTopos.Internal.compile G 0 s X e = some r ∧
    encTy r.2 = some A ∧ enc G kz ks s X e = some M

/-- The completeness of the encoding at a term, of the family of terms of a type, and, where the
term checks against a product of families of terms, at the body of the abstraction it is, in
every environment of the extended types. -/
def TmComplete (G : FreeTopos.Internal.Globals) (kz ks : ℕ) (M : Expr) : Prop :=
  (∀ (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (A : Expr),
    encCtx (e.map Prod.snd) = some ΓLF → Expr.FoldsClosed M = true →
    judge sig M ΓLF (.check (tm A)) = true → TmConcl G kz ks M X e A) ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a : PartialHorn.Tree) (A' B' : Expr),
    encCtx Γ = some ΓLF → encTy a = some A' → Expr.FoldsClosed M = true →
    judge sig M ΓLF (.check (Expr.pi (tm A') (tm B'))) = true →
    ∃ body, M = Expr.lam body ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = a :: Γ → TmConcl G kz ks body X e B')

/-- Encoding is onto the canonical LF terms whose folds are closed: every such term of the family
of terms of a type, in an encoded context, decodes to a term of the internal language that
compiles, in an environment of the context's types, to a type the type encodes, and whose
encoding it is. -/
theorem tmComplete (hz : G.prims[kz]? = some FreeTopos.Internal.zeroPrim)
    (hs : G.prims[ks]? = some FreeTopos.Internal.succPrim) : ∀ M : Expr, TmComplete G kz ks M :=
  RoseTree.ind fun l cs ih ↦ by
    refine ⟨fun X e ΓLF A hΓ hfc hj ↦ ?_, fun Γ ΓLF a A' B' hΓ ha hfc hj ↦ ?_⟩
    rotate_left
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      refine ⟨body, rfl, fun X e he ↦ ?_⟩
      exact (ih body (by simp)).1 X e (tm A' :: ΓLF) B' (by rw [he]; exact encCtx_cons ha hΓ)
        (foldsClosed_child hfc (by simp)) hbJ
    unfold TmConcl
    obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hM
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    have hheads := encCtx_heads hΓ
    rcases h with i | c
    · obtain ⟨hCs, hCh⟩ := hheads i C hC
      obtain ⟨a, A', ha, hA', rfl⟩ := varType_encCtx_inv hΓ hC
      have hlen := (spine_headDepth _ _ _ hCs hS).2
      rw [show (tm A).headDepth.2 = 0 from rfl, show (tm A').headDepth.2 = 0 from rfl,
        List.length_map] at hlen
      obtain rfl := List.length_eq_zero_iff.mp (by omega : cs.length = 0)
      simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq,
        tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] at hS
      subst hS
      obtain ⟨f, hf⟩ := env_of_map_snd ha
      refine ⟨FreeTopos.Internal.Term.var i, (f, a), rfl,
        FreeTopos.Internal.compile_var_iff.mpr ⟨rfl, hf⟩, hA', ?_⟩
      rw [FreeTopos.Internal.Term.var, enc_node]
      rfl
    · have hCs := Sig.ok_typeShape sig_ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C _ hCs hS
      obtain ⟨hc₁, hc₂⟩ := sig_head_tm hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (tm A).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      have hchild : ∀ c' ∈ cs, Expr.FoldsClosed c' = true := fun c' hc' ↦ foldsClosed_child hfc hc'
      interval_cases c
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (tm one))
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        simp only [List.map_nil, spine, List.foldlM_nil, Option.pure_def, Option.some.injEq,
          tm, Expr.const, Expr.app, node_inj, List.cons.injEq, and_true, true_and] at hS
        subst hS
        refine ⟨FreeTopos.Internal.Term.star, _,
          (by rw [dec_node]; rfl), FreeTopos.Internal.compile_star_iff.mpr ⟨rfl, rfl⟩, rfl, ?_⟩
        rw [FreeTopos.Internal.Term.star, enc_node]
        rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.pi tp (Expr.pi tp
          (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (prod (v 1) (v 0))))))))
        obtain ⟨A', cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨B', t, u, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads A' hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads B' hT.2
        have hAc := encTy_closed a A' ha
        have hBc := encTy_closed b B' hb
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a'⟩, hdt, hct, hrt, het⟩ :=
          (ih t (by simp)).1 X e ΓLF A' hΓ (hchild t (by simp)) ht
        obtain ⟨su, ⟨g, b'⟩, hdu, hcu, hru, heu⟩ :=
          (ih u (by simp)).1 X e ΓLF B' hΓ (hchild u (by simp)) hu
        obtain rfl := encTy_inj hrt ha
        obtain rfl := encTy_inj hru hb
        refine ⟨FreeTopos.Internal.Term.pair st su, (FreeTopos.pair f g, FreeTopos.prod a' b'),
          ?_, FreeTopos.Internal.compile_pair_iff.mpr ⟨st, su, f, a', g, b', rfl, hct, hcu, rfl⟩,
          by rw [encTy_prod, ha, hb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.pair, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, hcu, ha, hb, het, heu,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 1))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hBc := encTy_closed b X2 hb
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, hp, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy (FreeTopos.prod a b) = some (prod X1 X2) := by
          rw [encTy_prod, ha, hb]; rfl
        obtain ⟨sp, ⟨f, c'⟩, hdp, hcp, hrp, hep⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ (hchild X3 (by simp)) hp
        obtain rfl := encTy_inj hrp hab
        refine ⟨FreeTopos.Internal.Term.fst sp, _, ?_,
          FreeTopos.Internal.compile_fst_iff.mpr ⟨sp, f, a, b, rfl, hcp, rfl⟩, ha, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdp]
          rfl
        · rw [FreeTopos.Internal.Term.fst, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcp, ha, hb, hep, Option.bind_eq_bind,
            Option.bind_some, FreeTopos.Internal.prodParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (prod (v 1) (v 0))) (tm (v 0))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hBc := encTy_closed b X2 hb
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, hp, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy (FreeTopos.prod a b) = some (prod X1 X2) := by
          rw [encTy_prod, ha, hb]; rfl
        obtain ⟨sp, ⟨f, c'⟩, hdp, hcp, hrp, hep⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ (hchild X3 (by simp)) hp
        obtain rfl := encTy_inj hrp hab
        refine ⟨FreeTopos.Internal.Term.snd sp, _, ?_,
          FreeTopos.Internal.compile_snd_iff.mpr ⟨sp, f, a, b, rfl, hcp, rfl⟩, hb, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdp]
          rfl
        · rw [FreeTopos.Internal.Term.snd, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcp, ha, hb, hep, Option.bind_eq_bind,
            Option.bind_some, FreeTopos.Internal.prodParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0)))
            (tm (exp (v 1) (v 0)))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hBc := encTy_closed b X2 hb
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, hf, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨body, rfl, hbody⟩ := (ih X3 (by simp)).2 (e.map Prod.snd) ΓLF a X1 X2 hΓ ha
          (hchild X3 (by simp)) hf
        obtain ⟨sb, ⟨fb, b'⟩, hdb, hcb, hrb, heb⟩ :=
          hbody (FreeTopos.prod X a) (FreeTopos.Internal.extEnv X a e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        obtain rfl := encTy_inj hrb hb
        refine ⟨FreeTopos.Internal.Term.lam a sb, _, ?_,
          FreeTopos.Internal.compile_lam_iff.mpr ⟨sb, fb, b', rfl, isTy_of_encTy G a X1 ha, hcb,
            rfl⟩, by rw [encTy_exp, ha, hrb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, RoseTree.label_node,
            ↓reduceIte, dec_node, hdb, decTy_encTy a X1 ha]
          rfl
        · rw [FreeTopos.Internal.Term.lam, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcb, ha, hrb, heb,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (exp (v 1) (v 0)))
            (Expr.arrow (tm (v 1)) (tm (v 0)))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hBc := encTy_closed b X2 hb
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hab : encTy (FreeTopos.exp a b) = some (exp X1 X2) := by
          rw [encTy_exp, ha, hb]; rfl
        obtain ⟨st, ⟨f, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X3 (by simp)).1 X e ΓLF (exp X1 X2) hΓ (hchild X3 (by simp)) ht
        obtain ⟨su, ⟨g, a'⟩, hdu, hcu, hru, heu⟩ :=
          (ih X4 (by simp)).1 X e ΓLF X1 hΓ (hchild X4 (by simp)) hu
        obtain rfl := encTy_inj hrt hab
        obtain rfl := encTy_inj ha hru
        refine ⟨FreeTopos.Internal.Term.app st su, _, ?_,
          FreeTopos.Internal.compile_app_iff.mpr ⟨st, su, rfl, f, a, b, hct, g, hcu, rfl⟩, hb, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.app, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, ha, hb, het, heu,
            Option.bind_eq_bind, Option.bind_some, FreeTopos.Internal.expParts_eq_some.mpr rfl]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm one) (tm nat)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, one, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF one hΓ (hchild X1 (by simp)) ht
        obtain rfl := encTy_inj hrt (rfl : encTy FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr kz [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hz, g, hct, rfl, rfl, rfl⟩, rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm nat) (tm nat)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF nat hΓ (hchild X1 (by simp)) ht
        obtain rfl := encTy_inj hrt (rfl : encTy FreeTopos.nat = some nat)
        have hne : ks ≠ kz := fun h ↦ by
          subst h
          have hd := congrArg FreeTopos.Internal.Prim.dom (Option.some.inj (hz.symm.trans hs))
          exact absurd (congrArg RoseTree.label hd) (by decide)
        refine ⟨FreeTopos.Internal.Term.arr ks [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hs, g, hct, rfl, rfl, rfl⟩, rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hne, ↓reduceIte, het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0)))
            (Expr.arrow (tm nat) (tm (v 0)))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 3 + 1)
        obtain ⟨X2, X3, X4, rfl⟩ :=
          List.length_eq_three.mp (Nat.succ.inj (hlen : cs.length + 1 = 3 + 1))
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨c, hc⟩ := tyComplete hheads X1 (spine_tp₁ hS)
        have hCc := encTy_closed c X1 hc
        simp only [tm, tp, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hCc,
          hsubWith_closed hCc]
        obtain ⟨-, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨hz0, b, rfl, hb1⟩ := foldsClosed_natRec hfc
        have hnil : ∀ i < 0, ΓLF[i]? = ([] : Ctx)[i]? := fun _ hi ↦ absurd hi (Nat.not_lt_zero _)
        unfold judge at hzJ hfJ
        rw [judgeWith_congr_ctx X2 ΓLF [] 0 _ hnil hz0] at hzJ
        rw [judgeWith_congr_ctx (Expr.lam b) ΓLF [] 0 _ hnil
          (freeBelow_node_iff.mpr ⟨(fun _ h ↦ nomatch h), fun idx hidx ↦ by
            rcases idx with _ | idx
            · exact hb1
            · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)⟩)] at hfJ
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ :=
          (ih X2 (by simp)).1 FreeTopos.one [] [] X1 rfl (hchild X2 (by simp)) hzJ
        obtain ⟨body, hbody, hbc⟩ := (ih (Expr.lam b) (by simp)).2 [] [] c X1 X1 rfl hc
          (hchild _ (by simp)) hfJ
        obtain rfl : b = body := (List.cons.inj (node_inj.mp hbody).2).1
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ := hbc c [(FreeTopos.idt c, c)] rfl
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ :=
          (ih X4 (by simp)).1 X e ΓLF nat hΓ (hchild X4 (by simp)) hm
        obtain rfl := encTy_inj hc hrz
        obtain rfl := encTy_inj hc hrs
        obtain rfl := encTy_inj hrm (rfl : encTy FreeTopos.nat = some nat)
        refine ⟨FreeTopos.Internal.Term.natRec sz ss sm, _, ?_,
          FreeTopos.Internal.compile_natRec_iff.mpr ⟨sz, ss, sm, rfl, fz, c, hcz, fs, hcs, fm,
            hcm, rfl⟩, hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, RoseTree.label_node,
            ↓reduceIte, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.natRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (tm (v 0)) (tm omega)))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha⟩ := tyComplete hheads X1 (spine_tp₁ hS)
        have hAc := encTy_closed a X1 ha
        simp only [tm, tp, omega, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          hsubWith_closed hAc]
        obtain ⟨-, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a₁⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF X1 hΓ (hchild X2 (by simp)) ht
        obtain ⟨su, ⟨g, a₂⟩, hdu, hcu, hru, heu⟩ :=
          (ih X3 (by simp)).1 X e ΓLF X1 hΓ (hchild X3 (by simp)) hu
        obtain rfl := encTy_inj ha hrt
        obtain rfl := encTy_inj ha hru
        refine ⟨FreeTopos.Internal.Term.eq st su, _, ?_,
          FreeTopos.Internal.compile_eq_iff.mpr ⟨st, su, rfl, f, a, hct, g, hcu, rfl⟩, rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, hdu]
          rfl
        · rw [FreeTopos.Internal.Term.eq, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hct, ha, het, heu,
            Option.bind_eq_bind, Option.bind_some]
          rfl

end Completeness

end Geb.LF.Topos

end
