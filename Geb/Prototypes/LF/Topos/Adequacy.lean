/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Internal.Substitution
public import Geb.Prototypes.LF.Metatheory.Substitution
public import Geb.Prototypes.LF.Topos.Signature
import Mathlib.Tactic.NormNum
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The adequacy of the representation of the internal language

The representation of a fragment of the internal language by the signature
{name}`Geb.LF.Topos.sig` is adequate ({cite}`HarperLicata2007`, Section 3.2): the encoding of a
term of the language, typed by {lit}`Geb.FreeTopos.Internal.compile`, is a canonical LF term of
{lit}`tm A` for the encoding {lit}`A` of its type in the encoding of its context; decoding inverts
encoding; and every canonical LF term of {lit}`tm A` in such a context decodes to a term of the
language of the type that {lit}`A` encodes, whose encoding it is. The fragment's types are those
built from the terminal object, binary products, exponentials, the subobject classifier, the
natural numbers object, list objects, the rose-tree object of natural-number labels and rose-tree
objects of labels of any type, and its terms the variables, the element of the terminal object,
pairs and their components, abstraction and application, zero and the successor, the empty list
and the construction of a list, the constructions of rose trees, the folds of the natural numbers,
of lists and of rose trees, and equality.

The encoding of terms ({lit}`enc`) is computed from the compilation, which supplies the types
that the constants of the signature take as arguments; decoding ({lit}`dec`) forgets them. The
fold of the signature is the fold of the language: its start a term of the fold's context and its
step an LF abstraction over the value, whose body is the language's step, a term of the context
extended by the value, so that both may mention the variables around the fold.

## Main definitions

* {lit}`encTy`, {lit}`decTy` — the encoding of the fragment's types, and its inverse.
* {lit}`enc`, {lit}`dec` — the encoding of the fragment's terms, and its inverse.

## Main statements

* {lit}`decTy_encTy` — decoding inverts the encoding of types.
* {lit}`encTy_closed`, {lit}`encTy_checks` — encoded types are closed canonical terms of
  {lit}`tp`.
* {lit}`tyComplete` — every canonical term of {lit}`tp` is an encoded type.
* {lit}`enc_checks` — the encoding of a compiled term checks against the family of terms of its
  encoded type.
* {lit}`dec_enc` — decoding inverts the encoding of terms.
* {lit}`tmComplete` — every canonical term of a family of terms, in an encoded context, is the
  encoding of a compiled term of the type the family's index encodes.

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
classifier, the natural numbers object, a list object and the rose-tree objects, the operations of
indices 4, 6, 22, 25, 29, 33, 37 and 40 of the combinators, are the constants of the same
names. -/
def encTyStep (l : ℕ) (cs : List (Option Expr)) : Option Expr :=
  match l, cs with
    | 5, [] => some one
    | 7, [a, b] => do pure (prod (← a) (← b))
    | 23, [a, b] => do pure (exp (← a) (← b))
    | 26, [] => some omega
    | 30, [] => some nat
    | 34, [a] => do pure (list (← a))
    | 38, [] => some rose
    | 41, [a] => do pure (lrose (← a))
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
    | .app (.const 30), [a] => do pure (FreeTopos.list (← a))
    | .app (.const 37), [] => some FreeTopos.rose
    | .app (.const 42), [a] => do pure (FreeTopos.lrose (← a))
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
      (l = 26 ∧ cs = [] ∧ A = omega) ∨ (l = 30 ∧ cs = [] ∧ A = nat) ∨
      (l = 34 ∧ ∃ a, cs = [some a] ∧ A = list a) ∨ (l = 38 ∧ cs = [] ∧ A = rose) ∨
      (l = 41 ∧ ∃ a, cs = [some a] ∧ A = lrose a) := by
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
  · exact .inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩))))
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, a, by rw [ha], (Option.some.inj h).symm⟩)))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨rfl, rfl, (Option.some.inj h).symm⟩))))))
  · obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp h
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨rfl, a, by rw [ha],
      (Option.some.inj h).symm⟩))))))
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
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ |
        ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩
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
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        rw [list, Expr.const, Expr.app, decTy_node]
        simp only [List.map_cons, List.map_nil, decTyStep, ih c₁ (by simp) a hcs]
        rfl
      · simp at hcs
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        rw [lrose, Expr.const, Expr.app, decTy_node]
        simp only [List.map_cons, List.map_nil, decTyStep, ih c₁ (by simp) a hcs]
        rfl
      · simp at hcs

/-- The encoding of a type is closed. -/
theorem encTy_closed :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy a = some A → A.FreeBelow 0 = true :=
  RoseTree.ind fun l cs ih A h ↦ by
    rw [encTy_node] at h
    rcases encTyStep_eq_some h with ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ |
        ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩
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
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        refine freeBelow_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
        rcases idx with _ | idx
        · exact ih c₁ (by simp) a hcs
        · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
      · simp at hcs
    · rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        refine freeBelow_node_iff.mpr ⟨(fun i h ↦ nomatch h), fun idx hidx ↦ ?_⟩
        rcases idx with _ | idx
        · exact ih c₁ (by simp) a hcs
        · exact absurd hidx (by simp only [List.length_cons, List.length_nil]; omega)
      · simp at hcs

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
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ |
        ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩
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
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have ha := ih c₁ (by simp) a hcs Γ
        have hac := encTy_closed c₁ a hcs
        refine judge_const (T := Expr.arrow tp tp) rfl ?_ rfl
        simp only [tp, Expr.const, Expr.app] at ha ⊢
        lf_spine [ha, rename_closed hac, hsubWith_closed hac]
      · simp at hcs
    · exact judge_const (T := tp) rfl rfl rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have ha := ih c₁ (by simp) a hcs Γ
        have hac := encTy_closed c₁ a hcs
        refine judge_const (T := Expr.arrow tp tp) rfl ?_ rfl
        simp only [tp, Expr.const, Expr.app] at ha ⊢
        lf_spine [ha, rename_closed hac, hsubWith_closed hac]
      · simp at hcs

/-- The encoding of a context of the fragment's types: each type {lit}`a` is the type
{lit}`tm A` of an LF variable, {lit}`A` the encoding of {lit}`a`. -/
def encCtx (Γ : List PartialHorn.Tree) : Option Ctx := Γ.mapM fun a ↦ (encTy a).map tm

/-- A term of the internal language. -/
abbrev MTerm : Type := FreeTopos.Internal.Term

/-- An environment of the compilation of the internal language: an arrow and a type for each
variable. -/
abbrev MEnv : Type := List (PartialHorn.Tree × PartialHorn.Tree)

/-- The indices of the primitive arrows of the language that the signature's constants of zero,
the successor, the empty list, the construction of a list and the constructions of rose trees
stand for. -/
structure PrimIdx where
  /-- The index of zero. -/
  zero : ℕ
  /-- The index of the successor. -/
  succ : ℕ
  /-- The index of the empty list. -/
  nil : ℕ
  /-- The index of the construction of a list. -/
  cons : ℕ
  /-- The index of the construction of a rose tree of natural-number labels. -/
  node : ℕ
  /-- The index of the construction of a rose tree of labels of a type. -/
  lnode : ℕ

/-- The primitive arrows of the globals at the indices are those the indices name. -/
structure PrimIdx.Valid (k : PrimIdx) (G : FreeTopos.Internal.Globals) : Prop where
  /-- Zero. -/
  zero : G.prims[k.zero]? = some FreeTopos.Internal.zeroPrim
  /-- The successor. -/
  succ : G.prims[k.succ]? = some FreeTopos.Internal.succPrim
  /-- The empty list. -/
  nil : G.prims[k.nil]? = some FreeTopos.Internal.nilPrim
  /-- The construction of a list. -/
  cons : G.prims[k.cons]? = some FreeTopos.Internal.consPrim
  /-- The construction of a rose tree of natural-number labels. -/
  node : G.prims[k.node]? = some FreeTopos.Internal.nodePrim
  /-- The construction of a rose tree of labels of a type. -/
  lnode : G.prims[k.lnode]? = some FreeTopos.Internal.lnodePrim

section Encoding

variable (G : FreeTopos.Internal.Globals) (k : PrimIdx)

open FreeTopos.Internal in
/-- One step of the encoding of a term of the internal language, at a node of a label, from its
children's encodings, in an environment over {lit}`X`: each constructor of the fragment is the
constant of the same name, applied to the encodings of the types of its children, which the
compilation computes, and of the children; an abstraction's body and a fold's step are LF
abstractions, the step over the fold's type, the type of its start, and over the element type
before it for a list, and over the pair of a label and the list of the children's values for a rose
tree; zero, the successor, the empty list and the constructions of a list and of a rose tree are
the primitive arrows the indices name. A term outside the fragment, or with a type
outside it, has no encoding. -/
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
    | .arr i [], [(_, et)] =>
      if i = k.zero then zeroAt <$> et X e else if i = k.succ then succ <$> et X e
      else if i = k.node then node <$> et X e else none
    | .arr i [a], [(_, et)] =>
      if i = k.nil then do pure (nilAt (← encTy a) (← et X e))
      else if i = k.cons then do pure (cons (← encTy a) (← et X e))
      else if i = k.lnode then do pure (lnode (← encTy a) (← et X e)) else none
    | .natRec, [(z, ez), (_, es), (_, em)] => do
      let (_, c) ← compile G 0 z X e
      pure (natRec (← encTy c) (← ez X e)
        (Expr.lam (← es (FreeTopos.prod X c) (extEnv X c e))) (← em X e))
    | .listRec, [(z, ez), (_, es), (m, em)] => do
      let (_, c) ← compile G 0 z X e
      let (_, t) ← compile G 0 m X e
      let a ← listPart t
      pure (listRec (← encTy a) (← encTy c) (← ez X e)
        (Expr.lam (Expr.lam (← es (FreeTopos.prod (FreeTopos.prod X a) c)
          (extEnv (FreeTopos.prod X a) c (extEnv X a e))))) (← em X e))
    | .roseRec c, [(_, es), (m, em)] => do
      let (_, t) ← compile G 0 m X e
      match t.label, t.children with
      | 38, [] =>
        pure (roseRec (← encTy c) (Expr.lam (← es (FreeTopos.prod X (FreeTopos.prod FreeTopos.nat
          (FreeTopos.list c))) (extEnv X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) e)))
          (← em X e))
      | 41, [a] =>
        pure (lroseRec (← encTy a) (← encTy c) (Expr.lam (← es (FreeTopos.prod X (FreeTopos.prod a
          (FreeTopos.list c))) (extEnv X (FreeTopos.prod a (FreeTopos.list c)) e))) (← em X e))
      | _, _ => none
    | .eq, [(t, et), (_, eu)] => do
      let (_, a) ← compile G 0 t X e
      pure (eq (← encTy a) (← et X e) (← eu X e))
    | _, _ => none

/-- The encoding of a term of the internal language in an environment. -/
def enc : MTerm → PartialHorn.Tree → MEnv → Option Expr := RoseTree.para (encStep G k)

/-- The computation rule of the encoding of terms. -/
theorem enc_node (l : FreeTopos.Internal.Label) (cs : List MTerm) :
    enc G k (RoseTree.node l cs) =
      encStep G k l (cs.map fun c ↦ (c, enc G k c)) :=
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

/-- The encoding of a list type. -/
theorem encTy_list (a : PartialHorn.Tree) :
    encTy (FreeTopos.list a) = (encTy a).map list := by
  rw [FreeTopos.list, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy a <;> rfl

/-- The encoding of a rose-tree type of labels of a type. -/
theorem encTy_lrose (a : PartialHorn.Tree) :
    encTy (FreeTopos.lrose a) = (encTy a).map lrose := by
  rw [FreeTopos.lrose, PartialHorn.op, encTy_node]
  simp only [List.map_cons, List.map_nil, encTyStep]
  cases encTy a <;> rfl

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

/-- An abstraction of the internal language with its bound variable's type replaced, where the
term is an abstraction: the decoding of an LF abstraction carries a placeholder type, which the
constant applied to it supplies. -/
def relam (a : PartialHorn.Tree) (s : MTerm) : Option MTerm :=
  match s.label, s.children with
    | .lam _, [b] => some (FreeTopos.Internal.Term.lam a b)
    | _, _ => none

/-- The replacement of an abstraction's type. -/
theorem relam_lam (a a' : PartialHorn.Tree) (b : MTerm) :
    relam a (FreeTopos.Internal.Term.lam a' b) = some (FreeTopos.Internal.Term.lam a b) := rfl

/-- The replacement of a term's type as an abstraction is defined exactly at the abstractions. -/
theorem relam_eq_some {a : PartialHorn.Tree} {s r : MTerm} :
    relam a s = some r ↔ ∃ a' b, s = FreeTopos.Internal.Term.lam a' b ∧
      r = FreeTopos.Internal.Term.lam a b := by
  constructor
  · intro h
    rw [← RoseTree.node_label_children s] at h ⊢
    unfold relam at h
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · next a' b heq hcs =>
      rw [heq, hcs]
      exact ⟨a', b, rfl, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · rintro ⟨a', b, rfl, rfl⟩
    rfl

/-- The body of an abstraction of the internal language. -/
def lamBody (s : MTerm) : Option MTerm :=
  match s.label, s.children with
    | .lam _, [b] => some b
    | _, _ => none

/-- The body of an abstraction. -/
@[simp] theorem lamBody_lam (a : PartialHorn.Tree) (b : MTerm) :
    lamBody (FreeTopos.Internal.Term.lam a b) = some b := rfl

/-- The body of a term as an abstraction is defined exactly at the abstractions. -/
theorem lamBody_eq_some {s b : MTerm} :
    lamBody s = some b ↔ ∃ a, s = FreeTopos.Internal.Term.lam a b := by
  constructor
  · intro h
    rw [← RoseTree.node_label_children s] at h ⊢
    unfold lamBody at h
    simp only [RoseTree.label_node, RoseTree.children_node] at h
    split at h
    · next a b' heq hcs =>
      rw [heq, hcs, ← Option.some.inj h]
      exact ⟨a, rfl⟩
    · exact absurd h (by simp)
  · rintro ⟨a, rfl⟩
    rfl

section Decoding

variable (k : PrimIdx)

/-- One step of the decoding of a canonical LF term of the fragment, at a node of a label, from
its children, each paired with its decoding: each constant is the constructor of the same name,
its type arguments dropped but for an abstraction's domain, which is decoded as a type; an LF
abstraction is an abstraction of a placeholder type, which the constant of an abstraction applied
to it replaces by the domain, and whose body is the step of the fold applied to it, the body of
the body for a list; zero, the successor, the empty list and the constructions of a list and of
rose trees are the primitive arrows the indices name, the empty list, the construction of a list
and that of a rose tree of labels of a type at the decoded type; the folds of rose trees carry
their decoded type. -/
def decStep (l : Label) (cs : List (Expr × Option MTerm)) : Option MTerm :=
  match l, cs with
    | .app (.var i), [] => some (FreeTopos.Internal.Term.var i)
    | .app (.const 7), [] => some FreeTopos.Internal.Term.star
    | .app (.const 8), [_, _, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.pair (← t) (← u))
    | .app (.const 9), [_, _, (_, t)] => FreeTopos.Internal.Term.fst <$> t
    | .app (.const 10), [_, _, (_, t)] => FreeTopos.Internal.Term.snd <$> t
    | .app (.const 11), [(A, _), _, (_, t)] => do relam (← decTy A) (← t)
    | .app (.const 12), [_, _, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.app (← t) (← u))
    | .app (.const 13), [(_, t)] => FreeTopos.Internal.Term.arr k.zero [] <$> t
    | .app (.const 14), [(_, t)] => FreeTopos.Internal.Term.arr k.succ [] <$> t
    | .app (.const 15), [(_, _), (_, z), (_, s), (_, m)] => do
      pure (FreeTopos.Internal.Term.natRec (← z) (← lamBody (← s)) (← m))
    | .app (.const 16), [_, (_, t), (_, u)] => do
      pure (FreeTopos.Internal.Term.eq (← t) (← u))
    | .app (.const 31), [(A, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.nil [← decTy A] (← t))
    | .app (.const 32), [(A, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.cons [← decTy A] (← t))
    | .app (.const 33), [(_, _), (_, _), (_, z), (_, s), (_, m)] => do
      pure (FreeTopos.Internal.Term.listRec (← z) (← lamBody (← lamBody (← s))) (← m))
    | .app (.const 38), [(_, t)] => FreeTopos.Internal.Term.arr k.node [] <$> t
    | .app (.const 39), [(C, _), (_, s), (_, t)] => do
      pure (FreeTopos.Internal.Term.roseRec (← decTy C) (← lamBody (← s)) (← t))
    | .app (.const 43), [(A, _), (_, t)] => do
      pure (FreeTopos.Internal.Term.arr k.lnode [← decTy A] (← t))
    | .app (.const 44), [_, (C, _), (_, s), (_, t)] => do
      pure (FreeTopos.Internal.Term.roseRec (← decTy C) (← lamBody (← s)) (← t))
    | .lam, [(_, d)] => FreeTopos.Internal.Term.lam FreeTopos.one <$> d
    | _, _ => none

/-- The decoding of a canonical LF term of the fragment as a term of the internal language. -/
def dec : Expr → Option MTerm := RoseTree.para (decStep k)

/-- The computation rule of the decoding. -/
theorem dec_node (l : Label) (cs : List Expr) :
    dec k (RoseTree.node l cs) = decStep k l (cs.map fun c ↦ (c, dec k c)) :=
  RoseTree.para_node _ l cs

end Decoding

/-- Decoding inverts encoding. -/
theorem dec_enc {G : FreeTopos.Internal.Globals} {k : PrimIdx} :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (M : Expr), enc G k s X e = some M →
      dec k M = some s :=
  RoseTree.ind fun l cs ih X e M henc ↦ by
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨j, θ⟩ | _ | _ | c | ⟨j, θ⟩ | _
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
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
          ih t (by simp) _ _ Mb hMb, decTy_encTy a A hA]
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
      · rcases θ with _ | ⟨θ₀, _ | ⟨θ₁, θ⟩⟩
        · by_cases hkz : j = k.zero
          · subst hkz
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.map_eq_map,
              Option.map_eq_some_iff] at henc
            obtain ⟨Mt, hMt, rfl⟩ := henc
            rw [zeroAt, Expr.const, Expr.app, dec_node]
            simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
            rfl
          · by_cases hks : j = k.succ
            · subst hks
              simp only [encStep, List.map_cons, List.map_nil, hkz, ↓reduceIte,
                Option.map_eq_map, Option.map_eq_some_iff] at henc
              obtain ⟨Mt, hMt, rfl⟩ := henc
              rw [succ, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
              rfl
            · by_cases hkd : j = k.node
              · subst hkd
                simp only [encStep, List.map_cons, List.map_nil, hkz, hks, ↓reduceIte,
                  Option.map_eq_map, Option.map_eq_some_iff] at henc
                obtain ⟨Mt, hMt, rfl⟩ := henc
                rw [node, Expr.const, Expr.app, dec_node]
                simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt]
                rfl
              · simp [encStep, hkz, hks, hkd] at henc
        · by_cases hkn : j = k.nil
          · subst hkn
            simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
            rw [nilAt, Expr.const, Expr.app, dec_node]
            simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
              decTy_encTy θ₀ A hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
            rfl
          · by_cases hkc : j = k.cons
            · subst hkc
              simp only [encStep, List.map_cons, List.map_nil, hkn, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
              rw [cons, Expr.const, Expr.app, dec_node]
              simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                decTy_encTy θ₀ A hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
              rfl
            · by_cases hkl : j = k.lnode
              · subst hkl
                simp only [encStep, List.map_cons, List.map_nil, hkn, hkc, ↓reduceIte,
                  Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                  Option.some.injEq] at henc
                obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
                rw [lnode, Expr.const, Expr.app, dec_node]
                simp only [List.map_cons, List.map_nil, decStep, ih t (by simp) X e Mt hMt,
                  decTy_encTy θ₀ A hA, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
                rfl
              · simp [encStep, hkn, hkc, hkl] at henc
        · simp [encStep] at henc
      · simp [encStep] at henc
    · rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, c, -, C, -, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
        rw [natRec, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
          ih z (by simp) X e Mz hMz, ih s (by simp) _ _ Ms hMs, ih m (by simp) X e Mm hMm]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨z, _ | ⟨s, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.exists] at henc
        obtain ⟨-, c, -, -, t, -, a, -, -, -, -, -, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
        rw [listRec, Expr.const, Expr.app, dec_node]
        simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
          ih z (by simp) X e Mz hMz, ih s (by simp) _ _ Ms hMs, ih m (by simp) X e Mm hMm,
          Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map,
          Option.pure_def]
        rfl
      · simp [encStep] at henc
    · rcases cs with _ | ⟨s, _ | ⟨m, _ | ⟨d, cs⟩⟩⟩
      · simp [encStep] at henc
      · simp [encStep] at henc
      · simp only [encStep, List.map_cons, List.map_nil, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Prod.exists] at henc
        obtain ⟨_, t, _, henc⟩ := henc
        split at henc
        · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
          rw [roseRec, Expr.const, Expr.app, dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
            decTy_encTy c C hC, ih s (by simp) _ _ Ms hMs, ih m (by simp) X e Mm hMm,
            Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some,
            Option.map_eq_map, Option.pure_def]
          rfl
        · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨A, -, C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
          rw [lroseRec, Expr.const, Expr.app, dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node,
            decTy_encTy c C hC, ih s (by simp) _ _ Ms hMs, ih m (by simp) X e Mm hMm,
            Option.map_some, lamBody_lam, Option.bind_eq_bind, Option.bind_some,
            Option.map_eq_map, Option.pure_def]
          rfl
        · simp at henc
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

/-- The declarations whose types end in {lit}`tp` are the object types, of indices 1 to 5, of
index 30, of index 37 and of index 42. -/
theorem sig_head_tp {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 0) :
    c ∈ [1, 2, 3, 4, 5, 30, 37, 42] := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 0) ||
      decide (p.2 ∈ [1, 2, 3, 4, 5, 30, 37, 42])) = true := by decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- The declarations whose types end in {lit}`tm` are the term constructors, of indices from 7
to 16, from 31 to 33, 38 and 39, and 43 and 44. -/
theorem sig_head_tm {c : ℕ} {T : Expr} (hc : sig[c]? = some T) (h : T.headDepth.1 = some 6) :
    c ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 31, 32, 33, 38, 39, 43, 44] := by
  have key : (sig.zipIdx.all fun p ↦ !(p.1.headDepth.1 == some 6) ||
      decide (p.2 ∈ [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 31, 32, 33, 38, 39, 43, 44])) =
        true := by
    decide +kernel
  rw [List.all_eq_true] at key
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hc
  have := key (sig[c], c) (by
    rw [List.mem_iff_getElem]
    exact ⟨c, by simpa using hlt, by simp⟩)
  simp only [h, beq_self_eq_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
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

/-- Every canonical term of {lit}`tp`, in a context whose variables' types do not end in
{lit}`tp`, is the encoding of a type. -/
theorem tyComplete {Γ : Ctx}
    (hΓ : ∀ i t, varType Γ i = some t → t.TypeShape = true ∧ t.headDepth.1 ≠ some 0) :
    ∀ A : Expr, judge sig A Γ (.check tp) = true → ∃ a, encTy a = some A :=
  RoseTree.ind fun l cs ih hj ↦ by
    obtain ⟨h, ms, hA⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hA
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    rcases h with i | c
    · obtain ⟨hCs, hCh⟩ := hΓ i C hC
      exact absurd (by rw [← (spine_headDepth _ C tp hCs hS).1]; rfl) hCh
    · have hCs := Sig.ok_typeShape sig_ok c C hC
      obtain ⟨h₁, h₂⟩ := spine_headDepth _ C tp hCs hS
      have hc := sig_head_tp hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show tp.headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.arrow tp tp))
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha⟩ := ih x (by simp) hS
        exact ⟨FreeTopos.list a, by rw [encTy_list, ha]; rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some tp)
        obtain rfl := List.length_eq_zero_iff.mp (hlen : cs.length = 0)
        exact ⟨FreeTopos.rose, rfl⟩
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some (Expr.arrow tp tp))
        obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨a, ha⟩ := ih x (by simp) hS
        exact ⟨FreeTopos.lrose a, by rw [encTy_lrose, ha]; rfl⟩

/-- The encoding of types is injective. -/
theorem encTy_inj {a b : PartialHorn.Tree} {A : Expr} (ha : encTy a = some A)
    (hb : encTy b = some A) : a = b :=
  Option.some.inj ((decTy_encTy a A ha).symm.trans (decTy_encTy b A hb))

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

/-- The variables of an encoded context are of no type ending in {lit}`tp`. -/
theorem encCtx_heads₀ {Γ : List PartialHorn.Tree} {ΓLF : Ctx} (h : encCtx Γ = some ΓLF) :
    ∀ i t, varType ΓLF i = some t → t.TypeShape = true ∧ t.headDepth.1 ≠ some 0 :=
  fun i t ht ↦ ⟨(encCtx_heads h i t ht).1, by rw [(encCtx_heads h i t ht).2]; decide⟩

/-- The encoded types are types of the internal language, built from operations of
{name}`Geb.FreeTopos.Internal.tyOps`. -/
theorem isTy_of_encTy (G : FreeTopos.Internal.Globals) :
    ∀ (a : PartialHorn.Tree) (A : Expr), encTy a = some A → FreeTopos.Internal.IsTy G 0 a = true :=
  RoseTree.ind fun l cs ih A h ↦ by
    rw [encTy_node] at h
    unfold FreeTopos.Internal.IsTy
    rw [RoseTree.para_node]
    rcases encTyStep_eq_some h with ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, b, hcs, rfl⟩ |
        ⟨rfl, a, b, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩ |
        ⟨rfl, hcs, rfl⟩ | ⟨rfl, a, hcs, rfl⟩
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
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have h₁ := ih c₁ (by simp) a hcs
        unfold FreeTopos.Internal.IsTy at h₁
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.all_cons,
          List.all_nil, h₁, Bool.and_true]
        rfl
      · simp at hcs
    · rw [List.map_eq_nil_iff] at hcs
      subst hcs
      rfl
    · rcases cs with _ | ⟨c₁, _ | ⟨c₂, cs⟩⟩
      · simp at hcs
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcs
        have h₁ := ih c₁ (by simp) a hcs
        unfold FreeTopos.Internal.IsTy at h₁
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil, List.all_cons,
          List.all_nil, h₁, Bool.and_true]
        rfl
      · simp at hcs

/-- The inversion of the judgment of the encoding of a pair of a term and an abstraction: the
term checks against the first factor, the abstraction's body against the product of families of
terms its types name, and the pair's type is the product of the two, the second the exponential
of the abstraction's types. -/
theorem judge_pair_lam_inv {Γ : Ctx}
    (hΓ : ∀ i t, varType Γ i = some t → t.TypeShape = true ∧ t.headDepth.1 ≠ some 0)
    {A B Mz C B' Mf T : Expr} (h : judge sig (pair A B Mz (lam C B' Mf)) Γ (.check (tm T)) = true) :
    judge sig Mz Γ (.check (tm A)) = true ∧
      judge sig Mf Γ (.check (Expr.pi (tm C) (tm B'))) = true ∧ T = prod A B ∧ B = exp C B' := by
  obtain ⟨C₈, hC₈, hS⟩ := judge_app_inv h
  obtain rfl := Option.some.inj (hC₈.symm.trans rfl : some C₈ = some (Expr.pi tp (Expr.pi tp
    (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (prod (v 1) (v 0))))))))
  simp only [List.map_cons, List.map_nil] at hS
  have hT := spine_tp₂ hS
  obtain ⟨a, ha⟩ := tyComplete hΓ A hT.1
  obtain ⟨b, hb⟩ := tyComplete hΓ B hT.2
  have hAc := encTy_closed a A ha
  have hBc := encTy_closed b B hb
  simp only [tm, tp, prod, Expr.const, Expr.app] at hS
  lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
    rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
  obtain ⟨-, -, hz, hl, hT⟩ := hS
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hT
  obtain ⟨C₁₁, hC₁₁, hS'⟩ := judge_app_inv hl
  obtain rfl := Option.some.inj (hC₁₁.symm.trans rfl : some C₁₁ = some (Expr.pi tp (Expr.pi tp
    (Expr.arrow (Expr.arrow (tm (v 1)) (tm (v 0))) (tm (exp (v 1) (v 0)))))))
  simp only [List.map_cons, List.map_nil] at hS'
  have hT' := spine_tp₂ hS'
  obtain ⟨c, hc⟩ := tyComplete hΓ C hT'.1
  obtain ⟨b', hb'⟩ := tyComplete hΓ B' hT'.2
  have hCc := encTy_closed c C hc
  have hB'c := encTy_closed b' B' hb'
  simp only [tm, tp, exp, Expr.const, Expr.app] at hS'
  lf_spine_at hS' [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hCc,
    rename_closed hB'c, hsubWith_closed hCc, hsubWith_closed hB'c]
  obtain ⟨-, -, hf, hB⟩ := hS'
  simp only [node_inj, List.cons.injEq, and_true, true_and] at hB
  exact ⟨hz, hf, hT.symm, hB.symm⟩

/-- The empty list's domain at an element type is the terminal object. -/
theorem subst_nilPrim_dom (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.nilPrim.dom = FreeTopos.one := by
  simp [FreeTopos.Internal.nilPrim, FreeTopos.one, FreeTopos.subst_op]

/-- The empty list's codomain at an element type is the list type. -/
theorem subst_nilPrim_cod (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.nilPrim.cod = FreeTopos.list a := by
  simp [FreeTopos.Internal.nilPrim, FreeTopos.subst_list, FreeTopos.subst_x]

/-- The construction's domain at an element type is the product of the element type and the list
type. -/
theorem subst_consPrim_dom (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.consPrim.dom =
      FreeTopos.prod a (FreeTopos.list a) := by
  simp [FreeTopos.Internal.consPrim, FreeTopos.subst_prod, FreeTopos.subst_list,
    FreeTopos.subst_x]

/-- The construction's codomain at an element type is the list type. -/
theorem subst_consPrim_cod (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.consPrim.cod = FreeTopos.list a := by
  simp [FreeTopos.Internal.consPrim, FreeTopos.subst_list, FreeTopos.subst_x]

/-- The domain of the construction of a rose tree of labels of a type at a type. -/
theorem subst_lnodePrim_dom (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.lnodePrim.dom =
      FreeTopos.prod a (FreeTopos.list (FreeTopos.lrose a)) := by
  simp [FreeTopos.Internal.lnodePrim, FreeTopos.subst_prod, FreeTopos.subst_list,
    FreeTopos.subst_lrose, FreeTopos.subst_x]

/-- The codomain of the construction of a rose tree of labels of a type at a type. -/
theorem subst_lnodePrim_cod (a : PartialHorn.Tree) :
    PartialHorn.subst [a] FreeTopos.Internal.lnodePrim.cod = FreeTopos.lrose a := by
  simp [FreeTopos.Internal.lnodePrim, FreeTopos.subst_lrose, FreeTopos.subst_x]

/-- The rose-tree object of natural-number labels, as the datum of a fold. -/
theorem roseParts_rose :
    FreeTopos.Internal.roseParts FreeTopos.rose = some (FreeTopos.nat, FreeTopos.roseRec) := by
  unfold FreeTopos.Internal.roseParts
  exact ite_eq_left rfl

/-- The two rose-tree objects differ. -/
theorem lrose_ne_rose (a : PartialHorn.Tree) : FreeTopos.lrose a ≠ FreeTopos.rose := fun h ↦ by
  have h' := congrArg RoseTree.label h
  simp only [FreeTopos.lrose, FreeTopos.rose, PartialHorn.op, RoseTree.label_node] at h'
  exact absurd h' (by decide)

/-- The rose-tree object of labels of a type, as the datum of a fold. -/
theorem roseParts_lrose (a : PartialHorn.Tree) :
    FreeTopos.Internal.roseParts (FreeTopos.lrose a) = some (a, FreeTopos.lroseRec a) := by
  unfold FreeTopos.Internal.roseParts
  rw [ite_eq_right (lrose_ne_rose a)]
  exact ite_eq_left rfl

/-- The indices of the empty list and of the construction of valid indices differ. -/
theorem PrimIdx.Valid.cons_ne_nil {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.cons ≠ k.nil := fun h ↦ by
  have hd := congrArg FreeTopos.Internal.Prim.dom
    (Option.some.inj (hk.nil.symm.trans (h ▸ hk.cons)))
  exact absurd (congrArg RoseTree.label hd) (by decide)

/-- The index of the construction of a rose tree of valid indices is neither zero's nor the
successor's. -/
theorem PrimIdx.Valid.node_ne {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.node ≠ k.zero ∧ k.node ≠ k.succ :=
  ⟨fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.dom
      (Option.some.inj (hk.zero.symm.trans (h ▸ hk.node)))
    exact absurd (congrArg RoseTree.label hd) (by decide),
  fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.dom
      (Option.some.inj (hk.succ.symm.trans (h ▸ hk.node)))
    exact absurd (congrArg RoseTree.label hd) (by decide)⟩

/-- The index of the construction of a rose tree of labels of a type of valid indices is neither
the empty list's nor the construction of a list's. -/
theorem PrimIdx.Valid.lnode_ne {k : PrimIdx} {G : FreeTopos.Internal.Globals}
    (hk : k.Valid G) : k.lnode ≠ k.nil ∧ k.lnode ≠ k.cons :=
  ⟨fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.cod
      (Option.some.inj (hk.nil.symm.trans (h ▸ hk.lnode)))
    exact absurd (congrArg RoseTree.label hd) (by decide),
  fun h ↦ by
    have hd := congrArg FreeTopos.Internal.Prim.cod
      (Option.some.inj (hk.cons.symm.trans (h ▸ hk.lnode)))
    exact absurd (congrArg RoseTree.label hd) (by decide)⟩

section Soundness

variable {G : FreeTopos.Internal.Globals} {k : PrimIdx}

/-- Encoding is sound: the encoding of a term of the fragment, in an environment whose types are
encoded, is a canonical LF term of the family of terms of the encoding of its type. -/
theorem enc_checks (hk : k.Valid G) :
    ∀ (s : MTerm) (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (M : Expr)
      (r : PartialHorn.Tree × PartialHorn.Tree),
      encCtx (e.map Prod.snd) = some ΓLF → enc G k s X e = some M →
      FreeTopos.Internal.compile G 0 s X e = some r →
      ∃ A, encTy r.2 = some A ∧ judge sig M ΓLF (.check (tm A)) = true :=
  RoseTree.ind fun l cs ih X e ΓLF M r hΓ henc hcomp ↦ by
    rw [enc_node] at henc
    rcases l with i | _ | _ | _ | _ | a | _ | ⟨j, θ⟩ | _ | _ | c | ⟨j, θ⟩ | _
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
      rcases θ with _ | ⟨θ₀, _ | ⟨θ₁, θ⟩⟩
      · by_cases hkz : j = k.zero
        · subst hkz
          rw [hk.zero, Option.some.injEq] at hp
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
        · by_cases hks : j = k.succ
          · subst hks
            rw [hk.succ, Option.some.injEq] at hp
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
          · by_cases hkd : j = k.node
            · subst hkd
              rw [hk.node, Option.some.injEq] at hp
              subst hp
              simp only [encStep, List.map_cons, List.map_nil, hkz, hks, ↓reduceIte,
                Option.map_eq_map, Option.map_eq_some_iff] at henc
              obtain ⟨Mt, hMt, rfl⟩ := henc
              obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
              simp only [FreeTopos.Internal.nodePrim, PartialHorn.subst_nil] at hP ⊢
              rw [show encTy (FreeTopos.prod FreeTopos.nat (FreeTopos.list FreeTopos.rose)) =
                some (prod nat (list rose)) from rfl, Option.some.injEq] at hP
              subst hP
              refine ⟨rose, rfl, judge_const (T := Expr.arrow (tm (prod nat (list rose)))
                (tm rose)) rfl ?_ rfl⟩
              simp only [tm, nat, rose, prod, list, Expr.const, Expr.app] at hMtJ ⊢
              lf_spine [hMtJ]
            · simp [encStep, hkz, hks, hkd] at henc
      · by_cases hkn : j = k.nil
        · subst hkn
          rw [hk.nil, Option.some.injEq] at hp
          subst hp
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, Option.bind_eq_bind,
            Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
          obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
          obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
          rw [subst_nilPrim_dom, show encTy FreeTopos.one = some one from rfl,
            Option.some.injEq] at hP
          subst hP
          refine ⟨list A, by rw [subst_nilPrim_cod, encTy_list, hA]; rfl,
            judge_const (T := Expr.pi tp (Expr.arrow (tm one) (tm (list (v 0))))) rfl ?_ rfl⟩
          have hAt := encTy_checks θ₀ A hA ΓLF
          have hAc := encTy_closed θ₀ A hA
          simp only [tm, tp, one, list, Expr.const, Expr.app] at hAt hMtJ ⊢
          lf_spine [hAt, hMtJ, rename_closed hAc, hsubWith_closed hAc]
        · by_cases hkc : j = k.cons
          · subst hkc
            rw [hk.cons, Option.some.injEq] at hp
            subst hp
            simp only [encStep, List.map_cons, List.map_nil, hkn, ↓reduceIte, Option.bind_eq_bind,
              Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
            obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
            obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
            rw [subst_consPrim_dom, encTy_prod, encTy_list, hA] at hP
            simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
            subst hP
            refine ⟨list A, by rw [subst_consPrim_cod, encTy_list, hA]; rfl,
              judge_const (T := Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (v 0))))
                (tm (list (v 0))))) rfl ?_ rfl⟩
            have hAt := encTy_checks θ₀ A hA ΓLF
            have hAc := encTy_closed θ₀ A hA
            simp only [tm, tp, prod, list, Expr.const, Expr.app] at hAt hMtJ ⊢
            lf_spine [hAt, hMtJ, rename_closed hAc, hsubWith_closed hAc]
          · by_cases hkl : j = k.lnode
            · subst hkl
              rw [hk.lnode, Option.some.injEq] at hp
              subst hp
              simp only [encStep, List.map_cons, List.map_nil, hkn, hkc, ↓reduceIte,
                Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
                Option.some.injEq] at henc
              obtain ⟨A, hA, Mt, hMt, rfl⟩ := henc
              obtain ⟨P, hP, hMtJ⟩ := ih t (by simp) X e ΓLF Mt _ hΓ hMt hct
              rw [subst_lnodePrim_dom, encTy_prod, encTy_list, encTy_lrose, hA] at hP
              simp only [Option.map_some, Option.bind_some, Option.some.injEq] at hP
              subst hP
              refine ⟨lrose A, by rw [subst_lnodePrim_cod, encTy_lrose, hA]; rfl,
                judge_const (T := Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (lrose (v 0)))))
                  (tm (lrose (v 0))))) rfl ?_ rfl⟩
              have hAt := encTy_checks θ₀ A hA ΓLF
              have hAc := encTy_closed θ₀ A hA
              simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hAt hMtJ ⊢
              lf_spine [hAt, hMtJ, rename_closed hAc, hsubWith_closed hAc]
            · simp [encStep, hkn, hkc, hkl] at henc
      · simp [encStep] at henc
    · obtain ⟨z, s, m, rfl, -⟩ := FreeTopos.Internal.compile_natRec_iff.mp hcomp
      obtain ⟨⟨zf, hcz⟩, ⟨sf, hcs⟩, mf, hcm⟩ := FreeTopos.Internal.compile_natRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, Option.bind_eq_bind,
        Option.bind_some, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      have hΓ' : encCtx ((FreeTopos.Internal.extEnv X r.2 e).map Prod.snd) =
          some (tm C :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons hC (by simpa [Function.comp_def] using hΓ)
      obtain ⟨A₁, hA₁, hMzJ⟩ := ih z (by simp) X e ΓLF Mz _ hΓ hMz hcz
      obtain ⟨A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ hΓ' hMs hcs
      obtain ⟨N, hN, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ hΓ hMm hcm
      simp only [hC, Option.some.injEq] at hA₁ hA₂
      subst hA₁ hA₂
      rw [show encTy FreeTopos.nat = some nat from rfl, Option.some.injEq] at hN
      subst hN
      have hfJ : judge sig (Expr.lam Ms) ΓLF (.check (Expr.pi (tm C) (tm C))) = true :=
        judge_lam hMsJ
      refine ⟨C, hC, judge_const (T := Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 0)) (tm (v 0))) (Expr.arrow (tm nat) (tm (v 0))))))
        rfl ?_ rfl⟩
      have hCt := encTy_checks r.2 C hC ΓLF
      have hCc := encTy_closed r.2 C hC
      simp only [tm, tp, nat, Expr.const, Expr.app, Expr.pi] at hCt hMzJ hfJ hMmJ ⊢
      lf_spine [hCt, hMzJ, hfJ, hMmJ, rename_closed hCc, hsubWith_closed hCc]
    · obtain ⟨z, s, m, rfl, -⟩ := FreeTopos.Internal.compile_listRec_iff.mp hcomp
      obtain ⟨mf, a, hcm, ⟨zf, hcz⟩, sf, hcs⟩ := FreeTopos.Internal.compile_listRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcz, hcm,
        FreeTopos.Internal.listPart_eq_some.mpr rfl, Option.bind_eq_bind, Option.bind_some,
        Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
      obtain ⟨A, hA, C, hC, Mz, hMz, Ms, hMs, Mm, hMm, rfl⟩ := henc
      have hΓ' : encCtx ((FreeTopos.Internal.extEnv (FreeTopos.prod X a) r.2
          (FreeTopos.Internal.extEnv X a e)).map Prod.snd) = some (tm C :: tm A :: ΓLF) := by
        simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
        exact encCtx_cons hC (encCtx_cons hA (by simpa [Function.comp_def] using hΓ))
      obtain ⟨A₁, hA₁, hMzJ⟩ := ih z (by simp) X e ΓLF Mz _ hΓ hMz hcz
      obtain ⟨A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ hΓ' hMs hcs
      obtain ⟨L, hL, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ hΓ hMm hcm
      simp only [hC, Option.some.injEq] at hA₁ hA₂
      subst hA₁ hA₂
      rw [encTy_list, hA, Option.map_some, Option.some.injEq] at hL
      subst hL
      have hfJ : judge sig (Expr.lam (Expr.lam Ms)) ΓLF
          (.check (Expr.pi (tm A) (Expr.pi (tm C) (tm C)))) = true :=
        judge_lam (judge_lam hMsJ)
      refine ⟨C, hC, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
        (Expr.arrow (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (v 0))))
          (Expr.arrow (tm (list (v 1))) (tm (v 0))))))) rfl ?_ rfl⟩
      have hAt := encTy_checks a A hA ΓLF
      have hCt := encTy_checks r.2 C hC ΓLF
      have hAc := encTy_closed a A hA
      have hCc := encTy_closed r.2 C hC
      simp only [tm, tp, list, Expr.const, Expr.app, Expr.pi] at hAt hCt hMzJ hfJ hMmJ ⊢
      lf_spine [hAt, hCt, hMzJ, hfJ, hMmJ, rename_closed hAc, rename_closed hCc,
        hsubWith_closed hAc, hsubWith_closed hCc]
    · obtain ⟨s, m, -, -, -, -, -, rfl, -⟩ := FreeTopos.Internal.compile_roseRec_iff.mp hcomp
      obtain ⟨hct, hrc, mf, t, a, F, hcm, ht, sf, hcs⟩ :=
        FreeTopos.Internal.compile_roseRec_parts hcomp
      simp only [encStep, List.map_cons, List.map_nil, hcm, Option.bind_eq_bind,
        Option.bind_some] at henc
      split at henc
      · next htl htc =>
        obtain rfl : t = FreeTopos.rose := by
          rw [← RoseTree.node_label_children t, htl, htc]
          rfl
        obtain ⟨rfl, rfl⟩ : a = FreeTopos.nat ∧ F = FreeTopos.roseRec := by
          simpa [FreeTopos.Internal.roseParts] using ht.symm
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
        obtain ⟨C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hpc : encTy (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) =
            some (prod nat (list C)) := by rw [encTy_prod, encTy_list, hC]; rfl
        have hΓ' : encCtx ((FreeTopos.Internal.extEnv X (FreeTopos.prod FreeTopos.nat
            (FreeTopos.list c)) e).map Prod.snd) = some (tm (prod nat (list C)) :: ΓLF) := by
          simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
          exact encCtx_cons hpc (by simpa [Function.comp_def] using hΓ)
        obtain ⟨A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ hΓ' hMs hcs
        obtain ⟨T, hT, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ hΓ hMm hcm
        simp only [hC, Option.some.injEq] at hA₂
        subst hA₂
        rw [show encTy FreeTopos.rose = some rose from rfl, Option.some.injEq] at hT
        subst hT
        have hfJ : judge sig (Expr.lam Ms) ΓLF
            (.check (Expr.pi (tm (prod nat (list C))) (tm C))) = true :=
          judge_lam hMsJ
        refine ⟨C, by rw [hrc]; exact hC, judge_const (T := Expr.pi tp (Expr.arrow
          (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0))) (Expr.arrow (tm rose) (tm (v 0)))))
          rfl ?_ rfl⟩
        have hCt := encTy_checks c C hC ΓLF
        have hCc := encTy_closed c C hC
        simp only [tm, tp, nat, rose, prod, list, Expr.const, Expr.app, Expr.pi] at hCt hfJ hMmJ ⊢
        lf_spine [hCt, hfJ, hMmJ, rename_closed hCc, hsubWith_closed hCc]
      · next a' htl htc =>
        obtain rfl : t = FreeTopos.lrose a' := by
          rw [← RoseTree.node_label_children t, htl, htc]
          rfl
        rw [roseParts_lrose, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at henc
        obtain ⟨A, hA, C, hC, Ms, hMs, Mm, hMm, rfl⟩ := henc
        have hpc : encTy (FreeTopos.prod a' (FreeTopos.list c)) = some (prod A (list C)) := by
          rw [encTy_prod, encTy_list, hA, hC]; rfl
        have hΓ' : encCtx ((FreeTopos.Internal.extEnv X (FreeTopos.prod a'
            (FreeTopos.list c)) e).map Prod.snd) = some (tm (prod A (list C)) :: ΓLF) := by
          simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]
          exact encCtx_cons hpc (by simpa [Function.comp_def] using hΓ)
        obtain ⟨A₂, hA₂, hMsJ⟩ := ih s (by simp) _ _ _ Ms _ hΓ' hMs hcs
        obtain ⟨T, hT, hMmJ⟩ := ih m (by simp) X e ΓLF Mm _ hΓ hMm hcm
        simp only [hC, Option.some.injEq] at hA₂
        subst hA₂
        rw [encTy_lrose, hA, Option.map_some, Option.some.injEq] at hT
        subst hT
        have hfJ : judge sig (Expr.lam Ms) ΓLF
            (.check (Expr.pi (tm (prod A (list C))) (tm C))) = true :=
          judge_lam hMsJ
        refine ⟨C, by rw [hrc]; exact hC, judge_const (T := Expr.pi tp (Expr.pi tp (Expr.arrow
          (Expr.arrow (tm (prod (v 1) (list (v 0)))) (tm (v 0)))
          (Expr.arrow (tm (lrose (v 1))) (tm (v 0)))))) rfl ?_ rfl⟩
        have hAt := encTy_checks a' A hA ΓLF
        have hCt := encTy_checks c C hC ΓLF
        have hAc := encTy_closed a' A hA
        have hCc := encTy_closed c C hC
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app, Expr.pi] at hAt hCt hfJ hMmJ ⊢
        lf_spine [hAt, hCt, hfJ, hMmJ, rename_closed hAc, hsubWith_closed hAc, rename_closed hCc,
          hsubWith_closed hCc]
      · simp at henc
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

section Completeness

variable {G : FreeTopos.Internal.Globals} {k : PrimIdx}

/-- The conclusion of the completeness of the encoding at a term, an environment and a type: the
term decodes to a term of the internal language that compiles in the environment to a type that
the type encodes, and whose encoding it is. -/
def TmConcl (G : FreeTopos.Internal.Globals) (k : PrimIdx) (M : Expr) (X : PartialHorn.Tree)
    (e : MEnv) (A : Expr) : Prop :=
  ∃ s r, dec k M = some s ∧ FreeTopos.Internal.compile G 0 s X e = some r ∧
    encTy r.2 = some A ∧ enc G k s X e = some M

/-- The completeness of the encoding at a term, of the family of terms of a type, and, where the
term checks against a product of families of terms, or against a product of families of terms
into such a product, at the body of the abstraction it is, or of the abstraction that is its body,
in every environment of the extended types. -/
def TmComplete (G : FreeTopos.Internal.Globals) (k : PrimIdx) (M : Expr) : Prop :=
  (∀ (X : PartialHorn.Tree) (e : MEnv) (ΓLF : Ctx) (A : Expr),
    encCtx (e.map Prod.snd) = some ΓLF →
    judge sig M ΓLF (.check (tm A)) = true → TmConcl G k M X e A) ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a : PartialHorn.Tree) (A' B' : Expr),
    encCtx Γ = some ΓLF → encTy a = some A' →
    judge sig M ΓLF (.check (Expr.pi (tm A') (tm B'))) = true →
    ∃ body, M = Expr.lam body ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = a :: Γ → TmConcl G k body X e B') ∧
  (∀ (Γ : List PartialHorn.Tree) (ΓLF : Ctx) (a b : PartialHorn.Tree) (A' B' C' : Expr),
    encCtx Γ = some ΓLF → encTy a = some A' → encTy b = some B' →
    judge sig M ΓLF (.check (Expr.pi (tm A') (Expr.pi (tm B') (tm C')))) = true →
    ∃ body, M = Expr.lam (Expr.lam body) ∧
      ∀ (X : PartialHorn.Tree) (e : MEnv), e.map Prod.snd = b :: a :: Γ →
        TmConcl G k body X e C')

/-- Encoding is onto the canonical LF terms: every canonical term of the family of terms of a type,
in an encoded context, decodes to a term of the internal language that compiles, in an
environment of the context's types, to a type the type encodes, and whose encoding it is. -/
theorem tmComplete (hk : k.Valid G) :
    ∀ M : Expr, TmComplete G k M :=
  RoseTree.ind fun l cs ih ↦ by
    refine ⟨fun X e ΓLF A hΓ hj ↦ ?_, fun Γ ΓLF a A' B' hΓ ha hj ↦ ?_,
      fun Γ ΓLF a b A' B' C' hΓ ha hb hj ↦ ?_⟩
    rotate_left
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      refine ⟨body, rfl, fun X e he ↦ ?_⟩
      exact (ih body (by simp)).1 X e (tm A' :: ΓLF) B' (by rw [he]; exact encCtx_cons ha hΓ)
        hbJ
    · obtain ⟨body, hbody, hbJ⟩ := judge_check_pi_inv hj
      obtain ⟨rfl, rfl⟩ := node_inj.mp hbody
      obtain ⟨body', rfl, hb'⟩ :=
        (ih body (by simp)).2.1 (a :: Γ) (tm A' :: ΓLF) b B' C' (encCtx_cons ha hΓ) hb hbJ
      exact ⟨body', rfl, hb'⟩
    unfold TmConcl
    obtain ⟨h, ms, hM⟩ := judge_atomic_app rfl hj
    obtain ⟨rfl, rfl⟩ := node_inj.mp hM
    obtain ⟨C, hC, hS⟩ := judge_app_inv hj
    have hheads := encCtx_heads hΓ
    have hheads₀ := encCtx_heads₀ hΓ
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
      have hc := sig_head_tm hC (by rw [← h₁]; rfl)
      have hlen : cs.length = C.headDepth.2 := by
        rw [show (tm A).headDepth.2 = 0 from rfl, List.length_map] at h₂
        omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
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
        obtain ⟨a, ha⟩ := tyComplete hheads₀ A' hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads₀ B' hT.2
        have hAc := encTy_closed a A' ha
        have hBc := encTy_closed b B' hb
        simp only [tm, tp, prod, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a'⟩, hdt, hct, hrt, het⟩ :=
          (ih t (by simp)).1 X e ΓLF A' hΓ ht
        obtain ⟨su, ⟨g, b'⟩, hdu, hcu, hru, heu⟩ :=
          (ih u (by simp)).1 X e ΓLF B' hΓ hu
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
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads₀ X2 hT.2
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
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ hp
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
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads₀ X2 hT.2
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
          (ih X3 (by simp)).1 X e ΓLF (prod X1 X2) hΓ hp
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
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads₀ X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hBc := encTy_closed b X2 hb
        simp only [tm, tp, exp, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hBc, hsubWith_closed hAc, hsubWith_closed hBc]
        obtain ⟨-, -, hf, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨body, rfl, hbody⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF a X1 X2 hΓ ha
          hf
        obtain ⟨sb, ⟨fb, b'⟩, hdb, hcb, hrb, heb⟩ :=
          hbody (FreeTopos.prod X a) (FreeTopos.Internal.extEnv X a e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        obtain rfl := encTy_inj hrb hb
        refine ⟨FreeTopos.Internal.Term.lam a sb, _, ?_,
          FreeTopos.Internal.compile_lam_iff.mpr ⟨sb, fb, b', rfl, isTy_of_encTy G a X1 ha, hcb,
            rfl⟩, by rw [encTy_exp, ha, hrb]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam,
            dec_node, hdb, decTy_encTy a X1 ha]
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
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 hT.1
        obtain ⟨b, hb⟩ := tyComplete hheads₀ X2 hT.2
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
          (ih X3 (by simp)).1 X e ΓLF (exp X1 X2) hΓ ht
        obtain ⟨su, ⟨g, a'⟩, hdu, hcu, hru, heu⟩ :=
          (ih X4 (by simp)).1 X e ΓLF X1 hΓ hu
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
          (ih X1 (by simp)).1 X e ΓLF one hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr k.zero [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.zero, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
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
          (ih X1 (by simp)).1 X e ΓLF nat hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy FreeTopos.nat = some nat)
        have hne : k.succ ≠ k.zero := fun h ↦ by
          have hd := congrArg FreeTopos.Internal.Prim.dom
            (Option.some.inj (hk.zero.symm.trans (h ▸ hk.succ)))
          exact absurd (congrArg RoseTree.label hd) (by decide)
        refine ⟨FreeTopos.Internal.Term.arr k.succ [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.succ, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
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
        obtain ⟨c, hc⟩ := tyComplete hheads₀ X1 (spine_tp₁ hS)
        have hCc := encTy_closed c X1 hc
        simp only [tm, tp, nat, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hCc,
          hsubWith_closed hCc]
        obtain ⟨-, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ := (ih X2 (by simp)).1 X e ΓLF X1 hΓ hzJ
        obtain ⟨body, rfl, hbc⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF c X1 X1 hΓ hc hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X c) (FreeTopos.Internal.extEnv X c e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X4 (by simp)).1 X e ΓLF nat hΓ hm
        obtain rfl := encTy_inj hc hrz
        obtain rfl := encTy_inj hc hrs
        obtain rfl := encTy_inj hrm (rfl : encTy FreeTopos.nat = some nat)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_natRec_of_parts hcz hcs hcm
        refine ⟨FreeTopos.Internal.Term.natRec sz ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.natRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (v 0)) (Expr.arrow (tm (v 0)) (tm omega)))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 (spine_tp₁ hS)
        have hAc := encTy_closed a X1 ha
        simp only [tm, tp, omega, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          hsubWith_closed hAc]
        obtain ⟨-, ht, hu, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨f, a₁⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF X1 hΓ ht
        obtain ⟨su, ⟨g, a₂⟩, hdu, hcu, hru, heu⟩ :=
          (ih X3 (by simp)).1 X e ΓLF X1 hΓ hu
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
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm one) (tm (list (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 (spine_tp₁ hS)
        have hAc := encTy_closed a X1 ha
        simp only [tm, tp, one, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          hsubWith_closed hAc]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ := (ih X2 (by simp)).1 X e ΓLF one hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy FreeTopos.one = some one)
        refine ⟨FreeTopos.Internal.Term.arr k.nil [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.nil, g,
            by rw [subst_nilPrim_dom]; exact hct, rfl,
            by simp [isTy_of_encTy G a X1 ha], rfl⟩,
          by rw [subst_nilPrim_cod, encTy_list, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, ↓reduceIte, ha, het,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (v 0)))) (tm (list (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 (spine_tp₁ hS)
        have hAc := encTy_closed a X1 ha
        simp only [tm, tp, prod, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          hsubWith_closed hAc]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpl : encTy (FreeTopos.prod a (FreeTopos.list a)) = some (prod X1 (list X1)) := by
          rw [encTy_prod, encTy_list, ha]; rfl
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF (prod X1 (list X1)) hΓ ht
        obtain rfl := encTy_inj hrt hpl
        refine ⟨FreeTopos.Internal.Term.arr k.cons [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.cons, g,
            by rw [subst_consPrim_dom]; exact hct, rfl,
            by simp [isTy_of_encTy G a X1 ha], rfl⟩,
          by rw [subst_consPrim_cod, encTy_list, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hk.cons_ne_nil, ↓reduceIte, ha, het,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (tm (v 0))
            (Expr.arrow (Expr.arrow (tm (v 1)) (Expr.arrow (tm (v 0)) (tm (v 0))))
              (Expr.arrow (tm (list (v 1))) (tm (v 0))))))))
        obtain ⟨X1, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (hlen : cs.length = 4 + 1)
        obtain ⟨X2, cs, rfl⟩ :=
          List.exists_cons_of_length_eq_add_one (Nat.succ.inj (hlen : cs.length + 1 = 4 + 1))
        obtain ⟨X3, X4, X5, rfl⟩ := List.length_eq_three.mp
          (Nat.succ.inj (Nat.succ.inj (hlen : cs.length + 1 + 1 = 4 + 1)))
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 hT.1
        obtain ⟨c, hc⟩ := tyComplete hheads₀ X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hCc := encTy_closed c X2 hc
        simp only [tm, tp, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          rename_closed hCc, hsubWith_closed hAc, hsubWith_closed hCc]
        obtain ⟨-, -, hzJ, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨sz, ⟨fz, cz⟩, hdz, hcz, hrz, hez⟩ := (ih X3 (by simp)).1 X e ΓLF X2 hΓ hzJ
        obtain ⟨body, rfl, hbc⟩ :=
          (ih X4 (by simp)).2.2 (e.map Prod.snd) ΓLF a c X1 X2 X2 hΓ ha hc hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod (FreeTopos.prod X a) c)
            (FreeTopos.Internal.extEnv (FreeTopos.prod X a) c (FreeTopos.Internal.extEnv X a e))
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        have hla : encTy (FreeTopos.list a) = some (list X1) := by rw [encTy_list, ha]; rfl
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X5 (by simp)).1 X e ΓLF (list X1) hΓ hm
        obtain rfl := encTy_inj hc hrz
        obtain rfl := encTy_inj hc hrs
        obtain rfl := encTy_inj hrm hla
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_listRec_of_parts hcm hcz hcs
        refine ⟨FreeTopos.Internal.Term.listRec sz ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hdz, hds, hdm]
          rfl
        · rw [FreeTopos.Internal.Term.listRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcz, hcm,
            FreeTopos.Internal.listPart_eq_some.mpr rfl, ha, hc, hez, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.arrow (tm (prod nat (list rose))) (tm rose)))
        obtain ⟨X1, rfl⟩ := List.length_eq_one_iff.mp (hlen : cs.length = 1)
        simp only [List.map_cons, List.map_nil, tm, nat, rose, prod, list, Expr.const,
          Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some]
        obtain ⟨ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X1 (by simp)).1 X e ΓLF (prod nat (list rose)) hΓ ht
        obtain rfl := encTy_inj hrt (rfl : encTy (FreeTopos.prod FreeTopos.nat
          (FreeTopos.list FreeTopos.rose)) = some (prod nat (list rose)))
        refine ⟨FreeTopos.Internal.Term.arr k.node [] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.node, g, hct, rfl, rfl, rfl⟩,
          rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt]
          rfl
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hk.node_ne.1, hk.node_ne.2, ↓reduceIte,
            het]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (Expr.arrow (tm (prod nat (list (v 0)))) (tm (v 0)))
            (Expr.arrow (tm rose) (tm (v 0))))))
        obtain ⟨X1, X2, X3, rfl⟩ := List.length_eq_three.mp (hlen : cs.length = 3)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨c, hc⟩ := tyComplete hheads₀ X1 (spine_tp₁ hS)
        have hCc := encTy_closed c X1 hc
        simp only [tm, tp, nat, rose, prod, list, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hCc,
          hsubWith_closed hCc]
        obtain ⟨-, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpc : encTy (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) =
            some (prod nat (list X1)) := by rw [encTy_prod, encTy_list, hc]; rfl
        obtain ⟨body, rfl, hbc⟩ := (ih X2 (by simp)).2.1 (e.map Prod.snd) ΓLF _ _ X1 hΓ hpc hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)))
            (FreeTopos.Internal.extEnv X (FreeTopos.prod FreeTopos.nat (FreeTopos.list c)) e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ := (ih X3 (by simp)).1 X e ΓLF rose hΓ hm
        obtain rfl := encTy_inj hc hrs
        obtain rfl := encTy_inj hrm (rfl : encTy FreeTopos.rose = some rose)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_roseRec_of_parts
          (isTy_of_encTy G c X1 hc) hcm (show FreeTopos.Internal.roseParts FreeTopos.rose =
            some (FreeTopos.nat, FreeTopos.roseRec) by simp [FreeTopos.Internal.roseParts]) hcs
        refine ⟨FreeTopos.Internal.Term.roseRec c ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hds, hdm,
            decTy_encTy c X1 hc]
          rfl
        · rw [FreeTopos.Internal.Term.roseRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcm, hc, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.arrow (tm (prod (v 0) (list (lrose (v 0))))) (tm (lrose (v 0))))))
        obtain ⟨X1, X2, rfl⟩ := List.length_eq_two.mp (hlen : cs.length = 2)
        simp only [List.map_cons, List.map_nil] at hS
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 (spine_tp₁ hS)
        have hAc := encTy_closed a X1 ha
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          hsubWith_closed hAc]
        obtain ⟨-, ht, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpl : encTy (FreeTopos.prod a (FreeTopos.list (FreeTopos.lrose a))) =
            some (prod X1 (list (lrose X1))) := by
          rw [encTy_prod, encTy_list, encTy_lrose, ha]; rfl
        obtain ⟨st, ⟨g, c'⟩, hdt, hct, hrt, het⟩ :=
          (ih X2 (by simp)).1 X e ΓLF (prod X1 (list (lrose X1))) hΓ ht
        obtain rfl := encTy_inj hrt hpl
        refine ⟨FreeTopos.Internal.Term.arr k.lnode [a] st, _, ?_,
          FreeTopos.Internal.compile_arr_iff.mpr ⟨st, rfl, _, hk.lnode, g,
            by rw [subst_lnodePrim_dom]; exact hct, rfl,
            by simp [isTy_of_encTy G a X1 ha], rfl⟩,
          by rw [subst_lnodePrim_cod, encTy_lrose, ha]; rfl, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, hdt, decTy_encTy a X1 ha,
            Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        · rw [FreeTopos.Internal.Term.arr, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hk.lnode_ne.1, hk.lnode_ne.2,
            ↓reduceIte, ha, het, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
          rfl
      · obtain rfl := Option.some.inj (hC.symm.trans rfl : some C = some
          (Expr.pi tp (Expr.pi tp (Expr.arrow (Expr.arrow (tm (prod (v 1) (list (v 0))))
            (tm (v 0))) (Expr.arrow (tm (lrose (v 1))) (tm (v 0)))))))
        obtain ⟨X1, X2, X3, X4, rfl⟩ := List.length_eq_four.mp (hlen : cs.length = 4)
        simp only [List.map_cons, List.map_nil] at hS
        have hT := spine_tp₂ hS
        obtain ⟨a, ha⟩ := tyComplete hheads₀ X1 hT.1
        obtain ⟨c, hc⟩ := tyComplete hheads₀ X2 hT.2
        have hAc := encTy_closed a X1 ha
        have hCc := encTy_closed c X2 hc
        simp only [tm, tp, prod, list, lrose, Expr.const, Expr.app] at hS
        lf_spine_at hS [Option.bind_eq_some_iff, Option.ite_none_right_eq_some, rename_closed hAc,
          hsubWith_closed hAc, rename_closed hCc, hsubWith_closed hCc]
        obtain ⟨-, -, hfJ, hm, hA⟩ := hS
        simp only [node_inj, List.cons.injEq, and_true, true_and] at hA
        subst hA
        have hpc : encTy (FreeTopos.prod a (FreeTopos.list c)) = some (prod X1 (list X2)) := by
          rw [encTy_prod, encTy_list, ha, hc]; rfl
        obtain ⟨body, rfl, hbc⟩ := (ih X3 (by simp)).2.1 (e.map Prod.snd) ΓLF _ _ X2 hΓ hpc hfJ
        obtain ⟨ss, ⟨fs, cs'⟩, hds, hcs, hrs, hes⟩ :=
          hbc (FreeTopos.prod X (FreeTopos.prod a (FreeTopos.list c)))
            (FreeTopos.Internal.extEnv X (FreeTopos.prod a (FreeTopos.list c)) e)
            (by simp only [FreeTopos.Internal.extEnv, List.map_cons, List.map_map]; rfl)
        obtain ⟨sm, ⟨fm, cm⟩, hdm, hcm, hrm, hem⟩ :=
          (ih X4 (by simp)).1 X e ΓLF (lrose X1) hΓ hm
        obtain rfl := encTy_inj hc hrs
        obtain rfl := encTy_inj hrm (show encTy (FreeTopos.lrose a) = some (lrose X1) by
          rw [encTy_lrose, ha]; rfl)
        obtain ⟨r, hr, hrc⟩ := FreeTopos.Internal.compile_roseRec_of_parts
          (isTy_of_encTy G c X2 hc) hcm (roseParts_lrose a) hcs
        refine ⟨FreeTopos.Internal.Term.roseRec c ss sm, r, ?_, hr, by rw [hrc]; exact hc, ?_⟩
        · rw [dec_node]
          simp only [List.map_cons, List.map_nil, decStep, Expr.lam, dec_node, hds, hdm,
            decTy_encTy c X2 hc]
          rfl
        · rw [FreeTopos.Internal.Term.roseRec, enc_node]
          simp only [encStep, List.map_cons, List.map_nil, hcm, FreeTopos.lrose, PartialHorn.op,
            RoseTree.label_node, RoseTree.children_node, Nat.reduceAdd, ha, hc, hes, hem,
            Option.bind_eq_bind, Option.bind_some]
          rfl

end Completeness

end Geb.LF.Topos

end
