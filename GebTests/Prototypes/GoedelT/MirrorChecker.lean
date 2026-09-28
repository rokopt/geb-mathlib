/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.GoedelT.MirrorRules

set_option doc.verso true in
/-!
# The checker of Gödel's T written in Geb decides as the kernel's

The rules of {lit}`GebTests.Prototypes.GoedelT.MirrorRules` are assembled, arity by arity, into
the agreement of the mirror's dispatch with {name}`Geb.GoedelT.checkCore` and
{name}`Geb.GoedelT.checkMore` at every node: at a label and number of children no rule has,
both give nothing. The mirror's checker is a fold over the certificate; its step at a node, from
children whose checkers agree, gives a checker that agrees, so by induction on the certificate
the mirror's checker gives the encoding of {name}`Geb.GoedelT.check`'s conclusion at every
certificate, program, theorems, global environment, context and hypotheses.

## Main statements

* {lit}`checkCore_eq`, {lit}`checkMore_eq` — the mirror's rules agree with the kernel's at every
  node whose children agree.
* {lit}`checkCert_eq` — the mirror's checker gives the encoding of the kernel's conclusion.

## Tags

certificate, checker, agreement, mirror
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.GoedelT.MirrorChecker

open Geb Geb.Kernel Geb.GoedelT GebTests.Prototypes.GoedelT.MirrorTyping
  GebTests.Prototypes.GoedelT.MirrorEquations GebTests.Prototypes.GoedelT.MirrorRules
open scoped FinEnum

/-- The mirror's rules and the kernel's give nothing at a node of a label and a number of
children that no rule has. -/
macro (name := ruleNone) "rule_none" : tactic => `(tactic| (rule_dispatch <;> rfl))

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node without children. -/
theorem core_nil (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) []
      ([].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  match l, hl with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ | 16, _ | 17, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _
  | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of one child. -/
theorem core_one (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (ha : Agrees E G (p a) (P a)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) [a]
      ([a].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([a].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl with
  | 0, _ => exact core_hyp E G a (p a) (P a) Γ H
  | 1, _ => exact core_refl E G a (p a) (P a) Γ H
  | 2, _ => exact core_symm E G a (p a) (P a) ha Γ H
  | 7, _ => exact core_congFst E G a (p a) (P a) ha Γ H
  | 8, _ => exact core_congSnd E G a (p a) (P a) ha Γ H
  | 12, _ => exact core_eta E G a (p a) (P a) Γ H
  | 15, _ => exact core_etaPair E G a (p a) (P a) Γ H
  | 16, _ => exact core_etaUnit E G a (p a) (P a) Γ H
  | 17, _ => exact core_delta E G a [] (p a) [] (P a) [] rfl Γ H
  | 18, _ => exact core_weaken E G a (p a) (P a) ha Γ H
  | 3, _ | 4, _ | 5, _ | 6, _ | 9, _ | 10, _ | 11, _ | 13, _ | 14, _ | 19, _ | 20, _ | 21, _
  | 22, _ | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of two children. -/
theorem core_two (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a b : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (ha : Agrees E G (p a) (P a)) (hb : Agrees E G (p b) (P b)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) [a, b]
      ([a, b].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([a, b].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl with
  | 3, _ => exact core_trans E G a b (p a) (p b) (P a) (P b) ha hb Γ H
  | 4, _ => exact core_congApp E G a b (p a) (p b) (P a) (P b) ha hb Γ H
  | 5, _ => exact core_congLam E G a b (p a) (p b) (P a) (P b) hb Γ H
  | 6, _ => exact core_congPair E G a b (p a) (p b) (P a) (P b) ha hb Γ H
  | 9, _ => exact core_congCons E G a b (p a) (p b) (P a) (P b) ha hb Γ H
  | 13, _ => exact core_betaFst E G a b (p a) (p b) (P a) (P b) Γ H
  | 14, _ => exact core_betaSnd E G a b (p a) (p b) (P a) (P b) Γ H
  | 17, _ => exact core_delta E G a [b] (p a) [(b, p b)] (P a) [(b, P b)] rfl Γ H
  | 19, _ => exact core_cut E G a b (p a) (p b) (P a) (P b) ha hb Γ H
  | 20, _ => exact core_instVar E G a b (p a) (p b) (P a) (P b) hb Γ H
  | 0, _ | 1, _ | 2, _ | 7, _ | 8, _ | 10, _ | 11, _ | 12, _ | 15, _ | 16, _ | 18, _ | 21, _
  | 22, _ | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of three children. -/
theorem core_three (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a b c : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (ha : Agrees E G (p a) (P a)) (hb : Agrees E G (p b) (P b)) (hc : Agrees E G (p c) (P c))
    (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) [a, b, c]
      ([a, b, c].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([a, b, c].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl with
  | 10, _ => exact core_congCond E G a b c (p a) (p b) (p c) (P a) (P b) (P c) ha hb hc Γ H
  | 11, _ => exact core_beta E G a b c (p a) (p b) (p c) (P a) (P b) (P c) Γ H
  | 17, _ =>
    exact core_delta E G a [b, c] (p a) [(b, p b), (c, p c)] (P a)
      [(b, P b), (c, P c)] rfl Γ H
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 12, _ | 13, _ | 14, _
  | 15, _ | 16, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of four children. -/
theorem core_four (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a b c d : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (hc : Agrees E G (p c) (P c)) (hd : Agrees E G (p d) (P d)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) [a, b, c, d]
      ([a, b, c, d].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([a, b, c, d].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl with
  | 21, _ => exact core_foldrNil E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) Γ H
  | 23, _ =>
    exact core_indList E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) hc hd Γ H
  | 17, _ =>
    exact core_delta E G a [b, c, d] (p a) [(b, p b), (c, p c), (d, p d)] (P a)
      [(b, P b), (c, P c), (d, P d)] rfl Γ H
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ | 16, _ | 18, _ | 19, _ | 20, _ | 22, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of five children. -/
theorem core_five (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a b c d e : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) [a, b, c, d, e]
      ([a, b, c, d, e].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([a, b, c, d, e].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl with
  | 17, _ =>
    exact core_delta E G a [b, c, d, e] (p a) [(b, p b), (c, p c), (d, p d), (e, p e)] (P a)
      [(b, P b), (c, P c), (d, P d), (e, P e)] rfl Γ H
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ | 16, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of six children. -/
theorem core_six (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a b c d e f : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) [a, b, c, d, e, f]
      ([a, b, c, d, e, f].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ([a, b, c, d, e, f].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl with
  | 22, _ =>
    exact core_foldrCons E G a b c d e f (p a) (p b) (p c) (p d) (p e) (p f) (P a) (P b) (P c)
      (P d) (P e) (P f) Γ H
  | 17, _ =>
    exact core_delta E G a [b, c, d, e, f] (p a)
      [(b, p b), (c, p c), (d, p d), (e, p e), (f, p f)] (P a)
      [(b, P b), (c, P c), (d, P d), (e, P e), (f, P f)] rfl Γ H
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ | 16, _ | 18, _ | 19, _ | 20, _ | 21, _ | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's rules below case analysis of lists at a node of seven or more children. -/
theorem core_many (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (a b c d e f g : Tree)
    (rest : List Tree) (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx)
    (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l)
      (a :: b :: c :: d :: e :: f :: g :: rest)
      ((a :: b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkCore l ((a :: b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, P c)) E G Γ
        H).map encEqn) := by
  simp only [List.map_cons]
  match l, hl with
  | 17, _ =>
    exact core_delta E G a (b :: c :: d :: e :: f :: g :: rest) (p a)
      ((b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, p c)) (P a)
      ((b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, P c))
      (by simp [List.map_map, Function.comp_def]) Γ H
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ | 16, _ | 18, _ | 19, _ | 20, _ | 21, _ | 22, _ | 23, _ => rule_none
  | _ + 24, h => exact absurd h (by omega)

/-- The mirror's rules below case analysis of lists agree with the kernel's at every node whose
children agree. -/
theorem checkCore_eq (E : Env) (G : List Glob) (l : ℕ) (hl : l < 24) (cs : List Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (hp : ∀ c ∈ cs, Agrees E G (p c) (P c)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCore E.defs (G.map (·.1)) (leaf l) cs (cs.map fun c ↦ (c, p c)) Γ
      (H.map encEqn) = enc ((checkCore l (cs.map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩
  · exact core_nil E G l hl p P Γ H
  · exact core_one E G l hl a p P (hp a (by simp)) Γ H
  · exact core_two E G l hl a b p P (hp a (by simp)) (hp b (by simp)) Γ H
  · exact core_three E G l hl a b c p P (hp a (by simp)) (hp b (by simp)) (hp c (by simp)) Γ H
  · exact core_four E G l hl a b c d p P (hp c (by simp)) (hp d (by simp)) Γ H
  · exact core_five E G l hl a b c d e p P Γ H
  · exact core_six E G l hl a b c d e f p P Γ H
  · exact core_many E G l hl a b c d e f g rest p P Γ H

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node without children. -/
theorem more_nil (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) []
      ([].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  match l, hl, hl' with
  | 24, _, _ | 25, _, _ | 26, _, _ | 27, _, _ | 28, _, _ | 29, _, _ | 30, _, _ | 31, _, _
  | 32, _, _ | 33, _, _ | 34, _, _ | 35, _, _ | 36, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of one child. -/
theorem more_one (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37) (a : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) [a]
      ([a].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([a].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl, hl' with
  | 31, _, _ => exact more_unfold E G a (p a) (P a) Γ H
  | 33, _, _ =>
    exact more_ax E G a [] (p a) [] (P a)
      [] rfl Γ H
  | 36, _, _ =>
    exact more_thm E G a [] (p a) [] (P a)
      [] rfl Γ H
  | 24, _, _ | 25, _, _ | 26, _, _ | 27, _, _ | 28, _, _ | 29, _, _ | 30, _, _ | 32, _, _
  | 34, _, _ | 35, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of two children. -/
theorem more_two (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37) (a b : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) [a, b]
      ([a, b].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([a, b].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl, hl' with
  | 33, _, _ =>
    exact more_ax E G a [b] (p a) [(b, p b)] (P a)
      [(b, P b)] rfl Γ H
  | 36, _, _ =>
    exact more_thm E G a [b] (p a) [(b, p b)] (P a)
      [(b, P b)] rfl Γ H
  | 24, _, _ | 25, _, _ | 26, _, _ | 27, _, _ | 28, _, _ | 29, _, _ | 30, _, _ | 31, _, _
  | 32, _, _ | 34, _, _ | 35, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of three children. -/
theorem more_three (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37) (a b c : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (hc : Agrees E G (p c) (P c)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) [a, b, c]
      ([a, b, c].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([a, b, c].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl, hl' with
  | 26, _, _ => exact more_iterZero E G a b c (p a) (p b) (p c) (P a) (P b) (P c) Γ H
  | 29, _, _ => exact more_indTree E G a b c (p a) (p b) (p c) (P a) (P b) (P c) hc Γ H
  | 32, _, _ => exact more_condQuote E G a b c (p a) (p b) (p c) (P a) (P b) (P c) Γ H
  | 33, _, _ =>
    exact more_ax E G a [b, c] (p a) [(b, p b), (c, p c)] (P a)
      [(b, P b), (c, P c)] rfl Γ H
  | 36, _, _ =>
    exact more_thm E G a [b, c] (p a) [(b, p b), (c, p c)] (P a)
      [(b, P b), (c, P c)] rfl Γ H
  | 24, _, _ | 25, _, _ | 27, _, _ | 28, _, _ | 30, _, _ | 31, _, _ | 34, _, _
  | 35, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of four children. -/
theorem more_four (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37) (a b c d : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (hc : Agrees E G (p c) (P c)) (hd : Agrees E G (p d) (P d)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) [a, b, c, d]
      ([a, b, c, d].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([a, b, c, d].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl, hl' with
  | 24, _, _ => exact more_lcaseNil E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) Γ H
  | 27, _, _ => exact more_iterSucc E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) Γ H
  | 28, _, _ => exact more_foldNode E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) Γ H
  | 30, _, _ =>
    exact more_indLabel E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) hc hd Γ H
  | 34, _, _ => exact more_iterLabel E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) Γ H
  | 35, _, _ => exact more_condIter E G a b c d (p a) (p b) (p c) (p d) (P a) (P b) (P c) (P d) Γ H
  | 33, _, _ =>
    exact more_ax E G a [b, c, d] (p a) [(b, p b), (c, p c), (d, p d)] (P a)
      [(b, P b), (c, P c), (d, P d)] rfl Γ H
  | 36, _, _ =>
    exact more_thm E G a [b, c, d] (p a) [(b, p b), (c, p c), (d, p d)] (P a)
      [(b, P b), (c, P c), (d, P d)] rfl Γ H
  | 25, _, _ | 26, _, _ | 29, _, _ | 31, _, _ | 32, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of five children. -/
theorem more_five (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37) (a b c d e : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) [a, b, c, d, e]
      ([a, b, c, d, e].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([a, b, c, d, e].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl, hl' with
  | 33, _, _ =>
    exact more_ax E G a [b, c, d, e] (p a) [(b, p b), (c, p c), (d, p d), (e, p e)] (P a)
      [(b, P b), (c, P c), (d, P d), (e, P e)] rfl Γ H
  | 36, _, _ =>
    exact more_thm E G a [b, c, d, e] (p a) [(b, p b), (c, p c), (d, p d), (e, p e)] (P a)
      [(b, P b), (c, P c), (d, P d), (e, P e)] rfl Γ H
  | 24, _, _ | 25, _, _ | 26, _, _ | 27, _, _ | 28, _, _ | 29, _, _ | 30, _, _ | 31, _, _
  | 32, _, _ | 34, _, _ | 35, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of six children. -/
theorem more_six (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37) (a b c d e f : Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) [a, b, c, d, e, f]
      ([a, b, c, d, e, f].map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ([a, b, c, d, e, f].map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  simp only [List.map_cons, List.map_nil]
  match l, hl, hl' with
  | 25, _, _ =>
    exact more_lcaseCons E G a b c d e f (p a) (p b) (p c) (p d) (p e) (p f) (P a) (P b) (P c)
      (P d) (P e) (P f) Γ H
  | 33, _, _ =>
    exact more_ax E G a [b, c, d, e, f] (p a)
      [(b, p b), (c, p c), (d, p d), (e, p e), (f, p f)] (P a)
      [(b, P b), (c, P c), (d, P d), (e, P e), (f, P f)] rfl Γ H
  | 36, _, _ =>
    exact more_thm E G a [b, c, d, e, f] (p a)
      [(b, p b), (c, p c), (d, p d), (e, p e), (f, p f)] (P a)
      [(b, P b), (c, P c), (d, P d), (e, P e), (f, P f)] rfl Γ H
  | 24, _, _ | 26, _, _ | 27, _, _ | 28, _, _ | 29, _, _ | 30, _, _ | 31, _, _ | 32, _, _
  | 34, _, _ | 35, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

set_option maxHeartbeats 1000000 in
-- each label's case evaluates the chain of the checker's tests of label and arity
/-- The mirror's other rules at a node of seven or more children. -/
theorem more_many (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (hl' : l < 37)
    (a b c d e f g : Tree) (rest : List Tree) (p : Tree → List Tree → List Tree → Tree)
    (P : Tree → Chk) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l)
      (a :: b :: c :: d :: e :: f :: g :: rest)
      ((a :: b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l ((a :: b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, P c)) E G Γ
        H).map encEqn) := by
  simp only [List.map_cons]
  match l, hl, hl' with
  | 33, _, _ =>
    exact more_ax E G a (b :: c :: d :: e :: f :: g :: rest) (p a)
      ((b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, p c)) (P a)
      ((b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, P c))
      (by simp [List.map_map, Function.comp_def]) Γ H
  | 36, _, _ =>
    exact more_thm E G a (b :: c :: d :: e :: f :: g :: rest) (p a)
      ((b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, p c)) (P a)
      ((b :: c :: d :: e :: f :: g :: rest).map fun c ↦ (c, P c))
      (by simp [List.map_map, Function.comp_def]) Γ H
  | 24, _, _ | 25, _, _ | 26, _, _ | 27, _, _ | 28, _, _ | 29, _, _ | 30, _, _ | 31, _, _
  | 32, _, _ | 34, _, _ | 35, _, _ => rule_none
  | 0, h, _ | 1, h, _ | 2, h, _ | 3, h, _ | 4, h, _ | 5, h, _ | 6, h, _ | 7, h, _ | 8, h, _
  | 9, h, _ | 10, h, _ | 11, h, _ | 12, h, _ | 13, h, _ | 14, h, _ | 15, h, _ | 16, h, _
  | 17, h, _ | 18, h, _ | 19, h, _ | 20, h, _ | 21, h, _ | 22, h, _
  | 23, h, _ => exact absurd h (by omega)
  | _ + 37, _, h => exact absurd h (by omega)

/-- The kernel's rules give nothing at a node whose label is past its rules. -/
theorem checkMore_other (E : Env) (G : List Glob) (l : ℕ) (hl : 36 < l) (cs : List (Tree × Chk))
    (Γ : Ctx) (H : List Eqn) : checkMore l cs E G Γ H = none := by
  unfold checkMore
  split <;> first | omega | rfl

/-- The mirror's rules give nothing at a node whose label is past its rules. -/
theorem more_other (E : Env) (G : List Glob) (l : ℕ) (hl : 36 < l) (cs : List Tree)
    (ps : List (Tree × (List Tree → List Tree → Tree))) (Γ : Ctx) (H : List Tree) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) cs ps Γ H =
      enc none := by
  simp only [GebMirror.GoedelT.checkMore, ↓reduceIte, shape_label, and_label, eq_leaf, lt_leaf,
    length_eq, show l ≠ 24 by omega, show l ≠ 25 by omega, show l ≠ 26 by omega,
    show l ≠ 27 by omega, show l ≠ 28 by omega, show l ≠ 29 by omega, show l ≠ 30 by omega,
    show l ≠ 31 by omega, show l ≠ 32 by omega, show l ≠ 33 by omega, show l ≠ 34 by omega,
    show l ≠ 35 by omega, show l ≠ 36 by omega, false_and]
  rfl

/-- The mirror's rules from case analysis of lists on agree with the kernel's at every node whose
children agree. -/
theorem checkMore_eq (E : Env) (G : List Glob) (l : ℕ) (hl : 24 ≤ l) (cs : List Tree)
    (p : Tree → List Tree → List Tree → Tree) (P : Tree → Chk)
    (hp : ∀ c ∈ cs, Agrees E G (p c) (P c)) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkMore E.defs (E.thms.map encThm) (G.map (·.1)) (leaf l) cs
      (cs.map fun c ↦ (c, p c)) Γ (H.map encEqn) =
      enc ((checkMore l (cs.map fun c ↦ (c, P c)) E G Γ H).map encEqn) := by
  by_cases hl' : l < 37
  · rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, _ | ⟨f, _ | ⟨g, rest⟩⟩⟩⟩⟩⟩⟩
    · exact more_nil E G l hl hl' p P Γ H
    · exact more_one E G l hl hl' a p P Γ H
    · exact more_two E G l hl hl' a b p P Γ H
    · exact more_three E G l hl hl' a b c p P (hp c (by simp)) Γ H
    · exact more_four E G l hl hl' a b c d p P (hp c (by simp)) (hp d (by simp)) Γ H
    · exact more_five E G l hl hl' a b c d e p P Γ H
    · exact more_six E G l hl hl' a b c d e f p P Γ H
    · exact more_many E G l hl hl' a b c d e f g rest p P Γ H
  · rw [more_other E G l (by omega), checkMore_other E G l (by omega)]
    rfl

/-- The trees of a list of certificates with their checkers. -/
theorem crTrees_eq (rs : List (Tree × (List Tree → List Tree → Tree))) :
    GebMirror.GoedelT.crTrees rs = rs.map (·.1) :=
  rs.rec rfl fun _ _ ih ↦ by
    simp only [GebMirror.GoedelT.crTrees, Const.foldr, List.foldr_cons] at ih ⊢
    rw [ih]
    rfl

/-- The step of the mirror's checker at a certificate node: the node rebuilt, and its checker as
a function of the context and the hypotheses. -/
def certStep (D Th Gt : List Tree) (l : Tree) (rs : List (Tree × (List Tree → List Tree → Tree))) :
    Tree × (List Tree → List Tree → Tree) :=
  (Const.node l (GebMirror.GoedelT.crTrees rs), fun Γ H ↦
    if (Const.lt l (leaf 24)).label ≠ 0 then
      GebMirror.GoedelT.checkCore D Gt l (GebMirror.GoedelT.crTrees rs) rs Γ H
    else GebMirror.GoedelT.checkMore D Th Gt l (GebMirror.GoedelT.crTrees rs) rs Γ H)

/-- The mirror's checker is the fold of its step. -/
theorem checkCert_def (D Th Gt : List Tree) (c : Tree) (Γ H : List Tree) :
    GebMirror.GoedelT.checkCert D Th Gt c Γ H = (Const.fold (certStep D Th Gt) c).2 Γ H := rfl

/-- The fold of the mirror's checker gives each certificate with a checker agreeing with the
kernel's. -/
theorem fold_certStep (E : Env) (G : List Glob) : ∀ c : Tree,
    (Const.fold (certStep E.defs (E.thms.map encThm) (G.map (·.1))) c).1 = c ∧
      Agrees E G (Const.fold (certStep E.defs (E.thms.map encThm) (G.map (·.1))) c).2
        (check c) :=
  RoseTree.ind fun l cs ih ↦ by
    rw [fold_node]
    have hrs : cs.map (Const.fold (certStep E.defs (E.thms.map encThm) (G.map (·.1)))) =
        cs.map fun c ↦
          (c, (Const.fold (certStep E.defs (E.thms.map encThm) (G.map (·.1))) c).2) :=
      List.map_congr_left fun c hc ↦ Prod.ext (ih c hc).1 rfl
    have htr : GebMirror.GoedelT.crTrees
        (cs.map (Const.fold (certStep E.defs (E.thms.map encThm) (G.map (·.1))))) = cs := by
      rw [crTrees_eq, List.map_map]
      exact (List.map_congr_left fun c hc ↦ (ih c hc).1).trans (List.map_id cs)
    refine ⟨by simp only [certStep, htr]; rfl, fun Γ H ↦ ?_⟩
    simp only [certStep, htr, lt_leaf]
    rw [hrs]
    simp only [check, RoseTree.para_node, checkStep]
    split_ifs with h
    · exact checkCore_eq E G l h cs _ check (fun c hc ↦ (ih c hc).2) Γ H
    · exact checkMore_eq E G l (by omega) cs _ check (fun c hc ↦ (ih c hc).2) Γ H

/-- The checker of Gödel's T written in Geb decides as the kernel's: at a certificate, a program's
definitions and theorems, a global environment, a context and hypotheses, all encoded, it gives
the encoding of the kernel's conclusion, or nothing where the kernel gives nothing. -/
theorem checkCert_eq (E : Env) (G : List Glob) (c : Tree) (Γ : Ctx) (H : List Eqn) :
    GebMirror.GoedelT.checkCert E.defs (E.thms.map encThm) (G.map (·.1)) c Γ (H.map encEqn) =
      enc ((check c E G Γ H).map encEqn) :=
  (fold_certStep E G c).2 Γ H

end GebTests.Prototypes.GoedelT.MirrorChecker

end
