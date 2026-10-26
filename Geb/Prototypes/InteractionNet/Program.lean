/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Mathlib.Logic.Equiv.Fin.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# First-order programs as interaction systems

An expression contains data constructors, named calls, and variables. A call has a principal
argument and finitely many further arguments. Its rule inspects the constructor of the
principal argument and returns an expression over that constructor's children and the other
arguments. The rules are first order: functions are names, never host-language closures
stored in runtime values.

The translation uses an evaluation agent for each expression and an environment constructor.
Evaluating a constructor or call first fans the environment out to its subexpressions, then
evaluates those subexpressions, and finally constructs the result or invokes the named call.
Even unused environment entries are consumed by zero-output fans. Each interaction sees
only its two principal agents. The right-hand side never inspects an auxiliary-port term.

This supplies the program-specific agents used by the first bootstrap stage. It is a
mechanical interface for writing local rules; the sequential calculus is in
{name}`Geb.InteractionNet.System.step`.

## Main definitions

* {lit}`Expr` — first-order expressions with a finite context of variables.
* {lit}`Program` — one constructor-dispatch rule for a named call.
* {lit}`Agent`, {lit}`netArity` — data, environments, fans, evaluators, and calls.
* {lit}`evalRule`, {lit}`callRule`, {lit}`system` — the interaction-system translation.
* {lit}`initial` — a closed expression's initial configuration.

## References

* {cite}`MackiePintoVilaca2009`, for program-specific interaction systems.
* {cite}`HassanMackieSato2015`, Section 3, for the textual interaction calculus.

## Tags

interaction net, first-order program, compilation, defunctionalization, environment
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.FirstOrder

variable {δ φ : Type} (dataArity : δ → ℕ)

/-- Expression constructors: data and a named call with its number of further arguments. -/
abbrev Symbol := δ ⊕ (φ × ℕ)

/-- Every call has a principal argument, in addition to its further arguments. -/
abbrev exprArity : Symbol (δ := δ) (φ := φ) → ℕ
  | .inl a => dataArity a
  | .inr (_, n) => n + 1

/-- A first-order expression over a finite context. -/
abbrev Expr (n : ℕ) := Term (exprArity (φ := φ) dataArity) (Fin n)

namespace Expr

variable {dataArity}

/-- A constructor applied to its children. -/
def con {n : ℕ} (a : δ) (xs : Fin (dataArity a) → Expr (φ := φ) dataArity n) :
    Expr (φ := φ) dataArity n := Term.agent (.inl a) xs

/-- A call with one principal argument and a list of further arguments. -/
def call {n : ℕ} (f : φ) (x : Expr (φ := φ) dataArity n)
    (xs : List (Expr (φ := φ) dataArity n)) : Expr (φ := φ) dataArity n :=
  Term.agent (.inr (f, xs.length)) (Fin.cases x xs.get)

end Expr

/-- Dispatch on the first argument's constructor. Rule variables are its children followed
by the further arguments, in their original order. -/
structure Program where
  /-- A rule may reject a constructor or an incorrect number of further arguments. -/
  rewrite : (f : φ) → (others : ℕ) → (a : δ) →
    Option (Expr (φ := φ) dataArity (dataArity a + others))

/-- Net agents: constructors and environments, then fans, expression evaluators, and calls. -/
abbrev Agent := (δ ⊕ ℕ) ⊕ (ℕ ⊕ ((Σ n, Expr (φ := φ) dataArity n) ⊕ (φ × ℕ)))

/-- The arity of a data constructor or an environment constructor. -/
abbrev constructorArity : δ ⊕ ℕ → ℕ
  | .inl a => dataArity a
  | .inr n => n

/-- The auxiliary ports of each agent. Evaluators have a result port; calls also have
their further arguments. -/
abbrev netArity : Agent (φ := φ) dataArity → ℕ
  | .inl a => constructorArity dataArity a
  | .inr (.inl k) => k
  | .inr (.inr (.inl _)) => 1
  | .inr (.inr (.inr (_, n))) => n + 1

/-- A data agent. -/
abbrev data (a : δ) : Agent (φ := φ) dataArity := .inl (.inl a)

/-- An environment's entries are its auxiliary ports. -/
abbrev env (n : ℕ) : Agent (φ := φ) dataArity := .inl (.inr n)

/-- A fan copies data, including environments, constructor by constructor. -/
abbrev fan (k : ℕ) : Agent (φ := φ) dataArity := .inr (.inl k)

/-- The evaluator for one expression occurrence. -/
abbrev ev {n : ℕ} (e : Expr (φ := φ) dataArity n) : Agent (φ := φ) dataArity :=
  .inr (.inr (.inl ⟨n, e⟩))

/-- A named call. Port zero is the result; the remaining ports are further arguments. -/
abbrev app (f : φ) (n : ℕ) : Agent (φ := φ) dataArity := .inr (.inr (.inr (f, n)))

/-- The fan rule, for either a program's data or an environment. -/
def fanRule (k : ℕ) (a : δ ⊕ ℕ) :
    Rule (netArity (φ := φ) dataArity) (fan dataArity k) (.inl a) where
  fresh := constructorArity dataArity a * k
  equations :=
    (List.ofFn fun i : Fin (constructorArity dataArity a) ↦
      (Term.agent (fan dataArity k) fun j ↦ Term.var (.inr (finProdFinEquivC (i, j))),
        Term.var (.inl (.inr i)))) ++
    (List.ofFn fun j : Fin k ↦
      (Term.var (.inl (.inl j)),
        Term.agent (.inl a) fun i ↦ Term.var (.inr (finProdFinEquivC (i, j)))))

/-- Finish an expression root after its children have supplied their result wires. -/
def finish {ν : Type} (a : Symbol (δ := δ) (φ := φ))
    (out : Term (netArity (φ := φ) dataArity) ν)
    (rs : Fin (exprArity dataArity a) → Term (netArity (φ := φ) dataArity) ν) :
    Equation (netArity (φ := φ) dataArity) ν :=
  match a with
  | .inl a => (out, Term.agent (data dataArity a) rs)
  | .inr (f, k) =>
    (Term.agent (app dataArity f k) (Fin.cases out fun i ↦ rs i.succ), rs 0)

/-- Evaluate one expression root against its environment. Subexpressions receive distinct
copies of each environment entry, produced by fans before their evaluation starts. -/
def evalRule {n : ℕ} (e : Expr (φ := φ) dataArity n) :
    Rule (netArity (φ := φ) dataArity) (ev dataArity e) (env dataArity n) :=
  match e with
  | .pure i =>
    { fresh := 0
      equations :=
        List.ofFn fun j : Fin n ↦
          (if j = i then Term.var (.inl (.inl 0)) else
            Term.agent (fan dataArity 0) Fin.elim0, Term.var (.inl (.inr j))) }
  | .liftBind a es =>
    let m := exprArity dataArity a
    let wire (j : Fin m) (i : Fin n) : Fin (m * n + m) :=
      Fin.castAdd m (finProdFinEquivC (j, i))
    let result (j : Fin m) : Fin (m * n + m) := Fin.natAdd (m * n) j
    let resultTerm (j : Fin m) := Term.var (.inr (result j))
    { fresh := m * n + m
      equations :=
        (List.ofFn fun i : Fin n ↦
          (Term.agent (fan dataArity m) fun j ↦ Term.var (.inr (wire j i)),
            Term.var (.inl (.inr i)))) ++
        (List.ofFn fun j : Fin m ↦
          (Term.agent (ev dataArity (es j)) fun _ ↦ resultTerm j,
            Term.agent (env dataArity n) fun i ↦ Term.var (.inr (wire j i)))) ++
        [finish dataArity a (Term.var (.inl (.inl 0))) resultTerm] }

/-- Transfer a call's arguments to the evaluator of its rule body, without inspecting or
duplicating any auxiliary-port term. -/
def callRule (f : φ) (others : ℕ) (a : δ)
    (body : Expr (φ := φ) dataArity (dataArity a + others)) :
    Rule (netArity (φ := φ) dataArity) (app dataArity f others) (data dataArity a) where
  fresh := 0
  equations :=
    [(Term.agent (ev dataArity body) fun _ ↦ Term.var (.inl (.inl 0)),
      Term.agent (env dataArity (dataArity a + others)) fun i ↦
        Fin.addCases
          (fun j ↦ Term.var (.inl (.inr j)))
          (fun j ↦ Term.var (.inl (.inl j.succ))) i)]

/-- The program's interaction system. Rules are registered in one orientation only. -/
def system (p : Program (φ := φ) dataArity) : System (netArity (φ := φ) dataArity) where
  rule a b := match a, b with
    | .inr (.inl k), .inl a => some (fanRule dataArity k a)
    | .inr (.inr (.inl ⟨n, e⟩)), .inl (.inr m) =>
      if h : n = m then h ▸ some (evalRule dataArity e) else none
    | .inr (.inr (.inr (f, k))), .inl (.inl a) =>
      (p.rewrite f k a).map (callRule dataArity f k a)
    | _, _ => none

/-- A closed expression starts at one output wire and an empty environment. -/
def initial (e : Expr (φ := φ) dataArity 0) : Config (netArity (φ := φ) dataArity) where
  interface := [Term.var 0]
  equations := [(Term.agent (ev dataArity e) fun _ ↦ Term.var 0,
    Term.agent (env dataArity 0) Fin.elim0)]
  nextName := 1

end Geb.InteractionNet.FirstOrder

end
