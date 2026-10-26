/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.Calculus
public import Geb.Prototypes.RoseTree.Basic
import Geb.Prototypes.InteractionNet.FiniteSum
import Geb.Cslib.Foundations.Data.PFunctor.Free
public import Geb.Mathlib.Logic.Equiv.Fin.Basic
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Constructor copying and erasure

A data agent has a label and a finite number of children. A fan has one principal input and
as many auxiliary outputs as requested copies. Zero outputs erases; one forwards a copy;
two duplicates. A fan interacts with one constructor, allocates a wire for each child in
each copy, and delegates copying of the children to further fans. It never inspects a child
or copies a subtree in the host language.

Rose trees are represented by these constructor agents, with their natural-number labels
as attributes. This is the data-copying part of the first interaction-net stage described
in the bootstrap. It also applies to defunctionalized closures represented as data.

## Main definitions

* {lit}`Agent`, {lit}`arity` — constructors and fans.
* {lit}`copyRule`, {lit}`system` — the local constructor-copying rule and its reducer.
* {lit}`encode`, {lit}`readback` — rose-tree representation and partial read-back.
* {lit}`copyInput` — a closed input with an ordered list of requested copies.

## Main statements

* {lit}`readback_encode` — read-back recovers every encoded tree.
* {lit}`encode_names` — encoded trees contain no wire names.

## References

* {cite}`HassanMackieSato2015`, Section 3, for the underlying interaction calculus.

## Tags

interaction net, copying, erasure, rose tree, read-back
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Data

/-- Constructor labels and arities, or a fan's number of output ports. -/
abbrev Agent := (ℕ × ℕ) ⊕ ℕ

/-- The number of auxiliary ports. -/
abbrev arity : Agent → ℕ
  | .inl (_, n) => n
  | .inr k => k

/-- A data constructor with its label and number of children as attributes. -/
abbrev node (l n : ℕ) : Agent := .inl (l, n)

/-- A fan with the given number of requested copies. -/
abbrev fan (k : ℕ) : Agent := .inr k

/-- A fan copies a constructor and sends a fan to each of its children. -/
def copyRule (k l n : ℕ) : Rule arity (fan k) (node l n) where
  fresh := n * k
  equations :=
    (List.ofFn fun i : Fin n ↦
      (Term.agent (fan k) fun j ↦ Term.var (.inr (finProdFinEquivC (i, j))),
        Term.var (.inl (.inr i)))) ++
    (List.ofFn fun j : Fin k ↦
      (Term.var (.inl (.inl j)),
        Term.agent (node l n) fun i ↦ Term.var (.inr (finProdFinEquivC (i, j)))))

/-- Copying preserves every boundary wire and binds every allocated wire twice. -/
theorem copyRule_linear (k l n : ℕ) : (copyRule k l n).Linear := by
  dsimp [Rule.Linear, Rule.names, copyRule]
  constructor
  · intro i
    cases i <;>
      simp [Term.names_agent, Term.names_var,
        List.count_flatMap, List.count_flatten, List.map_ofFn, finSum_ofFn,
        List.count_singleton, Function.comp_def]
  · intro j
    obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquivC.surjective j
    simp [Term.names_agent, Term.names_var, List.count_flatMap,
      List.count_flatten, List.map_ofFn, finSum_ofFn, List.count_singleton,
      Function.comp_def, ite_and]

/-- The constructor-copying system. No pair of data constructors interacts. -/
def system : System arity where
  rule a b := match a, b with
    | .inr k, .inl (l, n) => some (copyRule k l n)
    | _, _ => none

/-- Encode a rose tree as a closed term of data constructors. -/
def encode : RoseTree ℕ → Term arity ℕ :=
  RoseTree.elim fun l ts ↦ Term.agent (node l ts.length) ts.get

/-- Encoding preserves a constructor and encodes its children. -/
@[simp] theorem encode_node (l : ℕ) (ts : List (RoseTree ℕ)) :
    encode (RoseTree.node l ts) =
      Term.agent (node l (ts.map encode).length) (ts.map encode).get := by
  change RoseTree.elim _ _ = _
  rw [RoseTree.elim_node]
  rfl

/-- The read-back of a constructor's children, failing at a name or a fan. -/
def readback : Term arity ℕ → Option (RoseTree ℕ) :=
  PFunctor.FreeM.rec (fun _ ↦ none) (fun a _ rs ↦
    match a with
    | .inl (l, _) => (List.ofFn rs).mapM id |>.map (RoseTree.node l)
    | .inr _ => none)

/-- Read-back at a constructor reads all children. -/
@[simp] theorem readback_node (l n : ℕ) (ts : Fin n → Term arity ℕ) :
    readback (Term.agent (node l n) ts) =
      ((List.ofFn fun i ↦ readback (ts i)).mapM id).map (RoseTree.node l) := rfl

/-- Read-back recovers every encoded tree. -/
theorem readback_encode (t : RoseTree ℕ) : readback (encode t) = some t := by
  apply RoseTree.ind (P := fun t ↦ readback (encode t) = some t) (fun l ts ih ↦ ?_) t
  rw [encode_node, readback_node]
  simp only [← Function.comp_def, ← List.map_ofFn, List.ofFn_get, List.map_map]
  have h : ts.map (readback ∘ encode) = ts.map some :=
    List.map_congr_left fun x hx ↦ ih x hx
  rw [h, List.mapM_map]
  have hs : (List.mapM some ts : Option (List (RoseTree ℕ))) = some ts :=
    List.rec (by rfl) (fun a as ih ↦ by simp [List.mapM_cons, ih]) ts
  exact congrArg (Option.map (RoseTree.node l)) hs

/-- Encoding a tree introduces no wire names. -/
theorem encode_names (t : RoseTree ℕ) : (encode t).names = [] := by
  apply RoseTree.ind (P := fun t ↦ (encode t).names = []) (fun l ts ih ↦ ?_) t
  rw [encode_node, Term.names_agent]
  simp only [← Function.comp_def, ← List.map_ofFn, List.ofFn_get, List.map_map]
  simp only [List.flatten_eq_nil_iff, List.mem_map, forall_exists_index,
    and_imp]
  intro xs x hx heq
  exact heq ▸ ih x hx

/-- Request a specified number of copies of a closed data tree. -/
def copyInput (k : ℕ) (t : RoseTree ℕ) : Config arity where
  interface := List.ofFn fun i : Fin k ↦ Term.var i.val
  equations := [(Term.agent (fan k) (fun i ↦ Term.var i.val), encode t)]
  nextName := k

/-- Read all observable trees, failing if any observable port is still unresolved. -/
def readInterface (c : Config arity) : Option (List (RoseTree ℕ)) := c.interface.mapM readback

end Geb.InteractionNet.Data

end
