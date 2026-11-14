/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.SourceAnnotation
public import Geb.Prototypes.Kernel.Printer
public import Geb.Prototypes.Kernel.Modules
public import GebHost.Locate
public import GebBoot

set_option doc.verso true

/-!
# Located kernel typing failures

An untrusted explanation of a rejection by the compiled kernel checker. Each node delegates
its type to {lit}`Check.checkNode`; on failure it follows the failing operand, extending the
context at a lambda and leaving types and quoted data outside the term traversal. A mismatch
reports the expected and actual types at the operand's vertex.

Kernel declarations, including {lit}`defn`, can be diagnosed after module elaboration. The
source correspondence of {name}`Geb.Kernel.SourceAnnotation.trace` maps the vertex back to the
original expression. A program prefix using datatype declarations or other unsupported forms
has no explanation from this pass and keeps the compiler's declaration diagnostic.

## Main definitions

* {lit}`check` — the compiled checker's type or a located explanation of its failure.
* {lit}`inProgram` — the first typing failure of a kernel program at a named definition.
* {lit}`occurrences` — source spans corresponding to the failed kernel vertex.

## Tags

kernel, typing, diagnostics, source span
-/

open Geb Geb.Kernel Geb.Kernel.Document GebHost.Locate

public section

namespace GebHost.Typing

/-- A failed kernel vertex and an explanation of its rejection. -/
structure Fault where
  /-- The path from the term's root, in kernel child indices. -/
  path : List Nat
  /-- What the checker requires at that vertex. -/
  message : String

/-- A type or failure, as a function of the types of bound variables. -/
abbrev Check : Type := Ctx → Except Fault Tree

/-- The compiled checker's optional-tree representation of a diagnostic result. -/
def optional (r : Except Fault Tree) : Tree :=
  match r with
  | .ok A => mk 1 [A]
  | .error _ => leaf 0

/-- A kernel type in its source spelling. -/
def typeText (A : Tree) : String :=
  String.ofList (printAt #[] ⟨[plain (printType A)], []⟩).dropLast

/-- Explain a rejected node after all its term operands have checked. -/
def mismatch (raw : Tree) (types : List (Option Tree)) : Fault :=
  let ty (i : Nat) := (types[i]?.join).getD tT
  let expected (i : Nat) (A : Tree) : Fault :=
    ⟨[i], s!"expected {typeText A}, got {typeText (ty i)}"⟩
  let shape (i : Nat) (s : String) : Fault :=
    ⟨[i], s!"expected {s}, got {typeText (ty i)}"⟩
  match raw.label with
  | Label.app =>
    if (GebBoot.«Check.isArrow» (ty 0)).label != 0 then
      expected 1 ((ty 0).children.getD 0 tT)
    else shape 0 "a function type"
  | Label.fst | Label.snd => shape 0 "a product type"
  | Label.cond => if (Const.equal (ty 0) tT).label == 0 then expected 0 tT else expected 2 (ty 1)
  | Label.cons =>
    if (GebBoot.«Check.isListTy» (ty 1)).label != 0 then
      expected 0 ((ty 1).children.getD 0 tT)
    else shape 1 "a list type"
  | Label.var => ⟨[], "the variable is outside its binding context"⟩
  | Label.ref => ⟨[], "the definition is outside the preceding program"⟩
  | _ => ⟨[], "malformed kernel expression or type annotation"⟩

/-- One node's diagnostic, using the compiled checker for the decision and the type. -/
def checkStep (G : List Tree) (l : Nat) (cs : List (Tree × Check)) : Check := fun Γ ↦ do
  let raw := mk l (cs.map Prod.fst)
  let rr := cs.map fun (t, r) ↦ (t, fun ctx ↦ optional (r ctx))
  let result := GebBoot.«Check.checkNode» G raw rr Γ
  if result.label != 0 then return result.children.getD 0 tT
  let operands : List (Nat × Ctx) :=
    match l with
    | Label.lam => [(1, (cs[0]?.map (·.1)).getD tT :: Γ)]
    | Label.app | Label.pair | Label.cons => [(0, Γ), (1, Γ)]
    | Label.fst | Label.snd => [(0, Γ)]
    | Label.cond => [(0, Γ), (1, Γ), (2, Γ)]
    | _ => []
  for (i, ctx) in operands do
    if let some (_, r) := cs[i]? then
      match r ctx with
      | .error f => throw { f with path := i :: f.path }
      | .ok _ => pure ()
  throw (mismatch raw (cs.map fun (_, r) ↦ (r Γ).toOption))

/-- The checker's type or a failed vertex, without evaluating the program's definitions. -/
def check (G : List Tree) (Γ : Ctx) (t : Tree) : Except Fault Tree :=
  RoseTree.para (checkStep G) t Γ

/-- Desugar a kernel declaration, retaining the source spans of its body and type annotation.
The generated result binder is reserved to the implementation. -/
def kernelForm (t : Located) : Option Located :=
  if ["def", "deftype", "defnum"].any (headIs ·.toList t) then some t
  else if headIs "defn".toList t then
    match t.children with
    | [_, name, ps, res, body] =>
      let atom (s : String) := atomAt t.label.1 s.toList
      let list (xs : List Located) := RoseTree.node (t.label.1, none) xs
      let bound := list [atom "let", atom "%result", res, body, atom "%result"]
      some (list [atom "def", name, list [atom "lam", ps, bound]])
    | _ => none
  else none

/-- Diagnose a kernel prefix after module elaboration, stopping at unsupported syntax or a
failure to resolve. The named definition must be the first typing failure. -/
def inProgram (text : List Char) (name : String) : Option Fault := do
  let es ← (elabModules (← readSExps text)).toOption
  let step (st : Option (TypeNames × NumNames × List (List Char × Tree) × List Tree))
      (e : SExp) : Except Fault (Option
        (TypeNames × NumNames × List (List Char × Tree) × List Tree)) := do
    let some (tys, nums, ds, G) := st | return none
    let some k := kernelForm (e.map (fun a ↦ (default, a))) | return none
    let some (tys', nums', ds') := readFormStep (some (tys, nums, ds)) (k.map Prod.snd)
      | return none
    if ds'.length == ds.length then return some (tys', nums', ds', G)
    let some (n, t) := ds'.getLast? | return none
    match check G [] t with
    | .ok A => return some (tys', nums', ds', G ++ [A])
    | .error f => if String.ofList n == name then throw f else return none
  match es.foldlM step (some ([], [], [], [])) with
  | .error f => some f
  | .ok _ => none

/-- Source spans for a kernel vertex of a declaration, including within nested modules.
Only syntax correspondences contribute; binder spellings are separate annotations. -/
def occurrences (items : List Located) (name : String) (path : List Nat) : List Span :=
  let visit : Located → List (List Char) → List Span :=
    RoseTree.para fun l cs pre ↦
      let t := RoseTree.node l (cs.map Prod.fst)
      let n := (t.children[1]?.bind (·.label.2)).getD []
      let here := pre ++ [n]
      if Locate.headIs "module".toList t then (cs.drop 2).flatMap fun (_, r) ↦ r here
      else if qualified here != name then []
      else match kernelForm t with
        | none => []
        | some k =>
          match k.children[2]? with
          | none => []
          | some body =>
            (SourceAnnotation.trace [] (body.map Prod.snd)).filterMap fun o ↦
              if o.role == .syntax && o.core == path then
                (Identity.subtree? body o.source).map (·.label.1)
              else none
  items.flatMap fun t ↦ visit t []

end GebHost.Typing

end
