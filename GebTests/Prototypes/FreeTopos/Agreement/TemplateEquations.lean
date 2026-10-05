/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Lean.DocString.Syntax
public import Lean.Meta.Tactic.Simp.RegisterCommand
meta import Lean.Meta.Tactic.Simp.Attr
public meta import Lean.Elab.Command -- shake: keep

set_option doc.verso true in
/-!
# The equations of the templates' instances in the mirror

The bootstrap compiler emits each instance of a template of the datatype language as copies of the
template's definitions under the instance's name, and
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Templates` states each such definition once as a Lean
function. The command {lit}`template_equations` declares, for each copy among the constants of a
namespace, its equation with that function, closed by reflexivity, as a simp lemma, also of the
set {lit}`template`, the set in which the agreement proofs collect the equations of definitions
with the forms the proofs reason about. The module holds elaboration code alone, and
{lit}`GebMeta.classicalAllowedModules` admits it as it admits the commands of
{lit}`GebTests.Prototypes.ProgramCommand`.

## Main definitions

* {lit}`template` — the simp set.
* {lit}`template_equations` — the equations of a namespace's instances with the templates'
  functions.

## Tags

template, module, agreement, mirror, command
-/

set_option doc.verso true

public section

namespace GebTests.Prototypes.FreeTopos.Agreement.TemplateEquations

/-- The simp set of the equations of the templates' instances with the functions of
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Templates`. -/
register_simp_attr template

open Lean Elab Command Meta in
/-- {lit}`template_equations ns`: for each constant of the namespace {lit}`ns` whose name's last
component names a definition of a template's instance, {lit}`P/I.f` with {lit}`f` a function of
{lit}`GebTests.Prototypes.FreeTopos.Agreement.Templates` of the same type, the theorem {lit}`P/I.f_template` equating it with {lit}`f`, by
reflexivity, a simp lemma in the default set and the set {lit}`template`. -/
elab "template_equations " ns:ident : command => do
  let ns := ns.getId
  let here := `GebTests.Prototypes.FreeTopos.Agreement.Templates
  let fns := ["single", "length", "append", "reverse", "tail", "drop", "atOr", "nothing", "just",
    "isJust", "fromMaybe", "nthOf", "allJust", "all", "any", "isEmpty", "take", "map", "l2", "l3",
    "l4", "l5", "l6", "res", "bad", "ok", "pure", "fail", "orElse"]
  let cands := (← getEnv).constants.fold (init := #[]) fun acc c _ ↦
    match c with
    | .str p s => if p == ns && s.contains '/' then acc.push (c, s) else acc
    | _ => acc
  for (c, s) in cands.qsort (fun a b ↦ a.2 < b.2) do
    let f := (s.splitOn ".").getLast!
    unless fns.contains f do continue
    let t := here ++ Name.mkSimple f
    let same ← liftTermElabM do
      isDefEq (← getConstInfo c).type (← getConstInfo t).type
    unless same do continue
    elabCommand (← `(command|
      @[simp, template] theorem $(mkIdent (Name.mkSimple (s ++ "_template"))) :
          $(mkIdent c) = $(mkIdent t) := rfl))

end GebTests.Prototypes.FreeTopos.Agreement.TemplateEquations

end
