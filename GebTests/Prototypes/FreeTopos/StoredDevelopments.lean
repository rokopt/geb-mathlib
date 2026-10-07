/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.FreeTopos.Stored -- shake: keep
public import Lean.Elab.Command -- shake: keep

set_option doc.verso true in
/-!
# Stored developments in the environment

The environment extension that carries the developments of the internal language checked in one
module to the modules importing it, each development under its name and each theorem as the list
of natural numbers {name}`GebTests.Prototypes.FreeTopos.Stored.thmToNats` gives. The module is
packaging: Lean's persistent environment extensions depend on {lit}`Classical.choice`, so that it
is admitted to {lit}`GebMeta.classicalAllowedModules`, while the encoding it stores is held to
the strict set in {lit}`Stored`.

## Main definitions

* {lit}`developments` — the stored developments, by name.
* {lit}`store`, {lit}`stored` — storing a development's theorems, and retrieving them.

## Tags

internal language, development, environment extension, test
-/

set_option doc.verso true

@[expose] public section

namespace GebTests.Prototypes.FreeTopos.Stored

open Geb Geb.FreeTopos
open Internal (Thm)

/-- The stored developments: each with its name, its theorems with theirs, each stored as a list
of natural numbers. -/
initialize developments :
    Lean.SimplePersistentEnvExtension (String × List (String × List ℕ))
      (List (String × List (String × List ℕ))) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun s e ↦ e :: s
    addImportedFn := fun as ↦ as.foldl (fun acc a ↦ a.toList ++ acc) [] }

/-- The storing of a development's theorems under a name. -/
def store (name : String) (as : List (String × Thm)) : Lean.Elab.Command.CommandElabM Unit :=
  Lean.modifyEnv (developments.addEntry · (name, as.map fun (n, a) ↦ (n, thmToNats a)))

/-- The theorems of the development stored under a name, where every one reads back. -/
def stored (name : String) : Lean.Elab.Command.CommandElabM (Option (List (String × Thm))) := do
  pure (((developments.getState (← Lean.getEnv)).lookup name).bind fun as ↦
    as.mapM fun (n, ns) ↦ (thmOfNats ns).map (n, ·))

end GebTests.Prototypes.FreeTopos.Stored

end
