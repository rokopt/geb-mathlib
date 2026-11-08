/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.MarkupVerso -- shake: keep
public meta import Geb.Prototypes.Kernel.MarkupVerso -- shake: keep
public import GebTests.Prototypes.Kernel.Markup -- shake: keep
public meta import GebTests.Prototypes.Kernel.Markup -- shake: keep

set_option doc.verso true in
/-!
# Markup of comments as Verso reads it

Verso's parser in Lean's core, with the tokens of the environment of this module, reads every
text the recorded subset admits ({lit}`Geb.Kernel.Markup.Tests.accepted`) to the blocks the subset
reads.

## Main definitions

* {lit}`versoAgrees` — whether Verso's parser reads a text to the subset's blocks.

## Tags

documentation, markup, Verso, parser, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Markup.Tests

/-- Whether Verso's parser, with the tokens of an environment, reads a text to the blocks the
subset reads. -/
def versoAgrees (env : Lean.Environment) (t : String) : Bool :=
  match versoBlocks env t, prose t with
  | .ok a, .ok b => a == b
  | _, _ => false

-- Verso's parser reads every admitted text to the subset's blocks
run_cmd do
  let env ← Lean.getEnv
  for t in accepted do
    unless versoAgrees env t do
      Lean.throwError m!"Verso reads {repr t} as {repr (versoBlocks env t)}, the subset as \
        {repr (prose t)}"

end Geb.Kernel.Markup.Tests

end
