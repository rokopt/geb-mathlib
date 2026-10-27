/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebTests.Prototypes.InteractionNet.CompilerGraph
public meta import GebTests.Prototypes.InteractionNet.CompilerGraph -- shake: keep
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Larger recursive graph executions

The five-node examples exercise nested recursion through the finite graph compiler and
partner-array runtime. They run separately from the routine three-node regressions because
the prototype's current indexing and compaction costs make these executions much slower.

## Tags

interaction net, graph runtime, recursion, slow test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Tests.CompilerGraph

open Geb.Kernel

#guard runText 10000 Geb.Kernel.Tests.size.toList
  (RoseTree.node 1 [leaf 2, RoseTree.node 3 [leaf 4, leaf 5]]) = some (leaf 5)
#guard runText 20000 Geb.Kernel.Tests.mirror.toList
  (RoseTree.node 1 [leaf 2, RoseTree.node 3 [leaf 4, leaf 5]]) =
    some (RoseTree.node 1 [RoseTree.node 3 [leaf 5, leaf 4], leaf 2])

end Geb.InteractionNet.Tests.CompilerGraph

end
