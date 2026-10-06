/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import GebMirror.Kernel
public import GebMirror.Metalogic

/-!
# The Lean of Geb programs whose agreement with Lean functions is proved

One module for each such program, the Lean the bootstrap compiler emits from it, regenerated and
compared by `scripts/bootstrap.sh`. The metalogic's is a module per layer of its program, beside
the modules of `GebMirror.Metalogic.Load`, which declare the program's loading through each layer,
each step checked by the kernel; those are imported where the loading is used, not here.
-/
