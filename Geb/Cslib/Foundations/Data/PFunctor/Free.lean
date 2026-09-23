/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Init
public import Cslib.Foundations.Data.PFunctor.Free
public import Mathlib.Util.CompileInductive

set_option doc.verso true in
/-!
# Executable code for the recursor of the free monad

Supplies executable code for {name}`PFunctor.FreeM.rec`, the recursor of the free monad of a
polynomial functor, so that a definition recursing through it is computable. A fold through
{name}`PFunctor.FreeM.liftM` into a monad is computable without it, but its result cannot
depend on the term: a subterm selected by a path whose type depends on the term needs the
dependent recursor.

## Implementation notes

The code generator supports no recursor directly. {lit}`compile_inductive%` compiles the
recursor and the case analysis of an inductive type from its structure. Issuing it again where
it is already in scope fails, so a module needing the compiled recursor imports this one.

## Tags

free monad, polynomial functor, recursor, code generation
-/

set_option doc.verso true

compile_inductive% PFunctor.FreeM
