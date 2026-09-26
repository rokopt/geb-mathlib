/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Compile
public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Internal.Prove
public import Geb.Prototypes.FreeTopos.Internal.Semantics
public import Geb.Prototypes.FreeTopos.Internal.Soundness
public import Geb.Prototypes.FreeTopos.Internal.Sorting
public import Geb.Prototypes.FreeTopos.Internal.Square
public import Geb.Prototypes.FreeTopos.Internal.Substitution
public import Geb.Prototypes.FreeTopos.Internal.Syntax

set_option doc.verso true in
/-!
# The internal language of the topos

The Mitchell–Bénabou language of the free elementary topos with data objects: its terms, their
typing and compilation to the combinators, its definitions, compiled to definitions of the
combinators, and the proof that compiling a term and unfolding the combinators' definitions
agrees, in every model, with unfolding the language's definitions and compiling; its derivations
of equations, their checker and a prover, and the proof that the checker is sound.
-/

set_option doc.verso true
