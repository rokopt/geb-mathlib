/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Bibliography
import Geb.Mathlib.Data.W.Basic

/-! # W-types chapter -/

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "W-types and term algebras" =>

A W-type is the type of well-founded trees over a signature: a
type of shapes together with a family assigning each shape its
branching. mathlib's {name}`WType` provides the type and its fold
{name}`WType.elim`, the morphism into an algebra of the polynomial
endofunctor `X ↦ Σ a, β a → X`. The development adds the two laws
mathlib does not state: the computation rule {name}`WType.elim_mk`
and the uniqueness {name}`WType.elim_unique`. Together they make
the W-type the initial algebra of that endofunctor, stated
concretely.

{name}`WType.para` generalises the fold to a paramorphism, whose
step additionally sees each node's children as subtrees paired
with their folded values {citep Meertens1992}[]:

```signature
WType.para {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ
```

Its computation rule is {name}`WType.para_mk`: the paramorphism at
a node applies the step to the node's children paired with their
own paramorphisms.

The module itself follows, rendered from its source: its module
docstring as the prose of the section, and each declaration beside
its docstring.

{includeLiterate "." Geb.Mathlib.Data.W.Basic "The module Geb.Mathlib.Data.W.Basic" (level := 1)}
