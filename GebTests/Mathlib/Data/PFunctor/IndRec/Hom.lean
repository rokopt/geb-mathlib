/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Hom

/-!
# Tests for the homset of IR codes

The five clauses of `IR.Hom` (Definition 8 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]) are checked to reduce
definitionally; `IR.sigmaPush`, `IR.deltaEmptyPush`, `IR.mprecomp`,
`IR.msigmaPush`, and `IR.deltaNavBase`/`IR.deltaNav` are exercised at
concrete instantiations. `IR.id` is checked at each code constructor
(the `ι` check reduces because that homset is a subsingleton); a named
definition built from `IR.id` gives the `GebMeta` axiom linter a
declaration to inspect.

## Tags

inductive-recursive, morphism, homset, category
-/

@[expose] public section

open IndRec IndRec.IR

universe uA uB uI uO

-- The five `IR.Hom` clauses (Definition 8) reduce definitionally.

example (I : Type uI) (O : Type uO) (o o' : O) :
    IR.Hom.{uA, uB, uI, uO} I O (iota I O o) (iota I O o')
      = ULift.{max uA uB uI} (PLift (o = o')) := rfl

example (I : Type uI) (O : Type uO) (o : O) (A : Type (max uA uB))
    (K : A → IR.{max uA uB, uB, uI, uO} I O) :
    IR.Hom I O (iota I O o) (sigma I O A K)
      = Σ a, IR.Hom I O (iota I O o) (K a) := rfl

example (I : Type uI) (O : Type uO) (o : O) (B : Type uB)
    (K : (B → I) → IR.{max uA uB, uB, uI, uO} I O) :
    IR.Hom.{uA, uB, uI, uO} I O (iota I O o) (delta I O B K)
      = Σ e : B → PEmpty.{1}, IR.Hom I O (iota I O o) (K (fun b => (e b).elim))
    := rfl

example (I : Type uI) (O : Type uO) (A : Type (max uA uB))
    (K : A → IR.{max uA uB, uB, uI, uO} I O) (g' : IR I O) :
    IR.Hom I O (sigma I O A K) g' = ∀ a, IR.Hom I O (K a) g' := rfl

example (I : Type uI) (O : Type uO) (B : Type uB)
    (K : (B → I) → IR.{max uA uB, uB, uI, uO} I O) (g' : IR I O) :
    IR.Hom I O (delta I O B K) g'
      = ∀ i : B → I, IR.Hom I O (K i) (IR.precomp I O B i g') := rfl

-- `IR.sigmaPush` injects a `Hom` into the `a' = true` summand of a
-- `sigma`-code (which is the codomain here; the domain is `ι`). A
-- typecheck-only sample: `sigmaPush` is defined through `IndRec.IR.rec`,
-- whose propositional computation rule is not yet stated (see the `IR`
-- `Basic` module docstring, Implementation notes), so the result does
-- not reduce definitionally against an independently-built witness; the
-- check exercises the construction's type correctness, not its value.

example :
    IR.Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
      (sigma PUnit PUnit Bool (fun _ => iota PUnit PUnit PUnit.unit)) :=
  sigmaPush PUnit PUnit (iota PUnit PUnit PUnit.unit) Bool
    (fun _ => iota PUnit PUnit PUnit.unit) true (ULift.up (PLift.up rfl))

-- `IR.deltaEmptyPush` injects a `Hom` into an `iota`-domain `delta`-code
-- over an empty direction witness (`PEmpty → PEmpty`). A typecheck-only
-- sample, for the same reason as the `sigmaPush` sample above.

example :
    IR.Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
      (delta PUnit PUnit PEmpty (fun _ => iota PUnit PUnit PUnit.unit)) :=
  deltaEmptyPush PUnit PUnit (iota PUnit PUnit PUnit.unit) PEmpty PEmpty.elim
    (fun _ => iota PUnit PUnit PUnit.unit) (ULift.up (PLift.up rfl))

-- `IR.mprecomp` at the empty stack is the identity code.

example (o : PUnit) :
    mprecomp PUnit PUnit ([] : List (SupObj.{uB, uI} PUnit)) (iota PUnit PUnit o)
      = iota PUnit PUnit o := rfl

-- `IR.mprecomp` at a singleton stack is one `IR.precomp`.

example (γ : IR.{max uA uB, uB, uI, uO} PUnit PUnit) (Q : Type uB) (i : Q → PUnit) :
    mprecomp PUnit PUnit [(⟨Q, i⟩ : SupObj.{uB, uI} PUnit)] γ = IR.precomp PUnit PUnit Q i γ :=
  rfl

-- `IR.mprecomp` fixes an `iota` code at an arbitrary stack.

example (o : PUnit) (Q : Type uB) (i : Q → PUnit) :
    mprecomp PUnit PUnit [(⟨Q, i⟩ : SupObj.{uB, uI} PUnit)] (iota PUnit PUnit o)
      = iota PUnit PUnit o :=
  mprecomp_iota PUnit PUnit [(⟨Q, i⟩ : SupObj.{uB, uI} PUnit)] o

-- `IR.mprecomp` over a two-element stack composes the two `IR.precomp`s,
-- exercising `List.foldl` beyond one step.

example (γ : IR.{max uA uB, uB, uI, uO} PUnit PUnit) (a b : SupObj.{uB, uI} PUnit) :
    mprecomp PUnit PUnit [a, b] γ
      = IR.precomp PUnit PUnit b.1 b.2 (IR.precomp PUnit PUnit a.1 a.2 γ) := rfl

-- `IR.msigmaPush` at the empty stack agrees with `IR.sigmaPush`.

example :
    msigmaPush.{0, 0, 0, 0} PUnit PUnit (iota PUnit PUnit PUnit.unit) Bool
        (fun _ => iota PUnit PUnit PUnit.unit) true [] (ULift.up (PLift.up rfl) :
          IR.Hom PUnit PUnit (iota PUnit PUnit PUnit.unit) (iota PUnit PUnit PUnit.unit))
      = sigmaPush PUnit PUnit (iota PUnit PUnit PUnit.unit) Bool
          (fun _ => iota PUnit PUnit PUnit.unit) true (ULift.up (PLift.up rfl) :
            IR.Hom PUnit PUnit (iota PUnit PUnit PUnit.unit) (iota PUnit PUnit PUnit.unit)) :=
  rfl

-- `IR.deltaNav` at the empty stack agrees, up to the `mprecomp_snoc`
-- transport, with `IR.deltaNavBase`: a typecheck-only sample confirming
-- the transported nil case is well-formed at `IR.deltaNavBase`'s type.

example (Bout : Type uB) (iout : Bout → PUnit) (Bin : Type uB)
    (K : (Bin → PUnit) → IR.{max uA uB, uB, uI, uO} PUnit PUnit) (g : Bin → Bout)
    (f : Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
      (IR.precomp PUnit PUnit Bout iout (K (iout ∘ g)))) :
    Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
      (IR.precomp PUnit PUnit Bout iout (delta PUnit PUnit Bin K)) :=
  deltaNavBase PUnit PUnit (iota PUnit PUnit PUnit.unit) Bout iout Bin K g f

example (Bout : Type uB) (iout : Bout → PUnit) (Bin : Type uB)
    (K : (Bin → PUnit) → IR.{max uA uB, uB, uI, uO} PUnit PUnit) (g : Bin → Bout)
    (f : Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
      (mprecomp PUnit PUnit [(⟨Bout, iout⟩ : SupObj.{uB, uI} PUnit)] (K (iout ∘ g)))) :
    Hom PUnit PUnit (iota PUnit PUnit PUnit.unit)
      (mprecomp PUnit PUnit [(⟨Bout, iout⟩ : SupObj.{uB, uI} PUnit)] (delta PUnit PUnit Bin K)) :=
  deltaNav PUnit PUnit (iota PUnit PUnit PUnit.unit) Bout iout Bin K g [] f

-- `IR.id` at the constant (`iota`) code equals the reflexivity witness.
-- The `ι` homset `ULift (PLift (o = o))` is a subsingleton, so this
-- `rfl` holds for any inhabitant; it does not witness that the
-- `rec`-driven `id` reduces (that needs `IR.rec`'s computation rule).

example (I : Type uI) (O : Type uO) (o : O) :
    IR.id.{uA, uB, uI, uO} I O (iota I O o)
      = (ULift.up (PLift.up rfl) : IR.Hom.{uA, uB, uI, uO} I O (iota I O o) (iota I O o)) := rfl

-- `IR.id` typechecks at the dependent-sum and dependent-product codes.

example (I : Type uI) (O : Type uO) (A : Type (max uA uB))
    (K : A → IR.{max uA uB, uB, uI, uO} I O) :
    IR.Hom I O (sigma I O A K) (sigma I O A K) := IR.id I O (sigma I O A K)

example (I : Type uI) (O : Type uO) (B : Type uB)
    (K : (B → I) → IR.{max uA uB, uB, uI, uO} I O) :
    IR.Hom I O (delta I O B K) (delta I O B K) := IR.id I O (delta I O B K)

/-- An `IR.id` instance at a concrete code, for the `GebMeta` axiom
linter to inspect. -/
def idSample : IR.Hom PUnit PUnit (iota PUnit PUnit PUnit.unit) (iota PUnit PUnit PUnit.unit) :=
  IR.id PUnit PUnit (iota PUnit PUnit PUnit.unit)
