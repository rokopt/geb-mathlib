/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.Oitavem.Syntax
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Sig
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# The bundle signature of Oitavem-coded bitstreams

A finitary slice polynomial signature whose W-trees at the root index are
Oitavem expressions of one normal and no safe argument under a single root
node: the finitary analogue of {lit}`Geb.BitStream.WConstruction.bundleSig`,
whose root has one child for each depth. Here the root has one child, the
expression, and the infinitely many observations of a stream are the values
of that expression at the depths.

The shapes are the root and the shapes of {name}`Geb.Oitavem.sig`. Every
shape is coded uniformly: a set bit, which is the numeral zero, five tag
bits naming the shape's constructor, and eight numerals, the arity a node
produces, the arity it requires of its first child, the arity it requires
of its other children, its number of children, and one parameter. A shape's
constructor determines the numerals from its parameters by a table of atomic
constraints, each an equality, a successor relation, an order or a bound
between two numerals or a numeral and a small constant; the decoder checks
the table and builds the shape from the numerals. The redundancy of the
numerals is what makes a child's arity readable from its own label without
a dispatch on the child's constructor.

# Main definitions

* {lit}`Kind`, {lit}`kind`, {lit}`tag`, {lit}`readTag` — the constructors,
  their five tag bits, and the reading of a tag.
* {lit}`fields`, {lit}`Atom`, {lit}`atoms`, {lit}`check`, {lit}`mk`,
  {lit}`build` — the numerals of a shape, the atomic constraints, the table
  at each kind, the check of the table, and the shape built from numerals.
* {lit}`code`, {lit}`decode` — the code of a shape and the decoder.
* {lit}`sig`, {lit}`finitary`, {lit}`coded` — the signature, the explicit
  enumeration of its directions, and the coded signature.

# Main statements

* {lit}`readTag_tag`, {lit}`tag_of_readTag` — the tag is read back, and a
  tag that reads is the tag of what it reads to.
* {lit}`build_kind_fields`, {lit}`kind_fields_of_build` — the table holds at
  every shape's numerals, and a shape built from numerals has them.
* {lit}`decode_code`, {lit}`code_of_decode` — the decoder inverts the code.
* {lit}`card_eq`, {lit}`q_eq`, {lit}`rCurried_dir_eq` — the count of a
  shape's directions, the arity it produces and the arities it requires are
  its numerals.

# References

* {cite}`Oitavem2010`, Definition 3.1.

# Tags

bitstream, M-type, slice polynomial functor, coded signature, logspace
-/

set_option doc.verso true

namespace Geb.BitStream.Oitavem

open Geb.Oitavem (Shape Initial Direction childArity resultArity)
open Geb.SizeBounded.Logspace.WTree (CodedSig)
open Geb.SizeBounded.Logspace.WTree.Numeral (natCode readNatCode readNatCode_natCode_append
  readNatCode_eq_some)

public section

/-- The constructors of the shapes: the root, the twelve initial function
families, and the four schemes. -/
inductive Kind
  | root | zero | proj | succ | pred | iterPred | numericSucc | numericPred | numericSub
  | length | last | cond | product | comp | safeRec | concatRec | logTransition
  deriving DecidableEq, Repr

/-- The constructor of a shape. -/
@[expose] def kind : Option Shape → Kind
  | none => .root
  | some (.initial (.zero _)) => .zero
  | some (.initial (.proj _ _)) => .proj
  | some (.initial (.succ _)) => .succ
  | some (.initial .pred) => .pred
  | some (.initial .iterPred) => .iterPred
  | some (.initial .numericSucc) => .numericSucc
  | some (.initial .numericPred) => .numericPred
  | some (.initial .numericSub) => .numericSub
  | some (.initial .length) => .length
  | some (.initial .last) => .last
  | some (.initial .cond) => .cond
  | some (.initial .product) => .product
  | some (.comp _ _ _) => .comp
  | some (.safeRec _) => .safeRec
  | some (.concatRec _) => .concatRec
  | some (.logTransition _) => .logTransition

/-- The five tag bits of a constructor: the first set for the root alone, the
other four the index of a shape's constructor. -/
@[expose] def tag : Kind → List Bool
  | .root => [true, false, false, false, false]
  | .zero => [false, false, false, false, false]
  | .proj => [false, false, false, false, true]
  | .succ => [false, false, false, true, false]
  | .pred => [false, false, false, true, true]
  | .iterPred => [false, false, true, false, false]
  | .numericSucc => [false, false, true, false, true]
  | .numericPred => [false, false, true, true, false]
  | .numericSub => [false, false, true, true, true]
  | .length => [false, true, false, false, false]
  | .last => [false, true, false, false, true]
  | .cond => [false, true, false, true, false]
  | .product => [false, true, false, true, true]
  | .comp => [false, true, true, false, false]
  | .safeRec => [false, true, true, false, true]
  | .concatRec => [false, true, true, true, false]
  | .logTransition => [false, true, true, true, true]

/-- The constructor with a tag. -/
@[expose] def readTag : List Bool → Option Kind
  | [true, false, false, false, false] => some .root
  | [false, false, false, false, false] => some .zero
  | [false, false, false, false, true] => some .proj
  | [false, false, false, true, false] => some .succ
  | [false, false, false, true, true] => some .pred
  | [false, false, true, false, false] => some .iterPred
  | [false, false, true, false, true] => some .numericSucc
  | [false, false, true, true, false] => some .numericPred
  | [false, false, true, true, true] => some .numericSub
  | [false, true, false, false, false] => some .length
  | [false, true, false, false, true] => some .last
  | [false, true, false, true, false] => some .cond
  | [false, true, false, true, true] => some .product
  | [false, true, true, false, false] => some .comp
  | [false, true, true, false, true] => some .safeRec
  | [false, true, true, true, false] => some .concatRec
  | [false, true, true, true, true] => some .logTransition
  | _ => none

/-- The tag of a constructor reads back. -/
theorem readTag_tag (k : Kind) : readTag (tag k) = some k := by cases k <;> rfl

/-- Five bits that read to a constructor are its tag. -/
theorem tag_of_readTag (b0 b1 b2 b3 b4 : Bool) (k : Kind)
    (h : readTag [b0, b1, b2, b3, b4] = some k) : [b0, b1, b2, b3, b4] = tag k := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases k <;>
    first | rfl | (simp only [readTag, reduceCtorEq, Option.some.injEq] at h)

/-- The tag has five bits. -/
theorem length_tag (k : Kind) : (tag k).length = 5 := by cases k <;> rfl

/-- The eight numerals of a shape: the arity it produces, normal then safe;
the arity it requires of its first child; the arity it requires of its other
children; its number of children; and one parameter. -/
abbrev Fields := Fin 8 → ℕ

/-- The parameter of an initial function beyond its arity: the index of a
projection, the bit of a successor. -/
@[expose] def initialParam : Initial → ℕ
  | .proj _ i => i
  | .succ b => b.toNat
  | _ => 0

/-- The numerals of a shape. -/
@[expose] def fields : Option Shape → Fields
  | none => ![0, 0, 1, 0, 0, 0, 1, 0]
  | some (.initial p) => ![p.arity, 0, 0, 0, 0, 0, 0, initialParam p]
  | some (.comp n m b) => ![n, b.toNat, m, b.toNat, n, 0, m + 1, 0]
  | some (.safeRec n) => ![n + 1, 0, n, 0, n + 1, 1, 3, 0]
  | some (.concatRec n) => ![n + 1, 0, n, 0, n + 1, 0, 3, 0]
  | some (.logTransition n) => ![n + 2, 1, n + 1, 0, 0, 0, 1, n]

/-- An atomic constraint on the numerals: two are equal, one is a small
constant, one is the successor of another, one is below another, or one is
a bit. -/
inductive Atom
  | eq (i j : Fin 8)
  | const (i : Fin 8) (c : ℕ)
  | succ (i j : Fin 8)
  | lt (i j : Fin 8)
  | bit (i : Fin 8)
  deriving DecidableEq, Repr

/-- Whether a constraint holds at numerals. -/
@[expose] def Atom.holds (fs : Fields) : Atom → Bool
  | .eq i j => decide (fs i = fs j)
  | .const i c => decide (fs i = c)
  | .succ i j => decide (fs j = fs i + 1)
  | .lt i j => decide (fs i < fs j)
  | .bit i => decide (fs i ≤ 1)

/-- The constraints setting the listed numerals to zero. -/
@[expose] def zeros (is : List (Fin 8)) : List Atom := is.map fun i ↦ .const i 0

/-- The constraints of an initial function producing a fixed arity, with no
child and no parameter. -/
@[expose] def initialAtoms (arity : ℕ) : List Atom :=
  .const 0 arity :: zeros [1, 2, 3, 4, 5, 6, 7]

/-- The table of constraints at each constructor. -/
@[expose] def atoms : Kind → List Atom
  | .root => [.const 0 0, .const 1 0, .const 2 1, .const 3 0, .const 4 0, .const 5 0,
      .const 6 1, .const 7 0]
  | .zero => zeros [1, 2, 3, 4, 5, 6, 7]
  | .proj => .lt 7 0 :: zeros [1, 2, 3, 4, 5, 6]
  | .succ => .const 0 1 :: .bit 7 :: zeros [1, 2, 3, 4, 5, 6]
  | .pred | .numericSucc | .numericPred | .length | .last => initialAtoms 1
  | .iterPred | .numericSub | .product => initialAtoms 2
  | .cond => initialAtoms 3
  | .comp => [.bit 1, .eq 3 1, .eq 4 0, .const 5 0, .succ 2 6, .const 7 0]
  | .safeRec => [.succ 2 0, .const 1 0, .const 3 0, .eq 4 0, .const 5 1, .const 6 3, .const 7 0]
  | .concatRec =>
      [.succ 2 0, .const 1 0, .const 3 0, .eq 4 0, .const 5 0, .const 6 3, .const 7 0]
  | .logTransition =>
      [.succ 7 2, .succ 2 0, .const 1 1, .const 3 0, .const 4 0, .const 5 0, .const 6 1]

/-- The check of the table at numerals. -/
@[expose] def check (k : Kind) (fs : Fields) : Bool := (atoms k).all (Atom.holds fs)

/-- The shape a constructor builds from numerals, meaningful when the table
holds. -/
@[expose] def mk (k : Kind) (fs : Fields) : Option Shape :=
  match k with
  | .root => none
  | .zero => some (.initial (.zero (fs 0)))
  | .proj => some (.initial (if h : fs 7 < fs 0 then .proj (fs 0) ⟨fs 7, h⟩ else .zero (fs 0)))
  | .succ => some (.initial (.succ (fs 7 == 1)))
  | .pred => some (.initial .pred)
  | .iterPred => some (.initial .iterPred)
  | .numericSucc => some (.initial .numericSucc)
  | .numericPred => some (.initial .numericPred)
  | .numericSub => some (.initial .numericSub)
  | .length => some (.initial .length)
  | .last => some (.initial .last)
  | .cond => some (.initial .cond)
  | .product => some (.initial .product)
  | .comp => some (.comp (fs 0) (fs 2) (fs 1 == 1))
  | .safeRec => some (.safeRec (fs 2))
  | .concatRec => some (.concatRec (fs 2))
  | .logTransition => some (.logTransition (fs 7))

/-- The shape with a constructor and numerals: built when the table holds. -/
@[expose] def build (k : Kind) (fs : Fields) : Option (Option Shape) :=
  if check k fs then some (mk k fs) else none

/-- A bit read back from its number. -/
theorem toNat_beq_one : ∀ n : ℕ, n ≤ 1 → (n == 1).toNat = n
  | 0, _ => rfl
  | 1, _ => rfl
  | _ + 2, h => absurd h (by omega)

/-- The table holds at every shape's numerals, and building recovers the
shape. -/
theorem build_kind_fields (a : Option Shape) : build (kind a) (fields a) = some a := by
  rcases a with _ | c
  · rfl
  cases c with
  | initial p =>
    cases p with
    | proj n i => simp [build, kind, check, atoms, zeros, Atom.holds, fields, mk, initialParam, i.2]
    | succ b => cases b <;> rfl
    | _ => rfl
  | comp n m b =>
    cases b <;> simp [build, kind, check, atoms, Atom.holds, fields, mk]
  | safeRec n => simp [build, kind, check, atoms, Atom.holds, fields, mk]
  | concatRec n => simp [build, kind, check, atoms, Atom.holds, fields, mk]
  | logTransition n => simp [build, kind, check, atoms, Atom.holds, fields, mk]

/-- Numerals agreeing at each of the eight positions are equal. -/
theorem Fields.ext8 (f g : Fields) (h0 : f 0 = g 0) (h1 : f 1 = g 1) (h2 : f 2 = g 2)
    (h3 : f 3 = g 3) (h4 : f 4 = g 4) (h5 : f 5 = g 5) (h6 : f 6 = g 6) (h7 : f 7 = g 7) :
    f = g := by
  funext i
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3
  | ⟨4, _⟩ => exact h4
  | ⟨5, _⟩ => exact h5
  | ⟨6, _⟩ => exact h6
  | ⟨7, _⟩ => exact h7
  | ⟨_ + 8, h⟩ => exact absurd h (by omega)

/-- A shape built from numerals has that constructor and those numerals. -/
theorem kind_fields_of_build {k : Kind} {fs : Fields} {a : Option Shape}
    (h : build k fs = some a) : kind a = k ∧ fields a = fs := by
  unfold build at h
  split at h
  · rename_i hc
    obtain rfl := Option.some.inj h
    cases k <;>
      simp only [check, atoms, initialAtoms, zeros, List.map, List.all_cons, List.all_nil,
        Atom.holds, Bool.and_eq_true, decide_eq_true_eq, and_true] at hc
    case proj =>
      refine ⟨by simp only [mk, kind, dite_eq_left hc.1],
        Fields.ext8 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
        simp only [mk, fields, initialParam, Initial.arity, Matrix.cons_val, dite_eq_left hc.1] <;>
        omega
    case succ =>
      refine ⟨rfl, Fields.ext8 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
        simp only [mk, fields, initialParam, Initial.arity, Matrix.cons_val] <;>
        first | omega | exact toNat_beq_one _ hc.2.1
    case comp =>
      refine ⟨rfl, Fields.ext8 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
        simp only [mk, fields, Matrix.cons_val] <;>
        first | omega | exact toNat_beq_one _ hc.1 | (rw [hc.2.1]; exact toNat_beq_one _ hc.1)
    all_goals
      refine ⟨rfl, Fields.ext8 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩ <;>
        simp only [mk, fields, initialParam, Initial.arity, Matrix.cons_val] <;> omega
  · cases h

/-- Numerals from a list, zero beyond its end. -/
@[expose] def ofList (l : List ℕ) : Fields := fun i ↦ l.getD i 0

/-- A list of eight numbers is recovered from its numerals. -/
theorem ofFn_ofList (l : List ℕ) (h : l.length = 8) : List.ofFn (ofList l) = l := by
  refine List.ext_getElem (by rw [List.length_ofFn, h]) fun i h1 h2 ↦ ?_
  rw [List.getElem_ofFn]
  simp only [ofList, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- Numerals are recovered from their list. -/
theorem ofList_ofFn (fs : Fields) : ofList (List.ofFn fs) = fs := by
  funext i
  simp only [ofList, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.2, dite_true,
    Option.getD_some]

/-- The codes of a list of numbers, in order. -/
@[expose] def codes (l : List ℕ) : List Bool := l.flatMap natCode

/-- The code of a shape: a set bit, the tag of its constructor and the codes
of its numerals. -/
@[expose] def code (a : Option Shape) : List Bool :=
  true :: tag (kind a) ++ codes (List.ofFn (fields a))

/-- Read a number of coded numbers, with the unconsumed suffix. -/
@[expose] def readFields : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, w => some ([], w)
  | n + 1, w => (readNatCode w).bind fun p ↦ (readFields n p.2).map fun q ↦ (p.1 :: q.1, q.2)

/-- The codes of a list read back with the suffix intact. -/
theorem readFields_codes_append : ∀ (l : List ℕ) (rest : List Bool),
    readFields l.length (codes l ++ rest) = some (l, rest)
  | [], rest => rfl
  | n :: l, rest => by
    simp only [List.length_cons, readFields, codes, List.flatMap_cons, List.append_assoc,
      readNatCode_natCode_append, Option.bind_some]
    rw [show List.flatMap natCode l = codes l from rfl, readFields_codes_append l rest]
    rfl

/-- A successful read of numbers identifies their codes and the suffix. -/
theorem readFields_eq_some : ∀ (n : ℕ) (w : List Bool) (l : List ℕ) (rest : List Bool),
    readFields n w = some (l, rest) → l.length = n ∧ w = codes l ++ rest
  | 0, w, l, rest, h => by
    simp only [readFields, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | n + 1, w, l, rest, h => by
    simp only [readFields] at h
    cases hr : readNatCode w with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr, Option.bind_some] at h
      cases hq : readFields n p.2 with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, hw⟩ := readFields_eq_some n p.2 q.1 q.2 hq
        refine ⟨by rw [List.length_cons, hl], ?_⟩
        rw [readNatCode_eq_some w p.1 p.2 hr, hw]
        simp only [codes, List.flatMap_cons, List.append_assoc]

/-- The decoder: a set bit, a tag that reads, eight coded numbers filling the
rest of the word, and the table holding at them. -/
@[expose] def decode : List Bool → Option (Option Shape)
  | true :: b0 :: b1 :: b2 :: b3 :: b4 :: rest =>
    (readTag [b0, b1, b2, b3, b4]).bind fun k ↦ (readFields 8 rest).bind fun p ↦
      if p.2 = [] then build k (ofList p.1) else none
  | _ => none

/-- Decoding a code built from a constructor and numerals builds the shape. -/
theorem decode_tag_codes (k : Kind) (fs : Fields) :
    decode (true :: tag k ++ codes (List.ofFn fs)) = build k fs := by
  have hr := readFields_codes_append (List.ofFn fs) []
  rw [List.append_nil, List.length_ofFn] at hr
  cases k <;> simp only [tag, List.cons_append, List.nil_append, decode, readTag, Option.bind_some,
    hr, ite_true, ofList_ofFn]

/-- The decoder inverts the code. -/
theorem decode_code (a : Option Shape) : decode (code a) = some a := by
  rw [code, decode_tag_codes, build_kind_fields]

/-- A word that decodes is the code of what it decodes to. -/
theorem code_of_decode {w : List Bool} {a : Option Shape} (h : decode w = some a) : code a = w := by
  match w, h with
  | true :: b0 :: b1 :: b2 :: b3 :: b4 :: rest, h =>
    simp only [decode] at h
    cases hk : readTag [b0, b1, b2, b3, b4] with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk, Option.bind_some] at h
      cases hf : readFields 8 rest with
      | none => rw [hf] at h; cases h
      | some p =>
        rw [hf, Option.bind_some] at h
        by_cases he : p.2 = []
        · rw [ite_eq_left he] at h
          obtain ⟨hk', hf'⟩ := kind_fields_of_build h
          obtain ⟨hl, hw⟩ := readFields_eq_some 8 rest p.1 p.2 hf
          rw [code, hk', hf', ofFn_ofList p.1 hl, ← tag_of_readTag b0 b1 b2 b3 b4 k hk, hw, he,
            List.append_nil]
          rfl
        · rw [ite_eq_right he] at h
          cases h

/-- The directions of a shape: one at the root, those of Logs otherwise. -/
@[expose, reducible] def Dir : Option Shape → Type
  | none => Unit
  | some a => Direction a

/-- The signature: the root, producing the root index and requiring of its
child one normal and no safe argument; and the shapes of Logs, over the
arities Logs assigns. -/
@[expose] def sig : SlicePFunctor (Option (ℕ × ℕ)) (Option (ℕ × ℕ)) where
  A := Option Shape
  B := Dir
  r x := match x with
    | ⟨none, _⟩ => some (1, 0)
    | ⟨some a, d⟩ => some (childArity a d)
  q a := a.map resultArity

/-- The single direction of a root or a log-transition. -/
@[expose] def unitEquiv : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv _ := rfl
  right_inv i := Fin.ext (by omega)

/-- The directions of a recursion in order: the base, the step on a
{lit}`false` bit, the step on a {lit}`true` bit. -/
@[expose] def recEquiv : Unit ⊕ Bool ≃ Fin 3 where
  toFun
    | .inl _ => 0
    | .inr false => 1
    | .inr true => 2
  invFun j := match j with
    | ⟨0, _⟩ => .inl ()
    | ⟨1, _⟩ => .inr false
    | ⟨_ + 2, _⟩ => .inr true
  left_inv x := by rcases x with _ | _ | _ <;> rfl
  right_inv j := by
    match j with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

/-- The directions enumerated: the root's one; none at an initial function;
the head then the arguments of a composition; the base then the steps of a
recursion; the one of a log-transition. -/
@[expose, instance_reducible] def finitary : sig.toPFunctor.Finitary
  | none => @FinEnum.mk Unit 1 unitEquiv inferInstance
  | some (.initial _) => @FinEnum.mk (Fin 0) 0 (Equiv.refl (Fin 0)) inferInstance
  | some (.comp _ m _) =>
    @FinEnum.mk (Unit ⊕ Fin m) (m + 1) (Geb.SizeBounded.Logspace.WTree.Sig.compEquiv m)
      inferInstance
  | some (.safeRec _) => @FinEnum.mk (Unit ⊕ Bool) 3 recEquiv inferInstance
  | some (.concatRec _) => @FinEnum.mk (Unit ⊕ Bool) 3 recEquiv inferInstance
  | some (.logTransition _) => @FinEnum.mk Unit 1 unitEquiv inferInstance

/-- The enumeration, as an instance. -/
instance instFinitary : sig.toPFunctor.Finitary := finitary

/-- The bundle signature as a coded signature. -/
@[expose] def coded : CodedSig (Option (ℕ × ℕ)) where
  P := sig
  finitary := finitary
  code := code
  decode := decode
  decode_code := decode_code
  code_of_decode := code_of_decode

/-- The number of a shape's directions is its seventh numeral. -/
theorem card_eq : ∀ a, coded.card a = fields a 6
  | none => rfl
  | some (.initial _) => rfl
  | some (.comp _ _ _) => rfl
  | some (.safeRec _) => rfl
  | some (.concatRec _) => rfl
  | some (.logTransition _) => rfl

/-- The arity a shape of Logs produces is its first two numerals. -/
theorem resultArity_eq : ∀ c : Shape, resultArity c = (fields (some c) 0, fields (some c) 1)
  | .initial _ => rfl
  | .comp _ _ _ => rfl
  | .safeRec _ => rfl
  | .concatRec _ => rfl
  | .logTransition _ => rfl

/-- The index a shape produces: the root index at the root, the arity a shape
of Logs produces otherwise. -/
theorem q_eq : ∀ a, sig.q a = a.map fun c ↦ (fields (some c) 0, fields (some c) 1)
  | none => rfl
  | some c => congrArg some (resultArity_eq c)

/-- The arity a shape requires at the direction at a position: its third and
fourth numerals at the first position, its fifth and sixth after. -/
theorem rCurried_dir_eq (a : Option Shape) (j : ℕ) (h : j < coded.card a) :
    sig.rCurried a (coded.dir a ⟨j, h⟩) =
      some (if j = 0 then (fields a 2, fields a 3) else (fields a 4, fields a 5)) := by
  cases a with
  | none =>
    change j < 1 at h
    obtain rfl : j = 0 := by omega
    rfl
  | some c =>
    cases c with
    | initial p => exact absurd h (Nat.not_lt_zero j)
    | comp n m b =>
      change j < m + 1 at h
      cases j with
      | zero => rfl
      | succ j =>
        change sig.rCurried (some (.comp n m b))
          ((Geb.SizeBounded.Logspace.WTree.Sig.compEquiv m).symm ⟨j + 1, h⟩) = _
        rw [ite_eq_right (Nat.succ_ne_zero j)]
        rfl
    | safeRec n =>
      change j < 3 at h
      match j, h with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    | concatRec n =>
      change j < 3 at h
      match j, h with
      | 0, _ => rfl
      | 1, _ => rfl
      | 2, _ => rfl
    | logTransition n =>
      change j < 1 at h
      obtain rfl : j = 0 := by omega
      rfl

end

end Geb.BitStream.Oitavem
