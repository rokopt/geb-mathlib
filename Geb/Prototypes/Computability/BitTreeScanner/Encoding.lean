/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Cslib.Foundations.Data.PFunctor.Free
public import Mathlib.Control.Monad.Cont
public import Mathlib.Data.Nat.Bits
meta import GebMeta  -- shake: keep; supplies the cite docstring role

set_option doc.verso true

/-!
# Binary trees with bitstrings at the leaves, and their prefix encoding

The free monad of the polynomial functor {lit}`X ↦ X × X` at the type of
bitstrings: a tree is a bitstring, or a pair of trees. This module names the
type as an instance of Cslib's {name}`PFunctor.FreeM` and spells its trees as
bitstrings by a prefix code in a single pass.

A pair is spelled by the bit {lit}`true` followed by its two children's
spellings, and a leaf by the bit {lit}`false` followed by the Elias gamma code
of its bitstring's length plus one and then the bitstring itself. The gamma
code of {lit}`N ≥ 1`, from {cite}`Elias1975`, is {lit}`⌊log₂ N⌋` zeros followed
by the binary digits of {lit}`N` from the most significant, the first of which
is a one; it is a prefix code of length {lit}`2 ⌊log₂ N⌋ + 1`, so a leaf's
length costs a logarithmic number of bits rather than one bit per payload bit.
The bits at which the spelling branches are those of the recursive scheme
{cite}`Jacobson1989` § 1 states for unlabelled binary trees, {lit}`false` for
an absent subtree and {lit}`true` followed by the two subtrees' representations
for a node, two bits per node; the payload of a leaf follows its bit in place.
A tree of {lit}`p` pairs and {lit}`m` payload bits is spelled by
{lit}`2 * p + 1 + m` bits plus the gamma codes of its leaves' lengths,
{lit}`length_spell`.

## Main definitions

* {lit}`Geb.BitTreeScanner.square` — the polynomial functor {lit}`X ↦ X × X`.
* {lit}`Geb.BitTreeScanner.BitTree` — the free monad of {lit}`square` at {lit}`List Bool`.
* {lit}`Geb.BitTreeScanner.leaf`, {lit}`Geb.BitTreeScanner.pair` — the two forms of its
  trees.
* {lit}`Geb.BitTreeScanner.valueLE` — the number a list of binary digits denotes,
  least significant digit first, the inverse of {name}`Nat.bits`.
* {lit}`Geb.BitTreeScanner.gamma` — the Elias gamma code.
* {lit}`Geb.BitTreeScanner.leafBody` — the body of a leaf: the gamma code of its
  bitstring's length plus one, and the bitstring.
* {lit}`Geb.BitTreeScanner.spell` — the encoding.
* {lit}`Geb.BitTreeScanner.sumHandler`, {lit}`Geb.BitTreeScanner.pairs`,
  {lit}`Geb.BitTreeScanner.payload`, {lit}`Geb.BitTreeScanner.gammaLength` — a tree's count
  of pairs, of payload bits, and of length-code bits.

## Main statements

* {lit}`Geb.BitTreeScanner.valueLE_bits`, {lit}`Geb.BitTreeScanner.bits_valueLE` — the
  digits and their value invert each other, on the digit lists whose most
  significant digit is a one.
* {lit}`Geb.BitTreeScanner.exists_bits_eq_append_true` — a positive number's digits
  end in a one.
* {lit}`Geb.BitTreeScanner.gamma_valueLE` — the gamma code of a digit list's value,
  the form a reader of the code recovers.
* {lit}`Geb.BitTreeScanner.length_gamma` — the gamma code's length is twice the
  number of digits less one.
* {lit}`Geb.BitTreeScanner.spell_pure`, {lit}`Geb.BitTreeScanner.spell_liftBind`,
  {lit}`Geb.BitTreeScanner.spell_leaf`, {lit}`Geb.BitTreeScanner.spell_pair` — the
  encoding's equations at each constructor.
* {lit}`Geb.BitTreeScanner.pairs_pure`, {lit}`Geb.BitTreeScanner.pairs_liftBind`,
  {lit}`Geb.BitTreeScanner.payload_pure`, {lit}`Geb.BitTreeScanner.payload_liftBind`,
  {lit}`Geb.BitTreeScanner.gammaLength_pure`, {lit}`Geb.BitTreeScanner.gammaLength_liftBind`
  — the counts' equations at each constructor.
* {lit}`Geb.BitTreeScanner.length_leafBody`, {lit}`Geb.BitTreeScanner.length_spell` — the
  lengths of a leaf body and of a spelling.

## Implementation notes

The code generator does not compile {name}`PFunctor.FreeM.rec`, so
{lit}`spell` is the interpretation {name}`PFunctor.FreeM.liftM` of a tree
into the continuation monad {name}`Cont` at {lit}`List Bool`, applied to the
leaf's spelling as the final continuation: the pair handler receives the
continuation, applies it to each direction and concatenates.
{name}`PFunctor.FreeM.liftM` is structurally recursive in Cslib, so the
interpretation compiles, and its two equations reduce by {lit}`rfl`. The three
counts are the same interpretation at {lit}`ℕ`.

The gamma code is stated through mathlib's {name}`Nat.bits`, the binary digits
least significant first, reversed, and so are the lengths: the number of
digits is mathlib's {lit}`Nat.size`, which is {lit}`⌊log₂ N⌋ + 1` at
{lit}`N ≥ 1`, but that module's lemmas depend on {lit}`Classical.choice`, and
the length counts here stay choice-free by not citing them. The digit lists a
reader accumulates are least significant first, since it reads the most
significant digit first and prepends, so {lit}`valueLE` is stated on that
order and the round trip {lit}`bits_valueLE` is stated on the lists ending in
a one, which are exactly the lists {name}`Nat.bits` produces at a positive
number.

{lit}`pair` is spelled through {name}`cond` rather than {lit}`if`, so that a
pair's children reduce at the two literal directions without a decidability
instance.

## References

* {cite}`Elias1975`
* {cite}`Jacobson1989`

## Tags

binary tree, free monad, polynomial functor, prefix code, Elias gamma code,
succinct encoding
-/

@[expose] public section

namespace Geb.BitTreeScanner

/-- The polynomial functor {lit}`X ↦ X × X`: one shape with two directions. -/
abbrev square : PFunctor.{0, 0} := ⟨Unit, fun _ ↦ Bool⟩

/-- Binary trees with bitstrings at the leaves: the free monad of
{name}`square` at {lit}`List Bool`. -/
abbrev BitTree : Type := square.FreeM (List Bool)

/-- The tree that is a bitstring. -/
abbrev leaf (s : List Bool) : BitTree := .pure s

/-- The tree that is a pair, the direction {lit}`false` leading to {lit}`l` and
{lit}`true` to {lit}`r`. -/
abbrev pair (l r : BitTree) : BitTree := .liftBind () fun d ↦ cond d r l

section Gamma

/-- The number a list of binary digits denotes, least significant digit
first. -/
def valueLE (d : List Bool) : ℕ := d.foldr (fun b n ↦ Nat.bit b n) 0

/-- The empty digit list denotes zero. -/
@[simp] theorem valueLE_nil : valueLE [] = 0 := rfl

/-- A digit list denotes its head appended to the value of its tail at the
little end. -/
@[simp] theorem valueLE_cons (b : Bool) (d : List Bool) :
    valueLE (b :: d) = Nat.bit b (valueLE d) := rfl

/-- The value of a number's digits is the number. -/
theorem valueLE_bits (n : ℕ) : valueLE n.bits = n :=
  Nat.binaryRec' (motive := fun n ↦ valueLE n.bits = n) (by rw [Nat.zero_bits]; rfl)
    (fun b n h ih ↦ by rw [Nat.bits_append_bit n b h, valueLE_cons, ih]) n

/-- A digit list ending in a one denotes a positive number. -/
theorem valueLE_append_true_pos (r : List Bool) : 0 < valueLE (r ++ [true]) :=
  List.rec (motive := fun r ↦ 0 < valueLE (r ++ [true])) (by decide)
    (fun b _ ih ↦ by rw [List.cons_append, valueLE_cons, Nat.bit_val]; omega) r

/-- The digits of the value of a digit list ending in a one are that list. -/
theorem bits_valueLE (r : List Bool) : (valueLE (r ++ [true])).bits = r ++ [true] :=
  List.rec (motive := fun r ↦ (valueLE (r ++ [true])).bits = r ++ [true])
    (by rw [List.nil_append, valueLE_cons, valueLE_nil]; exact Nat.one_bits)
    (fun b r ih ↦ by
      rw [List.cons_append, valueLE_cons,
        Nat.bits_append_bit _ _ (fun h ↦ absurd h (Nat.ne_of_gt (valueLE_append_true_pos r))),
        ih]) r

/-- A positive number's digits end in a one. -/
theorem exists_bits_eq_append_true (n : ℕ) (h : 0 < n) : ∃ r, n.bits = r ++ [true] :=
  Nat.binaryRec' (motive := fun n ↦ 0 < n → ∃ r, n.bits = r ++ [true])
    (fun h ↦ absurd h (Nat.lt_irrefl 0))
    (fun b n hb ih _ ↦ by
      rw [Nat.bits_append_bit n b hb]
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [hb rfl, Nat.zero_bits]
        exact ⟨[], rfl⟩
      · obtain ⟨r, hr⟩ := ih hn
        exact ⟨b :: r, by rw [hr, List.cons_append]⟩) n h

/-- The Elias gamma code of a positive number: as many zeros as its bit length
less one, then its digits from the most significant. At zero, the empty
list. -/
def gamma (n : ℕ) : List Bool := List.replicate (n.bits.length - 1) false ++ n.bits.reverse

/-- The gamma code of the value of a digit list ending in a one: as many zeros
as the list has digits below the one, the one, and those digits reversed, which
is the form a reader of the code recovers. -/
theorem gamma_valueLE (r : List Bool) :
    gamma (valueLE (r ++ [true])) = List.replicate r.length false ++ true :: r.reverse := by
  rw [gamma, bits_valueLE, List.length_append, List.length_singleton, Nat.add_sub_cancel,
    List.reverse_append, List.reverse_singleton, List.singleton_append]

/-- The gamma code of a number has twice as many bits as the number has digits,
less one. -/
theorem length_gamma (n : ℕ) : (gamma n).length = 2 * n.bits.length - 1 := by
  rw [gamma, List.length_append, List.length_replicate, List.length_reverse]
  omega

end Gamma

/-- The body of a leaf: the gamma code of its bitstring's length plus one, then
the bitstring. -/
def leafBody (s : List Bool) : List Bool := gamma (s.length + 1) ++ s

/-- The pair handler of the interpretation: a pair is spelled by {lit}`true`
followed by the continuation at each of its two directions. -/
def pairHandler (a : square.A) : Cont (List Bool) (square.B a) :=
  fun k ↦ (true :: ((k false).run ++ (k true).run) : List Bool)

/-- The encoding: the interpretation of a tree into the continuation monad by
{name}`pairHandler`, run at the leaf's spelling, which is {lit}`false`
followed by its {name}`leafBody`. -/
def spell (t : BitTree) : List Bool := (t.liftM pairHandler).run fun s ↦ false :: leafBody s

/-- A bitstring is spelled by {lit}`false` followed by its body. -/
theorem spell_pure (s : List Bool) : spell (.pure s) = false :: leafBody s := rfl

/-- A pair is spelled by {lit}`true` followed by the spellings at its two
directions, in direction order. -/
theorem spell_liftBind (a : square.A) (c : square.B a → BitTree) :
    spell (.liftBind a c) = true :: (spell (c false) ++ spell (c true)) := rfl

/-- {name}`spell_pure` at {name}`leaf`. -/
theorem spell_leaf (s : List Bool) : spell (leaf s) = false :: leafBody s := rfl

/-- {name}`spell_liftBind` at {name}`pair`. -/
theorem spell_pair (l r : BitTree) : spell (pair l r) = true :: (spell l ++ spell r) := rfl

/-- The handler of a count: a pair sums the continuation at its two directions
and adds {lit}`c`. -/
def sumHandler (c : ℕ) (a : square.A) : Cont ℕ (square.B a) :=
  fun k ↦ ((k false).run + (k true).run + c : ℕ)

/-- A tree's count of pairs: one per pair, none per leaf. -/
def pairs (t : BitTree) : ℕ := (t.liftM (sumHandler 1)).run fun _ ↦ 0

/-- A tree's count of payload bits: the bitstring's length per leaf. -/
def payload (t : BitTree) : ℕ := (t.liftM (sumHandler 0)).run fun s ↦ s.length

/-- A tree's count of length-code bits: the length of the gamma code of the
bitstring's length plus one, per leaf. -/
def gammaLength (t : BitTree) : ℕ :=
  (t.liftM (sumHandler 0)).run fun s ↦ 2 * (s.length + 1).bits.length - 1

/-- A leaf has no pair. -/
theorem pairs_pure (s : List Bool) : pairs (.pure s) = 0 := rfl

/-- A pair's pairs are its directions' and itself. -/
theorem pairs_liftBind (a : square.A) (c : square.B a → BitTree) :
    pairs (.liftBind a c) = pairs (c false) + pairs (c true) + 1 := rfl

/-- A leaf's payload is its bitstring's length. -/
theorem payload_pure (s : List Bool) : payload (.pure s) = s.length := rfl

/-- A pair's payload is its directions'. -/
theorem payload_liftBind (a : square.A) (c : square.B a → BitTree) :
    payload (.liftBind a c) = payload (c false) + payload (c true) := rfl

/-- A leaf's length-code bits are its gamma code's. -/
theorem gammaLength_pure (s : List Bool) :
    gammaLength (.pure s) = 2 * (s.length + 1).bits.length - 1 := rfl

/-- A pair's length-code bits are its directions'. -/
theorem gammaLength_liftBind (a : square.A) (c : square.B a → BitTree) :
    gammaLength (.liftBind a c) = gammaLength (c false) + gammaLength (c true) := rfl

/-- A leaf body is the gamma code's bits and the payload's. -/
theorem length_leafBody (s : List Bool) :
    (leafBody s).length = 2 * (s.length + 1).bits.length - 1 + s.length := by
  rw [leafBody, List.length_append, length_gamma]

/-- A tree of {lit}`p` pairs and {lit}`m` payload bits is spelled by
{lit}`2 * p + 1 + m` bits and its leaves' length codes: one bit per node, of
which there are {lit}`2 * p + 1`, the payload, and a gamma code per leaf. -/
theorem length_spell (t : BitTree) :
    (spell t).length = 2 * pairs t + 1 + payload t + gammaLength t :=
  PFunctor.FreeM.rec
    (motive := fun t ↦ (spell t).length = 2 * pairs t + 1 + payload t + gammaLength t)
    (fun s ↦ by
      rw [spell_pure, List.length_cons, length_leafBody, pairs_pure, payload_pure,
        gammaLength_pure]
      omega)
    (fun a k ih ↦ by
      rw [spell_liftBind, List.length_cons, List.length_append, ih false, ih true,
        pairs_liftBind, payload_liftBind, gammaLength_liftBind]
      omega) t

end Geb.BitTreeScanner
