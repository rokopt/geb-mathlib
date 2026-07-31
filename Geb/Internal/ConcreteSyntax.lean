/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

/-!
# Concrete syntaxes for the Geb AST (prototype)

The abstract syntax is the initial algebra of `F X = Fin k + X ^ 2`.
A concrete syntax is a pair `parse : C → Option D`, `print : D → C`
satisfying the retraction law `parse (print d) = some d`; formatter
idempotence and injectivity of `print` are corollaries, proved once
here for every syntax.

This module carries the format-independent core (the rose
presentation, occurrence paths, the domain-separated Merkle fold) and
one worked concrete syntax, the RFC 9804 canonical S-expression form.

## References

* [RFC9804] Rivest and Eastlake, *SPKI S-Expressions*, June 2025.
* [RFC6962] Laurie, Langley and Kasper, *Certificate Transparency*,
  June 2013, section 2.1 (domain-separated Merkle hashing).
* [UustaluVene2011] Uustalu and Vene, *The recursion scheme from the
  cofree recursive comonad*, ENTCS 229(5), 2011.
-/

namespace Geb


/-! ## 1. Abstract syntax -/

/-- The Geb abstract syntax: the initial algebra of `F X = Fin k + X × X`.
A leaf carries a label in `Fin k`; a fork has exactly two children. -/
public inductive Ast (k : Nat) : Type where
  | leaf : Fin k → Ast k
  | fork : Ast k → Ast k → Ast k
  deriving Repr, DecidableEq

/-! ## 2. Annotated syntax -/

/-- `Ast k` with every node decorated by an `A`: the initial algebra of
`X ↦ A × F X`. The initial algebra rather than the terminal coalgebra,
because syntax trees are finite; the cofree comonad on `F` admits
infinitely deep trees and is the home of execution traces, not syntax. -/
public inductive Tree (k : Nat) (A : Type) : Type where
  | leaf : A → Fin k → Tree k A
  | fork : A → Tree k A → Tree k A → Tree k A
  deriving Repr, DecidableEq

/-- Relabel every node along `f`. -/
public def Tree.map {k : Nat} {A B : Type} (f : A → B) :
    Tree k A → Tree k B
  | .leaf a i => .leaf (f a) i
  | .fork a l r => .fork (f a) (l.map f) (r.map f)

/-- The comonad counit: the decoration at the root. -/
public def Tree.extract {k : Nat} {A : Type} : Tree k A → A
  | .leaf a _ => a
  | .fork a _ _ => a

/-- The comonad comultiplication: relabel each node with the annotated
subtree rooted at it. This is the redecoration map of
[UustaluVene2011]. -/
public def Tree.duplicate {k : Nat} {A : Type} :
    Tree k A → Tree k (Tree k A)
  | t@(.leaf _ i) => .leaf t i
  | t@(.fork _ l r) => .fork t l.duplicate r.duplicate

public theorem Tree.extract_duplicate {k : Nat} {A : Type} (t : Tree k A) :
    t.duplicate.extract = t := by
  cases t <;> rfl

public theorem Tree.map_extract_duplicate {k : Nat} {A : Type} (t : Tree k A) :
    t.duplicate.map Tree.extract = t := by
  induction t with
  | leaf a i => rfl
  | fork a l r ihl ihr => simp only [duplicate, map, ihl, ihr, extract]

public theorem Tree.duplicate_duplicate {k : Nat} {A : Type} (t : Tree k A) :
    t.duplicate.duplicate = t.duplicate.map Tree.duplicate := by
  induction t with
  | leaf a i => rfl
  | fork a l r ihl ihr => simp only [duplicate, map, ihl, ihr]

/-- Forget every decoration, recovering the bare tree. This is the fold
induced by the second projection `A × F X → F X`, not the comonad
counit. -/
public def Tree.erase {k : Nat} {A : Type} : Tree k A → Ast k
  | .leaf _ i => .leaf i
  | .fork _ l r => .fork l.erase r.erase

/-- The annotation vocabulary carried at a node. Durable metadata is an
annotation value, never a lexical comment: generic parsers discard
comments, and canonical forms differ over whether they are retained. -/
public structure Ann where
  /-- A name for the annotated occurrence. -/
  name : Option String := none
  /-- Prose documentation of the annotated occurrence. -/
  doc : Option String := none
  /-- References to material bearing on the annotated occurrence. -/
  links : List String := []
  deriving Repr, DecidableEq

/-- An annotated Geb document. -/
public abbrev Doc (k : Nat) : Type := Tree k Ann

/-- Decorate every node with the empty annotation. -/
public def Ast.trivialDoc {k : Nat} : Ast k → Doc k
  | .leaf i => .leaf {} i
  | .fork l r => .fork {} l.trivialDoc r.trivialDoc

public theorem Ast.erase_trivialDoc {k : Nat} (a : Ast k) :
    a.trivialDoc.erase = a := by
  induction a with
  | leaf i => rfl
  | fork l r ihl ihr => simp only [trivialDoc, Tree.erase, ihl, ihr]

/-! ## 3. The rose presentation and its bijection -/

/-- The rose-tree presentation: a label in `Fin k` and an arbitrary-length
list of children, satisfying the same fixed-point equation as `Ast k`. -/
public inductive Rose (k : Nat) : Type where
  | node : Fin k → List (Rose k) → Rose k
  deriving Repr

/-- The binary-to-rose direction, under the convention that the left child
of a fork is the head child and the right child carries the label and the
remaining siblings. Choosing the last child instead gives a different and
equally valid bijection, so the convention is normative and versioned:
annotation paths travel through it. -/
public def Ast.toRose {k : Nat} : Ast k → Rose k
  | .leaf i => .node i []
  | .fork l r =>
    match r.toRose with
    | .node i ts => .node i (l.toRose :: ts)

mutual

/-- The rose-to-binary direction, inverse to `Ast.toRose`. -/
public def Rose.ofRose {k : Nat} : Rose k → Ast k
  | .node i ts => Rose.ofRoseList i ts

/-- The sibling-list case of `Rose.ofRose`, folding a child list into the
right spine that carries the label `i` at its end. -/
public def Rose.ofRoseList {k : Nat} (i : Fin k) : List (Rose k) → Ast k
  | [] => .leaf i
  | t :: ts => .fork (Rose.ofRose t) (Rose.ofRoseList i ts)

end

public theorem ofRose_toRose {k : Nat} (a : Ast k) : a.toRose.ofRose = a := by
  induction a with
  | leaf i => rfl
  | fork l r ihl ihr =>
    simp only [Ast.toRose]
    cases h : r.toRose with
    | node j ts =>
      have hr : Rose.ofRoseList j ts = r := by
        rw [show Rose.ofRoseList j ts = Rose.ofRose (.node j ts) from rfl,
          ← h, ihr]
      simp [Rose.ofRose, Rose.ofRoseList, ihl, hr]

mutual

public theorem toRose_ofRose {k : Nat} (r : Rose k) : r.ofRose.toRose = r := by
  match r with
  | .node i ts => exact toRose_ofRoseList i ts

public theorem toRose_ofRoseList {k : Nat} (i : Fin k) (ts : List (Rose k)) :
    (Rose.ofRoseList i ts).toRose = .node i ts := by
  match ts with
  | [] => rfl
  | t :: ts' =>
    simp only [Rose.ofRoseList, Ast.toRose, toRose_ofRoseList i ts',
      toRose_ofRose t]

end

/-! ## 4. Occurrence paths -/

/-- A step into a fork. -/
public inductive Dir where
  | L
  | R
  deriving Repr, DecidableEq

/-- An occurrence in a tree, as a word over `Dir`. This is the normative
path vocabulary: the rose presentation names strictly fewer occurrences
(see `rosePathToBin_last`). -/
public abbrev Path : Type := List Dir

/-- The subtree at an occurrence, or `none` where the path leaves the
tree. -/
public def Ast.subtreeAt {k : Nat} : Ast k → Path → Option (Ast k)
  | a, [] => some a
  | .leaf _, _ :: _ => none
  | .fork l _, .L :: p => l.subtreeAt p
  | .fork _ r, .R :: p => r.subtreeAt p

/-- Whether a path names an occurrence of `a`. -/
public def Ast.validPath {k : Nat} (a : Ast k) (p : Path) : Bool :=
  (a.subtreeAt p).isSome

/-- Rose child index sequence to binary path: child `i` of a rose node at
binary position `q` sits at `q ++ replicate i R ++ [L]`. -/
public def rosePathToBin : List Nat → Path
  | [] => []
  | i :: is => List.replicate i .R ++ .L :: rosePathToBin is

/-- Binary occurrences named by the rose presentation are exactly the empty
path and those ending in `L`. -/
public theorem rosePathToBin_last (is : List Nat) :
    rosePathToBin is = [] ∨ (rosePathToBin is).getLast? = some .L := by
  induction is with
  | nil => exact Or.inl rfl
  | cons i is ih =>
    refine Or.inr ?_
    simp only [rosePathToBin, List.getLast?_append]
    cases ih with
    | inl h => simp [h]
    | inr h =>
      cases hh : rosePathToBin is with
      | nil => simp [hh] at h
      | cons x xs => simp [hh] at h ⊢; simpa [hh] using h

/-! ## 5. Shortest-form unsigned LEB128 -/

/-- Accumulator for `uvarint`, emitting base-128 digits least significant
first. -/
public def uvarintAux (n : Nat) (acc : ByteArray) : ByteArray :=
  if h : n < 128 then acc.push (UInt8.ofNat n)
  else uvarintAux (n / 128) (acc.push (UInt8.ofNat (n % 128 + 128)))
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- Shortest-form unsigned LEB128. Self-delimiting, which is what makes
the concatenations in `Ast.subtreeMH` uniquely parseable. -/
public def uvarint (n : Nat) : ByteArray := uvarintAux n ByteArray.empty

/-! ## 6. Multihash and domain separation -/

/-- A hash is a parameter: `code` is its multicodec number (SHA3-256 is
`0x16`), `run` the function itself. Every theorem below holds for any
`HashFn`; collision resistance is not asserted anywhere. -/
public structure HashFn where
  /-- The multicodec number of the hash function. -/
  code : Nat
  /-- The hash function itself. -/
  run : ByteArray → ByteArray

/-- SHA3-256, multicodec `0x16`, over a supplied implementation. The hash
is a parameter rather than a fixed function: every theorem here holds for
any `HashFn`, and the choice is a deployment decision. -/
public def sha3256 (impl : ByteArray → ByteArray) : HashFn :=
  { code := 0x16, run := impl }

/-- A digest tagged with the multicodec number of the function that
produced it. Carrying the algorithm at every level, rather than a bare
digest, supplies hash agility and a migration path. -/
public structure Multihash where
  /-- The multicodec number of the function that produced `digest`. -/
  code : Nat
  /-- The digest. -/
  digest : ByteArray

/-- Multihash serialization, `uvarint code ++ uvarint length ++ digest`.
Length-prefixed, hence self-delimiting, so concatenating two of them is
injective without any fixed-length side condition. -/
public def Multihash.encode (m : Multihash) : ByteArray :=
  uvarint m.code ++ uvarint m.digest.size ++ m.digest

/-- Hash a byte string and tag the digest with the function's code. -/
public def HashFn.mh (h : HashFn) (bs : ByteArray) : Multihash :=
  { code := h.code, digest := h.run bs }

/-- Domain-separation tag for a leaf. -/
public def tagLeaf : ByteArray := "geb/v1/core/leaf".toUTF8
/-- Domain-separation tag for a fork. -/
public def tagFork : ByteArray := "geb/v1/core/fork".toUTF8
/-- Domain-separation tag for a whole tree. -/
public def tagRoot : ByteArray := "geb/v1/core/root".toUTF8
/-- Domain-separation tag for an annotated document. -/
public def tagDoc  : ByteArray := "geb/v1/docs/root".toUTF8

/-- Domain-separation tags must be equal-length or prefix-free. -/
public theorem tags_equal_length : tagLeaf.size = 16 ∧ tagFork.size = 16
    ∧ tagRoot.size = 16 ∧ tagDoc.size = 16 := by
  simp [tagLeaf, tagFork, tagRoot, tagDoc]; decide

/-! ## 7. The Merkle fold -/

/-- The Merkle fold: the catamorphism of the hash algebra. Its universal
property supplies uniqueness, hence compositionality — a node's digest is
a function of its children's digests and nothing else — which is what
licenses incremental recomputation and subtree-level deduplication. The
converse, hash equality implying structural equality, is not a theorem;
it holds only under a collision-resistance assumption external to the
kernel. `k` is deliberately absent, so that equal subtrees share an
address across leaf alphabets containing them. -/
public def Ast.subtreeMH {k : Nat} (h : HashFn) : Ast k → Multihash
  | .leaf i => h.mh (tagLeaf ++ uvarint i.val)
  | .fork l r =>
    h.mh (tagFork ++ (l.subtreeMH h).encode ++ (r.subtreeMH h).encode)

/-- The semantic identity of a whole tree. `k` participates: the same
numeric tree read over different leaf alphabets is a different object.
Renaming, commenting and re-linking never change it. -/
public def Ast.coreMH {k : Nat} (h : HashFn) (a : Ast k) : Multihash :=
  h.mh (tagRoot ++ uvarint k ++ (a.subtreeMH h).encode)

/-! ## 8. Law skeletons for a concrete syntax `C` -/

section Laws

variable {D C : Type} (parseDoc : C → Option D) (printDoc : D → C)

/-- The document-level retraction law: the only law a syntax must prove. -/
public def Retraction : Prop := ∀ d : D, parseDoc (printDoc d) = some d

/-- The formatter, defined where parsing succeeds. -/
public def format (c : C) : Option C := (parseDoc c).map printDoc

public theorem format_idem (hr : Retraction parseDoc printDoc) (c : C) :
    (format parseDoc printDoc c).bind (format parseDoc printDoc)
      = format parseDoc printDoc c := by
  unfold format
  cases h : parseDoc c with
  | none => simp
  | some d => simp [hr d]

public theorem printDoc_injective (hr : Retraction parseDoc printDoc) :
    Function.Injective printDoc := by
  intro d1 d2 h
  have h1 := hr d1
  rw [h, hr d2] at h1
  exact (Option.some.inj h1).symm

end Laws


/-! ## 9. A concrete syntax: RFC 9804 canonical S-expressions -/

/-- Fuel measure for the recursive-descent parser. -/
@[expose] public def Ast.depth {k : Nat} : Ast k → Nat
  | .leaf _ => 1
  | .fork l r => 1 + l.depth + r.depth


/-- The ASCII character for a decimal digit; meaningful for `d < 10`. -/
@[expose] public def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal value of an ASCII digit character. -/
@[expose] public def charDigit (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48) else none

public theorem charDigit_digitChar (d : Nat) (h : d < 10) :
    charDigit (digitChar d) = some d := by
  revert h; revert d; decide

public theorem charsToDigits_map {ds : List Nat} (h : ∀ d ∈ ds, d < 10) :
    (ds.map digitChar).mapM charDigit = some ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hd : d < 10 := h d (by simp)
    have ht : ∀ x ∈ ds, x < 10 := fun x hx => h x (by simp [hx])
    simp [List.mapM_cons, charDigit_digitChar d hd, ih ht]

/-- Little-endian decimal digits; choice-free, and it runs in the
interpreter (mathlib's `Nat.digits` does neither). -/
@[expose] public def digitsLE (n : Nat) : List Nat :=
  if h : n = 0 then [] else n % 10 :: digitsLE (n / 10)
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

/-- The value of a little-endian decimal digit list. -/
@[expose] public def ofLE : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * ofLE ds

public theorem ofLE_digitsLE (n : Nat) : ofLE (digitsLE n) = n := by
  rw [digitsLE]
  split
  next h => simp [ofLE, h]
  next h =>
    have ih := ofLE_digitsLE (n / 10)
    simp only [ofLE, ih]
    omega
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

public theorem digitsLE_lt (n : Nat) : ∀ d, d ∈ digitsLE n → d < 10 := by
  intro d hd
  rw [digitsLE] at hd
  split at hd
  next => simp at hd
  next h =>
    rcases List.mem_cons.mp hd with rfl | hd'
    · omega
    · exact digitsLE_lt (n / 10) d hd'
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

public theorem digitsLE_ne_nil {n : Nat} (h : n ≠ 0) : digitsLE n ≠ [] := by
  rw [digitsLE]; simp [h]

/-- Shortest-form decimal, big-endian, `"0"` for zero. -/
@[expose] public def decOf (n : Nat) : List Char :=
  if n = 0 then ['0'] else (digitsLE n).reverse.map digitChar

/-- The value of a big-endian decimal digit string, or `none` if any
character is not a digit. Leading zeros are accepted: the parser may
admit more than the printer emits, since the retraction law constrains
only the composite. -/
@[expose] public def digitsVal (cs : List Char) : Option Nat :=
  (cs.mapM charDigit).map fun l => ofLE l.reverse

public theorem digitsVal_decOf (n : Nat) : digitsVal (decOf n) = some n := by
  unfold decOf digitsVal
  by_cases h : n = 0
  · subst h; decide
  · have hlt : ∀ d ∈ (digitsLE n).reverse, d < 10 := by
      intro d hd
      exact digitsLE_lt n d (List.mem_reverse.mp hd)
    rw [if_neg h, charsToDigits_map hlt]
    simp [ofLE_digitsLE]

public theorem decOf_all_digits (n : Nat) :
    ∀ c ∈ decOf n, (charDigit c).isSome := by
  intro c hc
  unfold decOf at hc
  by_cases h : n = 0
  · subst h; simp at hc; subst hc; decide
  · rw [if_neg h] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have : d < 10 := digitsLE_lt n d (List.mem_reverse.mp hd)
    simp [charDigit_digitChar d this]

public theorem decOf_ne_nil (n : Nat) : decOf n ≠ [] := by
  unfold decOf
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h]
    simp [digitsLE_ne_nil h]

/-! ## Reading a decimal prefix -/

/-- Split off the longest decimal prefix. -/
@[expose] public def readDigits : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
    match charDigit c with
    | some _ => let (ds, r) := readDigits cs; (c :: ds, r)
    | none => ([], c :: cs)

public theorem readDigits_append {ds rest : List Char}
    (hd : ∀ c ∈ ds, (charDigit c).isSome)
    (hr : ∀ c, rest = c :: _root_.List.tail rest → charDigit c = none) :
    readDigits (ds ++ rest) = (ds, rest) := by
  induction ds with
  | nil =>
    cases rest with
    | nil => rfl
    | cons c cs => simp [readDigits, hr c rfl]
  | cons d ds ih =>
    have h1 : (charDigit d).isSome := hd d (by simp)
    have h2 : ∀ c ∈ ds, (charDigit c).isSome := fun c hc => hd c (by simp [hc])
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h1
    simp [readDigits, hv, ih h2]

/-- Read a non-empty decimal prefix and its value. -/
@[expose] public def readNat (cs : List Char) : Option (Nat × List Char) :=
  let (ds, r) := readDigits cs
  if ds.isEmpty then none else (digitsVal ds).map (·, r)

/-! ## Canonical verbatim atoms -/

/-- The RFC 9804 verbatim encoding of an atom, `length ":" content`. -/
@[expose] public def printVerbatim (s : List Char) : List Char :=
  decOf s.length ++ ':' :: s

/-- Read one verbatim atom, returning it and the remaining input. -/
@[expose] public def readVerbatim (cs : List Char) :
    Option (List Char × List Char) :=
  match readNat cs with
  | some (n, ':' :: r) => if n ≤ r.length then some (r.take n, r.drop n) else none
  | _ => none

public theorem readVerbatim_append (s rest : List Char) :
    readVerbatim (printVerbatim s ++ rest) = some (s, rest) := by
  have hcolon : ∀ c, (':' :: (s ++ rest)) = c :: _root_.List.tail (':' :: (s ++ rest)) →
      charDigit c = none := by
    intro c hc; simp at hc; subst hc; decide
  have h : readNat (printVerbatim s ++ rest) = some (s.length, ':' :: (s ++ rest)) := by
    unfold readNat printVerbatim
    rw [List.append_assoc, List.cons_append,
      readDigits_append (decOf_all_digits s.length) hcolon]
    simp [decOf_ne_nil s.length, digitsVal_decOf, List.isEmpty_iff]
  simp [readVerbatim, h]

/-! ## Printer -/

/-- The head atom of a leaf s-expression. -/
@[expose] public def leafTok : List Char := ['l', 'e', 'a', 'f']
/-- The head atom of a fork s-expression. -/
@[expose] public def forkTok : List Char := ['f', 'o', 'r', 'k']

/-- Print a tree in RFC 9804 canonical form. A leaf label is its
shortest-form decimal, written as a verbatim atom: RFC 9804 tokens may
not begin with a digit, since a leading digit starts a length prefix. -/
@[expose] public def printAst {k : Nat} : Ast k → List Char
  | .leaf i => '(' :: (printVerbatim leafTok ++ printVerbatim (decOf i.val) ++ [')'])
  | .fork l r => '(' :: (printVerbatim forkTok ++ printAst l ++ printAst r ++ [')'])

/-! ## Parser -/

/-- Recursive descent over the canonical form, returning the tree and the
unconsumed input. The `Nat` argument is fuel: the recursion is on the
input's structure only through the remainder each call returns, which is
not a form Lean's structural recursion accepts. `parse` supplies the
input length, which `depth_le_length` shows is always enough. -/
@[expose] public def parseAst (k : Nat) : Nat → List Char → Option (Ast k × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, c :: cs =>
    if c = '(' then
      match readVerbatim cs with
      | some (tok, cs1) =>
        if tok = leafTok then
          match readVerbatim cs1 with
          | some (ds, ')' :: cs2) =>
            match digitsVal ds with
            | some n => if h : n < k then some (.leaf ⟨n, h⟩, cs2) else none
            | none => none
          | _ => none
        else if tok = forkTok then
          match parseAst k f cs1 with
          | some (l, cs2) =>
            match parseAst k f cs2 with
            | some (r, ')' :: cs3) => some (.fork l r, cs3)
            | _ => none
          | none => none
        else none
      | none => none
    else none

public theorem parseAst_printAst {k : Nat} (a : Ast k) :
    ∀ (f : Nat) (rest : List Char), a.depth ≤ f →
      parseAst k f (printAst a ++ rest) = some (a, rest) := by
  induction a with
  | leaf i =>
    intro f rest hf
    cases f with
    | zero => simp [Ast.depth] at hf
    | succ f =>
      simp only [printAst, List.cons_append, parseAst,
        List.append_assoc, List.nil_append]
      rw [readVerbatim_append]
      simp only []
      rw [readVerbatim_append]
      simp [digitsVal_decOf, i.isLt]
  | fork l r ihl ihr =>
    intro f rest hf
    cases f with
    | zero => simp [Ast.depth] at hf
    | succ f =>
      have hl : l.depth ≤ f := by simp [Ast.depth] at hf; omega
      have hr : r.depth ≤ f := by simp [Ast.depth] at hf; omega
      simp only [printAst, List.cons_append, parseAst,
        List.append_assoc, List.nil_append]
      rw [readVerbatim_append]
      have hne : forkTok ≠ leafTok := by decide
      simp only [if_neg hne]
      rw [ihl f _ hl]
      simp only []
      rw [ihr f _ hr]
      simp

public theorem depth_le_length {k : Nat} (a : Ast k) :
    a.depth ≤ (printAst a).length := by
  induction a with
  | leaf i => simp [Ast.depth, printAst]
  | fork l r ihl ihr =>
    simp only [Ast.depth, printAst, List.length_cons, List.length_append]
    omega

/-! ## The two syntax maps and the retraction law -/

/-- The printer of the canonical S-expression syntax. A concrete syntax
needs a deterministic printer, not a normative canonical form; that this
one also emits the format's canonical bytes is convenient rather than
required. -/
@[expose] public def print {k : Nat} (a : Ast k) : List Char := printAst a

/-- The parser of the canonical S-expression syntax, rejecting trailing
input. -/
@[expose] public def parse (k : Nat) (cs : List Char) : Option (Ast k) :=
  match parseAst k cs.length cs with
  | some (a, []) => some a
  | _ => none

public theorem parse_print {k : Nat} (a : Ast k) : parse k (print a) = some a := by
  unfold parse print
  rw [show printAst a = printAst a ++ [] by simp,
    parseAst_printAst a _ [] (by simpa using depth_le_length a)]


/-! ## 10. The generic corollaries, instantiated at the S-expression syntax -/

public theorem csexp_retraction (k : Nat) : Retraction (parse k) (print (k := k)) :=
  parse_print

public theorem csexp_format_idem (k : Nat) (c : List Char) :
    (format (parse k) print c).bind (format (parse k) print)
      = format (parse k) print c :=
  format_idem _ _ (csexp_retraction k) c

public theorem csexp_print_injective (k : Nat) :
    Function.Injective (print (k := k)) :=
  printDoc_injective _ _ (csexp_retraction k)

end Geb
