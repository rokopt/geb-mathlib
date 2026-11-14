/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import VersoManual
public import GebManual.Geb

/-! # The first Geb authoring milestone

A documented program, its statement and proof script, their durable encodings, and the record
from which the program and its checked certificate can be reproduced.
-/

open Verso.Genre Manual
open GebManual.Geb

#doc (Manual) "Writing a first Geb development" =>
%%%
tag := "first-authoring"
%%%

The development under `examples/authoring/` is a small program written
and proved in Geb. Its manifest chooses edition `0` and the source,
annotation and prose profiles. The statements and proof scripts live in
`Pair.proofs.geb`; the computational definitions live in `Pair.geb` and
`Lists.geb`.
The commands below compile the program, check the examples in its notes,
produce a certificate and replay it. This chapter includes the files
directly, checks their prose and references, and replays their certificate
while it builds.

# The development

{gebProgram "examples/authoring/pair.manifest" "Pair.proofs.geb" "record/pair.cert"}

The first theorem equates two closed functions, including their
abstractions; the second states the same equality at every pair of
arguments, and the example in the note separately checks one evaluation.
The others use a hypothesis, induction on a list, and an earlier theorem.
There is no Lean source belonging to this development.

# Running it

From the repository root:

```
lake build geb-author geb-defs
lake exe geb-author compile examples/authoring/pair.manifest /tmp/pair.img
lake exe geb-defs /tmp/pair.img /tmp/pair.defs
lake exe geb-author prove examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair.cert
lake exe geb-author replay examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair.cert
```

`compile` checks every example before writing the image. An example's two
expressions use fully qualified definition names and must return trees;
it evaluates both and compares their results. `prove` runs the script in
the prover written in Geb, checks the
result with the checker written in Geb, and replays it before writing the
certificate. A rejected input leaves an existing output in place. A program
the compiler rejects is reported at the line and column of the declaration
concerned, and a theorem whose statement or script does not read at the
theorem's name, as `FILE:LINE:COLUMN: error: MESSAGE`. A script that does
not prove its theorem is reported at each of its steps that fails, with the
goal of that step ({ref "proof-holes"}[Holes and goals]).

`prove` and `check` search for every theorem's derivation at each run
unless they are given a directory of caches
({ref "proof-cache"}[The cache of a development]).

`replay` checks the saved derivations against the source statements and
their names. It performs no proof search. Reducing `normalize`'s budget
to zero can make `prove` fail while `replay` continues to accept the saved
certificate. Changing the statement, its name, the program, or its
profile prevents that reuse. Comments and notes may change while the
compiled program stays the same; examples are checked again on replay.
A certificate of the program as it was before a change is carried to the
program after it by `transport`
({ref "proof-cache"}[The cache of a development]).

# The proof-source profile

A proof document is `(proofs V THEOREM…)`, its version `V` being `0`, `1`,
`2`, `3`, `4` or `5`, with one or more theorems of distinct names, each
`(theorem NAME STATEMENT (by SCRIPT))`. Version `1` reads:

```
STATEMENT ::= (forall ((x A) …) PROPOSITION) | PROPOSITION
PROPOSITION ::= (implies (h EQUATION) … EQUATION) | EQUATION
EQUATION ::= (equal TERM TERM)
SCRIPT ::= (normalize FUEL RULE…) | (reduce DEPTH RULE…)
         | (auto DEPTH SPLITS RULE…) | (extensionality x SCRIPT)
         | (induction x (y ys ih) SCRIPT SCRIPT)
         | (cases x (y ys) SCRIPT SCRIPT)
         | (reduce-hypotheses DEPTH (h …) SCRIPT)
DEPTH ::= head | weak | open | full
```

A type `A` is a type of the kernel: `T`, `Unit`, `(Prod A B)`,
`(Arrow A B)` or `(List A)`. A term is a term of the kernel, read by the Geb
reader in the scope of the bound variables, innermost last, with the
program's definitions under their qualified names; its translation into the
metalogic is that of the program's definitions. The two sides of an
equation have one type. The bound variables and the hypotheses are named
by atoms that are neither numerals nor reserved, distinct from one another,
from the program's definitions and from the theorems.

A script proves the equation of its goal in the goal's context and under
its hypotheses. `normalize` normalizes both sides within a budget,
unfolding definitions and computing applications of abstractions, the
components of pairs, the folds of lists and trees at their constructions,
the case analysis of a coproduct at its injections and the element of the
terminal type. `reduce` reduces both sides to a depth, the weak
head normal form, the weak normal form, the normal form but for the starts
and steps of folds, or the normal form, and `auto` reduces to a depth and
splits a list or coproduct variable on which the reduction is stuck, up to a number of
times, using the instances of the hypotheses. A rule names a hypothesis or
an earlier theorem, which each of these then rewrites by. `extensionality`
proves an equation of functions by that of their applications to a new
variable `x`. `induction` proves an equation by induction on its innermost
variable, of a list type: at the empty list, and at the list of a head `y`
and a tail `ys`, under the induction hypothesis `ih`. `cases` proves it by
the case analysis of any list variable, the variable kept in the context
and its cases named. `reduce-hypotheses` reduces the named hypotheses to a
depth, so that a rule rewrites by their reduced forms. The tactics
introduce no names but those a script writes, so a script names every
variable and hypothesis it refers to. These are the tactics of
`bootstrap/free-topos/tactics.geb` and `bootstrap/free-topos/prove.geb`,
`Geb.FreeTopos.Tactics` in Lean.

The reductions rewrite a term once its head is reduced, so a theorem's
left side as written rarely occurs in a reduced goal. In version `1` each
theorem is therefore followed in the certificate by its companion: the
theorem with its sides in weak normal form, derived from it at its own
variables and hypotheses, and a rule naming the theorem rewrites by its
companion.

Version `0` admits only theorems `(theorem NAME (equal LEFT RIGHT)
(by (normalize FUEL)))` whose sides are the names of definitions. It reads
their statements as version `1` does, and its normalization unfolds
definitions and computes applications of abstractions and the components
of pairs alone, so a document of either version keeps its meaning. It
cites no theorem, so its certificate saves no companion and has the format
`geb-proof/v1`, whose certificates therefore still replay; version `1`
writes `geb-proof/v2`, version `2` `geb-proof/v3`, version `3`
`geb-proof/v4`, version `4` `geb-proof/v5` and version `5` `geb-proof/v6`. An unknown or unbound
name, a name declared twice,
a malformed form, an unsupported version, a false equation or an
unsuccessful search is rejected. Failure of a bounded search does not establish that the
statement is false.

Statements are not yet written over the datatypes of the datatype language.
The statement reader and the script interpreter are in
`bootstrap/authoring.geb`; they add no rule to the metalogic.

# Statements over the internal language
%%%
tag := "internal-statements"
%%%

Version `2` reads what version `1` reads, and adds the program a document
names and the documents it cites, statements over the metalogic's internal
language in object variables, rules at objects, and the tactics of trees
and coproducts:

```
DOCUMENT ::= (proofs 2 HEADER… THEOREM…)
HEADER ::= (program NAME) | (import PATH)
STATEMENT ::= … | (internal (X…) QUANTIFIED)
QUANTIFIED ::= (forall ((x TYPE) …) PROPOSITION) | PROPOSITION
TYPE ::= T | Unit | (Prod TYPE TYPE) | (Arrow TYPE TYPE) | (List TYPE)
       | Bit | Bits | Omega | (Sum TYPE TYPE) | (Rose TYPE) | X
ITERM ::= x | NAME | unit | (pair ITERM ITERM) | (fst ITERM) | (snd ITERM)
        | (lam ((x TYPE) …) ITERM) | (ITERM ITERM…) | (equal ITERM ITERM)
        | (nil TYPE) | (cons TYPE ITERM ITERM) | (node TYPE ITERM)
        | (inl TYPE TYPE ITERM) | (inr TYPE TYPE ITERM)
        | (case TYPE TYPE TYPE ITERM)
        | (list-rec ITERM (y r) ITERM ITERM)
        | (rose-rec TYPE (n) ITERM ITERM)
        | (lib NAME TYPE… ITERM…) | (kernel TERM)
RULE ::= … | (NAME TYPE…)
SCRIPT ::= … | (fold-induction x (y r) ITERM FUEL RULE…)
         | (tree-fold-induction x (l rs) ITERM FUEL RULE…)
         | (sum-cases x (y) SCRIPT SCRIPT)
         | (tree-cases x (l cs) NAME SCRIPT)
         | (auto-trees DEPTH SPLITS NAME RULE…)
         | (generalize (y TYPE) ITERM SCRIPT)
         | (pointwise NAME DEPTH RULE…)
         | (mask-rewrite TYPE TYPE NAME LEMMA (ITERM…)
             ITERM ITERM ITERM ITERM ITERM ITERM)
LEMMA ::= NAME | (NAME TYPE…)
```

A statement `(internal (X…) Q)` binds the object variables `X…`, and `Q` has
the form of a statement of version `1` with the types and terms of the
internal language, an equation's sides `ITERM`s of one type. A type is the
translation of a kernel type, `T` the rose trees over the bitstrings and
`Unit`, `Prod`, `Arrow` and `List` the terminal object, products,
exponentials and list objects; the bits, `Bit`, which is `(Sum Unit Unit)`;
the bitstrings, `Bits`, which is `(List Bit)`; the truth values, `Omega`; a
coproduct; the rose trees over a type of labels, `T` being `(Rose Bits)`; or
an object variable.

A term of the internal language is a variable; a definition of the program by
its qualified name, at its translated type; the element `unit` of the
terminal type; a pair or a component; an abstraction; an application, the
function before its arguments; an equation, of the type `Omega`; or one of
the forms below. Each form carries the types that the internal language does
not infer.

* `(nil A)` is the empty list of `A`, and `(cons A h t)` the list of a head
  before a list.
* `(node A p)` is the tree of the pair `p` of a label of `A` and a list of
  trees.
* `(inl A B t)` and `(inr A B t)` are the injections into `(Sum A B)`, and
  `(case A B C p)` the function from `(Sum A B)` to `C` of the pair `p` of a
  function from `A` and one from `B`.
* `(list-rec z (y r) s l)` is the fold of the list `l`: `z` at the empty
  list, and at a head `y` before a list the term `s`, in which `r` is the
  fold's value at that list.
* `(rose-rec C (n) s t)` is the fold of the tree `t` into `C`: at a node the
  term `s`, in which `n` is the pair of the node's label and the list of the
  fold's values at its children.
* `(lib NAME A… t…)` applies a definition of the translation's library, with
  an object for each of its object parameters before its arguments. The
  names are `bnil`, `b0`, `b1`, `lab`, `unnode`, `children`, `cond`, `tail`,
  `headD`, `lcase`, `isNil`, `succ`, `length`, `pred`, `dbl`, `add`, `cmp`,
  `ltB`, `eqB`, `subE`, `sub`, `mul`, `divMod`, `log2`, `iter`, `mapApp`,
  `and`, `allZip` and `equal`, those of `Geb.FreeTopos.Translation.D`.
* `(kernel t)` is a term of the kernel, read and translated as version `1`
  reads a statement's terms, in the variables whose types are kernel types.

The names `inl`, `inr`, `case`, `list-rec`, `rose-rec`, `lib` and `kernel`
head these forms wherever a term of the internal language is read, and no
variable of an internal statement or of a script of version `2` takes one.
The terms a script writes are terms of the internal language. A statement of
either kind is rejected unless its sides have one type in its context.

A rule `(NAME A…)` rewrites by an earlier theorem in object variables at the
objects `A…`. The tactics added:

* `fold-induction` proves the goal by induction on its innermost variable
  `x`, a list, in the form of the uniqueness of a fold: the sides are equal
  at the empty list, and each side at a head `y` before a list is the step,
  in which `r` is that side's value at the list, each of the three by
  normalization within the budget.
* `tree-fold-induction` proves a goal whose one variable `x` is a tree by the
  uniqueness of the tree's fold: each side at the node of a label `l` is the
  step, in which `rs` is the list of that side's values at the children,
  each by normalization within the budget.
* `sum-cases` proves the goal at each injection of a new variable `y` for a
  variable of a coproduct, a bit among them, and `tree-cases` at the node of
  a new label `l` and children `cs` for a variable of the trees; `NAME` is
  the theorem that a tree is the node of its unfolding.
* `auto-trees` reduces to a depth and splits the list, coproduct or tree
  variable the reduction is stuck on, as `auto` does for lists and
  coproducts, with that theorem.
* `generalize` proves the goal with a new variable `y` for the occurrences of
  a term.
* `pointwise` proves an equation from the earlier theorem `NAME` that equates
  two functions: the goal's sides and the applications of the theorem's
  sides to the goal's innermost variable have the same normal forms at the
  depth.
* `mask-rewrite A B ABSORB LEMMA (t…) c d x x' z y` proves that the
  conditional on the test `c` between `y` and `d`, of the type `A`, is the
  conditional between `y` with `x'` for the occurrences of `x`, of the type
  `B`, and `d`. `LEMMA`, at its objects and at the terms `t…` for its
  variables, equates the conditionals on `c` between `x` and `z` and between
  `x'` and `z`, and `ABSORB` is the theorem that inside the branch a test
  selects, a conditional on the same test is its first branch.

The tactics that cite a theorem by `NAME`, and a `LEMMA`, cite it as stated,
where a rule rewrites by its companion. `fold-induction` is
`Geb.FreeTopos.Internal.byListInd` and `tree-fold-induction`
`Geb.FreeTopos.Internal.byRoseInd`; the others but `pointwise` are tactics of
`Geb.FreeTopos.Tactics`, and `pointwise` composes the derivation of the Lean
developments' pointwise lemmas in `bootstrap/authoring.geb`.

A form `(import PATH)` names a proof document whose theorems the document
cites, by a path as a manifest's source is, relative to the document's own
directory. A development is the documents a document imports, and those they
import, each read once and before the documents importing it, followed by
the document; an imported document is of version `1` or `2`. The theorems of
a development are one list: their names are distinct, a theorem cites those
before it, and the certificate holds the declarations of the imported
theorems before the document's own, so that it replays from the documents
alone and a change to an imported statement prevents its reuse.

A form `(program NAME)` names the program a document is proved against
where the command gives no manifest: the manifest whose program has that
name in the document's directory, or else in the nearest directory above
it that holds one, a directory holding several being rejected. A document
names no more than one program, and a manifest the command gives takes the
place of the program named. Only the document proved is consulted: the
documents it imports are read against its program, whatever they name, so
that a document that holds in every program names none, and a development
is proved again in a larger program by a document that imports it.

```
lake exe geb-author prove PROOFS CERTIFICATE
lake exe geb-author replay PROOFS CERTIFICATE
lake exe geb-author check FILE
```

`check` writes nothing. It proves a proof document, a file holding a form
`(proofs V …)`, against the program it names, and compiles any other file
as a source of a program, with the sources that the nearest manifest
listing it lists before it; an editor runs it on the file being edited.

The documents under `bootstrap/proofs/` state and prove in this profile the
development of `GebTests/Prototypes/FreeTopos/TreeCases.lean`, whose
statements are Lean values and whose scripts are Lean code, about the program
of `bootstrap/expansion.manifest`: `trees.proofs.geb` the lemmas on the
unfolding of trees, which hold in every program and name none, and
`tree-cases.proofs.geb`, which names the program `expansion` and imports
it, the conditional lemmas, the
soundness of the equality of bitstrings, the rewriting under a test, and that
a tree the reader names by the atom of the head of a definition's form is
that atom. Each theorem is stated as it is written and followed by its
companion, where the Lean development states a lemma's sides in the normal
form it computes. The lemma that the fold of the case analysis of lists
rebuilds its list is among those of `trees.proofs.geb`.

```
lake exe geb-author prove bootstrap/proofs/tree-cases.proofs.geb \
  /tmp/tree-cases.cert
lake exe geb-author replay bootstrap/proofs/tree-cases.proofs.geb \
  /tmp/tree-cases.cert
```

# Hypotheses and implications
%%%
tag := "hypothesis-scripts"
%%%

Version `3` reads what version `2` reads, and adds truth and implication to
the terms of the internal language, and the tactics of the induction on
trees with the hypothesis at each child, of the instances of a hypothesis,
of implications, of the alternative of two scripts and of the case analysis
of a bitstring to a number of bits:

```
DOCUMENT ::= (proofs 3 HEADER… THEOREM…)
ITERM ::= … | true | (implies ITERM ITERM)
SCRIPT ::= … | (tree-induction x (l cs ih) SCRIPT)
         | (child-hypotheses DEPTH h (CHILD…) SCRIPT)
         | (instances DEPTH h (INSTANCE…) SCRIPT)
         | (assume h SCRIPT)
         | (modus-ponens h (h…) SCRIPT)
         | (revert-cases h x (y ys) SCRIPT SCRIPT)
         | (first SCRIPT SCRIPT)
         | (bits-cases x BITS SCRIPT)
CHILD ::= (INSTANCE…)
INSTANCE ::= (h ITERM…)
```

Truth and implication are connectives of `Geb.FreeTopos.Internal.Logic`,
definitions of the internal language in terms of equality: `true` is the
equality of the element of the terminal type with itself, and
`(implies p q)`, of two terms of the type `Omega`, the equality of the
conjunction of `p` and `q` with `p`, a conjunction being the equality of the
pair of its formulas with the pair of truths. The three definitions follow
the program's among the definitions a development of version `3` is checked
with, and their rules, each with its derivation, are the first declarations
of its certificate, where the tactics of implications cite them
(`bootstrap/free-topos/logic.geb`). A statement is an equation, so a theorem
that an implication holds equates it with `true`. The names `true` and
`implies` are read so wherever version `3` reads a term of the internal
language, and no variable of an internal statement or of a script of version
`3` takes one.

The tactics added:

* `tree-induction` proves a goal without hypotheses by induction on its
  innermost variable `x`, a tree: the goal at the node of a label `l` and
  children `cs`, under the induction hypothesis `ih`. The hypothesis is one
  equation, of the list of the goal's formulas at the children with the list
  of as many truths. Where `x` has the kernel's type of trees, `cs` has the
  kernel's type of lists of trees.
* `child-hypotheses` brings the induction hypothesis `h` to the first
  children, as many as the `CHILD`s, of a list of children that is a
  construction to that number, as `revert-cases` leaves it. For each `CHILD`
  in order, the goal's formula at the child of that position is cut in, and
  each `INSTANCE` names its instance at the terms `t…`: the equation of the
  applications of the formula's two sides, functions, to the terms, reduced
  to the depth. An `INSTANCE` without terms names the formula.
* `instances` names so the instances of a hypothesis `h` that equates two
  functions.
* `assume` proves a goal whose sides reduce, at their heads, to the
  implication of an equation and to `true`, by the proof of the equation
  under the antecedent, named `h`.
* `modus-ponens` takes hypotheses `h…` that each equate with `true` an
  implication whose antecedent is the hypothesis `h`, and gives each name to
  the implication's conclusion, cut in.
* `revert-cases` proves the goal by the case analysis of a list variable `x`
  that the hypothesis `h` mentions: at the empty list, and at a head `y`
  before a list `ys`, under `h` at each. The implication of the goal by `h`
  is proved for every list by induction, and the goal follows from it at
  `x`.
* `first` proves the goal by its first script or, where that script does not
  prove it, by its second.
* `bits-cases` proves the goal by the case analysis of a variable `x` of the
  bitstrings to the number `BITS` of bits: at each bitstring of fewer bits,
  and at each bitstring of that number of bits before a bitstring, every
  case by the one script. Each bit of a case adds three variables, the head
  of a bitstring, the bitstring after it and the element of the head's
  injection, and one hypothesis, the goal at the bitstring after the head,
  none of them named. The script is read once for each number of bits, in
  the variables and hypotheses of the cases of that number, so that it
  cites those of the goal and those its own tactics name.

A hypothesis that a tactic reduces, or replaces by its conclusion or its
case, keeps its name, and the hypotheses a tactic cuts in besides are cited
by no name. `tree-induction` is `Geb.FreeTopos.Internal.byRoseIndHyp`, and
the others but the last two `withChildHyps`, `withInsts`, `byImpI`,
`withImpElim` and `revertCase` of `Geb.FreeTopos.Tactics`, by which the Lean
developments prove that weakening and substitution preserve types.
`bits-cases` composes the case analyses of a list and of a coproduct as
`Geb.FreeTopos.Tactics.byBits` does, and with `first` one script proves the
cases of a label's bits that differ in what proves them, as those
developments' proofs at a construction do.

`scripts/tests/test-proof-scripts.sh` proves with them, among other
theorems, that the fold of a tree that keeps the first child alone at each
node gives at its own result that result, a goal in the one variable `t`:

```
(tree-induction t (l cs ih)
  (revert-cases ih cs (c ys) (reduce full)
    (child-hypotheses weak ih (((hc))) (reduce full hc))))
```

At a node without children both sides reduce to the node. At a first child
`c` before the children `ys`, `hc` names the goal at `c`, the formula of
`ih` at the first child, taken at no arguments, and both sides reduce to the
node of the fold at `c` once `hc` rewrites.

A document of version `3` imports documents of versions `1` to `3`, and no
document imports one of a later version, whose certificate is laid out
otherwise.

# Abbreviations, folds and searches
%%%
tag := "development-scripts"
%%%

Version `3` reads, besides, abbreviations, the normal form of a theorem's
companion, rules that keep definitions folded, and the tactics that the
developments by induction on trees compose:

```
DOCUMENT ::= (proofs 3 HEADER… FORM…)
FORM ::= THEOREM | (abbreviation NAME ITEM…)
THEOREM ::= (theorem NAME STATEMENT (by SCRIPT))
          | (theorem NAME STATEMENT (by SCRIPT) (normal DEPTH RULE…))
RULE ::= … | (folded DEFINITION…)
DEFINITION ::= NAME | (lib NAME)
SCRIPT ::= … | (with-rules (RULE…) SCRIPT)
         | (fold-uniqueness x (y ys r) ITERM SCRIPT SCRIPT)
         | (tree-fold-uniqueness x (l cs rs) ITERM SCRIPT)
         | (instance LEMMA (ITERM…) (ITERM…) DEPTH RULE…)
         | (have h LEMMA (ITERM…) (ITERM…) SCRIPT)
         | (congruence h (g (z TYPE) ITERM) SCRIPT)
         | (holds h (g) SCRIPT)
         | (reduced DEPTH SCRIPT)
         | (succ-pred NAME SCRIPT)
         | (test-cases (NAME ARGUMENT…) ROUNDS NAME SCRIPT SCRIPT)
         | (mask-hypotheses NAME NAME ROUNDS SCRIPT)
         | (auto-conditions SPLITS NAME RULE…)
         | (bits-cases x BITS SCRIPT LABELLED…)
LABELLED ::= (LABEL…) SCRIPT
ARGUMENT ::= any | ITERM
```

An abbreviation `(abbreviation NAME ITEM…)` names one or more items, each
any form. In the forms after it in its document, the atom `NAME` in a list
stands for the items in its place, as they are written, the abbreviations
before it expanded in them; so it names a type, a term, part of a script,
or several rules. An abbreviation states nothing: the theorems of a
document are those of its forms with the abbreviations expanded, a
certificate holds none, and the names in an item are read where the item
stands, so that an item may mention a variable that each of its places
binds. An abbreviation is of its document alone, and a document that
imports another declares its own.

A theorem's companion is the theorem with its sides in weak normal form.
The form `(normal DEPTH RULE…)` after a theorem's script gives its
companion another: its sides reduced to the depth, rewriting by the rules,
which name the statement's hypotheses and the theorems before it. A lemma is
so stated as its source writes it and rewrites as the reduction that cites
it presents its left side, where the Lean developments compute a lemma's
statement by that reduction.

A rule `(folded DEFINITION…)` names definitions that a reduction keeps
folded, those of the program by their names and those of the translation's
library as `(lib NAME)`; the reduction unfolds every other. `with-rules`
proves the goal by its script with the rules before the language's and the
unfolding of the definitions, in place of the rules that a script around it
gives, so that each reduction of the script, those of the hypotheses and of
their instances among them, rewrites by them; a rule that a tactic of the
script names precedes them.

The tactics added:

* `fold-uniqueness` proves the goal by induction on its innermost variable
  `x`, a list, in the form of the uniqueness of a fold, as `fold-induction`
  does, each premise by a script: the first script proves the equation of
  the sides at the empty list, and the second, for each side, that the side
  at a head `y` before a list `ys` is the step, in which `r` is that side
  at `ys`.
* `tree-fold-uniqueness` proves a goal whose one variable `x` is a tree by
  the uniqueness of the tree's fold, as `tree-fold-induction` does: its
  script proves, for each side, that the side at the node of a label `l`
  and children `cs` is the step, in which `rs` is the list of that side at
  the children.
* `instance` proves a goal whose sides have, at the depth and with the
  rules, the normal forms of the sides of `LEMMA`, which equates two
  functions, at its objects and at the first terms for its variables,
  applied to the second terms. `pointwise` is the instance at a theorem's
  own variables, applied to the goal's innermost.
* `have` proves the goal under a hypothesis `h` cut in: the equation of the
  sides of `LEMMA` at its objects and at the first terms for its variables,
  applied to the second terms, as they are stated.
* `congruence` proves the goal under a hypothesis `g` cut in: the equation
  of the applications, to the two sides of the hypothesis `h`, of the
  function of `z` that the term is.
* `holds` proves the goal under a hypothesis `g` cut in: the left side of
  the hypothesis `h`, an equation whose right side is the equation of a
  term with itself.
* `reduced` proves the goal by its script's proof of the equation of the
  sides' normal forms at the depth.
* `succ-pred` proves an equation of two applications by its script's proof
  of it with each argument replaced by the left side, at the two innermost
  variables, of the theorem `NAME`, which equates the successor of the
  predecessor of a bit before a bitstring with that bitstring.
* `test-cases` analyses the values of tests to a number of rounds. The
  sides are reduced to weak normal form, and the first of their subterms,
  outside binders and folds, that applies the definition `NAME` of the
  program to arguments, each any term, written `any`, or the term given, is
  generalized to a tree, the value of a test. The tree is split to a node,
  and its label to the empty bitstring, where the test is false and the
  search repeats, and to a bit before a bitstring, where it is true and the
  first script proves the goal. Where no such subterm occurs, or the rounds
  are spent, the second script proves it. The theorem `NAME` is that a tree
  is the node of its unfolding.
* `mask-hypotheses` rewrites under masks to a number of rounds. The sides
  are reduced to weak normal form; where a conditional among their subterms
  has a test under which a hypothesis rewrites a term of its first branch,
  the equation of the conditional with the one rewritten is cut in and
  rewrites, and the search repeats. The script then proves the goal with
  the equations cut in before the rules. The theorems named are that inside
  the branch a test selects, a conditional on the test is its first branch,
  and that a conditional between two terms of one value is that value.
* `auto-conditions` reduces to weak normal form and splits the list,
  coproduct or tree variable that the reduction, or the test of a
  conditional kept folded, is stuck on, up to a number of times; the
  theorem `NAME` is that a tree is the node of its unfolding.
* `bits-cases` takes, after its script, scripts for the bitstrings of
  labels: at the bitstring of each label listed before a script, a numeral
  of fewer bits than `BITS`, that script proves the goal in place of the
  first. A script is read at each number of bits it proves at.

The scripts of `test-cases` and `mask-hypotheses` are read at each number
of rounds, in the variables and hypotheses the rounds add, none of them
named. The tactics are `byRoseIndWith`, `bySuccPred`, `byNF`, `byMaskSubs`
and `byAutoC` of `Geb.FreeTopos.Tactics`, and the derivations that the Lean
developments compose where they cut in an instance, a congruence or a
formula, which `bootstrap/authoring.geb` composes. A rule that names a
theorem is tried only where the root of its companion's left side occurs.

The documents `weakening.proofs.geb`, `substitution.proofs.geb` and
`expansion.proofs.geb` under `bootstrap/proofs/` state and prove with them
the developments of `GebTests/Prototypes/FreeTopos/Weakening.lean`,
`Substitution.lean` and `Expansion.lean`: that weakening and substitution
preserve the types the kernel's type checker infers, about the program of
`bootstrap/weakening.manifest`, the second importing the first; and that the
expansion of the datatype language is the identity on a program of kernel
forms, about the program of `bootstrap/kernel-forms.manifest`, whose module
`bootstrap/proofs/kernel-forms.geb` defines the predicates of kernel
expressions and forms and the two sides of each statement. A lemma's
companion is the theorem the Lean development states, node for node, but for
the lemmas that equate functions, which are cited as stated. A lemma about
a fold of the type checker, of the traversal or of the expansion states the
fold as the reduction presents it: the rose tree's fold that the kernel's
fold translates to, applied to the kernel's step, which the document writes
out as the source does, since no definition of the source names it. The
proof at a construction is chosen by the label, as the Lean developments
choose it:

```
(tree-induction t (l cs ih)
  (with-rules (typing-rules nth-weaken)
    (bits-cases l 5 by-reduction
      (8 13 14) (revert-cases ih cs (a as) by-reduction …)
      (9 10 12 20) …
      (16) …)))
```

`scripts/proofs.sh` proves and replays the developments, each document that
no other imports with those it imports. Their searches take from minutes to
tens of minutes compiled, so `slow-checks.yml` runs the script, and
`scripts/tests/test-proof-scripts.sh` proves the development of
`tree-cases.proofs.geb` and exercises each form on the example.

# Holes and goals
%%%
tag := "proof-holes"
%%%

In version `3` a hole stands where a script stands:

```
SCRIPT ::= … | ?NAME
```

`?NAME` is the authoring spelling of the form `(hole NAME)`, which the
strict encodings write. A hole proves nothing. A document with a hole is
not proved: `prove` and `check` report the hole where it is written, with
its goal, and write no certificate. For the document

```
(proofs 3 (program pair)
  (theorem append-nil (forall ((xs (List T))) (equal (Lists.append xs (nil T)) xs))
    (by (induction xs (y ys ih) (reduce weak) ?step))))
```

`lake exe geb-author check Draft.proofs.geb` writes one diagnostic, whose
line is broken here and its goal abridged, and exits with status 1:

```
Draft.proofs.geb:3:47: error: the script of the theorem append-nil leaves the hole ?step
open, at the goal (internal () (forall ((y T) (ys (List T))) (implies (ih …) (equal … …))))
  (internal ()
    (forall ((y T) (ys (List T)))
      (implies (ih (equal (Lists.append ys (nil T)) ys))
        (equal (Lists.append (cons T y ys) (nil T)) (cons T y ys)))))
```

The diagnostic's line holds the goal, so that an editor reading
diagnostics a line at a time keeps it; a goal of more than 72 characters
is also laid out on the lines after it. The problem matcher of the `geb`
extension and the format of `editors/efm-langserver/config.yaml` read the
line as they read every diagnostic.

The goal is a statement of the internal language
({ref "internal-statements"}[Statements over the internal language]),
whichever language the theorem is stated in: the object variables, the
variables of the context with their types, the hypotheses, and the equation
to prove. Its names are those the script has at the hole, here the `y`,
`ys` and `ih` that the induction's script gives. A variable or a hypothesis
that a tactic adds without a name, as the case analysis of bits and the
searches by rounds add them, and a variable that a term binds, is named by
an underscore before its position: `_3`, the variables counted from the
outermost, or `_h0`, the hypotheses from the first. The sides and the
hypotheses are reported reduced by β and by the components of pairs
wherever those apply, under binders too. A tactic that splits a variable,
generalizes a term or takes an induction states the goal of the script
within it by applying abstractions to the new variables, and the reduction
leaves the terms the script is written about. A type or a term that the
syntax of statements does not write is reported as `(opaque LABEL PART…)`,
which no document reads. A goal without one is a statement that a document
reads, so that a goal may be stated as a lemma as it is reported.

A script that does not prove its theorem is reported in the same form, at
each innermost step that fails, with the goal that step is given. With the
script `(induction xs (y ys ih) (normalize 0) …)` in the document above:

```
Draft.proofs.geb:3:33: error: the script of the theorem append-nil does not prove it: this
step does not prove the goal (internal () (equal (Lists.append (nil T) (nil T)) (nil T)))
```

The runner runs a script once as it is written. Where the script proves
nothing, the runner runs it again, each script within it then returning its
goal where it proves nothing, so that the steps reported are those that
fail with every script within them proving its goal or itself reported. An
alternative, `(first SCRIPT SCRIPT)`, is reported by the failure of its
second script, its first being run as it is written. A script that a
tactic reads at several cases, as `bits-cases` reads its scripts, is
reported once for each case at which its hole is reached or its step fails.
A hole that no proof reaches, as the second script of an alternative whose
first proves the goal, states no obligation, and its theorem is proved.

A theorem with an obligation is not proved, and the theorems after it are
proved under it: it and its companion are entries of the development
without derivations, so that a rule naming it rewrites by it. One run
therefore reports every theorem of a development that has an obligation,
and a theorem may be proved from a lemma whose proof is still a hole. The
development has no certificate until no obligation remains.

The report is the prover's and no checker certifies it. The tactic of a
hole returns, as the derivation of its goal, a leaf of no rule of the
checker that keeps the goal; the tactics build their derivations around
those of the scripts within them and read none of them, so the leaf reaches
the runner within the derivation of the theorem's script, and the runner
reports the leaves it finds there and gives that derivation to no checker.
The checker of developments rejects a derivation that holds one. The
checker of holes of the Bootstrap chapter
({ref "typed-holes"}[Typed holes]), which certifies a theorem under the
obligations of its holes, is a separate checker, written in Lean. The
hole's form, the leaf, the goal's statement and the report are in
`bootstrap/authoring.geb`, and the host finds an obligation's place in the
document as written, after the abbreviations are expanded, in
`GebHost/Authoring.lean`.

# Definitions and natural numbers
%%%
tag := "definition-scripts"
%%%

Version `4` reads what version `3` reads, and adds the natural numbers, the
definitions that a development declares, and every connective among the
constants of a development:

```
DOCUMENT ::= (proofs 4 HEADER… FORM…)
FORM ::= … | (definition NAME ((x TYPE) …) TYPE ITERM)
TYPE ::= … | Nat
ITERM ::= … | zero | (succ ITERM) | (nat-rec ITERM (r) ITERM ITERM)
        | NAME | (NAME ITERM…)
RULE ::= … | (unfold NAME)
SCRIPT ::= … | (nat-induction x FUEL RULE…)
```

`Nat` is the natural numbers object, `zero` and `(succ t)` its zero and
successor, and `(nat-rec z (r) s n)` the fold of the number `n`: `z` at
zero, and at a successor the term `s`, in which `r` is the fold's value at
the number before it. The zero and the successor are primitive arrows of a
development of version `4`, after those of the lists, the trees and the
coproducts, and its reductions compute the fold at each. No variable of a
document of version `4` takes the name `zero`, `succ` or `nat-rec`.

A form `(definition NAME ((x TYPE) …) TYPE ITERM)` declares a definition of
the internal language, in no object variables: `NAME` at parameters of the
types given is the term, of the type given, which is read in the parameters.
The name is one a variable may take, so none the kernel's reader reserves,
and is that of no definition of the program, of no theorem and of no
definition declared before it. The definitions of a development follow the
connectives' among the constants it is checked with, in the order of their
forms, each read and checked with those before it, and their declarations
follow the connectives' rules in its certificate, before the theorems',
under their names. In the forms after a definition's, of its document and
of the documents after it in the development, `(NAME t…)` applies it to a
term for each of its parameters, and `NAME` alone is a definition without
parameters. The name then stands for the definition wherever it is written
in those forms, as an abbreviation's does for its items, and `Nat` for the
natural numbers, so that no variable, hypothesis or theorem of those forms
takes either name. The reductions keep a declared definition folded, as they
keep the connectives: a rule `(unfold NAME)` unfolds it, and a rule
`(folded NAME…)` may name it among the definitions it keeps.

`nat-induction` proves the goal by induction on its innermost variable `x`,
a natural number: at zero, and at a successor under the induction
hypothesis, each by normalization within the budget with the rules, the
hypothesis rewriting at the successor. It is
`Geb.FreeTopos.Internal.byNatIndHyp`.

The connectives of a development of version `4` are those of
`Geb.FreeTopos.Internal.Logic`: truth, conjunction and implication and,
after them, the universal quantification, falsity, negation, disjunction and
the existential and unique existential quantifications, with the
introduction and elimination rules of each, which begin the certificate
(`bootstrap/free-topos/logic.geb`). A test compares the definitions and the
rules with Lean's
(`GebTests/Prototypes/FreeTopos/InternalLogicMirror.lean`). Version `4`
reads no term and no tactic of the connectives after implication; its
certificates have their layout, so that the forms that will read them add no
declaration to a certificate.

The cache of a development of version `4` keeps the declarations of its
definitions, and a development is aligned with a cache of the definitions it
declares alone: a definition declared after the others, or defined
otherwise, leaves every theorem checked or proved
({ref "proof-cache"}[The cache of a development]). A document of version `4`
imports documents of versions `1` to `4`.

The document `normalization-base.proofs.geb` under `bootstrap/proofs/`
begins in this version the development of
`GebTests/Prototypes/FreeTopos/NormalizationBase.lean`, the base of the
fundamental lemma of the evaluator, about the program of
`bootstrap/normalization.manifest`. It declares the addition of natural
numbers, by which the levels of the evaluator's fuel are counted, and
proves its lemmas: zero and a successor on each side, associativity and
commutativity. The rest of that development, and those of
`NormalizationConst.lean`, `NormalizationRel.lean` and `Normalization.lean`,
remain Lean deducers. Their statements are formulas of the connectives
rather than equations, and their deductions use the connectives' rules,
which version `5` exposes below. Naming the program's otherwise unnamed
folds and porting the remaining deductions are still outstanding.

# Formula statements and proofs
%%%
tag := "formula-scripts"
%%%

Version `5` accepts any internal term of type `Omega` as a conclusion or a
named hypothesis. It reads all the connectives already defined and checked
in version `4`:

```
DOCUMENT ::= (proofs 5 HEADER… FORM…)
PROPOSITION ::= FORMULA | (assuming (h FORMULA) … FORMULA)
FORMULA ::= ITERM                         ; checked at Omega
ITERM ::= … | false | (and ITERM ITERM) | (or ITERM ITERM) | (not ITERM)
        | (all TYPE ITERM) | (exists TYPE ITERM) | (exists-unique TYPE ITERM)
SCRIPT ::= … | (truth) | (hypothesis h) | (assume h SCRIPT)
         | (and-intro SCRIPT SCRIPT) | (and-elim h (hp hq) SCRIPT)
         | (imp-elim h SCRIPT name SCRIPT)
         | (or-left SCRIPT) | (or-right SCRIPT) | (or-elim h (hp hq) SCRIPT SCRIPT)
         | (all-intro x SCRIPT) | (all-elim h ITERM name SCRIPT)
         | (exists-intro ITERM SCRIPT) | (exists-elim h (x hx) SCRIPT)
         | (false-elim SCRIPT) | (unfold-formula SCRIPT)
         | (unfold-hypothesis h name SCRIPT)
         | (use THEOREM (TYPE …) (ITERM …) SCRIPT …)
```

These propositions occur inside `(internal (X …) PROPOSITION)`, optionally
under the existing outer `(forall ((x TYPE) …) PROPOSITION)` context binder.
The logical term `(implies P Q)` retains its binary meaning, including when
`P` is a predicate application such as `(P x)`. Named assumptions use
`assuming` so that those two forms are unambiguous. To move a version `4`
internal statement to version `5`, change its outer named-hypothesis form
from `implies` to `assuming`; logical implications stay as they are. The new
connective keywords and `assuming` are reserved in version `5`, so bindings
that used those names need renaming.
Kernel statements keep their existing equational grammar. Imported documents
retain their own version, and versions `0` through `4` retain their meanings
and certificate formats.

A quantifier takes a predicate of type `(Arrow TYPE Omega)`, either a
lambda such as `(lam ((x X)) (P x))` or a term such as `P`. `all-intro`
introduces a fresh variable; `all-elim` instantiates its named hypothesis
at a term and names the resulting hypothesis. `exists-intro` supplies a
witness; `exists-elim` introduces a fresh witness and its hypothesis only
within its child script. Instances of lambda predicates are beta-reduced
before the child script sees them. The checker validates the witness type
and the quantified proof's context.

`assume` proves an implication under its antecedent. `and-intro` proves its
two conjuncts; `and-elim` gives its child both conjuncts of a named
hypothesis. `imp-elim` proves the antecedent of its named implication with
its first script, then gives its second script the named consequent.
`or-left` and `or-right` choose a disjunct; `or-elim` proves the same
conclusion under each disjunct, with `hp` visible only in its first branch
and `hq` only in its second. `false-elim` proves the goal from its child's
proof of falsity. `hypothesis` requires the goal to match its named
hypothesis. Every introduced name is fresh in its scope.

`unfold-formula` unfolds the goal's outer definition once, and
`unfold-hypothesis` names the result of unfolding a hypothesis once. These
expose negation as implication to falsity, and unique existence as existence
conjoined with uniqueness, so their proofs use the same scripts.
They also unfold definitions declared by the document.
`use` applies an earlier theorem, including an imported one, at explicit
object and variable arguments in the order of its written binders. Its child
scripts prove the instantiated hypotheses in their written order; the
instantiated conclusion must match the goal.

Equation scripts still prove equations directly. At a general formula `P`,
they instead prove `(equal P true)` and convert that proof back to `P`.
Logical scripts can also prove a goal explicitly equating a formula with
truth. Formula declarations retain their original conclusions in the saved
certificate; their rewriting companions equate those conclusions with truth,
in the requested normal form. The adapters and logical scripts are written
in `bootstrap/formula.geb` and `bootstrap/authoring.geb`, and every resulting
derivation passes the existing checker. No rule is added to it.

The development in `examples/authoring/Logic.proofs.geb` uses these scopes
to transport an existential witness along a function. It also imports the
version `1` pair development.
Its canonical document and certificate are recorded beside that development's
artifacts, regenerated and replayed by `scripts/authoring.sh`.

```
lake exe geb-author prove examples/authoring/Logic.proofs.geb /tmp/logic.cert
lake exe geb-author replay examples/authoring/Logic.proofs.geb /tmp/logic.cert
```

`scripts/tests/test-proof-formulas.sh` exercises formula type checking, the
logical scripts, rejection of escaping or mistyped witnesses and branch
hypotheses, goal display, cache reuse, conversion between durable spellings
and replay against changed statements.

# The cache of a development
%%%
tag := "proof-cache"
%%%

`prove` and `check` take a directory of caches, here for a proof document
`Draft.proofs.geb` that names its program:

```
lake exe geb-author check --cache .lake/geb-proof-cache Draft.proofs.geb
lake exe geb-author prove --cache .lake/geb-proof-cache Draft.proofs.geb /tmp/draft.cert
```

With the option, a development is resumed from the cache of its proof
document in that directory, a file named by the document's file name and a
number of its path, and the cache is written as the run leaves it, whether
or not the development is proved. The command prints how the declarations
of the development's theorems were come by:

```
cache: 61 taken, 4 checked, 1 proved, 0 not proved
```

A cache keeps, for each theorem of the development in order, its name, its
statement, its script, the normal form its companion is to have and the
version of its document, with the sides of its companion and, where the
theorem is proved, the derivations of the theorem and of its companion. A
theorem's declarations are come by in the first of three ways that
applies.

* Taken. The cache's item at the theorem's position has its name,
  statement, script, normal form and version, and is proved; the cache is
  of the development's compiled program; and every theorem before it
  stands at its position in the cache with its statement and the sides of
  its companion. The constants and the entries before the theorem are then
  those its derivations were checked with, and its declarations are taken
  as they stand, with no search and no check.
* Checked. An item of the cache, at any position and of any program, has
  the theorem's name, statement, script, normal form and version, and is
  proved. A derivation cites an earlier theorem by the position of its
  entry, so the entries the item's derivation cites are renumbered to
  those of the theorems of the same names, and the checker of developments
  is given the derivation with the entries of the present development.
  Where it admits the derivation the theorem is declared with it, and the
  theorem's companion is derived again.
* Proved. The theorem's script is run, as without a cache.

A theorem that is not proved, one with a hole or a step that fails, keeps
no derivation, and its script is run at each run. So a script that changes
is run again, and the theorems after it are taken, their entries standing
as they stood; a theorem stated, removed or moved before others leaves them
checked, and none is searched for again unless its derivation cites what is
no longer stated; and a statement that changes is proved again, as is a
theorem after it whose derivation no longer checks. A script that does not
change is not run again when the prover changes, its derivation standing.

A term names a definition by its position among the constants: the
library's definitions, then the program's in the program's order, then,
in version `3`, the connectives. A statement and a derivation are
therefore of one compiled program, and a cache is kept beside the program
it is of. The items of a cache of another program are read with the
definitions they name at their places in the present program, by the
names the two programs give their definitions: a definition of the
program at the position of the present definition of its name, a
connective at its position after the present definitions, and a
definition that the present program does not declare at a position that
names none. Under a changed program every theorem is thus checked or
proved, none taken. A definition stated before or after the others, or
the definitions stated in another order, leaves every theorem checked and
none searched for. A theorem is proved again where its statement names a
definition that is no longer declared, and where its derivation unfolds a
definition that is defined otherwise, which the check rejects. The run
leaves a cache of the present program, from which the next run takes.

`check` with a cache replays nothing: a theorem taken was checked by the
run that left the cache, with the same constants and entries, and the
others are checked as they are found. `prove` replays the certificate
before writing it, as it does without a cache, so that a certificate is
checked whatever a cache holds; proved with the cache of the same prover,
it is the certificate of a development proved without one. A cache is no
durable artifact: its format is `geb-proof-cache/v1`, a file that does not
read, or that is of another format, theory or profile, is no cache, a
cache left by a development of another version holds no item for this
one, and deleting a cache costs a search. A development that does not
read leaves its cache as it is, and one the runner stops before its last
theorem leaves a cache of the theorems before that.

A certificate is of one compiled program as well, the program its
envelope holds, and `replay` accepts it against that program alone.
`transport` reads a certificate of another program as the items of a
cache are read, its declarations with the definitions they name at their
places in the present program, and writes the certificate of the present
program where that replays against the development:

```
lake exe geb-author transport Draft.proofs.geb /tmp/earlier.cert /tmp/draft.cert
```

It runs no script and decides nothing. Where the present program declares
no definition of a name the certificate's declarations cite, or defines
one otherwise than a derivation unfolds it, the development does not
replay, and nothing is written. The certificate read is left as it is.

The task `Geb: check saved file` of `.vscode/tasks.json` and the command
of `editors/efm-langserver/config.yaml` pass
`--cache .lake/geb-proof-cache`, so that a document checked when it is
saved is searched only where it changed. The cache's items, the three
ways, the renumbering of entries and the places of definitions are in
`bootstrap/authoring.geb` (`Authoring.resume`, `Authoring.itemsFor`,
`Authoring.transport`), the files and their envelopes in
`GebHost/Authoring.lean`, and `scripts/tests/test-proof-cache.sh`
exercises them.

# Keeping the source

The authoring spelling and the canonical, advanced and basic transport
encodings hold the same source document, including comments, names,
notes, examples and unknown optional fields. For example:

```
lake exe geb-author convert canonical examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair.proofs.csexp
lake exe geb-author convert advanced examples/authoring/pair.manifest \
  /tmp/pair.proofs.csexp /tmp/pair.proofs.advanced
lake exe geb-author convert authoring examples/authoring/pair.manifest \
  /tmp/pair.proofs.advanced /tmp/pair.proofs.geb
```

The same commands work on the program source. `compile`, `prove` and
`replay` accept every spelling. The `convert` output choices are
`canonical`, `advanced` and `authoring`; the reader also accepts canonical
bytes encoded in base-64 between braces. An authoring document gets its
profile from the manifest; a strict document carries it explicitly and
must agree with the manifest. Unsupported mandatory profile features are
rejected. The existing document retraction laws apply to these documents;
conversion does not promise to keep a particular whitespace layout.

The record in `examples/authoring/record/` contains the checked program
image, its elaborated definitions, the certificate, the compiler image, canonical copies of
the program's and the proofs' source documents, and the SHA-256 digests of the inputs. The digests
pin the compiler image and emitted compiler, the authoring runner and its
source dependencies, the manifest and sources, the Lean toolchain and
dependency lockfile. `record/compiler.img` retains the exact bytes of
`bootstrap/compiler.img` used at the milestone. The certificate envelope separately identifies
its format (`geb-proof/v2` for version `1`, `geb-proof/v3` for version `2`,
`geb-proof/v4` for version `3`, `geb-proof/v5` for version `4`), theory
(`free-topos/base/v1`),
document profile and exact compiled program; its declarations retain the
statements, their companions and their source names.

```
scripts/authoring.sh check
scripts/tests/test-authoring.sh
```

The first command regenerates and compares the record. Use
`scripts/authoring.sh regen` when intentionally updating it, then review
the sources and record together. `scripts/authoring.sh runtime` regenerates
only the emitted proof runner when its Geb source changes. The second
command tests conversion, metadata preservation, compilation, replay and
rejection through the command-line interface.

Edition `0` is still a pre-release edition. Keep the whole record with
work written against it. No migration to a future edition is implemented
here; its durable document, elaborated definitions and exact compiler
give that migration explicit inputs. The checker of holes in proofs, which
certifies a theorem under the obligations of its holes, statements over
datatypes and completion of datatype soundness remain separate work.

# Preserving a development

The preservation workflow applies the same compilation, example checking,
document conversion and certificate replay to any program manifest and
proof document accepted by the current authoring commands. For the
development under `examples/roundtrip/`, whose manifest orders a library
and its application in separate layers:

```
python3 scripts/preserve.py record examples/roundtrip/roundtrip.manifest \
  examples/roundtrip/Roundtrip.proofs.geb /tmp/roundtrip-record
python3 scripts/preserve.py verify /tmp/roundtrip-record
python3 scripts/preserve.py check /tmp/roundtrip-record
python3 scripts/preserve.py compare /tmp/roundtrip-record \
  examples/roundtrip/roundtrip.manifest examples/roundtrip/Roundtrip.proofs.geb
```

`record`, `check` and `compare` build the host executables first. Pass
`--no-build` before the subcommand to use the executables already built
in this checkout.

`record` first copies the manifest, every source in its order, and the
proof document with the documents it imports, retaining their original
bytes and relative paths.
It compiles those copies, checks the examples, produces and replays a
certificate, and writes canonical copies of the complete documents.
The record also holds the checked image, the elaborated definitions,
the exact compiler image and emitted compiler, the emitted proof runner,
the Geb source closures of the compiler and proof runner, the Lean
toolchain and dependency lockfile, and the SHA-256 identities of the
native host executables. Native executables and installed dependencies
are not copied; rebuilding a historical native host is outside this
workflow. The retained images, emitted code and source inputs are
available to a future migration.

The directory is published only after its checks succeed, by
[renaming](https://docs.python.org/3/library/os.html#os.rename) a
staged directory on the same filesystem. An existing record is never
replaced. A new record uses a new directory, so earlier inputs and results
remain available. To retain a proof that already checks, pass
`--certificate PATH` to `record`: it replays that certificate instead of
running proof search. In particular, insufficient search fuel does not
prevent recording or checking a development whose saved proof replays.

`record.json` identifies format `geb-development/v1`, the archived
manifest and proof document, the ordered source paths, and the SHA-256
digest of every other file; where the proof document imports documents the
format is `geb-development/v2`, and the record names them. `verify` checks
this inventory without Lake
or the original project. It rejects missing, modified and unlisted files,
symbolic links, paths outside the record and unsupported record formats.
These digests check integrity relative to the index; they neither
authenticate it nor establish a theorem.

`check` reads the archived sources with the current host, compares their
canonical documents, checked image and elaborated definitions with the
record, and replays its saved certificate, checking examples again.
It performs no proof search and does not regenerate the record. A moved
record therefore remains checkable after the original project is removed,
provided the current host still reads its profile and reproduces its core.

`compare` performs the same compilation and replay on the supplied
current sources. It reports document changes separately: edits to
comments, notes and script budgets may preserve the checked core and
permit replay. A different compiled program, even one equivalent by a
theorem, is rejected; comparing meanings through such a theorem requires
an explicit migration. A statement changed to another true statement is
also rejected by replay. Failure leaves the record unchanged.

The committed record under `examples/roundtrip/record/` is checked and
compared with its sources by `scripts/tests/test-preservation.sh`, which
also exercises relocation, documentation changes, reuse of a saved proof,
corrupt records and failed creation. Continuous integration runs this test.
The Pair development's earlier record remains in its original format.

## Migrating a proof document

The migration from proof-source version `1` to `2` enables the latter's
document imports while retaining the existing statements and scripts.
It accepts an immutable development record produced by `preserve.py`:

```
python3 scripts/preserve.py record examples/authoring/pair.manifest \
  examples/authoring/Pair.proofs.geb /tmp/pair-v1
python3 scripts/preserve.py migrate-proof-v2 /tmp/pair-v1 /tmp/pair-v2
python3 scripts/preserve.py check /tmp/pair-v2
```

The migration verifies and checks a copy of the old record. The host
`geb-author migrate-proof-v2` changes only the proof document's version
atom, retaining its decorated tree, including names, comments and
references. Program sources, including unknown note fields, are copied
verbatim. The migrated proof uses the authoring spelling; its layout may change.
It replays the saved
certificate payload against both versions and changes its envelope from
`geb-proof/v2` to `geb-proof/v3`; it runs no proof search. These versions
share the theorem-and-companion layout and the translated program.

The new record is published after the normal record checks, with its
checked image and elaborated definitions byte-identical to the old ones.
Its `migration.json` names operation `proofs/1-to-2` and the SHA-256 digest
of the predecessor's `record.json`. This receipt is included in the new
inventory. The old record remains unchanged; an existing destination is
rejected. The migrated source under the new record's `proofs/` directory
can be copied back into a working project. Keep both records.

`scripts/tests/test-proof-migration.sh` exercises a relocated archive
after deleting its original project. Its search budgets are insufficient
to regenerate the proof, while replay succeeds. Reversing the version
atom reproduces the entire old canonical decorated document; corrupt
records, rejected certificates and unsupported source versions publish
no new record. The migration establishes these checks for the accepted
development. It is neither a general preservation theorem nor a migration
between semantic editions or datatype representations.
