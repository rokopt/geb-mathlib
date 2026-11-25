/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Image
public import GebBoot

set_option doc.verso true

/-!
# A program compiled a layer at a time

A manifest divides a program's sources into layers ({lit}`Geb.Kernel.Manifest`). The compiler's
stages are folds of a program's forms from a state, so that the state after the forms of the
layers before one is what the layer is compiled against: the elaboration of modules
({lit}`Modules.elabForms`), the expansion of the datatype language ({lit}`Datatype.xpStep`), its
typing ({lit}`Expansion.checkStep`) and the reading with the kernel's check
({lit}`Support.readMore`). This module composes those stages a layer at a time, as
{lit}`Compile.readState` composes them over a whole program, and keeps the state after each
layer in a directory, under the layers' texts, so that a later compilation of a program that
begins with the same layers reads the state where it would compute it.

The program compiled so is the program of the layers' texts joined, and its bundle is the same.
Two stages read the whole program: the typing checks every form with the markers of all the
program's datatypes, of which a form reads those of the datatypes declared before it, and the
recognizer of a datatype is written where its marker stands when any form refers to it. A layer
is therefore compiled with the markers of its own and the earlier layers' datatypes; and where a
layer first refers to the recognizer of an earlier layer's datatype, the reader inserts it at
the datatype's marker in the saved kernel forms and reads those forms again. The elaboration,
expansion and datatype typing of the earlier layers are reused. For a program a stage rejects,
the composition gives nothing and the whole compilation reports the failure.

A state is kept as the image of a tree: the declarations of the expansion, the typing's and the
reading's declarations as the entries of their tries, which are built again when the state is
read, the markers, and the terms and names read. The state of the elaboration of modules is not
kept: the layers before the first compiled are elaborated again, which takes the time of that
stage alone. A kept state is used when the texts kept beside it are, byte for byte, the texts
of the layers and the compiler's identity, so that the name of its file, a hash of them, only
finds it. With the environment variable {lit}`GEB_LAYERS_TRACE` set, each state read, each layer
compiled and each state kept is reported on standard error with its time.

## Main definitions

* {lit}`State` — the stages' states after some of a program's layers.
* {lit}`advance` — the state after one more layer.
* {lit}`bundle` — a program's checked bundle from its layers, with a directory of kept states.

## Tags

bootstrap, compiler, layers, cache
-/

open Geb Geb.Kernel

public section

namespace GebHost.Layers

/-- The state of the elaboration of modules, as {lit}`bootstrap/modules.geb` declares it. -/
abbrev Modules : Type :=
  Tree × (Tree × (List Tree × (Tree × (List Tree × (List Tree × (List Tree × Tree))))))

/-- The state of the typing over supports, as {lit}`bootstrap/stage1/expansion.geb` declares
it. -/
abbrev Typing : Type := Tree × ((Tree × Tree) × List Tree)

/-- The state of the reading, as {lit}`bootstrap/support.geb` declares it. -/
abbrev Reading : Type := Tree × (Tree × (Tree × (Tree × (Tree × (List Tree × List Tree)))))

/-- The stages' states after some of a program's layers. -/
structure State where
  /-- The number of the module forms and of the declarations with type parameters read, which
  bounds the depth of nesting and of instantiation. -/
  count : Nat
  /-- The state of the elaboration of modules. -/
  modules : Modules
  /-- The declarations of the expansion of the datatype language. -/
  decls : List Tree
  /-- The state of the typing. -/
  typing : Typing
  /-- The markers of the datatypes declared, in order. -/
  markers : List Tree
  /-- Those of the markers whose recognizer no layer has written. -/
  pending : List Tree
  /-- The erased kernel forms, in source order, before inserting recognizers. -/
  kernelForms : List Tree
  /-- The state of the reading. -/
  reading : Reading

/-- The states before a program. -/
def State.start : State :=
  ⟨0, GebBoot.«Modules.stStart», [], GebBoot.«Expansion.start», [], [], [],
    GebBoot.«Support.readStart»⟩

/-- The value of an optional tree as the compiler represents it. -/
def some? (t : Tree) : Option Tree := if t.label = 1 then t.children.head? else none

/-- The forms of a layer's text as module elaboration writes them after the layers before it,
with the count that bounds the depth of the elaboration and its state after it, when the text reads,
names none of the implementation's names and its modules elaborate. -/
def elaborated (count : Nat) (modules : Modules) (text : ByteArray) :
    Option (Nat × Modules × List Tree) := do
  let sx ← some? (GebBoot.«Reader.readSExps» (ofBytes text).children)
  guard ((GebBoot.«Compile.userSource» sx).label ≠ 0)
  let count := count + (GebBoot.«Modules.moduleCount» sx.children).label
  let m := GebBoot.«Modules.elabForms» (GebBoot.«Modules.elabAt» (leaf (count + 1))) (mk 0 [])
    (modules.1, modules.2.1, [], modules.2.2.2) sx.children
  guard (m.1.label ≠ 0 ∧ m.2.2.2.2.1.isEmpty)
  return (count, m, m.2.2.1.reverse)

/-- Whether a form is a template's instance at opaque arguments, as the expansion tests it. -/
def isGeneric (e : Tree) : Bool :=
  (GebBoot.«Prelude.and» (GebBoot.«Datatype.isListTx» e)
    (GebBoot.«Datatype.namedTx» (GebBoot.«Datatype.nthTx» (GebBoot.«Datatype.elems» e) (leaf 0))
      GebBoot.«Datatype.kwGeneric»)).label ≠ 0

/-- The forms that replace a form where the recognizers a layer refers to are written, given
every marker and the atoms of the layer's forms that end as a recognizer's name does. -/
def written (markers refs : List Tree) (f : Tree) : Option (List Tree) :=
  (some? (GebBoot.«Recognize.recognizersAt» markers refs f)).map (·.children)

/-- Whether a marker is replaced by no form: no form of the layer refers to its recognizer. -/
def unwritten (markers refs : List Tree) (m : Tree) : Bool :=
  match written markers refs m with
  | some [] => true
  | _ => false

/-- The state after one more layer, given its text: its modules elaborated, its forms expanded,
checked with the markers of its own and the earlier layers' datatypes, erased, the recognizers it
refers to written, and the forms read and checked. A first reference to an earlier marker
requires rereading the kernel forms from the start. Nothing where a stage rejects the layer. -/
def advance (s : State) (text : ByteArray) : Option State := do
  let (count, modules, es) ← elaborated s.count s.modules text
  guard ((GebBoot.«Typing.Tx.member» (mk 2 es)).label ≠ 0)
  let x := es.foldl (init := ((leaf 1 : Tree), s.decls, ([] : List Tree))) fun x e ↦
    if isGeneric e then GebBoot.«Datatype.genericStep» x e else GebBoot.«Datatype.xpStep» x e
  guard (x.1.label ≠ 0)
  let expanded := x.2.2.reverse
  let typing := (GebBoot.«Datatype.markersFirst» expanded).foldl GebBoot.«Expansion.checkStep»
    s.typing
  guard (typing.1.label ≠ 1)
  let ks := GebBoot.«Datatype.kernelForms» expanded
  let own := GebBoot.«Recognize.markers» ks
  let markers := s.markers ++ own
  let refs := ks.flatMap GebBoot.«Recognize.memberAtoms»
  let kernelForms := s.kernelForms ++ ks
  let (forms, refs, start) := if s.pending.all (unwritten markers refs) then (ks, refs, s.reading)
    else (kernelForms, s.kernelForms.flatMap GebBoot.«Recognize.memberAtoms» ++ refs,
      GebBoot.«Support.readStart»)
  let fs ← forms.mapM (written markers refs)
  let reading := GebBoot.«Support.readMore» start fs.flatten
  guard ((GebBoot.«Support.unreadOf» reading).label ≠ 1 ∧
    (GebBoot.«Support.illTypedOf» reading).label ≠ 1)
  return ⟨count, modules, x.2.1, typing, markers,
    (s.pending ++ own).filter (unwritten markers refs), kernelForms, reading⟩

/-- The state after a layer whose later stages' states are known, given its text: the state of
the elaboration of modules alone, computed again. -/
def reelaborated (s : State) (text : ByteArray) : Option State := do
  let (count, modules, _) ← elaborated s.count s.modules text
  return { s with count, modules }

/-- The checked bundle of the layers compiled. -/
def State.bundle (s : State) : Option Tree := some? (GebBoot.«Support.readBundle» s.reading)

/-! ## Kept states -/

/-- The entries of a trie ({lit}`bootstrap/trie.geb`): at each node, those whose names' digits
end at it, the earliest first, and those of the tries below its digits. Put in this order into
the empty trie, they give the trie. -/
def entries : Tree → List Tree :=
  RoseTree.para fun _ kids ↦
    (((kids[16]?.map (·.1.children)).getD []).reverse) ++ (kids.take 16).flatMap (·.2)

/-- The trie of a list of entries, each put before those of its name already there. -/
def trie (es : List Tree) : Tree :=
  es.foldl (init := GebBoot.«Trie.empty») fun t e ↦
    GebBoot.«Trie.put» (e.children.getD 0 (leaf 0)) (e.children.getD 1 (leaf 0)) t

/-- The tree kept of a state: the later stages' states, their tries as their entries. -/
def State.kept (s : State) : Tree :=
  Kernel.mk 0 [Kernel.mk 0 s.decls,
    Kernel.mk 0 [Kernel.mk 0 (entries s.typing.2.1.1), s.typing.2.1.2, Kernel.mk 0 s.typing.2.2],
    Kernel.mk 0 s.markers, Kernel.mk 0 s.pending, Kernel.mk 0 s.kernelForms,
    Kernel.mk 0 [Kernel.mk 0 (entries s.reading.2.2.1), s.reading.2.2.2.1, s.reading.2.2.2.2.1,
      Kernel.mk 0 s.reading.2.2.2.2.2.1, Kernel.mk 0 s.reading.2.2.2.2.2.2]]

/-- The state a kept tree is of, but for the state of the elaboration of modules, which is that
before a program. -/
def State.ofKept (t : Tree) : Option State :=
  match t.children with
  | [decls, typing, markers, pending, kernelForms, reading] =>
    match typing.children, reading.children with
    | [td, serial, ms], [rd, rserial, count, terms, names] =>
      some ⟨0, State.start.modules, decls.children,
        (GebBoot.«Expansion.start».1, (trie td.children, serial), ms.children),
        markers.children, pending.children, kernelForms.children,
        (GebBoot.«Prelude.none», GebBoot.«Prelude.none», trie rd.children, rserial, count,
          terms.children, names.children)⟩
    | _, _ => none
  | _ => none

/-- The version of the kept states' form and of this composition, part of what a kept state is
kept under. -/
def version : String := "geb-layers/2"

/-- The identity of the compiled compiler: a hash of the Lean it is compiled from. -/
def compilerId : UInt64 := (include_str "../bootstrap/lean/GebBoot.lean").hash

/-- What the state after some layers is kept under: the version, the compiler's identity and
the layers' texts, each with its length. -/
def keyOf (texts : List ByteArray) : ByteArray :=
  texts.foldl (init := s!"{version} {compilerId}\n".toUTF8) fun acc t ↦
    acc ++ s!"{t.size}\n".toUTF8 ++ t

/-- The directory of the kept states in a directory of caches, which a development's cache
shares ({lit}`GebHost/Authoring.lean`). -/
def directory (dir : System.FilePath) : System.FilePath := ⟨s!"{dir}/layers"⟩

/-- The files of a kept state in a directory of caches: its image, and what it is kept under. -/
def paths (dir : System.FilePath) (key : ByteArray) : System.FilePath × System.FilePath :=
  let name := s!"{directory dir}/{(hash key).toNat}"
  (⟨s!"{name}.img"⟩, ⟨s!"{name}.key"⟩)

/-- The state kept under a key in a directory, where one is. -/
def load (dir : System.FilePath) (key : ByteArray) : IO (Option State) := do
  let (img, k) := paths dir key
  if !(← k.pathExists) || !(← img.pathExists) then return none
  if (← IO.FS.readBinFile k) != key then return none
  return (readImage (← IO.FS.readBinFile img)).bind State.ofKept

/-- Keep a state under a key in a directory of caches, each file put in place by a renaming. -/
def store (dir : System.FilePath) (key : ByteArray) (s : State) : IO Unit := do
  IO.FS.createDirAll (directory dir)
  let (img, k) := paths dir key
  let put (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
    let tmp : System.FilePath := ⟨s!"{path}.tmp{← IO.monoNanosNow}"⟩
    IO.FS.writeBinFile tmp bytes
    IO.FS.rename tmp path
  put img (writeImage s.kept)
  put k key

/-- The compiler state after a program's layers, with a directory of kept states:
the state kept after the longest run of the first layers is read, the layers of the run
elaborated again, the layers after it compiled, and the state after each kept. Nothing where the
composition gives nothing. -/
def compile (dir : System.FilePath) (layers : List ByteArray) : IO (Option State) := do
  let prefixes := (List.range (layers.length + 1)).map fun k ↦ layers.take k
  let trace (msg : String) (t0 : Nat) : IO Unit := do
    if (← IO.getEnv "GEB_LAYERS_TRACE").isSome then
      IO.eprintln s!"layers: {msg} {((← IO.monoNanosNow) - t0) / 1000000} ms"
  let mut hit : Nat × State := (0, State.start)
  for k in (List.range layers.length).reverse do
    if hit.1 = 0 then
      let t0 ← IO.monoNanosNow
      let key := keyOf (prefixes.getD (k + 1) [])
      let found ← load dir key
      trace s!"load {k + 1} ({found.isSome})" t0
      if let some s := found then
        let t1 ← IO.monoNanosNow
        let r := (layers.take (k + 1)).foldlM reelaborated s
        trace s!"reelaborate {r.isSome}" t1
        match r with
        | some s => hit := (k + 1, s)
        | none => return none
  let mut s := hit.2
  for k in List.range layers.length do
    if hit.1 ≤ k then
      let t0 ← IO.monoNanosNow
      match advance s (layers.getD k ByteArray.empty) with
      | some s' =>
        s := s'
        trace s!"advance {k + 1} {(s.bundle).isSome}" t0
        let t1 ← IO.monoNanosNow
        store dir (keyOf (prefixes.getD (k + 1) [])) s
        trace s!"store {k + 1}" t1
      | none => return none
  return some s

/-- The checked bundle at the end of the kept layers. -/
def bundle (dir : System.FilePath) (layers : List ByteArray) : IO (Option Tree) := do
  return (← compile dir layers).bind State.bundle

end GebHost.Layers

end
