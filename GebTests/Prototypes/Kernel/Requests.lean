/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Requests -- shake: keep
public meta import Geb.Prototypes.Kernel.Requests -- shake: keep

set_option doc.verso true in
/-!
# Examples of the requests of a program to its host

The trees of actions are decoded, and those that are none rejected: a status of {lit}`256`, a
request of another label, a path that is not a byte string. A step written in Lean, which reads
the file its first argument names and writes its bytes to the second, is run, by
{name}`Geb.Kernel.Requests.next` at each event, against a file system held in a state: it copies
a file, and receives the failure of a read of a missing file as a result; a step that returns no
action, or nothing, has no action. A path's bytes are decoded as UTF-8, and those that are not
UTF-8, or that hold the byte {lit}`0`, are rejected. The host's interpreter runs the program of
{lit}`examples/requests/` on the file system in {lit}`scripts/tests/test-requests.sh`.

## Main definitions

* {lit}`copyStep` — a step that copies a file.
* {lit}`Files` and {lit}`performIn` — a file system held in a state, and a request performed in
  it.
* {lit}`runOn` — a run of a step against such a file system, for a bounded number of events.

## Tags

host protocol, requests, files, test
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Requests.Tests

/-- The tree of a byte string's text. -/
def text (s : String) : Tree := ofBytes s.toUTF8

/-- A step that reads the file its first argument names and writes its bytes to the second,
exiting with status 0, or with 1 where the read or the write fails; it keeps the output's path in
its state while it reads, and the leaf 7 while it writes. -/
def copyStep (e : Tree) : Option Tree :=
  match e.label, e.children with
  | 0, [_, src, dst] => some (mk 1 [mk 0 [src], dst])
  | 1, [state, r] =>
    match r.label, r.children with
    | 1, [bytes] => some (mk 1 [mk 1 [state, bytes], leaf 7])
    | 1, [] => some (mk 0 [leaf 0])
    | _, _ => some (mk 0 [leaf 1])
  | _, _ => none

/-- Files held in a state: each path's bytes. -/
abbrev Files : Type := List (List UInt8 × List UInt8)

/-- A request performed on the files of the state: a read of a path the state lacks fails with
{lit}`notFound`. -/
def performIn : Request → StateM Files Tree
  | .read p => do
    match (← get).lookup p.data.toList with
    | some b => return succeeded [ofBytes ⟨b.toArray⟩]
    | none => return failed .notFound
  | .write p b => do
    modify fun fs ↦ (p.data.toList, b.data.toList) :: fs.filter (·.1 != p.data.toList)
    return succeeded []

/-- A run of a step on the arguments against files, for at most eight events: the exit status
where the step ends within them, and the files after the run. -/
def runOn (step : Tree → Option Tree) (args : List String) (fs : Files) : Option UInt8 × Files :=
  let go (acc : Tree ⊕ UInt8) (_ : Unit) : StateM Files (Tree ⊕ UInt8) :=
    match acc with
    | .inr status => return .inr status
    | .inl event =>
      match next step event with
      | .ok (.done status) => return .inr status
      | .ok (.call request state) => return .inl (resumeEvent state (← performIn request))
      | .error _ => return .inl event
  let start := startEvent (args.map String.toUTF8)
  let (r, fs) := ((List.replicate 8 ()).foldlM go (.inl start)).run fs
  (match r with | .inr status => some status | .inl _ => none, fs)

/-- The files of a state holding one file. -/
def oneFile : Files := [("in".toUTF8.data.toList, "bytes".toUTF8.data.toList)]

-- Actions decode, and trees that are none do not.
#guard (decodeAction (mk 0 [leaf 3])).isSome
#guard (decodeAction (mk 0 [leaf 256])).isNone
#guard (decodeAction (mk 1 [mk 0 [text "a"], leaf 5])).isSome
#guard (decodeAction (mk 1 [mk 1 [text "a", text "b"], leaf 5])).isSome
#guard (decodeAction (mk 1 [mk 2 [text "a"], leaf 5])).isNone
#guard (decodeAction (mk 1 [mk 0 [mk 0 [leaf 300]], leaf 5])).isNone
#guard (decodeAction (mk 1 [mk 0 [mk 0 [mk 97 [leaf 1]]], leaf 5])).isNone
#guard (decodeAction (mk 2 [])).isNone

-- The events and results are the protocol's trees.
#guard startEvent ["a".toUTF8] == mk 0 [leaf 0, text "a"]
#guard resumeEvent (leaf 7) (failed .denied) == mk 1 [leaf 7, mk 0 [mk 2 []]]
#guard failed (.other "m".toUTF8) == mk 0 [mk 0 [text "m"]]

-- A file is copied, and the run exits with the step's status.
#guard
  let (status, fs) := runOn copyStep ["in", "out"] oneFile
  status == some 0 && fs.lookup "out".toUTF8.data.toList == some "bytes".toUTF8.data.toList

-- The read of a missing file is a result, on which the step exits with its status 1.
#guard
  let (status, fs) := runOn copyStep ["missing", "out"] oneFile
  status == some 1 && fs == oneFile

-- A step that returns no action, or nothing, has no action at an event.
#guard (next (fun _ ↦ some (leaf 0)) (startEvent [])) matches .error _
#guard (next (fun _ ↦ none) (startEvent [])) matches .error _
#guard (next copyStep (startEvent ["a".toUTF8, "b".toUTF8])) matches .ok (.call (.read _) _)

-- UTF-8 decodes at each length, and is rejected where it is overlong, a surrogate, beyond
-- 0x10FFFF, truncated or a continuation byte alone.
#guard (utf8Chars ("aλ€😀".toUTF8.data.toList.map (·.toNat))).map String.ofList == some "aλ€😀"
#guard (utf8Chars [0xF4, 0x8F, 0xBF, 0xBF]) == some [Char.ofNat 0x10FFFF]
#guard (utf8Chars [0xC0, 0x80]).isNone
#guard (utf8Chars [0xE0, 0x9F, 0xBF]).isNone
#guard (utf8Chars [0xED, 0xA0, 0x80]).isNone
#guard (utf8Chars [0xF4, 0x90, 0x80, 0x80]).isNone
#guard (utf8Chars [0xE2, 0x82]).isNone
#guard (utf8Chars [0x80]).isNone

-- A path's text, and the paths that have none.
#guard pathText "dir/λ.txt".toUTF8 == .ok "dir/λ.txt"
#guard (pathText ⟨#[0xff]⟩) matches .error _
#guard (pathText ⟨#[0x61, 0]⟩) matches .error _

end Geb.Kernel.Requests.Tests
