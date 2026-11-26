/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Image
meta import GebMeta -- shake: keep

set_option doc.verso true in
/-!
# Requests of a program to its host

A kernel program is pure, so a program that reads and writes files does so by requests that its
host performs. The program is a definition of type {lit}`T → T`, its step, which the host applies
to an event and which returns an action: the end of the run with an exit status, or a request with
the state in which the program resumes. The host performs the request and applies the step again
to that state and the request's result. The program keeps no function between steps: its state is
a tree, which the host returns unread.

Every value exchanged is a tree in the representation of the datatype language, in which the value
of a constructor is the node labelled by the constructor's position in its declaration over its
fields' values, a last field {lit}`& E` giving the remaining children. In that language the
protocol's datatypes are

```
(data Bytes (bytes & T))
(data Event (start T & Bytes) (resume T Result))
(data Action (done T) (call Request T))
(data Request (read Bytes) (write Bytes Bytes))
(data Result (failed Failure) (succeeded & T))
(data Failure (other Bytes) (notFound) (denied))
```

A byte string is a node of label {lit}`0` whose children are the leaves of its bytes, as an entry's
input file is ({name}`Geb.Kernel.ofBytes`). The first event is {lit}`start`, of the leaf of the
protocol's version and of the arguments given to the host, each a byte string; each later event is
{lit}`resume`, of the state the program returned with its request and of the request's result. An
exit status is the leaf of a number below {lit}`256`. A read succeeds with the file's bytes, and a
write, which creates the file or replaces its contents, succeeds with nothing. A failure of the
file system is a result the program receives, not an end of its run: {lit}`notFound` where the
path names no file, {lit}`denied` where the system refuses access, and {lit}`other` with the
system's message otherwise. A path is the bytes of its UTF-8 text ({citeKey}`RFC3629`, § 3
and § 4), a relative path resolved against the host's working directory; a path that is not
UTF-8, or that holds the byte {lit}`0`, fails with {lit}`other`.

The version is {lit}`0`, the pre-release protocol, which changes with the host as the pre-release
edition {lit}`0` changes with the compiler; the start event names it, so that a program can reject
a host whose protocol it does not read. The host ends a run with a message, and no status of the
program's, where the step is not a function of trees to trees or returns a tree that is no action
of the protocol, an exit status of {lit}`256` or more among them.

This module states the protocol: its trees, and the action of a step at an event. The host's
executables perform the requests on the file system and run a step from its start to its end
({lit}`GebHost.Requests`).

## Main definitions

* {lit}`Geb.Kernel.Requests.version` — the protocol's version.
* {lit}`Geb.Kernel.Requests.Request`, {lit}`Geb.Kernel.Requests.Action` and
  {lit}`Geb.Kernel.Requests.Failure` — what a program asks, what its step returns, and how a
  request fails.
* {lit}`Geb.Kernel.Requests.decodeAction` — the action a tree represents.
* {lit}`Geb.Kernel.Requests.startEvent`, {lit}`Geb.Kernel.Requests.resumeEvent`,
  {lit}`Geb.Kernel.Requests.succeeded` and {lit}`Geb.Kernel.Requests.failed` — the trees of
  events and results.
* {lit}`Geb.Kernel.Requests.entry` — a bundle's definition of type {lit}`T → T`, loaded once.
* {lit}`Geb.Kernel.Requests.next` — the action of a step at an event.
* {lit}`Geb.Kernel.Requests.utf8Chars` and {lit}`Geb.Kernel.Requests.pathText` — the characters
  of UTF-8 bytes, and the text of a path.

## References

* {citeKey}`RFC3629`

## Tags

bootstrap, kernel, host protocol, input and output, files
-/

set_option doc.verso true

public section

namespace Geb.Kernel.Requests

/-- The version of the protocol, which the start event names. -/
def version : ℕ := 0

/-- A request of a program to its host. -/
inductive Request where
  /-- Read the file at a path. -/
  | read (path : ByteArray)
  /-- Write bytes to the file at a path, creating it or replacing its contents. -/
  | write (path bytes : ByteArray)

/-- What a program's step returns. -/
inductive Action where
  /-- The end of the run, with its exit status. -/
  | done (status : UInt8)
  /-- A request, with the state in which the program resumes. -/
  | call (request : Request) (state : Tree)

/-- How a request fails; the program receives the failure as the request's result. -/
inductive Failure where
  /-- A failure the protocol names no kind of, with the system's message. -/
  | other (message : ByteArray)
  /-- The path names no file. -/
  | notFound
  /-- The system refuses access. -/
  | denied

/-- The bytes a tree represents: those of a node of label {lit}`0` whose children are leaves of
labels below {lit}`256`. -/
def bytesOf (t : Tree) : Option ByteArray :=
  if t.label == 0 && t.children.all (·.children.isEmpty) then toBytes t else none

/-- The request a tree represents. -/
def decodeRequest (t : Tree) : Option Request :=
  match t.label, t.children with
  | 0, [p] => return .read (← bytesOf p)
  | 1, [p, b] => return .write (← bytesOf p) (← bytesOf b)
  | _, _ => none

/-- The action a tree represents. -/
def decodeAction (t : Tree) : Option Action :=
  match t.label, t.children with
  | 0, [s] => if s.children.isEmpty && s.label < 256 then some (.done s.label.toUInt8) else none
  | 1, [r, state] => return .call (← decodeRequest r) state
  | _, _ => none

/-- The first event, of the protocol's version and of the arguments. -/
def startEvent (args : List ByteArray) : Tree := mk 0 (leaf version :: args.map ofBytes)

/-- A later event, of the state the program returned with its request and of the result. -/
def resumeEvent (state result : Tree) : Tree := mk 1 [state, result]

/-- The tree of a failure. -/
def failureTree : Failure → Tree
  | .other m => mk 0 [ofBytes m]
  | .notFound => mk 1 []
  | .denied => mk 2 []

/-- The result of a request that failed. -/
def failed (f : Failure) : Tree := mk 0 [failureTree f]

/-- The result of a request that succeeded, with its values. -/
def succeeded (values : List Tree) : Tree := mk 1 values

/-- A bundle's definition of a name as a function of trees, the bundle loaded once; the function
gives nothing at an input where the definition is not of type {lit}`T → T`. -/
def entry (bundle : Tree) (name : List Char) : Option (Tree → Option Tree) := do
  return (← (← loadEntries bundle) name).apply

/-- The action a step returns at an event, or the message of what makes it none: the step is not
a function from trees to trees, or the tree it returns represents no action. -/
def next (step : Tree → Option Tree) (event : Tree) : Except String Action := do
  let some out := step event | .error "the step is not a function from trees to trees"
  let some action := decodeAction out
    | .error s!"the step returned no action of protocol {version}"
  return action

/-- The characters of a sequence of bytes that is UTF-8, decoded by the state of a left fold: the
characters decoded, in reverse, the number of bytes the present character still needs, its bits
so far, and the least code point a sequence of its length encodes. A sequence is UTF-8 where
each character is a leading byte below {lit}`0x80`, or one of {lit}`0xC0` to {lit}`0xF7` followed
by one to three bytes of {lit}`0x80` to {lit}`0xBF`, as the leading byte says, whose code point a
shorter sequence does not encode, is no surrogate of UTF-16 and is at most {lit}`0x10FFFF`
({citeKey}`RFC3629`, § 3 and the syntax of § 4). -/
def utf8Chars (bs : List ℕ) : Option (List Char) :=
  let step (s : Option (List Char × ℕ × ℕ × ℕ)) (b : ℕ) : Option (List Char × ℕ × ℕ × ℕ) := do
    let (cs, k, cp, lo) ← s
    match k with
    | 0 =>
      if b < 0x80 then some (Char.ofNat b :: cs, 0, 0, 0)
      else if b < 0xC0 then none
      else if b < 0xE0 then some (cs, 1, b % 0x20, 0x80)
      else if b < 0xF0 then some (cs, 2, b % 0x10, 0x800)
      else if b < 0xF8 then some (cs, 3, b % 0x08, 0x10000)
      else none
    | k + 1 =>
      if b < 0x80 ∨ 0xC0 ≤ b then none
      else
        let cp := cp * 64 + b % 64
        match k with
        | 0 =>
          if cp < lo ∨ (0xD800 ≤ cp ∧ cp < 0xE000) ∨ 0x10FFFF < cp then none
          else some (Char.ofNat cp :: cs, 0, 0, 0)
        | k + 1 => some (cs, k + 1, cp, lo)
  do
    let (cs, k, _, _) ← bs.foldl step (some ([], 0, 0, 0))
    if k = 0 then some cs.reverse else none

/-- The text of a path's bytes: their UTF-8 text, which holds no byte {lit}`0`, or the message of
what rejects them. -/
def pathText (bytes : ByteArray) : Except String String :=
  let bs := bytes.data.toList.map (·.toNat)
  if bs.any (· == 0) then .error "the path holds the byte 0"
  else match utf8Chars bs with
    | some cs => .ok (String.ofList cs)
    | none => .error "the path is not UTF-8"

end Geb.Kernel.Requests
