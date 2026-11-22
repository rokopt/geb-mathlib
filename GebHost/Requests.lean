/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Command
public import Geb.Prototypes.Kernel.Requests

set_option doc.verso true in
/-!
# The host's interpreter of requests

The host performs on the file system the requests a program makes of it
({name}`Geb.Kernel.Requests.Request`), and runs a program's step from its start to its end: it
applies the step to the start event of the arguments, and while the step returns a request,
performs it and applies the step to the state the step returned and the request's result. The run
ends with the program's exit status, or with a message where the step returns no action
({name}`Geb.Kernel.Requests.next`); it has no bound of its own on the number of requests.

A path is decoded from UTF-8 by {name}`Geb.Kernel.Requests.pathText`. A failure of the file
system is the request's result: a missing file is {lit}`notFound`, a refusal of access
{lit}`denied`, and any other failure {lit}`other` with the system's message.

## Main definitions

* {lit}`GebHost.Requests.perform` — a request performed on the file system.
* {lit}`GebHost.Requests.interact` — a run of a step from its start to its end.
* {lit}`GebHost.Requests.interactBundle` — a run of a bundle's definition as a step, which
  {lit}`geb-kernel interact` and {lit}`geb-author interact` share.

## Tags

host, requests, files, input and output
-/

set_option doc.verso true

public section

namespace GebHost.Requests

open Geb.Kernel Geb.Kernel.Requests

/-- The failure an error of the file system is. -/
def failureOf : IO.Error → Failure
  | .noFileOrDirectory .. | .noSuchThing .. => .notFound
  | .permissionDenied .. => .denied
  | e => .other (toString e).toUTF8

/-- The result of an operation on a path, a failure of the path ({name}`pathText`) or of the
operation being its failure. -/
def atPath (bytes : ByteArray) (op : System.FilePath → IO Tree) : IO Tree :=
  match pathText bytes with
  | .error msg => return failed (.other msg.toUTF8)
  | .ok path => try op path catch e => return failed (failureOf e)

/-- Perform a request on the file system. -/
def perform : Request → IO Tree
  | .read p => atPath p fun path ↦ return succeeded [ofBytes (← IO.FS.readBinFile path)]
  | .write p b => atPath p fun path ↦ do
    IO.FS.writeBinFile path b
    return succeeded []

/-- Run a step from the start event of the arguments to its end, performing its requests: the
program's exit status, raising the message of what ends the run without one, prefixed by what
names the step. -/
def interact (what : String) (step : Tree → Option Tree) (args : List ByteArray) : IO UInt8 :=
  IO.iterate (startEvent args) fun event ↦
    match next step event with
    | .error msg => throw <| IO.userError s!"{what}: {msg}"
    | .ok (.done status) => return .inr status
    | .ok (.call request state) => return .inl (resumeEvent state (← perform request))

/-- Run a bundle's definition of a name as a program's step on the arguments: the program's exit
status; what names the bundle identifies it in errors. -/
def interactBundle (what : String) (bundle : Tree) (name : String) (args : List String) :
    IO UInt32 := do
  let entryName := s!"{what}: {name}"
  let some step := entry bundle (Command.chars name.toUTF8)
    | throw <| IO.userError s!"{entryName} is not a definition of the program"
  return (← interact entryName step (args.map String.toUTF8)).toUInt32

end GebHost.Requests
