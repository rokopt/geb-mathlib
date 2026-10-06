module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Check

def «Prelude.append» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0

def «Prelude.length» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0

def «Prelude.reverse» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T)

def «Prelude.replicate» :=
  fun (x0 : T) (x1 : T) =>
    Const.iter
      (α := List T)
      (fun (x2 : List T) => (x1 :: x2))
      ([] : List T)
      x0

def «Prelude.single» := fun (x0 : T) => (x0 :: ([] : List T))

def «Prelude.some» :=
  fun (x0 : T) => Const.node (leaf 1) («Prelude.single» x0)

def «Prelude.none» := leaf 0

def «Prelude.isSome» :=
  fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «Prelude.get» := fun (x0 : T) => Const.child x0 (leaf 0)

def «Prelude.and» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then x1 else leaf 0

def «Prelude.or» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then leaf 1 else x1

def «Prelude.at» :=
  fun (x0 : List T) (x1 : T) => Const.child (Const.node (leaf 0) x0) x1

def «Prelude.nth» :=
  fun (x0 : List T) (x1 : T) =>
    if (Const.lt x1 («Prelude.length» x0)).label ≠ 0 then
      «Prelude.some» («Prelude.at» x0 x1)
    else
      «Prelude.none»

def «Prelude.tail» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2)

def «Prelude.drop» :=
  fun (x0 : T) (x1 : List T) =>
    Const.iter (α := List T) «Prelude.tail» x1 x0

def «Prelude.digitsMsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    (Const.iter
      (α := T × List T)
      (fun (x3 : T × List T) =>
        (Const.div (x3).1 x0, ((Const.mod (x3).1 x0) :: (x3).2)))
      (x1, ([] : List T))
      x2).2

def «Prelude.digitsLsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    «Prelude.reverse» («Prelude.digitsMsb» x0 x1 x2)

def «Reader.both» :=
  fun (x0 : T) (x1 : T) =>
    if («Prelude.isSome» x0).label ≠ 0 then
      «Prelude.isSome» x1
    else
      leaf 0

def «Reader.nonEmpty» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := T)
      x0
      (leaf 0)
      (fun (_ : T) (_ : List T) => leaf 1)

def «Reader.allSome» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        («Reader.both» x1 (x2).1, ((«Prelude.get» x1) :: (x2).2)))
      (leaf 1, ([] : List T))
      x0;
    if ((x1).1).label ≠ 0 then
      «Prelude.some» (Const.node (leaf 0) (x1).2)
    else
      «Prelude.none»

def «Reader.lexFail» := (([] : List T), (([] : List T), leaf 11))

def «Reader.lexIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) => (x0, (x1, x2))

def «Reader.lexIdle» :=
  fun (x0 : List T) => «Reader.lexIn» x0 ([] : List T) (leaf 0)

def «Reader.withLen» :=
  fun (x0 : T) (x1 : T) => Const.node x0 («Prelude.single» x1)

def «Reader.inRange» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    if (Const.lt x0 x1).label ≠ 0 then
      leaf 0
    else
      Const.lt x0 (Const.add x2 (leaf 1))

def «Reader.isDigit» :=
  fun (x0 : T) => «Reader.inRange» x0 (leaf 48) (leaf 57)

def «Reader.isSpace» :=
  fun (x0 : T) =>
    if (Const.eq x0 (leaf 32)).label ≠ 0 then
      leaf 1
    else
      if (Const.eq x0 (leaf 10)).label ≠ 0 then
        leaf 1
      else
        if (Const.eq x0 (leaf 9)).label ≠ 0 then
          leaf 1
        else
          if (Const.eq x0 (leaf 13)).label ≠ 0 then
            leaf 1
          else
            if (Const.eq x0 (leaf 11)).label ≠ 0 then
              leaf 1
            else
              Const.eq x0 (leaf 12)

def «Reader.isTokenStart» :=
  fun (x0 : T) =>
    if («Reader.inRange» x0 (leaf 65) (leaf 90)).label ≠ 0 then
      leaf 1
    else
      if («Reader.inRange» x0 (leaf 97) (leaf 122)).label ≠ 0 then
        leaf 1
      else
        if (Const.eq x0 (leaf 45)).label ≠ 0 then
          leaf 1
        else
          if (Const.eq x0 (leaf 46)).label ≠ 0 then
            leaf 1
          else
            if (Const.eq x0 (leaf 47)).label ≠ 0 then
              leaf 1
            else
              if (Const.eq x0 (leaf 95)).label ≠ 0 then
                leaf 1
              else
                if (Const.eq x0 (leaf 58)).label ≠ 0 then
                  leaf 1
                else
                  if (Const.eq x0 (leaf 42)).label ≠ 0 then
                    leaf 1
                  else
                    if (Const.eq x0 (leaf 43)).label ≠ 0 then
                      leaf 1
                    else
                      Const.eq x0 (leaf 61)

def «Reader.isTokenChar» :=
  fun (x0 : T) =>
    if («Reader.isTokenStart» x0).label ≠ 0 then
      leaf 1
    else
      «Reader.isDigit» x0

def «Reader.isPlainIn» :=
  fun (x0 : T) =>
    if («Reader.inRange» x0 (leaf 32) (leaf 126)).label ≠ 0 then
      if (Const.eq x0 (leaf 34)).label ≠ 0 then
        leaf 0
      else
        if (Const.eq x0 (leaf 92)).label ≠ 0 then leaf 0 else leaf 1
    else
      if (Const.eq x0 (leaf 10)).label ≠ 0 then
        leaf 1
      else
        if (Const.eq x0 (leaf 13)).label ≠ 0 then
          leaf 1
        else
          Const.lt (leaf 127) x0

def «Reader.atomTok» :=
  fun (x0 : List T) => Const.node (leaf 3) («Prelude.reverse» x0)

def «Reader.kwHole» := mk 0 [leaf 104, leaf 111, leaf 108, leaf 101]

def «Reader.holeToks» :=
  fun (x0 : List T) (x1 : List T) =>
    ((leaf 2) ::
      ((«Reader.atomTok» x0) ::
        ((Const.node (leaf 3) (Const.children «Reader.kwHole»)) ::
          ((leaf 1) :: x1))))

def «Reader.idleStep» :=
  fun (x0 : List T) (x1 : T) =>
    if (Const.eq x1 (leaf 59)).label ≠ 0 then
      «Reader.lexIn» x0 ([] : List T) (leaf 4)
    else
      if (Const.eq x1 (leaf 40)).label ≠ 0 then
        «Reader.lexIdle» ((leaf 1) :: x0)
      else
        if (Const.eq x1 (leaf 41)).label ≠ 0 then
          «Reader.lexIdle» ((leaf 2) :: x0)
        else
          if (Const.eq x1 (leaf 34)).label ≠ 0 then
            «Reader.lexIn»
              x0
              ([] : List T)
              («Reader.withLen» (leaf 5) «Prelude.none»)
          else
            if (Const.eq x1 (leaf 38)).label ≠ 0 then
              «Reader.lexIdle»
                ((Const.node (leaf 3) («Prelude.single» (leaf 38))) :: x0)
            else
              if (Const.eq x1 (leaf 63)).label ≠ 0 then
                «Reader.lexIn» x0 ([] : List T) (leaf 3)
              else
                if (Const.eq x1 (leaf 35)).label ≠ 0 then
                  «Reader.lexIn»
                    x0
                    ([] : List T)
                    («Reader.withLen» (leaf 13) «Prelude.none»)
                else
                  if (Const.eq x1 (leaf 124)).label ≠ 0 then
                    «Reader.lexIn»
                      x0
                      ([] : List T)
                      («Reader.withLen» (leaf 14) «Prelude.none»)
                  else
                    if («Reader.isSpace» x1).label ≠ 0 then
                      «Reader.lexIdle» x0
                    else
                      if («Reader.isDigit» x1).label ≠ 0 then
                        «Reader.lexIn» x0 («Prelude.single» x1) (leaf 2)
                      else
                        if («Reader.isTokenStart» x1).label ≠ 0 then
                          «Reader.lexIn» x0 («Prelude.single» x1) (leaf 1)
                        else
                          «Reader.lexFail»

def «Reader.endAtom» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    if (if («Prelude.isSome» x1).label ≠ 0 then
      Const.eq («Prelude.get» x1) («Prelude.length» x2)
    else
      leaf 1).label ≠ 0 then
      «Reader.lexIdle» ((Const.node (leaf 3) x2) :: x0)
    else
      «Reader.lexFail»

def «Reader.strStep» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) =>
    if (Const.eq x3 (leaf 34)).label ≠ 0 then
      «Reader.endAtom» x0 x2 («Prelude.reverse» x1)
    else
      if (Const.eq x3 (leaf 92)).label ≠ 0 then
        «Reader.lexIn» x0 x1 («Reader.withLen» (leaf 6) x2)
      else
        if («Reader.isPlainIn» x3).label ≠ 0 then
          «Reader.lexIn» x0 (x3 :: x1) («Reader.withLen» (leaf 5) x2)
        else
          «Reader.lexFail»

def «Reader.escChar» :=
  fun (x0 : T) =>
    if (Const.eq x0 (leaf 97)).label ≠ 0 then
      «Prelude.some» (leaf 7)
    else
      if (Const.eq x0 (leaf 98)).label ≠ 0 then
        «Prelude.some» (leaf 8)
      else
        if (Const.eq x0 (leaf 116)).label ≠ 0 then
          «Prelude.some» (leaf 9)
        else
          if (Const.eq x0 (leaf 118)).label ≠ 0 then
            «Prelude.some» (leaf 11)
          else
            if (Const.eq x0 (leaf 110)).label ≠ 0 then
              «Prelude.some» (leaf 10)
            else
              if (Const.eq x0 (leaf 102)).label ≠ 0 then
                «Prelude.some» (leaf 12)
              else
                if (Const.eq x0 (leaf 114)).label ≠ 0 then
                  «Prelude.some» (leaf 13)
                else
                  if (Const.eq x0 (leaf 34)).label ≠ 0 then
                    «Prelude.some» x0
                  else
                    if (Const.eq x0 (leaf 39)).label ≠ 0 then
                      «Prelude.some» x0
                    else
                      if (Const.eq x0 (leaf 63)).label ≠ 0 then
                        «Prelude.some» x0
                      else
                        if (Const.eq x0 (leaf 92)).label ≠ 0 then
                          «Prelude.some» x0
                        else
                          «Prelude.none»

def «Reader.hexVal» :=
  fun (x0 : T) =>
    if («Reader.isDigit» x0).label ≠ 0 then
      «Prelude.some» (Const.sub x0 (leaf 48))
    else
      if («Reader.inRange» x0 (leaf 65) (leaf 70)).label ≠ 0 then
        «Prelude.some» (Const.sub x0 (leaf 55))
      else
        if («Reader.inRange» x0 (leaf 97) (leaf 102)).label ≠ 0 then
          «Prelude.some» (Const.sub x0 (leaf 87))
        else
          «Prelude.none»

def «Reader.decodeHex» :=
  fun (x0 : List T) =>
    if (Const.eq
      (Const.mod («Prelude.length» x0) (leaf 2))
      (leaf 0)).label ≠ 0 then
      let x1 : T ×
        (List T ×
          T) := Const.foldr
        (α := T)
        (β := T × (List T × T))
        (fun (x1 : T) (x2 : T × (List T × T)) =>
          let x3 : T := «Reader.hexVal» x1;
          if (if ((x2).1).label ≠ 0 then
            «Prelude.isSome» x3
          else
            leaf 0).label ≠ 0 then
            if («Prelude.isSome» ((x2).2).2).label ≠ 0 then
              (leaf 1,
                (((Const.add
                  (Const.mul (leaf 16) («Prelude.get» x3))
                  («Prelude.get» ((x2).2).2)) ::
                  ((x2).2).1),
                  «Prelude.none»))
            else
              (leaf 1, (((x2).2).1, «Prelude.some» («Prelude.get» x3)))
          else
            (leaf 0, (x2).2))
        (leaf 1, (([] : List T), «Prelude.none»))
        x0;
      if ((x1).1).label ≠ 0 then
        «Prelude.some» (Const.node (leaf 0) ((x1).2).1)
      else
        «Prelude.none»
    else
      «Prelude.none»

def «Reader.base64Val» :=
  fun (x0 : T) =>
    if («Reader.inRange» x0 (leaf 65) (leaf 90)).label ≠ 0 then
      «Prelude.some» (Const.sub x0 (leaf 65))
    else
      if («Reader.inRange» x0 (leaf 97) (leaf 122)).label ≠ 0 then
        «Prelude.some» (Const.sub x0 (leaf 71))
      else
        if («Reader.isDigit» x0).label ≠ 0 then
          «Prelude.some» (Const.add x0 (leaf 4))
        else
          if (Const.eq x0 (leaf 43)).label ≠ 0 then
            «Prelude.some» (leaf 62)
          else
            if (Const.eq x0 (leaf 47)).label ≠ 0 then
              «Prelude.some» (leaf 63)
            else
              «Prelude.none»

def «Reader.b64Fail» :=
  (leaf 0, (([] : List T), (leaf 0, (leaf 0, leaf 0))))

def «Reader.base64Step» :=
  fun (x0 : T × (List T × (T × (T × T)))) (x1 : T) =>
    if ((x0).1).label ≠ 0 then
      let x2 : List T := ((x0).2).1;
      let x3 : T := (((x0).2).2).1;
      let x4 : T := ((((x0).2).2).2).1;
      let x5 : T := ((((x0).2).2).2).2;
      if (Const.eq x1 (leaf 61)).label ≠ 0 then
        if (Const.lt x5 (leaf 2)).label ≠ 0 then
          (leaf 1, (x2, (x3, (x4, Const.add x5 (leaf 1)))))
        else
          «Reader.b64Fail»
      else
        if (Const.eq x5 (leaf 0)).label ≠ 0 then
          let x6 : T := «Reader.base64Val» x1;
          if («Prelude.isSome» x6).label ≠ 0 then
            if (Const.lt (Const.add x4 (leaf 6)) (leaf 8)).label ≠ 0 then
              (leaf 1,
                (x2,
                  (Const.add (Const.mul (leaf 64) x3) («Prelude.get» x6),
                    (Const.add x4 (leaf 6), leaf 0))))
            else
              let x7 : T := Const.add (Const.mul (leaf 64) x3) («Prelude.get» x6);
              let x8 : T := Const.sub (Const.add x4 (leaf 6)) (leaf 8);
              let x9 : T := Const.iter
                (α := T)
                (fun (x9 : T) => Const.mul x9 (leaf 2))
                (leaf 1)
                x8;
              (leaf 1, (((Const.div x7 x9) :: x2), (Const.mod x7 x9, (x8, leaf 0))))
          else
            «Reader.b64Fail»
        else
          «Reader.b64Fail»
    else
      x0

def «Reader.decodeBase64» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (List T ×
        (T ×
          (T ×
            T))) := Const.foldr
      (α := T)
      (β := (T × (List T × (T × (T × T)))) → T × (List T × (T × (T × T))))
      (fun (x1 : T)
         (x2 : (T × (List T × (T × (T × T)))) → T × (List T × (T × (T × T))))
         (x3 : T × (List T × (T × (T × T)))) =>
        x2 («Reader.base64Step» x3 x1))
      (fun (x1 : T × (List T × (T × (T × T)))) => x1)
      x0
      (leaf 1, (([] : List T), (leaf 0, (leaf 0, leaf 0))));
    if (if ((x1).1).label ≠ 0 then
      Const.lt ((((x1).2).2).2).1 (leaf 6)
    else
      leaf 0).label ≠ 0 then
      «Prelude.some» (Const.node (leaf 0) («Prelude.reverse» ((x1).2).1))
    else
      «Prelude.none»

def «Reader.lengthStep» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : List T := «Prelude.reverse» x1;
    if (if (Const.lt (leaf 1) («Prelude.length» x3)).label ≠ 0 then
      Const.eq («Prelude.at» x3 (leaf 0)) (leaf 48)
    else
      leaf 0).label ≠ 0 then
      «Reader.lexFail»
    else
      let x4 : T := Const.foldr
        (α := T)
        (β := T)
        (fun (x4 : T) (x5 : T) =>
          Const.add (Const.sub x4 (leaf 48)) (Const.mul (leaf 10) x5))
        (leaf 0)
        x1;
      if (Const.eq x2 (leaf 58)).label ≠ 0 then
        if (Const.eq x4 (leaf 0)).label ≠ 0 then
          «Reader.lexIdle» ((Const.node (leaf 3) ([] : List T)) :: x0)
        else
          «Reader.lexIn»
            x0
            ([] : List T)
            (Const.node (leaf 12) («Prelude.single» x4))
      else
        if (Const.eq x2 (leaf 34)).label ≠ 0 then
          «Reader.lexIn»
            x0
            ([] : List T)
            («Reader.withLen» (leaf 5) («Prelude.some» x4))
        else
          if (Const.eq x2 (leaf 35)).label ≠ 0 then
            «Reader.lexIn»
              x0
              ([] : List T)
              («Reader.withLen» (leaf 13) («Prelude.some» x4))
          else
            if (Const.eq x2 (leaf 124)).label ≠ 0 then
              «Reader.lexIn»
                x0
                ([] : List T)
                («Reader.withLen» (leaf 14) («Prelude.some» x4))
            else
              «Reader.lexFail»

def «Reader.lexStep» :=
  fun (x0 : List T × (List T × T)) (x1 : T) =>
    let x2 : List T := (x0).1;
    let x3 : List T := ((x0).2).1;
    let x4 : T := ((x0).2).2;
    let x5 : T := Const.label x4;
    if (Const.eq x5 (leaf 0)).label ≠ 0 then
      «Reader.idleStep» x2 x1
    else
      if (Const.eq x5 (leaf 4)).label ≠ 0 then
        if (Const.eq x1 (leaf 10)).label ≠ 0 then «Reader.lexIdle» x2 else x0
      else
        if (Const.eq x5 (leaf 1)).label ≠ 0 then
          if («Reader.isTokenChar» x1).label ≠ 0 then
            «Reader.lexIn» x2 (x1 :: x3) x4
          else
            «Reader.idleStep» ((«Reader.atomTok» x3) :: x2) x1
        else
          if (Const.eq x5 (leaf 2)).label ≠ 0 then
            if («Reader.isDigit» x1).label ≠ 0 then
              «Reader.lexIn» x2 (x1 :: x3) x4
            else
              if (if («Reader.isTokenChar» x1).label ≠ 0 then
                leaf 1
              else
                if (Const.eq x1 (leaf 34)).label ≠ 0 then
                  leaf 1
                else
                  if (Const.eq x1 (leaf 35)).label ≠ 0 then
                    leaf 1
                  else
                    Const.eq x1 (leaf 124)).label ≠ 0 then
                «Reader.lengthStep» x2 x3 x1
              else
                «Reader.idleStep» ((«Reader.atomTok» x3) :: x2) x1
          else
            if (Const.eq x5 (leaf 3)).label ≠ 0 then
              if (if («Reader.isTokenChar» x1).label ≠ 0 then
                if («Reader.nonEmpty» x3).label ≠ 0 then
                  leaf 1
                else
                  if («Reader.isDigit» x1).label ≠ 0 then leaf 0 else leaf 1
              else
                leaf 0).label ≠ 0 then
                «Reader.lexIn» x2 (x1 :: x3) x4
              else
                if («Reader.nonEmpty» x3).label ≠ 0 then
                  «Reader.idleStep» («Reader.holeToks» x3 x2) x1
                else
                  «Reader.lexFail»
            else
              if (Const.eq x5 (leaf 11)).label ≠ 0 then
                x0
              else
                if (Const.eq x5 (leaf 12)).label ≠ 0 then
                  if (Const.lt (Const.child x4 (leaf 0)) (leaf 2)).label ≠ 0 then
                    «Reader.lexIdle» ((«Reader.atomTok» (x1 :: x3)) :: x2)
                  else
                    «Reader.lexIn»
                      x2
                      (x1 :: x3)
                      (Const.node
                        (leaf 12)
                        («Prelude.single» (Const.sub (Const.child x4 (leaf 0)) (leaf 1))))
                else
                  let x6 : T := Const.child x4 (leaf 0);
                  if (Const.eq x5 (leaf 5)).label ≠ 0 then
                    «Reader.strStep» x2 x3 x6 x1
                  else
                    if (Const.eq x5 (leaf 6)).label ≠ 0 then
                      let x7 : T := «Reader.escChar» x1;
                      if («Prelude.isSome» x7).label ≠ 0 then
                        «Reader.lexIn»
                          x2
                          ((«Prelude.get» x7) :: x3)
                          («Reader.withLen» (leaf 5) x6)
                      else
                        if (Const.eq x1 (leaf 120)).label ≠ 0 then
                          «Reader.lexIn»
                            x2
                            x3
                            (Const.node
                              (leaf 9)
                              (x6 :: ((leaf 0) :: («Prelude.single» (leaf 0)))))
                        else
                          if («Reader.inRange» x1 (leaf 48) (leaf 55)).label ≠ 0 then
                            «Reader.lexIn»
                              x2
                              x3
                              (Const.node
                                (leaf 10)
                                (x6 :: ((leaf 1) :: («Prelude.single» (Const.sub x1 (leaf 48))))))
                          else
                            if (Const.eq x1 (leaf 13)).label ≠ 0 then
                              «Reader.lexIn» x2 x3 («Reader.withLen» (leaf 7) x6)
                            else
                              if (Const.eq x1 (leaf 10)).label ≠ 0 then
                                «Reader.lexIn» x2 x3 («Reader.withLen» (leaf 8) x6)
                              else
                                «Reader.lexFail»
                    else
                      if (Const.eq x5 (leaf 7)).label ≠ 0 then
                        if (Const.eq x1 (leaf 10)).label ≠ 0 then
                          «Reader.lexIn» x2 x3 («Reader.withLen» (leaf 5) x6)
                        else
                          «Reader.strStep» x2 x3 x6 x1
                      else
                        if (Const.eq x5 (leaf 8)).label ≠ 0 then
                          if (Const.eq x1 (leaf 13)).label ≠ 0 then
                            «Reader.lexIn» x2 x3 («Reader.withLen» (leaf 5) x6)
                          else
                            «Reader.strStep» x2 x3 x6 x1
                        else
                          if (Const.eq x5 (leaf 9)).label ≠ 0 then
                            let x7 : T := «Reader.hexVal» x1;
                            if («Prelude.isSome» x7).label ≠ 0 then
                              if (Const.eq (Const.child x4 (leaf 1)) (leaf 1)).label ≠ 0 then
                                «Reader.lexIn»
                                  x2
                                  ((Const.add
                                    (Const.mul (leaf 16) (Const.child x4 (leaf 2)))
                                    («Prelude.get» x7)) ::
                                    x3)
                                  («Reader.withLen» (leaf 5) x6)
                              else
                                «Reader.lexIn»
                                  x2
                                  x3
                                  (Const.node
                                    (leaf 9)
                                    (x6 :: ((leaf 1) :: («Prelude.single» («Prelude.get» x7)))))
                            else
                              «Reader.lexFail»
                          else
                            if (Const.eq x5 (leaf 10)).label ≠ 0 then
                              if («Reader.inRange» x1 (leaf 48) (leaf 55)).label ≠ 0 then
                                let x7 : T := Const.add
                                  (Const.mul (leaf 8) (Const.child x4 (leaf 2)))
                                  (Const.sub x1 (leaf 48));
                                if (Const.eq (Const.child x4 (leaf 1)) (leaf 2)).label ≠ 0 then
                                  if (Const.lt x7 (leaf 256)).label ≠ 0 then
                                    «Reader.lexIn» x2 (x7 :: x3) («Reader.withLen» (leaf 5) x6)
                                  else
                                    «Reader.lexFail»
                                else
                                  «Reader.lexIn»
                                    x2
                                    x3
                                    (Const.node
                                      (leaf 10)
                                      (x6 ::
                                        ((Const.add (Const.child x4 (leaf 1)) (leaf 1)) ::
                                          («Prelude.single» x7))))
                              else
                                «Reader.lexFail»
                            else
                              if (Const.eq x5 (leaf 13)).label ≠ 0 then
                                if («Reader.isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if («Prelude.isSome» («Reader.hexVal» x1)).label ≠ 0 then
                                    «Reader.lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (Const.eq x1 (leaf 35)).label ≠ 0 then
                                      let x7 : T := «Reader.decodeHex» («Prelude.reverse» x3);
                                      if («Prelude.isSome» x7).label ≠ 0 then
                                        «Reader.endAtom» x2 x6 (Const.children («Prelude.get» x7))
                                      else
                                        «Reader.lexFail»
                                    else
                                      «Reader.lexFail»
                              else
                                if («Reader.isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if (if («Prelude.isSome» («Reader.base64Val» x1)).label ≠ 0 then
                                    leaf 1
                                  else
                                    Const.eq x1 (leaf 61)).label ≠ 0 then
                                    «Reader.lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (Const.eq x1 (leaf 124)).label ≠ 0 then
                                      let x7 : T := «Reader.decodeBase64» («Prelude.reverse» x3);
                                      if («Prelude.isSome» x7).label ≠ 0 then
                                        «Reader.endAtom» x2 x6 (Const.children («Prelude.get» x7))
                                      else
                                        «Reader.lexFail»
                                    else
                                      «Reader.lexFail»

def «Reader.lexEnd» :=
  fun (x0 : List T × (List T × T)) =>
    let x1 : List T := (x0).1;
    let x2 : List T := ((x0).2).1;
    let x3 : T := Const.label ((x0).2).2;
    if (if (Const.eq x3 (leaf 0)).label ≠ 0 then
      leaf 1
    else
      Const.eq x3 (leaf 4)).label ≠ 0 then
      «Prelude.some» (Const.node (leaf 0) («Prelude.reverse» x1))
    else
      if (if (Const.eq x3 (leaf 1)).label ≠ 0 then
        leaf 1
      else
        Const.eq x3 (leaf 2)).label ≠ 0 then
        «Prelude.some»
          (Const.node
            (leaf 0)
            («Prelude.reverse» ((«Reader.atomTok» x2) :: x1)))
      else
        if (Const.eq x3 (leaf 3)).label ≠ 0 then
          if («Reader.nonEmpty» x2).label ≠ 0 then
            «Prelude.some»
              (Const.node (leaf 0) («Prelude.reverse» («Reader.holeToks» x2 x1)))
          else
            «Prelude.none»
        else
          «Prelude.none»

def «Reader.tokenize» :=
  fun (x0 : List T) =>
    if (Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        if (Const.lt x1 (leaf 256)).label ≠ 0 then x2 else leaf 0)
      (leaf 1)
      x0).label ≠ 0 then
      «Reader.lexEnd»
        (Const.foldr
          (α := T)
          (β := (List T × (List T × T)) → List T × (List T × T))
          (fun (x1 : T)
             (x2 : (List T × (List T × T)) → List T × (List T × T))
             (x3 : List T × (List T × T)) =>
            x2 («Reader.lexStep» x3 x1))
          (fun (x1 : List T × (List T × T)) => x1)
          x0
          («Reader.lexIdle» ([] : List T)))
    else
      «Prelude.none»

def «Reader.fail» := (leaf 0, ([] : List (List T)))

def «Reader.parseStep» :=
  fun (x0 : T × List (List T)) (x1 : T) =>
    if ((x0).1).label ≠ 0 then
      Const.lcase
        (α := List T)
        (β := T × List (List T))
        (x0).2
        «Reader.fail»
        (fun (x2 : List T) (x3 : List (List T)) =>
          if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
            (leaf 1, (([] : List T) :: (x2 :: x3)))
          else
            if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
              (leaf 1, (((Const.node (leaf 1) (Const.children x1)) :: x2) :: x3))
            else
              Const.lcase
                (α := List T)
                (β := T × List (List T))
                x3
                «Reader.fail»
                (fun (x4 : List T) (x5 : List (List T)) =>
                  (leaf 1,
                    (((Const.node (leaf 2) («Prelude.reverse» x2)) :: x4) :: x5))))
    else
      x0

def «Reader.readSExps» :=
  fun (x0 : List T) =>
    let x1 : T := «Reader.tokenize» x0;
    if («Prelude.isSome» x1).label ≠ 0 then
      let x2 : T ×
        List
          (List
            T) := Const.foldr
        (α := T)
        (β := (T × List (List T)) → T × List (List T))
        (fun (x2 : T)
           (x3 : (T × List (List T)) → T × List (List T))
           (x4 : T × List (List T)) =>
          x3 («Reader.parseStep» x4 x2))
        (fun (x2 : T × List (List T)) => x2)
        (Const.children («Prelude.get» x1))
        (leaf 1, (([] : List T) :: ([] : List (List T))));
      if ((x2).1).label ≠ 0 then
        Const.lcase
          (α := List T)
          (β := T)
          (x2).2
          «Prelude.none»
          (fun (x3 : List T) (x4 : List (List T)) =>
            Const.lcase
              (α := List T)
              (β := T)
              x4
              («Prelude.some» (Const.node (leaf 0) («Prelude.reverse» x3)))
              (fun (_ : List T) (_ : List (List T)) => «Prelude.none»))
      else
        «Prelude.none»
    else
      «Prelude.none»

def «Reader.isAtom» :=
  fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «Reader.isList» :=
  fun (x0 : T) => Const.eq (Const.label x0) (leaf 2)

def «Reader.nameOf» :=
  fun (x0 : T) => Const.node (leaf 0) (Const.children x0)

def «Reader.named» :=
  fun (x0 : T) (x1 : T) =>
    if («Reader.isAtom» x0).label ≠ 0 then
      Const.equal («Reader.nameOf» x0) x1
    else
      leaf 0

def «Reader.kwT» := mk 0 [leaf 84]

def «Reader.kwUnit» := mk 0 [leaf 85, leaf 110, leaf 105, leaf 116]

def «Reader.kwProd» := mk 0 [leaf 80, leaf 114, leaf 111, leaf 100]

def «Reader.kwArrow» :=
  mk 0 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «Reader.kwList» := mk 0 [leaf 76, leaf 105, leaf 115, leaf 116]

def «Reader.kwLam» := mk 0 [leaf 108, leaf 97, leaf 109]

def «Reader.kwLet» := mk 0 [leaf 108, leaf 101, leaf 116]

def «Reader.kwPair» := mk 0 [leaf 112, leaf 97, leaf 105, leaf 114]

def «Reader.kwFst» := mk 0 [leaf 102, leaf 115, leaf 116]

def «Reader.kwSnd» := mk 0 [leaf 115, leaf 110, leaf 100]

def «Reader.kwIf» := mk 0 [leaf 105, leaf 102]

def «Reader.kwQuote» :=
  mk 0 [leaf 113, leaf 117, leaf 111, leaf 116, leaf 101]

def «Reader.kwCons» := mk 0 [leaf 99, leaf 111, leaf 110, leaf 115]

def «Reader.kwNil» := mk 0 [leaf 110, leaf 105, leaf 108]

def «Reader.kwFold» := mk 0 [leaf 102, leaf 111, leaf 108, leaf 100]

def «Reader.kwPara» := mk 0 [leaf 112, leaf 97, leaf 114, leaf 97]

def «Reader.kwIter» := mk 0 [leaf 105, leaf 116, leaf 101, leaf 114]

def «Reader.kwFoldr» :=
  mk 0 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «Reader.kwLcase» :=
  mk 0 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «Reader.kwUnitValue» :=
  mk 0 [leaf 117, leaf 110, leaf 105, leaf 116]

def «Reader.kwDef» := mk 0 [leaf 100, leaf 101, leaf 102]

def «Reader.kwDeftype» :=
  mk 0 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «Reader.kwDefnum» :=
  mk 0 [leaf 100, leaf 101, leaf 102, leaf 110, leaf 117, leaf 109]

def «Reader.primNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 108, leaf 97, leaf 98, leaf 101, leaf 108],
      mk 0 [leaf 97, leaf 114, leaf 105, leaf 116, leaf 121],
      mk 0 [leaf 99, leaf 104, leaf 105, leaf 108, leaf 100],
      mk 0 [leaf 110, leaf 111, leaf 100, leaf 101],
      mk 0 [leaf 99,
        leaf 104,
        leaf 105,
        leaf 108,
        leaf 100,
        leaf 114,
        leaf 101,
        leaf 110],
      mk 0 [leaf 97, leaf 100, leaf 100],
      mk 0 [leaf 115, leaf 117, leaf 98],
      mk 0 [leaf 109, leaf 117, leaf 108],
      mk 0 [leaf 100, leaf 105, leaf 118],
      mk 0 [leaf 109, leaf 111, leaf 100],
      mk 0 [leaf 101, leaf 113],
      mk 0 [leaf 108, leaf 116],
      mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108],
      mk 0 [leaf 108, leaf 111, leaf 103, leaf 50]])

def «Reader.indexOf» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x0 x2).label ≠ 0 then
          «Prelude.some» (leaf 0)
        else
          if («Prelude.isSome» x3).label ≠ 0 then
            «Prelude.some» (Const.add («Prelude.get» x3) (leaf 1))
          else
            «Prelude.none»)
      «Prelude.none»
      x1

def «Reader.lookupAbbrev» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x0 (Const.child x2 (leaf 0))).label ≠ 0 then
          «Prelude.some» (Const.child x2 (leaf 1))
        else
          x3)
      «Prelude.none»
      x1

def «Reader.numeral» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (T ×
        T) := Const.foldr
      (α := T)
      (β := T × (T × T))
      (fun (x1 : T) (x2 : T × (T × T)) =>
        if (Const.lt x1 (leaf 48)).label ≠ 0 then
          (leaf 0, (x2).2)
        else
          if (Const.lt (leaf 57) x1).label ≠ 0 then
            (leaf 0, (x2).2)
          else
            ((x2).1,
              (Const.add ((x2).2).1 (Const.mul (Const.sub x1 (leaf 48)) ((x2).2).2),
                Const.mul (leaf 10) ((x2).2).2)))
      (leaf 1, (leaf 0, leaf 1))
      x0;
    if («Reader.nonEmpty» x0).label ≠ 0 then
      if ((x1).1).label ≠ 0 then
        «Prelude.some» ((x1).2).1
      else
        «Prelude.none»
    else
      «Prelude.none»

def «Reader.expandNums» :=
  fun (x0 : List T) (x1 : T) =>
    Const.fold
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.node x2 x3;
        if («Reader.isAtom» x4).label ≠ 0 then
          let x5 : T := «Reader.lookupAbbrev» («Reader.nameOf» x4) x0;
          if («Prelude.isSome» x5).label ≠ 0 then «Prelude.get» x5 else x4
        else
          x4)
      x1

def «Reader.numOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «Reader.expandNums» x0 x1;
    if («Reader.isAtom» x2).label ≠ 0 then
      if («Prelude.isSome»
        («Reader.numeral» (Const.children x2))).label ≠ 0 then
        «Prelude.some» x2
      else
        «Prelude.none»
    else
      «Prelude.none»

def «Reader.rtTrees» :=
  fun (x0 : List (T × T)) =>
    Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «Reader.rtValues» :=
  fun (x0 : List (T × T)) =>
    Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0

def «Reader.node2» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node x0 (x1 :: («Prelude.single» x2))

def «Reader.some2» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    if («Reader.both» x1 x2).label ≠ 0 then
      «Prelude.some»
        («Reader.node2» x0 («Prelude.get» x1) («Prelude.get» x2))
    else
      «Prelude.none»

def «Reader.readType» :=
  fun (x0 : List T) (x1 : T) =>
    (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : T := Const.node x2 («Reader.rtTrees» x3);
        let x5 : List T := «Reader.rtValues» x3;
        (x4,
          if («Reader.isAtom» x4).label ≠ 0 then
            let x6 : T := «Reader.nameOf» x4;
            if (Const.equal x6 «Reader.kwT»).label ≠ 0 then
              «Prelude.some» (leaf 0)
            else
              if (Const.equal x6 «Reader.kwUnit»).label ≠ 0 then
                «Prelude.some» (leaf 1)
              else
                «Reader.lookupAbbrev» x6 x0
          else
            if («Reader.isList» x4).label ≠ 0 then
              let x6 : T := «Prelude.at» (Const.children x4) (leaf 0);
              let x7 : T := Const.arity x4;
              if («Reader.named» x6 «Reader.kwProd»).label ≠ 0 then
                if (Const.eq x7 (leaf 3)).label ≠ 0 then
                  «Reader.some2»
                    (leaf 2)
                    («Prelude.at» x5 (leaf 1))
                    («Prelude.at» x5 (leaf 2))
                else
                  «Prelude.none»
              else
                if («Reader.named» x6 «Reader.kwArrow»).label ≠ 0 then
                  if (Const.eq x7 (leaf 3)).label ≠ 0 then
                    «Reader.some2»
                      (leaf 3)
                      («Prelude.at» x5 (leaf 1))
                      («Prelude.at» x5 (leaf 2))
                  else
                    «Prelude.none»
                else
                  if («Reader.named» x6 «Reader.kwList»).label ≠ 0 then
                    if (Const.eq x7 (leaf 2)).label ≠ 0 then
                      if («Prelude.isSome» («Prelude.at» x5 (leaf 1))).label ≠ 0 then
                        «Prelude.some»
                          (Const.node
                            (leaf 4)
                            («Prelude.single» («Prelude.get» («Prelude.at» x5 (leaf 1)))))
                      else
                        «Prelude.none»
                    else
                      «Prelude.none»
                  else
                    «Prelude.none»
            else
              «Prelude.none»))
      x1).2

def «Reader.readDatum» :=
  fun (x0 : T) =>
    if («Reader.isAtom» x0).label ≠ 0 then
      let x1 : T := «Reader.numeral» (Const.children x0);
      if («Prelude.isSome» x1).label ≠ 0 then
        «Prelude.some» (Const.node («Prelude.get» x1) ([] : List T))
      else
        «Prelude.none»
    else
      let x1 : T := (Const.fold
        (α := T × T)
        (fun (x1 : T) (x2 : List (T × T)) =>
          let x3 : T := Const.node x1 («Reader.rtTrees» x2);
          (x3,
            if («Reader.isAtom» x3).label ≠ 0 then
              let x4 : T := «Reader.numeral» (Const.children x3);
              if («Prelude.isSome» x4).label ≠ 0 then
                «Prelude.some»
                  (Const.node
                    (leaf 0)
                    («Prelude.single» (Const.node («Prelude.get» x4) ([] : List T))))
              else
                «Prelude.some» (Const.node (leaf 0) (Const.children x3))
            else
              if («Reader.isList» x3).label ≠ 0 then
                Const.lcase
                  (α := T)
                  (β := T)
                  (Const.children x3)
                  «Prelude.none»
                  (fun (x4 : T) (_ : List T) =>
                    let x6 : T := (if («Reader.isAtom» x4).label ≠ 0 then
                      «Reader.numeral» (Const.children x4)
                    else
                      «Prelude.none»);
                    let x7 : T := «Reader.allSome»
                      («Prelude.tail» («Reader.rtValues» x2));
                    if («Reader.both» x6 x7).label ≠ 0 then
                      «Prelude.some»
                        (Const.node
                          (leaf 0)
                          («Prelude.single»
                            (Const.node
                              («Prelude.get» x6)
                              (Const.foldr
                                (α := T)
                                (β := List T)
                                (fun (x8 : T) (x9 : List T) =>
                                  «Prelude.append» (Const.children x8) x9)
                                ([] : List T)
                                (Const.children («Prelude.get» x7))))))
                    else
                      «Prelude.none»)
              else
                «Prelude.none»))
        x0).2;
      if («Prelude.isSome» x1).label ≠ 0 then
        «Prelude.some» (Const.child («Prelude.get» x1) (leaf 0))
      else
        «Prelude.none»

def «Reader.rrTrees» :=
  fun (x0 : List (T × (List T → T))) =>
    Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x1 : T × (List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «Reader.rrApply» :=
  fun (x0 : List (T × (List T → T))) (x1 : List T) =>
    Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x2 : T × (List T → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0

def «Reader/RRs.tail» :=
  fun (x0 : List (T × (List T → T))) =>
    Const.lcase
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      x0
      ([] : List (T × (List T → T)))
      (fun (_ : T × (List T → T)) (x2 : List (T × (List T → T))) => x2)

def «Reader.rrAt» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    Const.lcase
      (α := T × (List T → T))
      (β := List T → T)
      (Const.iter (α := List (T × (List T → T))) «Reader/RRs.tail» x0 x1)
      (fun (_ : List T) => «Prelude.none»)
      (fun (x3 : T × (List T → T)) (_ : List (T × (List T → T))) => (x3).2)
      x2

def «Reader.app» :=
  fun (x0 : T) (x1 : T) => «Reader.node2» (leaf 10) x0 x1

def «Reader.apps» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Reader.app» x3 x2)
      x0
      («Prelude.reverse» x1)

def «Reader.some1» :=
  fun (x0 : T) (x1 : T) =>
    if («Prelude.isSome» x1).label ≠ 0 then
      «Prelude.some» (Const.node x0 («Prelude.single» («Prelude.get» x1)))
    else
      «Prelude.none»

def «Reader.argsOf» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    «Reader.allSome»
      («Reader.rrApply»
        (Const.iter (α := List (T × (List T → T))) «Reader/RRs.tail» x0 x1)
        x2)

def «Reader.mkArgs» :=
  fun (x0 : T) (x1 : T) =>
    if («Prelude.isSome» x1).label ≠ 0 then
      «Prelude.some» (Const.node x0 (Const.children («Prelude.get» x1)))
    else
      «Prelude.none»

def «Reader.appsOpt» :=
  fun (x0 : T) (x1 : T) =>
    if («Reader.both» x0 x1).label ≠ 0 then
      «Prelude.some»
        («Reader.apps» («Prelude.get» x0) (Const.children («Prelude.get» x1)))
    else
      «Prelude.none»

def «Reader.binders» :=
  fun (x0 : T) =>
    if («Reader.isList» x0).label ≠ 0 then
      if (Const.eq (Const.arity x0) (leaf 2)).label ≠ 0 then
        if («Reader.isAtom» (Const.child x0 (leaf 0))).label ≠ 0 then
          «Prelude.single» x0
        else
          Const.children x0
      else
        Const.children x0
    else
      ([] : List T)

def «Reader.readBinders» :=
  fun (x0 : List T) (x1 : List T) =>
    «Reader.allSome»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) =>
          ((if («Reader.isList» x2).label ≠ 0 then
            if (Const.eq (Const.arity x2) (leaf 2)).label ≠ 0 then
              if («Reader.isAtom» (Const.child x2 (leaf 0))).label ≠ 0 then
                let x4 : T := «Reader.readType» x0 (Const.child x2 (leaf 1));
                if («Prelude.isSome» x4).label ≠ 0 then
                  «Prelude.some»
                    («Reader.node2»
                      (leaf 0)
                      («Reader.nameOf» (Const.child x2 (leaf 0)))
                      («Prelude.get» x4))
                else
                  «Prelude.none»
              else
                «Prelude.none»
            else
              «Prelude.none»
          else
            «Prelude.none») ::
            x3))
        ([] : List T)
        x1)

def «Reader.resolveAtom» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := «Reader.numeral» (Const.children x1);
    if («Prelude.isSome» x3).label ≠ 0 then
      «Prelude.some»
        (Const.node (leaf 15) («Prelude.single» («Prelude.get» x3)))
    else
      let x4 : T := «Reader.nameOf» x1;
      let x5 : T := «Reader.indexOf» x4 x2;
      if («Prelude.isSome» x5).label ≠ 0 then
        «Prelude.some»
          (Const.node (leaf 8) («Prelude.single» («Prelude.get» x5)))
      else
        let x6 : T := «Reader.indexOf» x4 x0;
        if («Prelude.isSome» x6).label ≠ 0 then
          «Prelude.some»
            (Const.node (leaf 23) («Prelude.single» («Prelude.get» x6)))
        else
          let x7 : T := «Reader.indexOf» x4 «Reader.primNames»;
          if («Prelude.isSome» x7).label ≠ 0 then
            «Prelude.some»
              (Const.node (leaf 22) («Prelude.single» («Prelude.get» x7)))
          else
            if (Const.equal x4 «Reader.kwUnitValue»).label ≠ 0 then
              «Prelude.some» (Const.node (leaf 11) ([] : List T))
            else
              «Prelude.none»

def «Reader.resolveList» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : List T := Const.children x1;
    let x5 : T := Const.arity x1;
    let x6 : T := «Prelude.at» x4 (leaf 0);
    if (Const.eq x5 (leaf 0)).label ≠ 0 then
      «Prelude.none»
    else
      if (if («Reader.named» x6 «Reader.kwLam»).label ≠ 0 then
        Const.eq x5 (leaf 3)
      else
        leaf 0).label ≠ 0 then
        let x7 : T := «Reader.readBinders»
          x0
          («Reader.binders» («Prelude.at» x4 (leaf 1)));
        if («Prelude.isSome» x7).label ≠ 0 then
          let x8 : List T := Const.children («Prelude.get» x7);
          if («Reader.nonEmpty» x8).label ≠ 0 then
            let x9 : T := «Reader.rrAt»
              x2
              (leaf 2)
              («Prelude.append»
                («Prelude.reverse»
                  (Const.foldr
                    (α := T)
                    (β := List T)
                    (fun (x9 : T) (x10 : List T) => ((Const.child x9 (leaf 0)) :: x10))
                    ([] : List T)
                    x8))
                x3);
            if («Prelude.isSome» x9).label ≠ 0 then
              «Prelude.some»
                (Const.foldr
                  (α := T)
                  (β := T)
                  (fun (x10 : T) (x11 : T) =>
                    «Reader.node2» (leaf 9) (Const.child x10 (leaf 1)) x11)
                  («Prelude.get» x9)
                  x8)
            else
              «Prelude.none»
          else
            «Prelude.none»
        else
          «Prelude.none»
      else
        if (if («Reader.named» x6 «Reader.kwLet»).label ≠ 0 then
          Const.eq x5 (leaf 5)
        else
          leaf 0).label ≠ 0 then
          let x7 : T := «Prelude.at» x4 (leaf 1);
          if («Reader.isAtom» x7).label ≠ 0 then
            let x8 : T := «Reader.readType» x0 («Prelude.at» x4 (leaf 2));
            let x9 : T := «Reader.rrAt» x2 (leaf 4) ((«Reader.nameOf» x7) :: x3);
            let x10 : T := «Reader.rrAt» x2 (leaf 3) x3;
            if («Reader.both» x8 («Reader.both» x9 x10)).label ≠ 0 then
              «Prelude.some»
                («Reader.app»
                  («Reader.node2» (leaf 9) («Prelude.get» x8) («Prelude.get» x9))
                  («Prelude.get» x10))
            else
              «Prelude.none»
          else
            «Prelude.none»
        else
          if («Reader.named» x6 «Reader.kwPair»).label ≠ 0 then
            «Reader.mkArgs» (leaf 12) («Reader.argsOf» x2 (leaf 1) x3)
          else
            if («Reader.named» x6 «Reader.kwFst»).label ≠ 0 then
              «Reader.mkArgs» (leaf 13) («Reader.argsOf» x2 (leaf 1) x3)
            else
              if («Reader.named» x6 «Reader.kwSnd»).label ≠ 0 then
                «Reader.mkArgs» (leaf 14) («Reader.argsOf» x2 (leaf 1) x3)
              else
                if («Reader.named» x6 «Reader.kwIf»).label ≠ 0 then
                  «Reader.mkArgs» (leaf 16) («Reader.argsOf» x2 (leaf 1) x3)
                else
                  if («Reader.named» x6 «Reader.kwCons»).label ≠ 0 then
                    «Reader.mkArgs» (leaf 20) («Reader.argsOf» x2 (leaf 1) x3)
                  else
                    if (if («Reader.named» x6 «Reader.kwQuote»).label ≠ 0 then
                      Const.eq x5 (leaf 2)
                    else
                      leaf 0).label ≠ 0 then
                      «Reader.some1»
                        (leaf 15)
                        («Reader.readDatum» («Prelude.at» x4 (leaf 1)))
                    else
                      if (if («Reader.named» x6 «Reader.kwNil»).label ≠ 0 then
                        Const.eq x5 (leaf 2)
                      else
                        leaf 0).label ≠ 0 then
                        «Reader.some1»
                          (leaf 19)
                          («Reader.readType» x0 («Prelude.at» x4 (leaf 1)))
                      else
                        if (if («Reader.named» x6 «Reader.kwFold»).label ≠ 0 then
                          Const.lt (leaf 1) x5
                        else
                          leaf 0).label ≠ 0 then
                          let x7 : T := «Reader.readType» x0 («Prelude.at» x4 (leaf 1));
                          if («Prelude.isSome» x7).label ≠ 0 then
                            «Reader.appsOpt»
                              («Prelude.some»
                                (Const.node (leaf 17) («Prelude.single» («Prelude.get» x7))))
                              («Reader.argsOf» x2 (leaf 2) x3)
                          else
                            «Prelude.none»
                        else
                          if (if («Reader.named» x6 «Reader.kwPara»).label ≠ 0 then
                            Const.lt (leaf 1) x5
                          else
                            leaf 0).label ≠ 0 then
                            let x7 : T := «Reader.readType» x0 («Prelude.at» x4 (leaf 1));
                            if («Prelude.isSome» x7).label ≠ 0 then
                              «Reader.appsOpt»
                                («Prelude.some»
                                  (Const.node (leaf 25) («Prelude.single» («Prelude.get» x7))))
                                («Reader.argsOf» x2 (leaf 2) x3)
                            else
                              «Prelude.none»
                          else
                            if (if («Reader.named» x6 «Reader.kwIter»).label ≠ 0 then
                              Const.lt (leaf 1) x5
                            else
                              leaf 0).label ≠ 0 then
                              let x7 : T := «Reader.readType» x0 («Prelude.at» x4 (leaf 1));
                              if («Prelude.isSome» x7).label ≠ 0 then
                                «Reader.appsOpt»
                                  («Prelude.some»
                                    (Const.node (leaf 18) («Prelude.single» («Prelude.get» x7))))
                                  («Reader.argsOf» x2 (leaf 2) x3)
                              else
                                «Prelude.none»
                            else
                              if (if («Reader.named» x6 «Reader.kwFoldr»).label ≠ 0 then
                                Const.lt (leaf 2) x5
                              else
                                leaf 0).label ≠ 0 then
                                let x7 : T := «Reader.some2»
                                  (leaf 21)
                                  («Reader.readType» x0 («Prelude.at» x4 (leaf 1)))
                                  («Reader.readType» x0 («Prelude.at» x4 (leaf 2)));
                                if («Prelude.isSome» x7).label ≠ 0 then
                                  «Reader.appsOpt» x7 («Reader.argsOf» x2 (leaf 3) x3)
                                else
                                  «Prelude.none»
                              else
                                if (if («Reader.named» x6 «Reader.kwLcase»).label ≠ 0 then
                                  Const.lt (leaf 2) x5
                                else
                                  leaf 0).label ≠ 0 then
                                  let x7 : T := «Reader.some2»
                                    (leaf 24)
                                    («Reader.readType» x0 («Prelude.at» x4 (leaf 1)))
                                    («Reader.readType» x0 («Prelude.at» x4 (leaf 2)));
                                  if («Prelude.isSome» x7).label ≠ 0 then
                                    «Reader.appsOpt» x7 («Reader.argsOf» x2 (leaf 3) x3)
                                  else
                                    «Prelude.none»
                                else
                                  «Reader.appsOpt»
                                    («Reader.rrAt» x2 (leaf 0) x3)
                                    («Reader.argsOf» x2 (leaf 1) x3)

def «Reader.resolve» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : List T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x4 : T) (x5 : List (T × (List T → T))) =>
        let x6 : T := Const.node x4 («Reader.rrTrees» x5);
        (x6,
          fun (x7 : List T) =>
            if («Reader.isAtom» x6).label ≠ 0 then
              «Reader.resolveAtom» x1 x6 x7
            else
              if («Reader.isList» x6).label ≠ 0 then
                «Reader.resolveList» x0 x6 x5 x7
              else
                «Prelude.none»))
      x2).2
      x3

def «Reader.reservedNames» :=
  «Prelude.append»
    («Reader.kwLam» ::
      («Reader.kwLet» ::
        («Reader.kwPair» ::
          («Reader.kwFst» ::
            («Reader.kwSnd» ::
              («Reader.kwIf» ::
                («Reader.kwQuote» ::
                  («Reader.kwCons» ::
                    («Reader.kwNil» ::
                      («Reader.kwFold» ::
                        («Reader.kwPara» ::
                          («Reader.kwIter» ::
                            («Reader.kwFoldr» ::
                              («Reader.kwLcase» ::
                                («Reader.kwUnitValue» ::
                                  («Reader.kwDef» ::
                                    («Reader.kwDeftype» ::
                                      («Reader.kwDefnum» ::
                                        («Reader.kwHole» ::
                                          ((mk 0 [leaf 42, leaf 97, leaf 110, leaf 110]) ::
                                            ((mk 0 [leaf 42, leaf 100, leaf 111, leaf 99]) ::
                                              («Reader.kwT» ::
                                                («Reader.kwUnit» ::
                                                  («Reader.kwProd» ::
                                                    («Reader.kwArrow» ::
                                                      («Prelude.single»
                                                        «Reader.kwList»))))))))))))))))))))))))))
    «Reader.primNames»

def «Reader.isFresh» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    if («Prelude.isSome»
      («Reader.indexOf» x3 «Reader.reservedNames»)).label ≠ 0 then
      leaf 0
    else
      if («Prelude.isSome» («Reader.indexOf» x3 x2)).label ≠ 0 then
        leaf 0
      else
        if («Prelude.isSome» («Reader.lookupAbbrev» x3 x0)).label ≠ 0 then
          leaf 0
        else
          if («Prelude.isSome» («Reader.lookupAbbrev» x3 x1)).label ≠ 0 then
            leaf 0
          else
            leaf 1

def «Reader.progStep» :=
  fun (x0 : T × (List T × (List T × (List T × List T)))) (x1 : T) =>
    let x2 : List T := ((x0).2).1;
    let x3 : List T := (((x0).2).2).1;
    let x4 : List T := ((((x0).2).2).2).1;
    let x5 : List T := ((((x0).2).2).2).2;
    if (if ((x0).1).label ≠ 0 then
      if («Reader.isList» x1).label ≠ 0 then
        if (Const.eq (Const.arity x1) (leaf 3)).label ≠ 0 then
          if («Reader.isAtom» (Const.child x1 (leaf 1))).label ≠ 0 then
            «Reader.isFresh» x2 x3 x4 («Reader.nameOf» (Const.child x1 (leaf 1)))
          else
            leaf 0
        else
          leaf 0
      else
        leaf 0
    else
      leaf 0).label ≠ 0 then
      let x6 : T := «Reader.nameOf» (Const.child x1 (leaf 1));
      if («Reader.named»
        (Const.child x1 (leaf 0))
        «Reader.kwDef»).label ≠ 0 then
        let x7 : T := «Reader.resolve»
          x2
          x4
          («Reader.expandNums» x3 (Const.child x1 (leaf 2)))
          ([] : List T);
        if («Prelude.isSome» x7).label ≠ 0 then
          (leaf 1,
            (x2,
              (x3,
                («Prelude.append» x4 («Prelude.single» x6),
                  «Prelude.append» x5 («Prelude.single» («Prelude.get» x7))))))
        else
          (leaf 0, (x0).2)
      else
        if («Reader.named»
          (Const.child x1 (leaf 0))
          «Reader.kwDeftype»).label ≠ 0 then
          let x7 : T := «Reader.readType» x2 (Const.child x1 (leaf 2));
          if («Prelude.isSome» x7).label ≠ 0 then
            (leaf 1,
              (((«Reader.node2» (leaf 0) x6 («Prelude.get» x7)) :: x2), ((x0).2).2))
          else
            (leaf 0, (x0).2)
        else
          if («Reader.named»
            (Const.child x1 (leaf 0))
            «Reader.kwDefnum»).label ≠ 0 then
            let x7 : T := «Reader.numOf» x3 (Const.child x1 (leaf 2));
            if («Prelude.isSome» x7).label ≠ 0 then
              (leaf 1,
                (x2,
                  (((«Reader.node2» (leaf 0) x6 («Prelude.get» x7)) :: x3),
                    (((x0).2).2).2)))
            else
              (leaf 0, (x0).2)
          else
            (leaf 0, (x0).2)
    else
      (leaf 0, (x0).2)

def «Reader.readProgram» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (List T ×
        (List T ×
          (List T ×
            List
              T))) := Const.foldr
      (α := T)
      (β := (T × (List T × (List T × (List T × List T)))) →
        T × (List T × (List T × (List T × List T))))
      (fun (x1 : T)
         (x2 : (T × (List T × (List T × (List T × List T)))) →
           T × (List T × (List T × (List T × List T))))
         (x3 : T × (List T × (List T × (List T × List T)))) =>
        x2 («Reader.progStep» x3 x1))
      (fun (x1 : T × (List T × (List T × (List T × List T)))) => x1)
      x0
      (leaf 1,
        (([] : List T), (([] : List T), (([] : List T), ([] : List T)))));
    if ((x1).1).label ≠ 0 then
      «Prelude.some»
        («Reader.node2»
          (leaf 100)
          (Const.node (leaf 101) ((((x1).2).2).2).2)
          (Const.node (leaf 102) ((((x1).2).2).2).1))
    else
      «Prelude.none»

def «Check.tyArrow» :=
  fun (x0 : T) (x1 : T) => «Reader.node2» (leaf 3) x0 x1

def «Check.tyList» :=
  fun (x0 : T) => Const.node (leaf 4) («Prelude.single» x0)

def «Check.isTy» :=
  fun (x0 : T) =>
    Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := «Prelude.length» x2;
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          if (Const.eq x1 (leaf 0)).label ≠ 0 then
            leaf 1
          else
            Const.eq x1 (leaf 1)
        else
          if (Const.eq x3 (leaf 1)).label ≠ 0 then
            «Prelude.and» (Const.eq x1 (leaf 4)) («Prelude.at» x2 (leaf 0))
          else
            if (Const.eq x3 (leaf 2)).label ≠ 0 then
              «Prelude.and»
                (if (Const.eq x1 (leaf 2)).label ≠ 0 then
                  leaf 1
                else
                  Const.eq x1 (leaf 3))
                («Prelude.and» («Prelude.at» x2 (leaf 0)) («Prelude.at» x2 (leaf 1)))
            else
              leaf 0)
      x0

def «Check.isProd» :=
  fun (x0 : T) =>
    «Prelude.and»
      (Const.eq (Const.label x0) (leaf 2))
      (Const.eq (Const.arity x0) (leaf 2))

def «Check.isArrow» :=
  fun (x0 : T) =>
    «Prelude.and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 2))

def «Check.isListTy» :=
  fun (x0 : T) =>
    «Prelude.and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq (Const.arity x0) (leaf 1))

def «Check.foldTy» :=
  fun (x0 : T) =>
    «Check.tyArrow»
      («Check.tyArrow» (leaf 0) («Check.tyArrow» («Check.tyList» x0) x0))
      («Check.tyArrow» (leaf 0) x0)

def «Check.iterTy» :=
  fun (x0 : T) =>
    «Check.tyArrow»
      («Check.tyArrow» x0 x0)
      («Check.tyArrow» x0 («Check.tyArrow» (leaf 0) x0))

def «Check.foldrTy» :=
  fun (x0 : T) (x1 : T) =>
    «Check.tyArrow»
      («Check.tyArrow» x0 («Check.tyArrow» x1 x1))
      («Check.tyArrow» x1 («Check.tyArrow» («Check.tyList» x0) x1))

def «Check.lcaseTy» :=
  fun (x0 : T) (x1 : T) =>
    «Check.tyArrow»
      («Check.tyList» x0)
      («Check.tyArrow»
        x1
        («Check.tyArrow»
          («Check.tyArrow» x0 («Check.tyArrow» («Check.tyList» x0) x1))
          x1))

def «Check.primTypes» :=
  let x0 : T := «Check.tyArrow» (leaf 0) (leaf 0);
  let x1 : T := «Check.tyArrow» (leaf 0) x0;
  «Prelude.append»
    (x0 ::
      (x0 ::
        (x1 ::
          ((«Check.tyArrow»
            (leaf 0)
            («Check.tyArrow» («Check.tyList» (leaf 0)) (leaf 0))) ::
            ((«Check.tyArrow» (leaf 0) («Check.tyList» (leaf 0))) ::
              ([] : List T))))))
    («Prelude.append»
      («Prelude.replicate» (leaf 8) x1)
      («Prelude.single» x0))

def «Check.checkNode» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : T := Const.label x1;
    let x5 : List T := Const.children x1;
    let x6 : T := Const.arity x1;
    if (Const.eq x4 (leaf 8)).label ≠ 0 then
      if (Const.eq x6 (leaf 1)).label ≠ 0 then
        «Prelude.nth» x3 (Const.label («Prelude.at» x5 (leaf 0)))
      else
        «Prelude.none»
    else
      if (Const.eq x4 (leaf 9)).label ≠ 0 then
        if (Const.eq x6 (leaf 2)).label ≠ 0 then
          let x7 : T := «Prelude.at» x5 (leaf 0);
          if («Check.isTy» x7).label ≠ 0 then
            let x8 : T := «Reader.rrAt» x2 (leaf 1) (x7 :: x3);
            if («Prelude.isSome» x8).label ≠ 0 then
              «Prelude.some» («Check.tyArrow» x7 («Prelude.get» x8))
            else
              «Prelude.none»
          else
            «Prelude.none»
        else
          «Prelude.none»
      else
        if (Const.eq x4 (leaf 10)).label ≠ 0 then
          if (Const.eq x6 (leaf 2)).label ≠ 0 then
            let x7 : T := «Reader.rrAt» x2 (leaf 0) x3;
            let x8 : T := «Reader.rrAt» x2 (leaf 1) x3;
            if («Reader.both» x7 x8).label ≠ 0 then
              if («Check.isArrow» («Prelude.get» x7)).label ≠ 0 then
                if (Const.equal
                  («Prelude.get» x8)
                  (Const.child («Prelude.get» x7) (leaf 0))).label ≠ 0 then
                  «Prelude.some» (Const.child («Prelude.get» x7) (leaf 1))
                else
                  «Prelude.none»
              else
                «Prelude.none»
            else
              «Prelude.none»
          else
            «Prelude.none»
        else
          if (Const.eq x4 (leaf 11)).label ≠ 0 then
            if (Const.eq x6 (leaf 0)).label ≠ 0 then
              «Prelude.some» (leaf 1)
            else
              «Prelude.none»
          else
            if (Const.eq x4 (leaf 12)).label ≠ 0 then
              if (Const.eq x6 (leaf 2)).label ≠ 0 then
                «Reader.some2»
                  (leaf 2)
                  («Reader.rrAt» x2 (leaf 0) x3)
                  («Reader.rrAt» x2 (leaf 1) x3)
              else
                «Prelude.none»
            else
              if (Const.eq x4 (leaf 13)).label ≠ 0 then
                if (Const.eq x6 (leaf 1)).label ≠ 0 then
                  let x7 : T := «Reader.rrAt» x2 (leaf 0) x3;
                  if («Prelude.isSome» x7).label ≠ 0 then
                    if («Check.isProd» («Prelude.get» x7)).label ≠ 0 then
                      «Prelude.some» (Const.child («Prelude.get» x7) (leaf 0))
                    else
                      «Prelude.none»
                  else
                    «Prelude.none»
                else
                  «Prelude.none»
              else
                if (Const.eq x4 (leaf 14)).label ≠ 0 then
                  if (Const.eq x6 (leaf 1)).label ≠ 0 then
                    let x7 : T := «Reader.rrAt» x2 (leaf 0) x3;
                    if («Prelude.isSome» x7).label ≠ 0 then
                      if («Check.isProd» («Prelude.get» x7)).label ≠ 0 then
                        «Prelude.some» (Const.child («Prelude.get» x7) (leaf 1))
                      else
                        «Prelude.none»
                    else
                      «Prelude.none»
                  else
                    «Prelude.none»
                else
                  if (Const.eq x4 (leaf 15)).label ≠ 0 then
                    if (Const.eq x6 (leaf 1)).label ≠ 0 then
                      «Prelude.some» (leaf 0)
                    else
                      «Prelude.none»
                  else
                    if (Const.eq x4 (leaf 16)).label ≠ 0 then
                      if (Const.eq x6 (leaf 3)).label ≠ 0 then
                        let x7 : T := «Reader.rrAt» x2 (leaf 0) x3;
                        let x8 : T := «Reader.rrAt» x2 (leaf 1) x3;
                        let x9 : T := «Reader.rrAt» x2 (leaf 2) x3;
                        if («Reader.both» x7 («Reader.both» x8 x9)).label ≠ 0 then
                          if (Const.equal («Prelude.get» x7) (leaf 0)).label ≠ 0 then
                            if (Const.equal («Prelude.get» x9) («Prelude.get» x8)).label ≠ 0 then
                              x8
                            else
                              «Prelude.none»
                          else
                            «Prelude.none»
                        else
                          «Prelude.none»
                      else
                        «Prelude.none»
                    else
                      if (Const.eq x4 (leaf 17)).label ≠ 0 then
                        if (Const.eq x6 (leaf 1)).label ≠ 0 then
                          if («Check.isTy» («Prelude.at» x5 (leaf 0))).label ≠ 0 then
                            «Prelude.some» («Check.foldTy» («Prelude.at» x5 (leaf 0)))
                          else
                            «Prelude.none»
                        else
                          «Prelude.none»
                      else
                        if (Const.eq x4 (leaf 25)).label ≠ 0 then
                          if (Const.eq x6 (leaf 1)).label ≠ 0 then
                            if («Check.isTy» («Prelude.at» x5 (leaf 0))).label ≠ 0 then
                              «Prelude.some» («Check.foldTy» («Prelude.at» x5 (leaf 0)))
                            else
                              «Prelude.none»
                          else
                            «Prelude.none»
                        else
                          if (Const.eq x4 (leaf 18)).label ≠ 0 then
                            if (Const.eq x6 (leaf 1)).label ≠ 0 then
                              if («Check.isTy» («Prelude.at» x5 (leaf 0))).label ≠ 0 then
                                «Prelude.some» («Check.iterTy» («Prelude.at» x5 (leaf 0)))
                              else
                                «Prelude.none»
                            else
                              «Prelude.none»
                          else
                            if (Const.eq x4 (leaf 19)).label ≠ 0 then
                              if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                if («Check.isTy» («Prelude.at» x5 (leaf 0))).label ≠ 0 then
                                  «Prelude.some» («Check.tyList» («Prelude.at» x5 (leaf 0)))
                                else
                                  «Prelude.none»
                              else
                                «Prelude.none»
                            else
                              if (Const.eq x4 (leaf 20)).label ≠ 0 then
                                if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                  let x7 : T := «Reader.rrAt» x2 (leaf 0) x3;
                                  let x8 : T := «Reader.rrAt» x2 (leaf 1) x3;
                                  if («Reader.both» x7 x8).label ≠ 0 then
                                    if («Check.isListTy» («Prelude.get» x8)).label ≠ 0 then
                                      if (Const.equal
                                        («Prelude.get» x7)
                                        (Const.child («Prelude.get» x8) (leaf 0))).label ≠ 0 then
                                        «Prelude.some» («Check.tyList» («Prelude.get» x7))
                                      else
                                        «Prelude.none»
                                    else
                                      «Prelude.none»
                                  else
                                    «Prelude.none»
                                else
                                  «Prelude.none»
                              else
                                if (Const.eq x4 (leaf 21)).label ≠ 0 then
                                  if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                    if («Prelude.and»
                                      («Check.isTy» («Prelude.at» x5 (leaf 0)))
                                      («Check.isTy» («Prelude.at» x5 (leaf 1)))).label ≠ 0 then
                                      «Prelude.some»
                                        («Check.foldrTy»
                                          («Prelude.at» x5 (leaf 0))
                                          («Prelude.at» x5 (leaf 1)))
                                    else
                                      «Prelude.none»
                                  else
                                    «Prelude.none»
                                else
                                  if (Const.eq x4 (leaf 22)).label ≠ 0 then
                                    if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                      «Prelude.nth»
                                        «Check.primTypes»
                                        (Const.label («Prelude.at» x5 (leaf 0)))
                                    else
                                      «Prelude.none»
                                  else
                                    if (Const.eq x4 (leaf 23)).label ≠ 0 then
                                      if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                        «Prelude.nth» x0 (Const.label («Prelude.at» x5 (leaf 0)))
                                      else
                                        «Prelude.none»
                                    else
                                      if (Const.eq x4 (leaf 24)).label ≠ 0 then
                                        if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                          if («Prelude.and»
                                            («Check.isTy» («Prelude.at» x5 (leaf 0)))
                                            («Check.isTy»
                                              («Prelude.at» x5 (leaf 1)))).label ≠ 0 then
                                            «Prelude.some»
                                              («Check.lcaseTy»
                                                («Prelude.at» x5 (leaf 0))
                                                («Prelude.at» x5 (leaf 1)))
                                          else
                                            «Prelude.none»
                                        else
                                          «Prelude.none»
                                      else
                                        «Prelude.none»

def «Check.typeIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x3 : T) (x4 : List (T × (List T → T))) =>
        let x5 : T := Const.node x3 («Reader.rrTrees» x4);
        (x5, fun (x6 : List T) => «Check.checkNode» x0 x5 x4 x6))
      x2).2
      x1

def «Check.typeOf» :=
  fun (x0 : List T) (x1 : T) => «Check.typeIn» x0 ([] : List T) x1

def «Check.checkProgram» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := (T × List T) → T × List T)
      (fun (x1 : T) (x2 : (T × List T) → T × List T) (x3 : T × List T) =>
        x2
          (if ((x3).1).label ≠ 0 then
            let x4 : T := «Check.typeOf» (x3).2 x1;
            if («Prelude.isSome» x4).label ≠ 0 then
              (leaf 1,
                «Prelude.append» (x3).2 («Prelude.single» («Prelude.get» x4)))
            else
              (leaf 0, (x3).2)
          else
            x3))
      (fun (x1 : T × List T) => x1)
      x0
      (leaf 1, ([] : List T));
    if ((x1).1).label ≠ 0 then
      «Prelude.some» (Const.node (leaf 0) (x1).2)
    else
      «Prelude.none»

end GebMirror.Check

end
