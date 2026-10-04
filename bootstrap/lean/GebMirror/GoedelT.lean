module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.GoedelT

def «append» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0

def «length» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0

def «reverse» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T)

def «replicate» :=
  fun (x0 : T) (x1 : T) =>
    Const.iter
      (α := List T)
      (fun (x2 : List T) => (x1 :: x2))
      ([] : List T)
      x0

def «single» := fun (x0 : T) => (x0 :: ([] : List T))

def «some» := fun (x0 : T) => Const.node (leaf 1) («single» x0)

def «none» := leaf 0

def «isSome» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «get» := fun (x0 : T) => Const.child x0 (leaf 0)

def «and» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then x1 else leaf 0

def «or» :=
  fun (x0 : T) (x1 : T) => if (x0).label ≠ 0 then leaf 1 else x1

def «at» :=
  fun (x0 : List T) (x1 : T) => Const.child (Const.node (leaf 0) x0) x1

def «nth» :=
  fun (x0 : List T) (x1 : T) =>
    if (Const.lt x1 («length» x0)).label ≠ 0 then
      «some» («at» x0 x1)
    else
      «none»

def «tail» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2)

def «drop» :=
  fun (x0 : T) (x1 : List T) => Const.iter (α := List T) «tail» x1 x0

def «digitsMsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    (Const.iter
      (α := T × List T)
      (fun (x3 : T × List T) =>
        (Const.div (x3).1 x0, ((Const.mod (x3).1 x0) :: (x3).2)))
      (x1, ([] : List T))
      x2).2

def «digitsLsb» :=
  fun (x0 : T) (x1 : T) (x2 : T) => «reverse» («digitsMsb» x0 x1 x2)

def «both» :=
  fun (x0 : T) (x1 : T) =>
    if («isSome» x0).label ≠ 0 then «isSome» x1 else leaf 0

def «nonEmpty» :=
  fun (x0 : List T) =>
    Const.lcase
      (α := T)
      (β := T)
      x0
      (leaf 0)
      (fun (_ : T) (_ : List T) => leaf 1)

def «allSome» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        («both» x1 (x2).1, ((«get» x1) :: (x2).2)))
      (leaf 1, ([] : List T))
      x0;
    if ((x1).1).label ≠ 0 then
      «some» (Const.node (leaf 0) (x1).2)
    else
      «none»

def «lexFail» := (([] : List T), (([] : List T), leaf 11))

def «lexIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) => (x0, (x1, x2))

def «lexIdle» :=
  fun (x0 : List T) => «lexIn» x0 ([] : List T) (leaf 0)

def «withLen» := fun (x0 : T) (x1 : T) => Const.node x0 («single» x1)

def «inRange» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    if (Const.lt x0 x1).label ≠ 0 then
      leaf 0
    else
      Const.lt x0 (Const.add x2 (leaf 1))

def «isDigit» := fun (x0 : T) => «inRange» x0 (leaf 48) (leaf 57)

def «isSpace» :=
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

def «isTokenStart» :=
  fun (x0 : T) =>
    if («inRange» x0 (leaf 65) (leaf 90)).label ≠ 0 then
      leaf 1
    else
      if («inRange» x0 (leaf 97) (leaf 122)).label ≠ 0 then
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

def «isTokenChar» :=
  fun (x0 : T) =>
    if («isTokenStart» x0).label ≠ 0 then leaf 1 else «isDigit» x0

def «isPlainIn» :=
  fun (x0 : T) =>
    if («inRange» x0 (leaf 32) (leaf 126)).label ≠ 0 then
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

def «atomTok» :=
  fun (x0 : List T) => Const.node (leaf 3) («reverse» x0)

def «kwHole» := mk 0 [leaf 104, leaf 111, leaf 108, leaf 101]

def «holeToks» :=
  fun (x0 : List T) (x1 : List T) =>
    ((leaf 2) ::
      ((«atomTok» x0) ::
        ((Const.node (leaf 3) (Const.children «kwHole»)) ::
          ((leaf 1) :: x1))))

def «idleStep» :=
  fun (x0 : List T) (x1 : T) =>
    if (Const.eq x1 (leaf 59)).label ≠ 0 then
      «lexIn» x0 ([] : List T) (leaf 4)
    else
      if (Const.eq x1 (leaf 40)).label ≠ 0 then
        «lexIdle» ((leaf 1) :: x0)
      else
        if (Const.eq x1 (leaf 41)).label ≠ 0 then
          «lexIdle» ((leaf 2) :: x0)
        else
          if (Const.eq x1 (leaf 34)).label ≠ 0 then
            «lexIn» x0 ([] : List T) («withLen» (leaf 5) «none»)
          else
            if (Const.eq x1 (leaf 38)).label ≠ 0 then
              «lexIdle» ((Const.node (leaf 3) («single» (leaf 38))) :: x0)
            else
              if (Const.eq x1 (leaf 63)).label ≠ 0 then
                «lexIn» x0 ([] : List T) (leaf 3)
              else
                if (Const.eq x1 (leaf 35)).label ≠ 0 then
                  «lexIn» x0 ([] : List T) («withLen» (leaf 13) «none»)
                else
                  if (Const.eq x1 (leaf 124)).label ≠ 0 then
                    «lexIn» x0 ([] : List T) («withLen» (leaf 14) «none»)
                  else
                    if («isSpace» x1).label ≠ 0 then
                      «lexIdle» x0
                    else
                      if («isDigit» x1).label ≠ 0 then
                        «lexIn» x0 («single» x1) (leaf 2)
                      else
                        if («isTokenStart» x1).label ≠ 0 then
                          «lexIn» x0 («single» x1) (leaf 1)
                        else
                          «lexFail»

def «endAtom» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    if (if («isSome» x1).label ≠ 0 then
      Const.eq («get» x1) («length» x2)
    else
      leaf 1).label ≠ 0 then
      «lexIdle» ((Const.node (leaf 3) x2) :: x0)
    else
      «lexFail»

def «strStep» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) =>
    if (Const.eq x3 (leaf 34)).label ≠ 0 then
      «endAtom» x0 x2 («reverse» x1)
    else
      if (Const.eq x3 (leaf 92)).label ≠ 0 then
        «lexIn» x0 x1 («withLen» (leaf 6) x2)
      else
        if («isPlainIn» x3).label ≠ 0 then
          «lexIn» x0 (x3 :: x1) («withLen» (leaf 5) x2)
        else
          «lexFail»

def «escChar» :=
  fun (x0 : T) =>
    if (Const.eq x0 (leaf 97)).label ≠ 0 then
      «some» (leaf 7)
    else
      if (Const.eq x0 (leaf 98)).label ≠ 0 then
        «some» (leaf 8)
      else
        if (Const.eq x0 (leaf 116)).label ≠ 0 then
          «some» (leaf 9)
        else
          if (Const.eq x0 (leaf 118)).label ≠ 0 then
            «some» (leaf 11)
          else
            if (Const.eq x0 (leaf 110)).label ≠ 0 then
              «some» (leaf 10)
            else
              if (Const.eq x0 (leaf 102)).label ≠ 0 then
                «some» (leaf 12)
              else
                if (Const.eq x0 (leaf 114)).label ≠ 0 then
                  «some» (leaf 13)
                else
                  if (Const.eq x0 (leaf 34)).label ≠ 0 then
                    «some» x0
                  else
                    if (Const.eq x0 (leaf 39)).label ≠ 0 then
                      «some» x0
                    else
                      if (Const.eq x0 (leaf 63)).label ≠ 0 then
                        «some» x0
                      else
                        if (Const.eq x0 (leaf 92)).label ≠ 0 then «some» x0 else «none»

def «hexVal» :=
  fun (x0 : T) =>
    if («isDigit» x0).label ≠ 0 then
      «some» (Const.sub x0 (leaf 48))
    else
      if («inRange» x0 (leaf 65) (leaf 70)).label ≠ 0 then
        «some» (Const.sub x0 (leaf 55))
      else
        if («inRange» x0 (leaf 97) (leaf 102)).label ≠ 0 then
          «some» (Const.sub x0 (leaf 87))
        else
          «none»

def «decodeHex» :=
  fun (x0 : List T) =>
    if (Const.eq
      (Const.mod («length» x0) (leaf 2))
      (leaf 0)).label ≠ 0 then
      let x1 : T ×
        (List T ×
          T) := Const.foldr
        (α := T)
        (β := T × (List T × T))
        (fun (x1 : T) (x2 : T × (List T × T)) =>
          let x3 : T := «hexVal» x1;
          if (if ((x2).1).label ≠ 0 then «isSome» x3 else leaf 0).label ≠ 0 then
            if («isSome» ((x2).2).2).label ≠ 0 then
              (leaf 1,
                (((Const.add (Const.mul (leaf 16) («get» x3)) («get» ((x2).2).2)) ::
                  ((x2).2).1),
                  «none»))
            else
              (leaf 1, (((x2).2).1, «some» («get» x3)))
          else
            (leaf 0, (x2).2))
        (leaf 1, (([] : List T), «none»))
        x0;
      if ((x1).1).label ≠ 0 then
        «some» (Const.node (leaf 0) ((x1).2).1)
      else
        «none»
    else
      «none»

def «base64Val» :=
  fun (x0 : T) =>
    if («inRange» x0 (leaf 65) (leaf 90)).label ≠ 0 then
      «some» (Const.sub x0 (leaf 65))
    else
      if («inRange» x0 (leaf 97) (leaf 122)).label ≠ 0 then
        «some» (Const.sub x0 (leaf 71))
      else
        if («isDigit» x0).label ≠ 0 then
          «some» (Const.add x0 (leaf 4))
        else
          if (Const.eq x0 (leaf 43)).label ≠ 0 then
            «some» (leaf 62)
          else
            if (Const.eq x0 (leaf 47)).label ≠ 0 then «some» (leaf 63) else «none»

def «b64Fail» := (leaf 0, (([] : List T), (leaf 0, (leaf 0, leaf 0))))

def «base64Step» :=
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
          «b64Fail»
      else
        if (Const.eq x5 (leaf 0)).label ≠ 0 then
          let x6 : T := «base64Val» x1;
          if («isSome» x6).label ≠ 0 then
            if (Const.lt (Const.add x4 (leaf 6)) (leaf 8)).label ≠ 0 then
              (leaf 1,
                (x2,
                  (Const.add (Const.mul (leaf 64) x3) («get» x6),
                    (Const.add x4 (leaf 6), leaf 0))))
            else
              let x7 : T := Const.add (Const.mul (leaf 64) x3) («get» x6);
              let x8 : T := Const.sub (Const.add x4 (leaf 6)) (leaf 8);
              let x9 : T := Const.iter
                (α := T)
                (fun (x9 : T) => Const.mul x9 (leaf 2))
                (leaf 1)
                x8;
              (leaf 1, (((Const.div x7 x9) :: x2), (Const.mod x7 x9, (x8, leaf 0))))
          else
            «b64Fail»
        else
          «b64Fail»
    else
      x0

def «decodeBase64» :=
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
        x2 («base64Step» x3 x1))
      (fun (x1 : T × (List T × (T × (T × T)))) => x1)
      x0
      (leaf 1, (([] : List T), (leaf 0, (leaf 0, leaf 0))));
    if (if ((x1).1).label ≠ 0 then
      Const.lt ((((x1).2).2).2).1 (leaf 6)
    else
      leaf 0).label ≠ 0 then
      «some» (Const.node (leaf 0) («reverse» ((x1).2).1))
    else
      «none»

def «lengthStep» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : List T := «reverse» x1;
    if (if (Const.lt (leaf 1) («length» x3)).label ≠ 0 then
      Const.eq («at» x3 (leaf 0)) (leaf 48)
    else
      leaf 0).label ≠ 0 then
      «lexFail»
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
          «lexIdle» ((Const.node (leaf 3) ([] : List T)) :: x0)
        else
          «lexIn» x0 ([] : List T) (Const.node (leaf 12) («single» x4))
      else
        if (Const.eq x2 (leaf 34)).label ≠ 0 then
          «lexIn» x0 ([] : List T) («withLen» (leaf 5) («some» x4))
        else
          if (Const.eq x2 (leaf 35)).label ≠ 0 then
            «lexIn» x0 ([] : List T) («withLen» (leaf 13) («some» x4))
          else
            if (Const.eq x2 (leaf 124)).label ≠ 0 then
              «lexIn» x0 ([] : List T) («withLen» (leaf 14) («some» x4))
            else
              «lexFail»

def «lexStep» :=
  fun (x0 : List T × (List T × T)) (x1 : T) =>
    let x2 : List T := (x0).1;
    let x3 : List T := ((x0).2).1;
    let x4 : T := ((x0).2).2;
    let x5 : T := Const.label x4;
    if (Const.eq x5 (leaf 0)).label ≠ 0 then
      «idleStep» x2 x1
    else
      if (Const.eq x5 (leaf 4)).label ≠ 0 then
        if (Const.eq x1 (leaf 10)).label ≠ 0 then «lexIdle» x2 else x0
      else
        if (Const.eq x5 (leaf 1)).label ≠ 0 then
          if («isTokenChar» x1).label ≠ 0 then
            «lexIn» x2 (x1 :: x3) x4
          else
            «idleStep» ((«atomTok» x3) :: x2) x1
        else
          if (Const.eq x5 (leaf 2)).label ≠ 0 then
            if («isDigit» x1).label ≠ 0 then
              «lexIn» x2 (x1 :: x3) x4
            else
              if (if («isTokenChar» x1).label ≠ 0 then
                leaf 1
              else
                if (Const.eq x1 (leaf 34)).label ≠ 0 then
                  leaf 1
                else
                  if (Const.eq x1 (leaf 35)).label ≠ 0 then
                    leaf 1
                  else
                    Const.eq x1 (leaf 124)).label ≠ 0 then
                «lengthStep» x2 x3 x1
              else
                «idleStep» ((«atomTok» x3) :: x2) x1
          else
            if (Const.eq x5 (leaf 3)).label ≠ 0 then
              if (if («isTokenChar» x1).label ≠ 0 then
                if («nonEmpty» x3).label ≠ 0 then
                  leaf 1
                else
                  if («isDigit» x1).label ≠ 0 then leaf 0 else leaf 1
              else
                leaf 0).label ≠ 0 then
                «lexIn» x2 (x1 :: x3) x4
              else
                if («nonEmpty» x3).label ≠ 0 then
                  «idleStep» («holeToks» x3 x2) x1
                else
                  «lexFail»
            else
              if (Const.eq x5 (leaf 11)).label ≠ 0 then
                x0
              else
                if (Const.eq x5 (leaf 12)).label ≠ 0 then
                  if (Const.lt (Const.child x4 (leaf 0)) (leaf 2)).label ≠ 0 then
                    «lexIdle» ((«atomTok» (x1 :: x3)) :: x2)
                  else
                    «lexIn»
                      x2
                      (x1 :: x3)
                      (Const.node
                        (leaf 12)
                        («single» (Const.sub (Const.child x4 (leaf 0)) (leaf 1))))
                else
                  let x6 : T := Const.child x4 (leaf 0);
                  if (Const.eq x5 (leaf 5)).label ≠ 0 then
                    «strStep» x2 x3 x6 x1
                  else
                    if (Const.eq x5 (leaf 6)).label ≠ 0 then
                      let x7 : T := «escChar» x1;
                      if («isSome» x7).label ≠ 0 then
                        «lexIn» x2 ((«get» x7) :: x3) («withLen» (leaf 5) x6)
                      else
                        if (Const.eq x1 (leaf 120)).label ≠ 0 then
                          «lexIn»
                            x2
                            x3
                            (Const.node (leaf 9) (x6 :: ((leaf 0) :: («single» (leaf 0)))))
                        else
                          if («inRange» x1 (leaf 48) (leaf 55)).label ≠ 0 then
                            «lexIn»
                              x2
                              x3
                              (Const.node
                                (leaf 10)
                                (x6 :: ((leaf 1) :: («single» (Const.sub x1 (leaf 48))))))
                          else
                            if (Const.eq x1 (leaf 13)).label ≠ 0 then
                              «lexIn» x2 x3 («withLen» (leaf 7) x6)
                            else
                              if (Const.eq x1 (leaf 10)).label ≠ 0 then
                                «lexIn» x2 x3 («withLen» (leaf 8) x6)
                              else
                                «lexFail»
                    else
                      if (Const.eq x5 (leaf 7)).label ≠ 0 then
                        if (Const.eq x1 (leaf 10)).label ≠ 0 then
                          «lexIn» x2 x3 («withLen» (leaf 5) x6)
                        else
                          «strStep» x2 x3 x6 x1
                      else
                        if (Const.eq x5 (leaf 8)).label ≠ 0 then
                          if (Const.eq x1 (leaf 13)).label ≠ 0 then
                            «lexIn» x2 x3 («withLen» (leaf 5) x6)
                          else
                            «strStep» x2 x3 x6 x1
                        else
                          if (Const.eq x5 (leaf 9)).label ≠ 0 then
                            let x7 : T := «hexVal» x1;
                            if («isSome» x7).label ≠ 0 then
                              if (Const.eq (Const.child x4 (leaf 1)) (leaf 1)).label ≠ 0 then
                                «lexIn»
                                  x2
                                  ((Const.add
                                    (Const.mul (leaf 16) (Const.child x4 (leaf 2)))
                                    («get» x7)) ::
                                    x3)
                                  («withLen» (leaf 5) x6)
                              else
                                «lexIn»
                                  x2
                                  x3
                                  (Const.node (leaf 9) (x6 :: ((leaf 1) :: («single» («get» x7)))))
                            else
                              «lexFail»
                          else
                            if (Const.eq x5 (leaf 10)).label ≠ 0 then
                              if («inRange» x1 (leaf 48) (leaf 55)).label ≠ 0 then
                                let x7 : T := Const.add
                                  (Const.mul (leaf 8) (Const.child x4 (leaf 2)))
                                  (Const.sub x1 (leaf 48));
                                if (Const.eq (Const.child x4 (leaf 1)) (leaf 2)).label ≠ 0 then
                                  if (Const.lt x7 (leaf 256)).label ≠ 0 then
                                    «lexIn» x2 (x7 :: x3) («withLen» (leaf 5) x6)
                                  else
                                    «lexFail»
                                else
                                  «lexIn»
                                    x2
                                    x3
                                    (Const.node
                                      (leaf 10)
                                      (x6 ::
                                        ((Const.add (Const.child x4 (leaf 1)) (leaf 1)) ::
                                          («single» x7))))
                              else
                                «lexFail»
                            else
                              if (Const.eq x5 (leaf 13)).label ≠ 0 then
                                if («isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if («isSome» («hexVal» x1)).label ≠ 0 then
                                    «lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (Const.eq x1 (leaf 35)).label ≠ 0 then
                                      let x7 : T := «decodeHex» («reverse» x3);
                                      if («isSome» x7).label ≠ 0 then
                                        «endAtom» x2 x6 (Const.children («get» x7))
                                      else
                                        «lexFail»
                                    else
                                      «lexFail»
                              else
                                if («isSpace» x1).label ≠ 0 then
                                  x0
                                else
                                  if (if («isSome» («base64Val» x1)).label ≠ 0 then
                                    leaf 1
                                  else
                                    Const.eq x1 (leaf 61)).label ≠ 0 then
                                    «lexIn» x2 (x1 :: x3) x4
                                  else
                                    if (Const.eq x1 (leaf 124)).label ≠ 0 then
                                      let x7 : T := «decodeBase64» («reverse» x3);
                                      if («isSome» x7).label ≠ 0 then
                                        «endAtom» x2 x6 (Const.children («get» x7))
                                      else
                                        «lexFail»
                                    else
                                      «lexFail»

def «lexEnd» :=
  fun (x0 : List T × (List T × T)) =>
    let x1 : List T := (x0).1;
    let x2 : List T := ((x0).2).1;
    let x3 : T := Const.label ((x0).2).2;
    if (if (Const.eq x3 (leaf 0)).label ≠ 0 then
      leaf 1
    else
      Const.eq x3 (leaf 4)).label ≠ 0 then
      «some» (Const.node (leaf 0) («reverse» x1))
    else
      if (if (Const.eq x3 (leaf 1)).label ≠ 0 then
        leaf 1
      else
        Const.eq x3 (leaf 2)).label ≠ 0 then
        «some» (Const.node (leaf 0) («reverse» ((«atomTok» x2) :: x1)))
      else
        if (Const.eq x3 (leaf 3)).label ≠ 0 then
          if («nonEmpty» x2).label ≠ 0 then
            «some» (Const.node (leaf 0) («reverse» («holeToks» x2 x1)))
          else
            «none»
        else
          «none»

def «tokenize» :=
  fun (x0 : List T) =>
    «lexEnd»
      (Const.foldr
        (α := T)
        (β := (List T × (List T × T)) → List T × (List T × T))
        (fun (x1 : T)
           (x2 : (List T × (List T × T)) → List T × (List T × T))
           (x3 : List T × (List T × T)) =>
          x2 («lexStep» x3 x1))
        (fun (x1 : List T × (List T × T)) => x1)
        x0
        («lexIdle» ([] : List T)))

def «fail» := (leaf 0, ([] : List (List T)))

def «parseStep» :=
  fun (x0 : T × List (List T)) (x1 : T) =>
    if ((x0).1).label ≠ 0 then
      Const.lcase
        (α := List T)
        (β := T × List (List T))
        (x0).2
        «fail»
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
                «fail»
                (fun (x4 : List T) (x5 : List (List T)) =>
                  (leaf 1, (((Const.node (leaf 2) («reverse» x2)) :: x4) :: x5))))
    else
      x0

def «readSExps» :=
  fun (x0 : List T) =>
    let x1 : T := «tokenize» x0;
    if («isSome» x1).label ≠ 0 then
      let x2 : T ×
        List
          (List
            T) := Const.foldr
        (α := T)
        (β := (T × List (List T)) → T × List (List T))
        (fun (x2 : T)
           (x3 : (T × List (List T)) → T × List (List T))
           (x4 : T × List (List T)) =>
          x3 («parseStep» x4 x2))
        (fun (x2 : T × List (List T)) => x2)
        (Const.children («get» x1))
        (leaf 1, (([] : List T) :: ([] : List (List T))));
      if ((x2).1).label ≠ 0 then
        Const.lcase
          (α := List T)
          (β := T)
          (x2).2
          «none»
          (fun (x3 : List T) (x4 : List (List T)) =>
            Const.lcase
              (α := List T)
              (β := T)
              x4
              («some» (Const.node (leaf 0) («reverse» x3)))
              (fun (_ : List T) (_ : List (List T)) => «none»))
      else
        «none»
    else
      «none»

def «isAtom» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 1)

def «isList» := fun (x0 : T) => Const.eq (Const.label x0) (leaf 2)

def «nameOf» :=
  fun (x0 : T) => Const.node (leaf 0) (Const.children x0)

def «named» :=
  fun (x0 : T) (x1 : T) =>
    if («isAtom» x0).label ≠ 0 then
      Const.equal («nameOf» x0) x1
    else
      leaf 0

def «kwT» := mk 0 [leaf 84]

def «kwUnit» := mk 0 [leaf 85, leaf 110, leaf 105, leaf 116]

def «kwProd» := mk 0 [leaf 80, leaf 114, leaf 111, leaf 100]

def «kwArrow» :=
  mk 0 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «kwList» := mk 0 [leaf 76, leaf 105, leaf 115, leaf 116]

def «kwLam» := mk 0 [leaf 108, leaf 97, leaf 109]

def «kwLet» := mk 0 [leaf 108, leaf 101, leaf 116]

def «kwPair» := mk 0 [leaf 112, leaf 97, leaf 105, leaf 114]

def «kwFst» := mk 0 [leaf 102, leaf 115, leaf 116]

def «kwSnd» := mk 0 [leaf 115, leaf 110, leaf 100]

def «kwIf» := mk 0 [leaf 105, leaf 102]

def «kwQuote» :=
  mk 0 [leaf 113, leaf 117, leaf 111, leaf 116, leaf 101]

def «kwCons» := mk 0 [leaf 99, leaf 111, leaf 110, leaf 115]

def «kwNil» := mk 0 [leaf 110, leaf 105, leaf 108]

def «kwFold» := mk 0 [leaf 102, leaf 111, leaf 108, leaf 100]

def «kwPara» := mk 0 [leaf 112, leaf 97, leaf 114, leaf 97]

def «kwIter» := mk 0 [leaf 105, leaf 116, leaf 101, leaf 114]

def «kwFoldr» :=
  mk 0 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «kwLcase» := mk 0 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «kwUnitValue» := mk 0 [leaf 117, leaf 110, leaf 105, leaf 116]

def «kwDef» := mk 0 [leaf 100, leaf 101, leaf 102]

def «kwDeftype» :=
  mk 0 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «kwDefnum» :=
  mk 0 [leaf 100, leaf 101, leaf 102, leaf 110, leaf 117, leaf 109]

def «primNames» :=
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

def «indexOf» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x0 x2).label ≠ 0 then
          «some» (leaf 0)
        else
          if («isSome» x3).label ≠ 0 then
            «some» (Const.add («get» x3) (leaf 1))
          else
            «none»)
      «none»
      x1

def «lookupAbbrev» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal x0 (Const.child x2 (leaf 0))).label ≠ 0 then
          «some» (Const.child x2 (leaf 1))
        else
          x3)
      «none»
      x1

def «numeral» :=
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
    if («nonEmpty» x0).label ≠ 0 then
      if ((x1).1).label ≠ 0 then «some» ((x1).2).1 else «none»
    else
      «none»

def «expandNums» :=
  fun (x0 : List T) (x1 : T) =>
    Const.fold
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := Const.node x2 x3;
        if («isAtom» x4).label ≠ 0 then
          let x5 : T := «lookupAbbrev» («nameOf» x4) x0;
          if («isSome» x5).label ≠ 0 then «get» x5 else x4
        else
          x4)
      x1

def «numOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «expandNums» x0 x1;
    if («isAtom» x2).label ≠ 0 then
      if («isSome» («numeral» (Const.children x2))).label ≠ 0 then
        «some» x2
      else
        «none»
    else
      «none»

def «rtTrees» :=
  fun (x0 : List (T × T)) =>
    Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «rtValues» :=
  fun (x0 : List (T × T)) =>
    Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0

def «node2» :=
  fun (x0 : T) (x1 : T) (x2 : T) => Const.node x0 (x1 :: («single» x2))

def «some2» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    if («both» x1 x2).label ≠ 0 then
      «some» («node2» x0 («get» x1) («get» x2))
    else
      «none»

def «readType» :=
  fun (x0 : List T) (x1 : T) =>
    (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : T := Const.node x2 («rtTrees» x3);
        let x5 : List T := «rtValues» x3;
        (x4,
          if («isAtom» x4).label ≠ 0 then
            let x6 : T := «nameOf» x4;
            if (Const.equal x6 «kwT»).label ≠ 0 then
              «some» (leaf 0)
            else
              if (Const.equal x6 «kwUnit»).label ≠ 0 then
                «some» (leaf 1)
              else
                «lookupAbbrev» x6 x0
          else
            if («isList» x4).label ≠ 0 then
              let x6 : T := «at» (Const.children x4) (leaf 0);
              let x7 : T := Const.arity x4;
              if («named» x6 «kwProd»).label ≠ 0 then
                if (Const.eq x7 (leaf 3)).label ≠ 0 then
                  «some2» (leaf 2) («at» x5 (leaf 1)) («at» x5 (leaf 2))
                else
                  «none»
              else
                if («named» x6 «kwArrow»).label ≠ 0 then
                  if (Const.eq x7 (leaf 3)).label ≠ 0 then
                    «some2» (leaf 3) («at» x5 (leaf 1)) («at» x5 (leaf 2))
                  else
                    «none»
                else
                  if («named» x6 «kwList»).label ≠ 0 then
                    if (Const.eq x7 (leaf 2)).label ≠ 0 then
                      if («isSome» («at» x5 (leaf 1))).label ≠ 0 then
                        «some» (Const.node (leaf 4) («single» («get» («at» x5 (leaf 1)))))
                      else
                        «none»
                    else
                      «none»
                  else
                    «none»
            else
              «none»))
      x1).2

def «readDatum» :=
  fun (x0 : T) =>
    if («isAtom» x0).label ≠ 0 then
      let x1 : T := «numeral» (Const.children x0);
      if («isSome» x1).label ≠ 0 then
        «some» (Const.node («get» x1) ([] : List T))
      else
        «none»
    else
      let x1 : T := (Const.fold
        (α := T × T)
        (fun (x1 : T) (x2 : List (T × T)) =>
          let x3 : T := Const.node x1 («rtTrees» x2);
          (x3,
            if («isAtom» x3).label ≠ 0 then
              let x4 : T := «numeral» (Const.children x3);
              if («isSome» x4).label ≠ 0 then
                «some»
                  (Const.node (leaf 0) («single» (Const.node («get» x4) ([] : List T))))
              else
                «some» (Const.node (leaf 0) (Const.children x3))
            else
              if («isList» x3).label ≠ 0 then
                Const.lcase
                  (α := T)
                  (β := T)
                  (Const.children x3)
                  «none»
                  (fun (x4 : T) (_ : List T) =>
                    let x6 : T := (if («isAtom» x4).label ≠ 0 then
                      «numeral» (Const.children x4)
                    else
                      «none»);
                    let x7 : T := «allSome» («tail» («rtValues» x2));
                    if («both» x6 x7).label ≠ 0 then
                      «some»
                        (Const.node
                          (leaf 0)
                          («single»
                            (Const.node
                              («get» x6)
                              (Const.foldr
                                (α := T)
                                (β := List T)
                                (fun (x8 : T) (x9 : List T) => «append» (Const.children x8) x9)
                                ([] : List T)
                                (Const.children («get» x7))))))
                    else
                      «none»)
              else
                «none»))
        x0).2;
      if («isSome» x1).label ≠ 0 then
        «some» (Const.child («get» x1) (leaf 0))
      else
        «none»

def «rrTrees» :=
  fun (x0 : List (T × (List T → T))) =>
    Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x1 : T × (List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0

def «rrApply» :=
  fun (x0 : List (T × (List T → T))) (x1 : List T) =>
    Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x2 : T × (List T → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0

def «rrTail» :=
  fun (x0 : List (T × (List T → T))) =>
    Const.lcase
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      x0
      ([] : List (T × (List T → T)))
      (fun (_ : T × (List T → T)) (x2 : List (T × (List T → T))) => x2)

def «rrAt» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    Const.lcase
      (α := T × (List T → T))
      (β := List T → T)
      (Const.iter (α := List (T × (List T → T))) «rrTail» x0 x1)
      (fun (_ : List T) => «none»)
      (fun (x3 : T × (List T → T)) (_ : List (T × (List T → T))) => (x3).2)
      x2

def «app» := fun (x0 : T) (x1 : T) => «node2» (leaf 10) x0 x1

def «apps» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «app» x3 x2)
      x0
      («reverse» x1)

def «some1» :=
  fun (x0 : T) (x1 : T) =>
    if («isSome» x1).label ≠ 0 then
      «some» (Const.node x0 («single» («get» x1)))
    else
      «none»

def «argsOf» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    «allSome»
      («rrApply»
        (Const.iter (α := List (T × (List T → T))) «rrTail» x0 x1)
        x2)

def «mkArgs» :=
  fun (x0 : T) (x1 : T) =>
    if («isSome» x1).label ≠ 0 then
      «some» (Const.node x0 (Const.children («get» x1)))
    else
      «none»

def «appsOpt» :=
  fun (x0 : T) (x1 : T) =>
    if («both» x0 x1).label ≠ 0 then
      «some» («apps» («get» x0) (Const.children («get» x1)))
    else
      «none»

def «binders» :=
  fun (x0 : T) =>
    if («isList» x0).label ≠ 0 then
      if (Const.eq (Const.arity x0) (leaf 2)).label ≠ 0 then
        if («isAtom» (Const.child x0 (leaf 0))).label ≠ 0 then
          «single» x0
        else
          Const.children x0
      else
        Const.children x0
    else
      ([] : List T)

def «readBinders» :=
  fun (x0 : List T) (x1 : List T) =>
    «allSome»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) =>
          ((if («isList» x2).label ≠ 0 then
            if (Const.eq (Const.arity x2) (leaf 2)).label ≠ 0 then
              if («isAtom» (Const.child x2 (leaf 0))).label ≠ 0 then
                let x4 : T := «readType» x0 (Const.child x2 (leaf 1));
                if («isSome» x4).label ≠ 0 then
                  «some»
                    («node2» (leaf 0) («nameOf» (Const.child x2 (leaf 0))) («get» x4))
                else
                  «none»
              else
                «none»
            else
              «none»
          else
            «none») ::
            x3))
        ([] : List T)
        x1)

def «resolveAtom» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := «numeral» (Const.children x1);
    if («isSome» x3).label ≠ 0 then
      «some» (Const.node (leaf 15) («single» («get» x3)))
    else
      let x4 : T := «nameOf» x1;
      let x5 : T := «indexOf» x4 x2;
      if («isSome» x5).label ≠ 0 then
        «some» (Const.node (leaf 8) («single» («get» x5)))
      else
        let x6 : T := «indexOf» x4 x0;
        if («isSome» x6).label ≠ 0 then
          «some» (Const.node (leaf 23) («single» («get» x6)))
        else
          let x7 : T := «indexOf» x4 «primNames»;
          if («isSome» x7).label ≠ 0 then
            «some» (Const.node (leaf 22) («single» («get» x7)))
          else
            if (Const.equal x4 «kwUnitValue»).label ≠ 0 then
              «some» (Const.node (leaf 11) ([] : List T))
            else
              «none»

def «resolveList» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : List T := Const.children x1;
    let x5 : T := Const.arity x1;
    let x6 : T := «at» x4 (leaf 0);
    if (Const.eq x5 (leaf 0)).label ≠ 0 then
      «none»
    else
      if (if («named» x6 «kwLam»).label ≠ 0 then
        Const.eq x5 (leaf 3)
      else
        leaf 0).label ≠ 0 then
        let x7 : T := «readBinders» x0 («binders» («at» x4 (leaf 1)));
        if («isSome» x7).label ≠ 0 then
          let x8 : List T := Const.children («get» x7);
          if («nonEmpty» x8).label ≠ 0 then
            let x9 : T := «rrAt»
              x2
              (leaf 2)
              («append»
                («reverse»
                  (Const.foldr
                    (α := T)
                    (β := List T)
                    (fun (x9 : T) (x10 : List T) => ((Const.child x9 (leaf 0)) :: x10))
                    ([] : List T)
                    x8))
                x3);
            if («isSome» x9).label ≠ 0 then
              «some»
                (Const.foldr
                  (α := T)
                  (β := T)
                  (fun (x10 : T) (x11 : T) =>
                    «node2» (leaf 9) (Const.child x10 (leaf 1)) x11)
                  («get» x9)
                  x8)
            else
              «none»
          else
            «none»
        else
          «none»
      else
        if (if («named» x6 «kwLet»).label ≠ 0 then
          Const.eq x5 (leaf 5)
        else
          leaf 0).label ≠ 0 then
          let x7 : T := «at» x4 (leaf 1);
          if («isAtom» x7).label ≠ 0 then
            let x8 : T := «readType» x0 («at» x4 (leaf 2));
            let x9 : T := «rrAt» x2 (leaf 4) ((«nameOf» x7) :: x3);
            let x10 : T := «rrAt» x2 (leaf 3) x3;
            if («both» x8 («both» x9 x10)).label ≠ 0 then
              «some» («app» («node2» (leaf 9) («get» x8) («get» x9)) («get» x10))
            else
              «none»
          else
            «none»
        else
          if («named» x6 «kwPair»).label ≠ 0 then
            «mkArgs» (leaf 12) («argsOf» x2 (leaf 1) x3)
          else
            if («named» x6 «kwFst»).label ≠ 0 then
              «mkArgs» (leaf 13) («argsOf» x2 (leaf 1) x3)
            else
              if («named» x6 «kwSnd»).label ≠ 0 then
                «mkArgs» (leaf 14) («argsOf» x2 (leaf 1) x3)
              else
                if («named» x6 «kwIf»).label ≠ 0 then
                  «mkArgs» (leaf 16) («argsOf» x2 (leaf 1) x3)
                else
                  if («named» x6 «kwCons»).label ≠ 0 then
                    «mkArgs» (leaf 20) («argsOf» x2 (leaf 1) x3)
                  else
                    if (if («named» x6 «kwQuote»).label ≠ 0 then
                      Const.eq x5 (leaf 2)
                    else
                      leaf 0).label ≠ 0 then
                      «some1» (leaf 15) («readDatum» («at» x4 (leaf 1)))
                    else
                      if (if («named» x6 «kwNil»).label ≠ 0 then
                        Const.eq x5 (leaf 2)
                      else
                        leaf 0).label ≠ 0 then
                        «some1» (leaf 19) («readType» x0 («at» x4 (leaf 1)))
                      else
                        if (if («named» x6 «kwFold»).label ≠ 0 then
                          Const.lt (leaf 1) x5
                        else
                          leaf 0).label ≠ 0 then
                          let x7 : T := «readType» x0 («at» x4 (leaf 1));
                          if («isSome» x7).label ≠ 0 then
                            «appsOpt»
                              («some» (Const.node (leaf 17) («single» («get» x7))))
                              («argsOf» x2 (leaf 2) x3)
                          else
                            «none»
                        else
                          if (if («named» x6 «kwPara»).label ≠ 0 then
                            Const.lt (leaf 1) x5
                          else
                            leaf 0).label ≠ 0 then
                            let x7 : T := «readType» x0 («at» x4 (leaf 1));
                            if («isSome» x7).label ≠ 0 then
                              «appsOpt»
                                («some» (Const.node (leaf 25) («single» («get» x7))))
                                («argsOf» x2 (leaf 2) x3)
                            else
                              «none»
                          else
                            if (if («named» x6 «kwIter»).label ≠ 0 then
                              Const.lt (leaf 1) x5
                            else
                              leaf 0).label ≠ 0 then
                              let x7 : T := «readType» x0 («at» x4 (leaf 1));
                              if («isSome» x7).label ≠ 0 then
                                «appsOpt»
                                  («some» (Const.node (leaf 18) («single» («get» x7))))
                                  («argsOf» x2 (leaf 2) x3)
                              else
                                «none»
                            else
                              if (if («named» x6 «kwFoldr»).label ≠ 0 then
                                Const.lt (leaf 2) x5
                              else
                                leaf 0).label ≠ 0 then
                                let x7 : T := «some2»
                                  (leaf 21)
                                  («readType» x0 («at» x4 (leaf 1)))
                                  («readType» x0 («at» x4 (leaf 2)));
                                if («isSome» x7).label ≠ 0 then
                                  «appsOpt» x7 («argsOf» x2 (leaf 3) x3)
                                else
                                  «none»
                              else
                                if (if («named» x6 «kwLcase»).label ≠ 0 then
                                  Const.lt (leaf 2) x5
                                else
                                  leaf 0).label ≠ 0 then
                                  let x7 : T := «some2»
                                    (leaf 24)
                                    («readType» x0 («at» x4 (leaf 1)))
                                    («readType» x0 («at» x4 (leaf 2)));
                                  if («isSome» x7).label ≠ 0 then
                                    «appsOpt» x7 («argsOf» x2 (leaf 3) x3)
                                  else
                                    «none»
                                else
                                  «appsOpt» («rrAt» x2 (leaf 0) x3) («argsOf» x2 (leaf 1) x3)

def «resolve» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : List T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x4 : T) (x5 : List (T × (List T → T))) =>
        let x6 : T := Const.node x4 («rrTrees» x5);
        (x6,
          fun (x7 : List T) =>
            if («isAtom» x6).label ≠ 0 then
              «resolveAtom» x1 x6 x7
            else
              if («isList» x6).label ≠ 0 then
                «resolveList» x0 x6 x5 x7
              else
                «none»))
      x2).2
      x3

def «reservedNames» :=
  «append»
    («kwLam» ::
      («kwLet» ::
        («kwPair» ::
          («kwFst» ::
            («kwSnd» ::
              («kwIf» ::
                («kwQuote» ::
                  («kwCons» ::
                    («kwNil» ::
                      («kwFold» ::
                        («kwPara» ::
                          («kwIter» ::
                            («kwFoldr» ::
                              («kwLcase» ::
                                («kwUnitValue» ::
                                  («kwDef» ::
                                    («kwDeftype» ::
                                      («kwDefnum» ::
                                        («kwHole» ::
                                          ((mk 0 [leaf 42, leaf 97, leaf 110, leaf 110]) ::
                                            ((mk 0 [leaf 42, leaf 100, leaf 111, leaf 99]) ::
                                              («kwT» ::
                                                («kwUnit» ::
                                                  («kwProd» ::
                                                    («kwArrow» ::
                                                      («single» «kwList»))))))))))))))))))))))))))
    «primNames»

def «isFresh» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    if («isSome» («indexOf» x3 «reservedNames»)).label ≠ 0 then
      leaf 0
    else
      if («isSome» («indexOf» x3 x2)).label ≠ 0 then
        leaf 0
      else
        if («isSome» («lookupAbbrev» x3 x0)).label ≠ 0 then
          leaf 0
        else
          if («isSome» («lookupAbbrev» x3 x1)).label ≠ 0 then leaf 0 else leaf 1

def «progStep» :=
  fun (x0 : T × (List T × (List T × (List T × List T)))) (x1 : T) =>
    let x2 : List T := ((x0).2).1;
    let x3 : List T := (((x0).2).2).1;
    let x4 : List T := ((((x0).2).2).2).1;
    let x5 : List T := ((((x0).2).2).2).2;
    if (if ((x0).1).label ≠ 0 then
      if («isList» x1).label ≠ 0 then
        if (Const.eq (Const.arity x1) (leaf 3)).label ≠ 0 then
          if («isAtom» (Const.child x1 (leaf 1))).label ≠ 0 then
            «isFresh» x2 x3 x4 («nameOf» (Const.child x1 (leaf 1)))
          else
            leaf 0
        else
          leaf 0
      else
        leaf 0
    else
      leaf 0).label ≠ 0 then
      let x6 : T := «nameOf» (Const.child x1 (leaf 1));
      if («named» (Const.child x1 (leaf 0)) «kwDef»).label ≠ 0 then
        let x7 : T := «resolve»
          x2
          x4
          («expandNums» x3 (Const.child x1 (leaf 2)))
          ([] : List T);
        if («isSome» x7).label ≠ 0 then
          (leaf 1,
            (x2,
              (x3, («append» x4 («single» x6), «append» x5 («single» («get» x7))))))
        else
          (leaf 0, (x0).2)
      else
        if («named» (Const.child x1 (leaf 0)) «kwDeftype»).label ≠ 0 then
          let x7 : T := «readType» x2 (Const.child x1 (leaf 2));
          if («isSome» x7).label ≠ 0 then
            (leaf 1, (((«node2» (leaf 0) x6 («get» x7)) :: x2), ((x0).2).2))
          else
            (leaf 0, (x0).2)
        else
          if («named» (Const.child x1 (leaf 0)) «kwDefnum»).label ≠ 0 then
            let x7 : T := «numOf» x3 (Const.child x1 (leaf 2));
            if («isSome» x7).label ≠ 0 then
              (leaf 1,
                (x2, (((«node2» (leaf 0) x6 («get» x7)) :: x3), (((x0).2).2).2)))
            else
              (leaf 0, (x0).2)
          else
            (leaf 0, (x0).2)
    else
      (leaf 0, (x0).2)

def «readProgram» :=
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
        x2 («progStep» x3 x1))
      (fun (x1 : T × (List T × (List T × (List T × List T)))) => x1)
      x0
      (leaf 1,
        (([] : List T), (([] : List T), (([] : List T), ([] : List T)))));
    if ((x1).1).label ≠ 0 then
      «some»
        («node2»
          (leaf 100)
          (Const.node (leaf 101) ((((x1).2).2).2).2)
          (Const.node (leaf 102) ((((x1).2).2).2).1))
    else
      «none»

def «tyArrow» := fun (x0 : T) (x1 : T) => «node2» (leaf 3) x0 x1

def «tyList» := fun (x0 : T) => Const.node (leaf 4) («single» x0)

def «isTy» :=
  fun (x0 : T) =>
    Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        let x3 : T := «length» x2;
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          if (Const.eq x1 (leaf 0)).label ≠ 0 then
            leaf 1
          else
            Const.eq x1 (leaf 1)
        else
          if (Const.eq x3 (leaf 1)).label ≠ 0 then
            «and» (Const.eq x1 (leaf 4)) («at» x2 (leaf 0))
          else
            if (Const.eq x3 (leaf 2)).label ≠ 0 then
              «and»
                (if (Const.eq x1 (leaf 2)).label ≠ 0 then
                  leaf 1
                else
                  Const.eq x1 (leaf 3))
                («and» («at» x2 (leaf 0)) («at» x2 (leaf 1)))
            else
              leaf 0)
      x0

def «isProd» :=
  fun (x0 : T) =>
    «and»
      (Const.eq (Const.label x0) (leaf 2))
      (Const.eq (Const.arity x0) (leaf 2))

def «isArrow» :=
  fun (x0 : T) =>
    «and»
      (Const.eq (Const.label x0) (leaf 3))
      (Const.eq (Const.arity x0) (leaf 2))

def «isListTy» :=
  fun (x0 : T) =>
    «and»
      (Const.eq (Const.label x0) (leaf 4))
      (Const.eq (Const.arity x0) (leaf 1))

def «foldTy» :=
  fun (x0 : T) =>
    «tyArrow»
      («tyArrow» (leaf 0) («tyArrow» («tyList» x0) x0))
      («tyArrow» (leaf 0) x0)

def «iterTy» :=
  fun (x0 : T) =>
    «tyArrow» («tyArrow» x0 x0) («tyArrow» x0 («tyArrow» (leaf 0) x0))

def «foldrTy» :=
  fun (x0 : T) (x1 : T) =>
    «tyArrow»
      («tyArrow» x0 («tyArrow» x1 x1))
      («tyArrow» x1 («tyArrow» («tyList» x0) x1))

def «lcaseTy» :=
  fun (x0 : T) (x1 : T) =>
    «tyArrow»
      («tyList» x0)
      («tyArrow»
        x1
        («tyArrow» («tyArrow» x0 («tyArrow» («tyList» x0) x1)) x1))

def «primTypes» :=
  let x0 : T := «tyArrow» (leaf 0) (leaf 0);
  let x1 : T := «tyArrow» (leaf 0) x0;
  «append»
    (x0 ::
      (x0 ::
        (x1 ::
          ((«tyArrow» (leaf 0) («tyArrow» («tyList» (leaf 0)) (leaf 0))) ::
            ((«tyArrow» (leaf 0) («tyList» (leaf 0))) :: ([] : List T))))))
    («append» («replicate» (leaf 8) x1) («single» x0))

def «checkNode» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : T := Const.label x1;
    let x5 : List T := Const.children x1;
    let x6 : T := Const.arity x1;
    if (Const.eq x4 (leaf 8)).label ≠ 0 then
      if (Const.eq x6 (leaf 1)).label ≠ 0 then
        «nth» x3 (Const.label («at» x5 (leaf 0)))
      else
        «none»
    else
      if (Const.eq x4 (leaf 9)).label ≠ 0 then
        if (Const.eq x6 (leaf 2)).label ≠ 0 then
          let x7 : T := «at» x5 (leaf 0);
          if («isTy» x7).label ≠ 0 then
            let x8 : T := «rrAt» x2 (leaf 1) (x7 :: x3);
            if («isSome» x8).label ≠ 0 then
              «some» («tyArrow» x7 («get» x8))
            else
              «none»
          else
            «none»
        else
          «none»
      else
        if (Const.eq x4 (leaf 10)).label ≠ 0 then
          if (Const.eq x6 (leaf 2)).label ≠ 0 then
            let x7 : T := «rrAt» x2 (leaf 0) x3;
            let x8 : T := «rrAt» x2 (leaf 1) x3;
            if («both» x7 x8).label ≠ 0 then
              if («isArrow» («get» x7)).label ≠ 0 then
                if (Const.equal
                  («get» x8)
                  (Const.child («get» x7) (leaf 0))).label ≠ 0 then
                  «some» (Const.child («get» x7) (leaf 1))
                else
                  «none»
              else
                «none»
            else
              «none»
          else
            «none»
        else
          if (Const.eq x4 (leaf 11)).label ≠ 0 then
            if (Const.eq x6 (leaf 0)).label ≠ 0 then «some» (leaf 1) else «none»
          else
            if (Const.eq x4 (leaf 12)).label ≠ 0 then
              if (Const.eq x6 (leaf 2)).label ≠ 0 then
                «some2» (leaf 2) («rrAt» x2 (leaf 0) x3) («rrAt» x2 (leaf 1) x3)
              else
                «none»
            else
              if (Const.eq x4 (leaf 13)).label ≠ 0 then
                if (Const.eq x6 (leaf 1)).label ≠ 0 then
                  let x7 : T := «rrAt» x2 (leaf 0) x3;
                  if («isSome» x7).label ≠ 0 then
                    if («isProd» («get» x7)).label ≠ 0 then
                      «some» (Const.child («get» x7) (leaf 0))
                    else
                      «none»
                  else
                    «none»
                else
                  «none»
              else
                if (Const.eq x4 (leaf 14)).label ≠ 0 then
                  if (Const.eq x6 (leaf 1)).label ≠ 0 then
                    let x7 : T := «rrAt» x2 (leaf 0) x3;
                    if («isSome» x7).label ≠ 0 then
                      if («isProd» («get» x7)).label ≠ 0 then
                        «some» (Const.child («get» x7) (leaf 1))
                      else
                        «none»
                    else
                      «none»
                  else
                    «none»
                else
                  if (Const.eq x4 (leaf 15)).label ≠ 0 then
                    if (Const.eq x6 (leaf 1)).label ≠ 0 then «some» (leaf 0) else «none»
                  else
                    if (Const.eq x4 (leaf 16)).label ≠ 0 then
                      if (Const.eq x6 (leaf 3)).label ≠ 0 then
                        let x7 : T := «rrAt» x2 (leaf 0) x3;
                        let x8 : T := «rrAt» x2 (leaf 1) x3;
                        let x9 : T := «rrAt» x2 (leaf 2) x3;
                        if («both» x7 («both» x8 x9)).label ≠ 0 then
                          if (Const.equal («get» x7) (leaf 0)).label ≠ 0 then
                            if (Const.equal («get» x9) («get» x8)).label ≠ 0 then x8 else «none»
                          else
                            «none»
                        else
                          «none»
                      else
                        «none»
                    else
                      if (Const.eq x4 (leaf 17)).label ≠ 0 then
                        if (Const.eq x6 (leaf 1)).label ≠ 0 then
                          if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                            «some» («foldTy» («at» x5 (leaf 0)))
                          else
                            «none»
                        else
                          «none»
                      else
                        if (Const.eq x4 (leaf 25)).label ≠ 0 then
                          if (Const.eq x6 (leaf 1)).label ≠ 0 then
                            if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                              «some» («foldTy» («at» x5 (leaf 0)))
                            else
                              «none»
                          else
                            «none»
                        else
                          if (Const.eq x4 (leaf 18)).label ≠ 0 then
                            if (Const.eq x6 (leaf 1)).label ≠ 0 then
                              if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                                «some» («iterTy» («at» x5 (leaf 0)))
                              else
                                «none»
                            else
                              «none»
                          else
                            if (Const.eq x4 (leaf 19)).label ≠ 0 then
                              if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                if («isTy» («at» x5 (leaf 0))).label ≠ 0 then
                                  «some» («tyList» («at» x5 (leaf 0)))
                                else
                                  «none»
                              else
                                «none»
                            else
                              if (Const.eq x4 (leaf 20)).label ≠ 0 then
                                if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                  let x7 : T := «rrAt» x2 (leaf 0) x3;
                                  let x8 : T := «rrAt» x2 (leaf 1) x3;
                                  if («both» x7 x8).label ≠ 0 then
                                    if («isListTy» («get» x8)).label ≠ 0 then
                                      if (Const.equal
                                        («get» x7)
                                        (Const.child («get» x8) (leaf 0))).label ≠ 0 then
                                        «some» («tyList» («get» x7))
                                      else
                                        «none»
                                    else
                                      «none»
                                  else
                                    «none»
                                else
                                  «none»
                              else
                                if (Const.eq x4 (leaf 21)).label ≠ 0 then
                                  if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                    if («and»
                                      («isTy» («at» x5 (leaf 0)))
                                      («isTy» («at» x5 (leaf 1)))).label ≠ 0 then
                                      «some» («foldrTy» («at» x5 (leaf 0)) («at» x5 (leaf 1)))
                                    else
                                      «none»
                                  else
                                    «none»
                                else
                                  if (Const.eq x4 (leaf 22)).label ≠ 0 then
                                    if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                      «nth» «primTypes» (Const.label («at» x5 (leaf 0)))
                                    else
                                      «none»
                                  else
                                    if (Const.eq x4 (leaf 23)).label ≠ 0 then
                                      if (Const.eq x6 (leaf 1)).label ≠ 0 then
                                        «nth» x0 (Const.label («at» x5 (leaf 0)))
                                      else
                                        «none»
                                    else
                                      if (Const.eq x4 (leaf 24)).label ≠ 0 then
                                        if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                          if («and»
                                            («isTy» («at» x5 (leaf 0)))
                                            («isTy» («at» x5 (leaf 1)))).label ≠ 0 then
                                            «some» («lcaseTy» («at» x5 (leaf 0)) («at» x5 (leaf 1)))
                                          else
                                            «none»
                                        else
                                          «none»
                                      else
                                        «none»

def «typeIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    (Const.fold
      (α := T × (List T → T))
      (fun (x3 : T) (x4 : List (T × (List T → T))) =>
        let x5 : T := Const.node x3 («rrTrees» x4);
        (x5, fun (x6 : List T) => «checkNode» x0 x5 x4 x6))
      x2).2
      x1

def «typeOf» :=
  fun (x0 : List T) (x1 : T) => «typeIn» x0 ([] : List T) x1

def «checkProgram» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := (T × List T) → T × List T)
      (fun (x1 : T) (x2 : (T × List T) → T × List T) (x3 : T × List T) =>
        x2
          (if ((x3).1).label ≠ 0 then
            let x4 : T := «typeOf» (x3).2 x1;
            if («isSome» x4).label ≠ 0 then
              (leaf 1, «append» (x3).2 («single» («get» x4)))
            else
              (leaf 0, (x3).2)
          else
            x3))
      (fun (x1 : T × List T) => x1)
      x0
      (leaf 1, ([] : List T));
    if ((x1).1).label ≠ 0 then
      «some» (Const.node (leaf 0) (x1).2)
    else
      «none»

def «eqn» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «eqTy» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x2);
    x1

def «eqLhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «eqRhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «bindO» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (if («isSome» x0).label ≠ 0 then
      x1 («get» x0)
    else
      «none»);
    x2

def «mapT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «allT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «mk1» :=
  fun (x0 : T) (x1 : T) => let x2 : T := Const.node x0 («single» x1); x2

def «mk3» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := Const.node x0 (x1 :: (x2 :: («single» x3))); x4

def «var» := fun (x0 : T) => let x1 : T := «mk1» (leaf 8) x0; x1

def «app2» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «app» («app» x0 x1) x2; x3

def «app3» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «app» («app» («app» x0 x1) x2) x3; x4

def «hasType» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «typeIn» x0 x1 x2;
                   if («isSome» x4).label ≠ 0 then
                     Const.equal («get» x4) x3
                   else
                     leaf 0);
    x4

def «trTrees» :=
  fun (x0 : List (T × (T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (T → T))
      (β := List T)
      (fun (x1 : T × (T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «trAll» :=
  fun (x0 : List (T × (T → T))) (x1 : T) =>
    let x2 : List
      T := Const.foldr
      (α := T × (T → T))
      (β := List T)
      (fun (x2 : T × (T → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0;
    x2

def «termNode» :=
  fun (x0 : T) =>
    let x1 : T := «or»
      (Const.eq x0 (leaf 10))
      («or»
        (Const.eq x0 (leaf 11))
        («or»
          (Const.eq x0 (leaf 12))
          («or»
            (Const.eq x0 (leaf 13))
            («or»
              (Const.eq x0 (leaf 14))
              («or» (Const.eq x0 (leaf 16)) (Const.eq x0 (leaf 20)))))));
    x1

def «trav» :=
  fun (x0 : T → T → T) (x1 : T) (x2 : T) =>
    let x3 : T := (Const.fold
      (α := T × (T → T))
      (fun (x3 : T) (x4 : List (T × (T → T))) =>
        let x5 : List T := «trTrees» x4;
        let x6 : T := «length» x5;
        (Const.node x3 x5,
          fun (x7 : T) =>
            if («and»
              (Const.eq x3 (leaf 8))
              (Const.eq x6 (leaf 1))).label ≠ 0 then
              x0 x7 (Const.label («at» x5 (leaf 0)))
            else
              if («and»
                (Const.eq x3 (leaf 9))
                (Const.eq x6 (leaf 2))).label ≠ 0 then
                «node2»
                  (leaf 9)
                  («at» x5 (leaf 0))
                  («at» («trAll» x4 (Const.add x7 (leaf 1))) (leaf 1))
              else
                if («termNode» x3).label ≠ 0 then
                  Const.node x3 («trAll» x4 x7)
                else
                  Const.node x3 x5))
      x1).2
      x2;
    x3

def «wkVar» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «var»
      (if (Const.lt x2 x1).label ≠ 0 then x2 else Const.add x2 x0);
    x3

def «wk» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «trav» («wkVar» x0) x1 (leaf 0); x2

def «wkAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «trav» («wkVar» x1) x2 x0; x3

def «substVar» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (if (Const.lt x2 x1).label ≠ 0 then
      «var» x2
    else
      if (Const.eq x2 x1).label ≠ 0 then
        «wk» x1 x0
      else
        «var» (Const.sub x2 (leaf 1)));
    x3

def «subst» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «trav» («substVar» x0) x1 (leaf 0); x2

def «eqWk» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «eqn»
      («eqTy» x1)
      («wk» x0 («eqLhs» x1))
      («wk» x0 («eqRhs» x1));
    x2

def «eqLower» :=
  fun (x0 : T) =>
    let x1 : T := «eqn»
      («eqTy» x0)
      («subst» («mk1» (leaf 15) (leaf 0)) («eqLhs» x0))
      («subst» («mk1» (leaf 15) (leaf 0)) («eqRhs» x0));
    x1

def «typedIn» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «and»
      («hasType» x0 x1 («eqLhs» x2) («eqTy» x2))
      («hasType» x0 x1 («eqRhs» x2) («eqTy» x2));
    x3

def «weakens» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «and»
      (Const.equal
        (Const.node (leaf 0) («mapT» («eqWk» (leaf 1)) x2))
        (Const.node (leaf 0) x3))
      («allT» («typedIn» x0 x1) x2);
    x4

def «mapBy» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «app3»
      («node2» (leaf 21) x0 («tyList» x1))
      («node2»
        (leaf 9)
        x0
        («node2»
          (leaf 9)
          («tyList» x1)
          («node2» (leaf 20) x2 («var» (leaf 0)))))
      («mk1» (leaf 19) x1)
      x3;
    x4

def «isQuote» :=
  fun (x0 : T) =>
    let x1 : T := «and»
      (Const.eq (Const.label x0) (leaf 15))
      (Const.eq (Const.arity x0) (leaf 1));
    x1

def «listElems» :=
  fun (x0 : T) =>
    let x1 : T := (Const.fold
      (α := T × T)
      (fun (x1 : T) (x2 : List (T × T)) =>
        let x3 : List T := «rtTrees» x2;
        let x4 : T := «length» x3;
        (Const.node x1 x3,
          if («and»
            (Const.eq x1 (leaf 19))
            (Const.eq x4 (leaf 1))).label ≠ 0 then
            «some» (Const.node (leaf 0) ([] : List T))
          else
            if («and»
              (Const.eq x1 (leaf 20))
              (Const.eq x4 (leaf 2))).label ≠ 0 then
              let x5 : T := «at» («rtValues» x2) (leaf 1);
              if («and» («isQuote» («at» x3 (leaf 0))) («isSome» x5)).label ≠ 0 then
                «some»
                  (Const.node
                    (leaf 0)
                    ((Const.child («at» x3 (leaf 0)) (leaf 0)) ::
                      (Const.children («get» x5))))
              else
                «none»
            else
              «none»))
      x0).2;
    x1

def «isLit» :=
  fun (x0 : T) =>
    let x1 : T := «or» («isQuote» x0) («isSome» («listElems» x0)); x1

def «litValue» :=
  fun (x0 : T) =>
    let x1 : T := (if («isQuote» x0).label ≠ 0 then
      Const.child x0 (leaf 0)
    else
      «get» («listElems» x0));
    x1

def «listLit» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) => «node2» (leaf 20) («mk1» (leaf 15) x1) x2)
      («mk1» (leaf 19) (leaf 0))
      x0;
    x1

def «delta» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      Const.label x1
    else
      if (Const.eq x0 (leaf 1)).label ≠ 0 then
        Const.arity x1
      else
        if (Const.eq x0 (leaf 2)).label ≠ 0 then
          Const.child x1 x2
        else
          if (Const.eq x0 (leaf 3)).label ≠ 0 then
            Const.node x1 (Const.children x2)
          else
            if (Const.eq x0 (leaf 4)).label ≠ 0 then
              Const.node (leaf 0) (Const.children x1)
            else
              if (Const.eq x0 (leaf 5)).label ≠ 0 then
                Const.add x1 x2
              else
                if (Const.eq x0 (leaf 6)).label ≠ 0 then
                  Const.sub x1 x2
                else
                  if (Const.eq x0 (leaf 7)).label ≠ 0 then
                    Const.mul x1 x2
                  else
                    if (Const.eq x0 (leaf 8)).label ≠ 0 then
                      Const.div x1 x2
                    else
                      if (Const.eq x0 (leaf 9)).label ≠ 0 then
                        Const.mod x1 x2
                      else
                        if (Const.eq x0 (leaf 10)).label ≠ 0 then
                          Const.eq x1 x2
                        else
                          if (Const.eq x0 (leaf 11)).label ≠ 0 then
                            Const.lt x1 x2
                          else
                            if (Const.eq x0 (leaf 12)).label ≠ 0 then
                              Const.equal x1 x2
                            else
                              Const.log2 x1);
    x3

def «thm» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «node2» (leaf 0) (Const.node (leaf 0) x0) x1; x2

def «eqSubst» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «eqn»
      («eqTy» x1)
      («subst» x0 («eqLhs» x1))
      («subst» x0 («eqRhs» x1));
    x2

def «eqWkAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «eqn»
      («eqTy» x2)
      («wkAt» x0 x1 («eqLhs» x2))
      («wkAt» x0 x1 («eqRhs» x2));
    x3

def «instAll» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.foldr
      (α := T)
      (β := T × (T → T))
      (fun (x2 : T) (x3 : T × (T → T)) =>
        (Const.add (x3).1 (leaf 1),
          fun (x4 : T) => (x3).2 («eqSubst» («wk» (x3).1 x2) x4)))
      (leaf 0, fun (x2 : T) => x2)
      x0).2
      x1;
    x2

def «typesMatch» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «and»
      (Const.eq («length» x2) («length» x3))
      (Const.foldr
        (α := T)
        (β := List T → T)
        (fun (x4 : T) (x5 : List T → T) (x6 : List T) =>
          Const.lcase
            (α := T)
            (β := T)
            x6
            (leaf 0)
            (fun (x7 : T) (x8 : List T) => «and» («hasType» x0 x1 x4 x7) (x5 x8)))
        (fun (_ : List T) => leaf 1)
        x2
        x3);
    x4

def «cite» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : List T := Const.children (Const.child x3 (leaf 0));
                   if («typesMatch» x0 x1 x2 x4).label ≠ 0 then
                     «some»
                       («instAll»
                         x2
                         («eqWkAt» («length» x4) («length» x1) (Const.child x3 (leaf 1))))
                   else
                     «none»);
    x4

def «tyT2» := «node2» (leaf 2) (leaf 0) (leaf 0)

def «tyLT» := «tyList» (leaf 0)

def «num» := fun (x0 : T) => let x1 : T := «mk1» (leaf 15) x0; x1

def «prim» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «apps» («mk1» (leaf 22) x0) x1; x2

def «prim1» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «prim» x0 («single» x1); x2

def «prim2» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «prim» x0 (x1 :: («single» x2)); x3

def «succT» :=
  fun (x0 : T) => let x1 : T := «prim2» (leaf 5) x0 («num» (leaf 1)); x1

def «v0» := «var» (leaf 0)

def «v1» := «var» (leaf 1)

def «v2» := «var» (leaf 2)

def «ctxT» := «single» (leaf 0)

def «ctxTT» := ((leaf 0) :: («single» (leaf 0)))

def «ctxTL» := ((leaf 0) :: («single» «tyLT»))

def «axLabelNode» :=
  «thm»
    «ctxTL»
    («eqn»
      (leaf 0)
      («prim1» (leaf 0) («prim2» (leaf 3) «v0» «v1»))
      («prim1» (leaf 0) «v0»))

def «axChildrenNode» :=
  «thm»
    «ctxTL»
    («eqn» «tyLT» («prim1» (leaf 4) («prim2» (leaf 3) «v0» «v1»)) «v1»)

def «axNodeEta» :=
  «thm»
    «ctxT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 3) («prim1» (leaf 0) «v0») («prim1» (leaf 4) «v0»))
      «v0»)

def «axChildrenLabel» :=
  «thm»
    «ctxT»
    («eqn»
      «tyLT»
      («prim1» (leaf 4) («prim1» (leaf 0) «v0»))
      («mk1» (leaf 19) (leaf 0)))

def «axLabelSucc» :=
  «thm»
    «ctxT»
    («eqn» (leaf 0) («prim1» (leaf 0) («succT» «v0»)) («succT» «v0»))

def «axAddIter» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 5) «v0» «v1»)
      («app3»
        («mk1» (leaf 18) (leaf 0))
        («node2» (leaf 9) (leaf 0) («succT» «v0»))
        («prim1» (leaf 0) «v0»)
        «v1»))

def «axPredIter» :=
  «thm»
    «ctxT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 6) «v0» («num» (leaf 1)))
      («mk1»
        (leaf 13)
        («app3»
          («mk1» (leaf 18) «tyT2»)
          («node2»
            (leaf 9)
            «tyT2»
            («node2»
              (leaf 12)
              («mk1» (leaf 14) «v0»)
              («succT» («mk1» (leaf 14) «v0»))))
          («node2» (leaf 12) («num» (leaf 0)) («num» (leaf 0)))
          «v0»)))

def «axSubIter» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 6) «v0» «v1»)
      («app3»
        («mk1» (leaf 18) (leaf 0))
        («node2» (leaf 9) (leaf 0) («prim2» (leaf 6) «v0» («num» (leaf 1))))
        («prim1» (leaf 0) «v0»)
        «v1»))

def «axMulIter» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 7) «v0» «v1»)
      («app3»
        («mk1» (leaf 18) (leaf 0))
        («node2» (leaf 9) (leaf 0) («prim2» (leaf 5) «v0» «v1»))
        («num» (leaf 0))
        «v1»))

def «divMod» :=
  «app3»
    («mk1» (leaf 18) «tyT2»)
    («node2»
      (leaf 9)
      «tyT2»
      («mk3»
        (leaf 16)
        («prim2» (leaf 10) («succT» («mk1» (leaf 14) «v0»)) «v2»)
        («node2» (leaf 12) («succT» («mk1» (leaf 13) «v0»)) («num» (leaf 0)))
        («node2»
          (leaf 12)
          («mk1» (leaf 13) «v0»)
          («succT» («mk1» (leaf 14) «v0»)))))
    («node2» (leaf 12) («num» (leaf 0)) («num» (leaf 0)))
    «v0»

def «axDivIter» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 8) «v0» «v1»)
      («mk1» (leaf 13) «divMod»))

def «axModIter» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 9) «v0» «v1»)
      («mk1» (leaf 14) «divMod»))

def «axEqDef» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 10) «v0» «v1»)
      («app3»
        («mk1» (leaf 18) (leaf 0))
        («node2» (leaf 9) (leaf 0) («num» (leaf 0)))
        («num» (leaf 1))
        («prim2»
          (leaf 5)
          («prim2» (leaf 6) «v0» «v1»)
          («prim2» (leaf 6) «v1» «v0»))))

def «axLtDef» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 11) «v0» «v1»)
      («app3»
        («mk1» (leaf 18) (leaf 0))
        («node2» (leaf 9) (leaf 0) («num» (leaf 1)))
        («num» (leaf 0))
        («prim2» (leaf 6) «v1» «v0»)))

def «axLog2Def» :=
  «thm»
    «ctxT»
    («eqn»
      (leaf 0)
      («prim1» (leaf 13) «v0»)
      («mk3»
        (leaf 16)
        («prim2» (leaf 11) «v0» («num» (leaf 2)))
        («num» (leaf 0))
        («succT»
          («prim1» (leaf 13) («prim2» (leaf 8) «v0» («num» (leaf 2)))))))

def «axArityDef» :=
  «thm»
    «ctxT»
    («eqn»
      (leaf 0)
      («prim1» (leaf 1) «v0»)
      («app3»
        («node2» (leaf 21) (leaf 0) (leaf 0))
        («node2» (leaf 9) (leaf 0) («node2» (leaf 9) (leaf 0) («succT» «v0»)))
        («num» (leaf 0))
        («prim1» (leaf 4) «v0»)))

def «tailT» :=
  «node2»
    (leaf 9)
    «tyLT»
    («app3»
      («node2» (leaf 24) (leaf 0) «tyLT»)
      «v0»
      («mk1» (leaf 19) (leaf 0))
      («node2» (leaf 9) (leaf 0) («node2» (leaf 9) «tyLT» «v0»)))

def «axChildDef» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («prim2» (leaf 2) «v0» «v1»)
      («app3»
        («node2» (leaf 24) (leaf 0) (leaf 0))
        («app3» («mk1» (leaf 18) «tyLT») «tailT» («prim1» (leaf 4) «v0») «v1»)
        («num» (leaf 0))
        («node2» (leaf 9) (leaf 0) («node2» (leaf 9) «tyLT» «v1»))))

def «axEqualRefl» :=
  «thm»
    «ctxT»
    («eqn» (leaf 0) («prim2» (leaf 12) «v0» «v0») («num» (leaf 1)))

def «axEqualSubst» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («mk3» (leaf 16) («prim2» (leaf 12) «v0» «v1») «v1» «v0»)
      «v0»)

def «axEqualBool» :=
  «thm»
    «ctxTT»
    («eqn»
      (leaf 0)
      («mk3»
        (leaf 16)
        («prim2» (leaf 12) «v0» «v1»)
        («num» (leaf 1))
        («num» (leaf 0)))
      («prim2» (leaf 12) «v0» «v1»))

def «axioms» :=
  («axLabelNode» ::
    («axChildrenNode» ::
      («axNodeEta» ::
        («axChildrenLabel» ::
          («axLabelSucc» ::
            («axAddIter» ::
              («axPredIter» ::
                («axSubIter» ::
                  («axMulIter» ::
                    («axDivIter» ::
                      («axModIter» ::
                        («axEqDef» ::
                          («axLtDef» ::
                            («axLog2Def» ::
                              («axArityDef» ::
                                («axChildDef» ::
                                  («axEqualRefl» ::
                                    («axEqualSubst» :: («single» «axEqualBool»)))))))))))))))))))

def «crTrees» :=
  fun (x0 : List (T × (List T → List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (List T → List T → T))
      (β := List T)
      (fun (x1 : T × (List T → List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «crTail» :=
  fun (x0 : List (T × (List T → List T → T))) =>
    let x1 : List
      (T ×
        (List T →
          List T →
            T)) := Const.lcase
      (α := T × (List T → List T → T))
      (β := List (T × (List T → List T → T)))
      x0
      ([] : List (T × (List T → List T → T)))
      (fun (_ : T × (List T → List T → T))
         (x2 : List (T × (List T → List T → T))) =>
        x2);
    x1

def «prem» :=
  fun (x0 : List (T × (List T → List T → T))) (x1 : T) =>
    let x2 : List T →
      List T →
        T := Const.lcase
      (α := T × (List T → List T → T))
      (β := List T → List T → T)
      (Const.iter (α := List (T × (List T → List T → T))) «crTail» x0 x1)
      (fun (_ : List T) (_ : List T) => «none»)
      (fun (x2 : T × (List T → List T → T))
         (_ : List (T × (List T → List T → T))) =>
        (x2).2);
    x2

def «shape» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «and» (Const.eq x0 x2) (Const.eq x1 x3); x4

def «checkCore» :=
  fun (_ : List T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List (T × (List T → List T → T)))
    (x5 : List T)
    (x6 : List T) =>
    let x7 : T := (let x7 : T := «length» x3;
                   let x8 : T := «at» x3 (leaf 0);
                   let x9 : T := «at» x3 (leaf 1);
                   let x10 : T := «at» x3 (leaf 2);
                   let x11 : T := «at» x3 (leaf 3);
                   if («shape» x2 x7 (leaf 0) (leaf 1)).label ≠ 0 then
                     «bindO»
                       («nth» x6 (Const.label x8))
                       (fun (x12 : T) =>
                         if («typedIn» x1 x5 x12).label ≠ 0 then «some» x12 else «none»)
                   else
                     if («shape» x2 x7 (leaf 1) (leaf 1)).label ≠ 0 then
                       «bindO»
                         («typeIn» x1 x5 x8)
                         (fun (x12 : T) => «some» («eqn» x12 x8 x8))
                     else
                       if («shape» x2 x7 (leaf 2) (leaf 1)).label ≠ 0 then
                         «bindO»
                           («prem» x4 (leaf 0) x5 x6)
                           (fun (x12 : T) =>
                             «some» («eqn» («eqTy» x12) («eqRhs» x12) («eqLhs» x12)))
                       else
                         if («shape» x2 x7 (leaf 3) (leaf 2)).label ≠ 0 then
                           «bindO»
                             («prem» x4 (leaf 0) x5 x6)
                             (fun (x12 : T) =>
                               «bindO»
                                 («prem» x4 (leaf 1) x5 x6)
                                 (fun (x13 : T) =>
                                   if («and»
                                     (Const.equal («eqTy» x12) («eqTy» x13))
                                     (Const.equal («eqRhs» x12) («eqLhs» x13))).label ≠ 0 then
                                     «some» («eqn» («eqTy» x12) («eqLhs» x12) («eqRhs» x13))
                                   else
                                     «none»))
                         else
                           if («shape» x2 x7 (leaf 4) (leaf 2)).label ≠ 0 then
                             «bindO»
                               («prem» x4 (leaf 0) x5 x6)
                               (fun (x12 : T) =>
                                 «bindO»
                                   («prem» x4 (leaf 1) x5 x6)
                                   (fun (x13 : T) =>
                                     let x14 : T := «eqTy» x12;
                                     if («isArrow» x14).label ≠ 0 then
                                       if (Const.equal
                                         («eqTy» x13)
                                         (Const.child x14 (leaf 0))).label ≠ 0 then
                                         «some»
                                           («eqn»
                                             (Const.child x14 (leaf 1))
                                             («app» («eqLhs» x12) («eqLhs» x13))
                                             («app» («eqRhs» x12) («eqRhs» x13)))
                                       else
                                         «none»
                                     else
                                       «none»))
                           else
                             if («shape» x2 x7 (leaf 5) (leaf 2)).label ≠ 0 then
                               if («isTy» x8).label ≠ 0 then
                                 «bindO»
                                   («prem» x4 (leaf 1) (x8 :: x5) («mapT» («eqWk» (leaf 1)) x6))
                                   (fun (x12 : T) =>
                                     «some»
                                       («eqn»
                                         («tyArrow» x8 («eqTy» x12))
                                         («node2» (leaf 9) x8 («eqLhs» x12))
                                         («node2» (leaf 9) x8 («eqRhs» x12))))
                               else
                                 «none»
                             else
                               if («shape» x2 x7 (leaf 6) (leaf 2)).label ≠ 0 then
                                 «bindO»
                                   («prem» x4 (leaf 0) x5 x6)
                                   (fun (x12 : T) =>
                                     «bindO»
                                       («prem» x4 (leaf 1) x5 x6)
                                       (fun (x13 : T) =>
                                         «some»
                                           («eqn»
                                             («node2» (leaf 2) («eqTy» x12) («eqTy» x13))
                                             («node2» (leaf 12) («eqLhs» x12) («eqLhs» x13))
                                             («node2» (leaf 12) («eqRhs» x12) («eqRhs» x13)))))
                               else
                                 if («shape» x2 x7 (leaf 7) (leaf 1)).label ≠ 0 then
                                   «bindO»
                                     («prem» x4 (leaf 0) x5 x6)
                                     (fun (x12 : T) =>
                                       if («isProd» («eqTy» x12)).label ≠ 0 then
                                         «some»
                                           («eqn»
                                             (Const.child («eqTy» x12) (leaf 0))
                                             («mk1» (leaf 13) («eqLhs» x12))
                                             («mk1» (leaf 13) («eqRhs» x12)))
                                       else
                                         «none»)
                                 else
                                   if («shape» x2 x7 (leaf 8) (leaf 1)).label ≠ 0 then
                                     «bindO»
                                       («prem» x4 (leaf 0) x5 x6)
                                       (fun (x12 : T) =>
                                         if («isProd» («eqTy» x12)).label ≠ 0 then
                                           «some»
                                             («eqn»
                                               (Const.child («eqTy» x12) (leaf 1))
                                               («mk1» (leaf 14) («eqLhs» x12))
                                               («mk1» (leaf 14) («eqRhs» x12)))
                                         else
                                           «none»)
                                   else
                                     if («shape» x2 x7 (leaf 9) (leaf 2)).label ≠ 0 then
                                       «bindO»
                                         («prem» x4 (leaf 0) x5 x6)
                                         (fun (x12 : T) =>
                                           «bindO»
                                             («prem» x4 (leaf 1) x5 x6)
                                             (fun (x13 : T) =>
                                               if (Const.equal
                                                 («eqTy» x13)
                                                 («tyList» («eqTy» x12))).label ≠ 0 then
                                                 «some»
                                                   («eqn»
                                                     («eqTy» x13)
                                                     («node2» (leaf 20) («eqLhs» x12) («eqLhs» x13))
                                                     («node2»
                                                       (leaf 20)
                                                       («eqRhs» x12)
                                                       («eqRhs» x13)))
                                               else
                                                 «none»))
                                     else
                                       if («shape» x2 x7 (leaf 10) (leaf 3)).label ≠ 0 then
                                         «bindO»
                                           («prem» x4 (leaf 0) x5 x6)
                                           (fun (x12 : T) =>
                                             «bindO»
                                               («prem» x4 (leaf 1) x5 x6)
                                               (fun (x13 : T) =>
                                                 «bindO»
                                                   («prem» x4 (leaf 2) x5 x6)
                                                   (fun (x14 : T) =>
                                                     if («and»
                                                       (Const.equal («eqTy» x12) (leaf 0))
                                                       (Const.equal
                                                         («eqTy» x14)
                                                         («eqTy» x13))).label ≠ 0 then
                                                       «some»
                                                         («eqn»
                                                           («eqTy» x13)
                                                           («mk3»
                                                             (leaf 16)
                                                             («eqLhs» x12)
                                                             («eqLhs» x13)
                                                             («eqLhs» x14))
                                                           («mk3»
                                                             (leaf 16)
                                                             («eqRhs» x12)
                                                             («eqRhs» x13)
                                                             («eqRhs» x14)))
                                                     else
                                                       «none»)))
                                       else
                                         if («shape» x2 x7 (leaf 11) (leaf 3)).label ≠ 0 then
                                           if («and»
                                             («isTy» x8)
                                             («hasType» x1 x5 x10 x8)).label ≠ 0 then
                                             «bindO»
                                               («typeIn» x1 (x8 :: x5) x9)
                                               (fun (x12 : T) =>
                                                 «some»
                                                   («eqn»
                                                     x12
                                                     («app» («node2» (leaf 9) x8 x9) x10)
                                                     («subst» x10 x9)))
                                           else
                                             «none»
                                         else
                                           if («shape» x2 x7 (leaf 12) (leaf 1)).label ≠ 0 then
                                             «bindO»
                                               («typeIn» x1 x5 x8)
                                               (fun (x12 : T) =>
                                                 if («isArrow» x12).label ≠ 0 then
                                                   if («isTy»
                                                     (Const.child x12 (leaf 0))).label ≠ 0 then
                                                     «some»
                                                       («eqn»
                                                         x12
                                                         x8
                                                         («node2»
                                                           (leaf 9)
                                                           (Const.child x12 (leaf 0))
                                                           («app»
                                                             («wk» (leaf 1) x8)
                                                             («var» (leaf 0)))))
                                                   else
                                                     «none»
                                                 else
                                                   «none»)
                                           else
                                             if («shape» x2 x7 (leaf 13) (leaf 2)).label ≠ 0 then
                                               «bindO»
                                                 («typeIn» x1 x5 x8)
                                                 (fun (x12 : T) =>
                                                   «bindO»
                                                     («typeIn» x1 x5 x9)
                                                     (fun (_ : T) =>
                                                       «some»
                                                         («eqn»
                                                           x12
                                                           («mk1»
                                                             (leaf 13)
                                                             («node2» (leaf 12) x8 x9))
                                                           x8)))
                                             else
                                               if («shape» x2 x7 (leaf 14) (leaf 2)).label ≠ 0 then
                                                 «bindO»
                                                   («typeIn» x1 x5 x8)
                                                   (fun (_ : T) =>
                                                     «bindO»
                                                       («typeIn» x1 x5 x9)
                                                       (fun (x13 : T) =>
                                                         «some»
                                                           («eqn»
                                                             x13
                                                             («mk1»
                                                               (leaf 14)
                                                               («node2» (leaf 12) x8 x9))
                                                             x9)))
                                               else
                                                 if («shape»
                                                   x2
                                                   x7
                                                   (leaf 15)
                                                   (leaf 1)).label ≠ 0 then
                                                   «bindO»
                                                     («typeIn» x1 x5 x8)
                                                     (fun (x12 : T) =>
                                                       if («isProd» x12).label ≠ 0 then
                                                         «some»
                                                           («eqn»
                                                             x12
                                                             («node2»
                                                               (leaf 12)
                                                               («mk1» (leaf 13) x8)
                                                               («mk1» (leaf 14) x8))
                                                             x8)
                                                       else
                                                         «none»)
                                                 else
                                                   if («shape»
                                                     x2
                                                     x7
                                                     (leaf 16)
                                                     (leaf 1)).label ≠ 0 then
                                                     if («hasType» x1 x5 x8 (leaf 1)).label ≠ 0 then
                                                       «some» («eqn» (leaf 1) x8 (leaf 11))
                                                     else
                                                       «none»
                                                   else
                                                     if («and»
                                                       (Const.eq x2 (leaf 17))
                                                       (Const.lt (leaf 0) x7)).label ≠ 0 then
                                                       let x12 : List T := «tail» x3;
                                                       if («nonEmpty» x5).label ≠ 0 then
                                                         «none»
                                                       else
                                                         if («allT» «isLit» x12).label ≠ 0 then
                                                           let x13 : T := «apps»
                                                             («mk1» (leaf 22) x8)
                                                             x12;
                                                           «bindO»
                                                             («typeIn» x1 ([] : List T) x13)
                                                             (fun (x14 : T) =>
                                                               let x15 : T := «delta»
                                                                 (Const.label x8)
                                                                 («litValue» («at» x12 (leaf 0)))
                                                                 («litValue» («at» x12 (leaf 1)));
                                                               if (Const.equal
                                                                 x14
                                                                 (leaf 0)).label ≠ 0 then
                                                                 «some»
                                                                   («eqn»
                                                                     x14
                                                                     x13
                                                                     («mk1» (leaf 15) x15))
                                                               else
                                                                 if (Const.equal
                                                                   x14
                                                                   («tyList»
                                                                     (leaf 0))).label ≠ 0 then
                                                                   «some»
                                                                     («eqn»
                                                                       x14
                                                                       x13
                                                                       («listLit»
                                                                         (Const.children x15)))
                                                                 else
                                                                   «none»)
                                                         else
                                                           «none»
                                                     else
                                                       if («shape»
                                                         x2
                                                         x7
                                                         (leaf 18)
                                                         (leaf 1)).label ≠ 0 then
                                                         Const.lcase
                                                           (α := T)
                                                           (β := T)
                                                           x5
                                                           «none»
                                                           (fun (_ : T) (x13 : List T) =>
                                                             «bindO»
                                                               («prem»
                                                                 x4
                                                                 (leaf 0)
                                                                 x13
                                                                 ([] : List T))
                                                               (fun (x14 : T) =>
                                                                 «some» («eqWk» (leaf 1) x14)))
                                                       else
                                                         if («shape»
                                                           x2
                                                           x7
                                                           (leaf 19)
                                                           (leaf 2)).label ≠ 0 then
                                                           «bindO»
                                                             («prem» x4 (leaf 0) x5 x6)
                                                             (fun (x12 : T) =>
                                                               «prem» x4 (leaf 1) x5 (x12 :: x6))
                                                         else
                                                           if («shape»
                                                             x2
                                                             x7
                                                             (leaf 20)
                                                             (leaf 2)).label ≠ 0 then
                                                             «bindO»
                                                               («typeIn» x1 x5 x8)
                                                               (fun (x12 : T) =>
                                                                 «bindO»
                                                                   («prem»
                                                                     x4
                                                                     (leaf 1)
                                                                     (x12 :: x5)
                                                                     («mapT» («eqWk» (leaf 1)) x6))
                                                                   (fun (x13 : T) =>
                                                                     «some»
                                                                       («eqn»
                                                                         («eqTy» x13)
                                                                         («subst» x8 («eqLhs» x13))
                                                                         («subst»
                                                                           x8
                                                                           («eqRhs» x13)))))
                                                           else
                                                             if («shape»
                                                               x2
                                                               x7
                                                               (leaf 21)
                                                               (leaf 4)).label ≠ 0 then
                                                               if («and»
                                                                 («isTy» x8)
                                                                 («and»
                                                                   («isTy» x9)
                                                                   («and»
                                                                     («hasType»
                                                                       x1
                                                                       x5
                                                                       x10
                                                                       («tyArrow»
                                                                         x8
                                                                         («tyArrow» x9 x9)))
                                                                     («hasType»
                                                                       x1
                                                                       x5
                                                                       x11
                                                                       x9)))).label ≠ 0 then
                                                                 «some»
                                                                   («eqn»
                                                                     x9
                                                                     («app3»
                                                                       («node2» (leaf 21) x8 x9)
                                                                       x10
                                                                       x11
                                                                       («mk1» (leaf 19) x8))
                                                                     x11)
                                                               else
                                                                 «none»
                                                             else
                                                               if («shape»
                                                                 x2
                                                                 x7
                                                                 (leaf 22)
                                                                 (leaf 6)).label ≠ 0 then
                                                                 let x12 : T := «at» x3 (leaf 4);
                                                                 let x13 : T := «at» x3 (leaf 5);
                                                                 let x14 : T := «node2»
                                                                   (leaf 21)
                                                                   x8
                                                                   x9;
                                                                 if («and»
                                                                   («isTy» x8)
                                                                   («and»
                                                                     («isTy» x9)
                                                                     («and»
                                                                       («hasType»
                                                                         x1
                                                                         x5
                                                                         x10
                                                                         («tyArrow»
                                                                           x8
                                                                           («tyArrow» x9 x9)))
                                                                       («and»
                                                                         («hasType» x1 x5 x11 x9)
                                                                         («and»
                                                                           («hasType» x1 x5 x12 x8)
                                                                           («hasType»
                                                                             x1
                                                                             x5
                                                                             x13
                                                                             («tyList»
                                                                               x8))))))).label ≠ 0 then
                                                                   «some»
                                                                     («eqn»
                                                                       x9
                                                                       («app3»
                                                                         x14
                                                                         x10
                                                                         x11
                                                                         («node2»
                                                                           (leaf 20)
                                                                           x12
                                                                           x13))
                                                                       («app2»
                                                                         x10
                                                                         x12
                                                                         («app3» x14 x10 x11 x13)))
                                                                 else
                                                                   «none»
                                                               else
                                                                 if («shape»
                                                                   x2
                                                                   x7
                                                                   (leaf 23)
                                                                   (leaf 4)).label ≠ 0 then
                                                                   Const.lcase
                                                                     (α := T)
                                                                     (β := T)
                                                                     x5
                                                                     «none»
                                                                     (fun (x12 : T)
                                                                        (x13 : List T) =>
                                                                       if («isListTy»
                                                                         x12).label ≠ 0 then
                                                                         let x14 : T := Const.child
                                                                           x12
                                                                           (leaf 0);
                                                                         «bindO»
                                                                           («typeIn» x1 x5 x8)
                                                                           (fun (x15 : T) =>
                                                                             let x16 : List
                                                                               T := «mapT»
                                                                               «eqLower»
                                                                               x6;
                                                                             let x17 : T := «node2»
                                                                               (leaf 20)
                                                                               («var» (leaf 1))
                                                                               («var» (leaf 0));
                                                                             let x18 : T := «mk1»
                                                                               (leaf 19)
                                                                               x14;
                                                                             if («and»
                                                                               («isTy» x14)
                                                                               («and»
                                                                                 («hasType»
                                                                                   x1
                                                                                   x5
                                                                                   x9
                                                                                   x15)
                                                                                 («and»
                                                                                   («weakens»
                                                                                     x1
                                                                                     x13
                                                                                     x16
                                                                                     x6)
                                                                                   («and»
                                                                                     (Const.equal
                                                                                       («prem»
                                                                                         x4
                                                                                         (leaf 2)
                                                                                         x13
                                                                                         x16)
                                                                                       («some»
                                                                                         («eqn»
                                                                                           x15
                                                                                           («subst»
                                                                                             x18
                                                                                             x8)
                                                                                           («subst»
                                                                                             x18
                                                                                             x9))))
                                                                                     (Const.equal
                                                                                       («prem»
                                                                                         x4
                                                                                         (leaf 3)
                                                                                         (x12 ::
                                                                                           (x14 ::
                                                                                             x13))
                                                                                         ((«eqn»
                                                                                           x15
                                                                                           («wkAt»
                                                                                             (leaf 1)
                                                                                             (leaf 1)
                                                                                             x8)
                                                                                           («wkAt»
                                                                                             (leaf 1)
                                                                                             (leaf 1)
                                                                                             x9)) ::
                                                                                           («mapT»
                                                                                             («eqWk»
                                                                                               (leaf 2))
                                                                                             x16)))
                                                                                       («some»
                                                                                         («eqn»
                                                                                           x15
                                                                                           («subst»
                                                                                             x17
                                                                                             («wkAt»
                                                                                               (leaf 1)
                                                                                               (leaf 2)
                                                                                               x8))
                                                                                           («subst»
                                                                                             x17
                                                                                             («wkAt»
                                                                                               (leaf 1)
                                                                                               (leaf 2)
                                                                                               x9))))))))).label ≠ 0 then
                                                                               «some»
                                                                                 («eqn» x15 x8 x9)
                                                                             else
                                                                               «none»)
                                                                       else
                                                                         «none»)
                                                                 else
                                                                   «none»);
    x7

def «checkMore» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : List T)
    (x5 : List (T × (List T → List T → T)))
    (x6 : List T)
    (x7 : List T) =>
    let x8 : T := (let x8 : T := «length» x4;
                   let x9 : T := «at» x4 (leaf 0);
                   let x10 : T := «at» x4 (leaf 1);
                   let x11 : T := «at» x4 (leaf 2);
                   let x12 : T := «at» x4 (leaf 3);
                   if («shape» x3 x8 (leaf 24) (leaf 4)).label ≠ 0 then
                     if («and»
                       («isTy» x9)
                       («and»
                         («isTy» x10)
                         («and»
                           («hasType» x2 x6 x11 x10)
                           («hasType»
                             x2
                             x6
                             x12
                             («tyArrow» x9 («tyArrow» («tyList» x9) x10)))))).label ≠ 0 then
                       «some»
                         («eqn»
                           x10
                           («app3» («node2» (leaf 24) x9 x10) («mk1» (leaf 19) x9) x11 x12)
                           x11)
                     else
                       «none»
                   else
                     if («shape» x3 x8 (leaf 25) (leaf 6)).label ≠ 0 then
                       let x13 : T := «at» x4 (leaf 4);
                       let x14 : T := «at» x4 (leaf 5);
                       if («and»
                         («isTy» x9)
                         («and»
                           («isTy» x10)
                           («and»
                             («hasType» x2 x6 x13 x10)
                             («and»
                               («hasType» x2 x6 x14 («tyArrow» x9 («tyArrow» («tyList» x9) x10)))
                               («and»
                                 («hasType» x2 x6 x11 x9)
                                 («hasType» x2 x6 x12 («tyList» x9))))))).label ≠ 0 then
                         «some»
                           («eqn»
                             x10
                             («app3»
                               («node2» (leaf 24) x9 x10)
                               («node2» (leaf 20) x11 x12)
                               x13
                               x14)
                             («app2» x14 x11 x12))
                       else
                         «none»
                     else
                       if («shape» x3 x8 (leaf 26) (leaf 3)).label ≠ 0 then
                         if («and»
                           («isTy» x9)
                           («and»
                             («hasType» x2 x6 x10 («tyArrow» x9 x9))
                             («hasType» x2 x6 x11 x9))).label ≠ 0 then
                           «some»
                             («eqn»
                               x9
                               («app3» («mk1» (leaf 18) x9) x10 x11 («mk1» (leaf 15) (leaf 0)))
                               x11)
                         else
                           «none»
                       else
                         if («shape» x3 x8 (leaf 27) (leaf 4)).label ≠ 0 then
                           if («and»
                             («isTy» x9)
                             («and»
                               («hasType» x2 x6 x10 («tyArrow» x9 x9))
                               («and»
                                 («hasType» x2 x6 x11 x9)
                                 («hasType» x2 x6 x12 (leaf 0))))).label ≠ 0 then
                             «some»
                               («eqn»
                                 x9
                                 («app3»
                                   («mk1» (leaf 18) x9)
                                   x10
                                   x11
                                   («app2»
                                     («mk1» (leaf 22) (leaf 5))
                                     x12
                                     («mk1» (leaf 15) (leaf 1))))
                                 («app» x10 («app3» («mk1» (leaf 18) x9) x10 x11 x12)))
                           else
                             «none»
                         else
                           if («shape» x3 x8 (leaf 28) (leaf 4)).label ≠ 0 then
                             if («and»
                               («isTy» x9)
                               («and»
                                 («hasType»
                                   x2
                                   x6
                                   x10
                                   («tyArrow» (leaf 0) («tyArrow» («tyList» x9) x9)))
                                 («and»
                                   («hasType» x2 x6 x11 (leaf 0))
                                   («hasType» x2 x6 x12 («tyList» (leaf 0)))))).label ≠ 0 then
                               «some»
                                 («eqn»
                                   x9
                                   («app2»
                                     («mk1» (leaf 17) x9)
                                     x10
                                     («app2» («mk1» (leaf 22) (leaf 3)) x11 x12))
                                   («app2»
                                     x10
                                     («app» («mk1» (leaf 22) (leaf 0)) x11)
                                     («mapBy»
                                       (leaf 0)
                                       x9
                                       («app2»
                                         («mk1» (leaf 17) x9)
                                         («wk» (leaf 2) x10)
                                         («var» (leaf 1)))
                                       x12)))
                             else
                               «none»
                           else
                             if («shape» x3 x8 (leaf 29) (leaf 3)).label ≠ 0 then
                               Const.lcase
                                 (α := T)
                                 (β := T)
                                 x6
                                 «none»
                                 (fun (x13 : T) (x14 : List T) =>
                                   «bindO»
                                     («typeIn» x2 x6 x9)
                                     (fun (x15 : T) =>
                                       let x16 : List T := «mapT» «eqLower» x7;
                                       let x17 : T := «app2»
                                         («mk1» (leaf 22) (leaf 3))
                                         («var» (leaf 1))
                                         («var» (leaf 0));
                                       if («and»
                                         (Const.equal x13 (leaf 0))
                                         («and»
                                           («isTy» x15)
                                           («and»
                                             («hasType» x2 x6 x10 x15)
                                             («and»
                                               («weakens» x2 x14 x16 x7)
                                               (Const.equal
                                                 («prem»
                                                   x5
                                                   (leaf 2)
                                                   ((«tyList» (leaf 0)) :: ((leaf 0) :: x14))
                                                   ((«eqn»
                                                     («tyList» x15)
                                                     («mapBy»
                                                       (leaf 0)
                                                       x15
                                                       («subst»
                                                         («var» (leaf 1))
                                                         («wkAt» (leaf 1) (leaf 4) x9))
                                                       («var» (leaf 0)))
                                                     («mapBy»
                                                       (leaf 0)
                                                       x15
                                                       («subst»
                                                         («var» (leaf 1))
                                                         («wkAt» (leaf 1) (leaf 4) x10))
                                                       («var» (leaf 0)))) ::
                                                     («mapT» («eqWk» (leaf 2)) x16)))
                                                 («some»
                                                   («eqn»
                                                     x15
                                                     («subst» x17 («wkAt» (leaf 1) (leaf 2) x9))
                                                     («subst»
                                                       x17
                                                       («wkAt»
                                                         (leaf 1)
                                                         (leaf 2)
                                                         x10))))))))).label ≠ 0 then
                                         «some» («eqn» x15 x9 x10)
                                       else
                                         «none»))
                             else
                               if («shape» x3 x8 (leaf 30) (leaf 4)).label ≠ 0 then
                                 Const.lcase
                                   (α := T)
                                   (β := T)
                                   x6
                                   «none»
                                   (fun (x13 : T) (x14 : List T) =>
                                     «bindO»
                                       («typeIn» x2 x6 x9)
                                       (fun (x15 : T) =>
                                         let x16 : List T := «mapT» «eqLower» x7;
                                         let x17 : T := «app2»
                                           («mk1» (leaf 22) (leaf 5))
                                           («var» (leaf 0))
                                           («mk1» (leaf 15) (leaf 1));
                                         let x18 : T := «app»
                                           («mk1» (leaf 22) (leaf 0))
                                           («var» (leaf 0));
                                         if («and»
                                           (Const.equal x13 (leaf 0))
                                           («and»
                                             («hasType» x2 x6 x10 x15)
                                             («and»
                                               («weakens» x2 x14 x16 x7)
                                               («and»
                                                 (Const.equal
                                                   («prem» x5 (leaf 2) x14 x16)
                                                   («some»
                                                     («eqn»
                                                       x15
                                                       («subst» («mk1» (leaf 15) (leaf 0)) x9)
                                                       («subst» («mk1» (leaf 15) (leaf 0)) x10))))
                                                 (Const.equal
                                                   («prem»
                                                     x5
                                                     (leaf 3)
                                                     x6
                                                     ((«eqn» x15 x9 x10) :: x7))
                                                   («some»
                                                     («eqn»
                                                       x15
                                                       («subst» x17 («wkAt» (leaf 1) (leaf 1) x9))
                                                       («subst»
                                                         x17
                                                         («wkAt»
                                                           (leaf 1)
                                                           (leaf 1)
                                                           x10))))))))).label ≠ 0 then
                                           «some»
                                             («eqn»
                                               x15
                                               («subst» x18 («wkAt» (leaf 1) (leaf 1) x9))
                                               («subst» x18 («wkAt» (leaf 1) (leaf 1) x10)))
                                         else
                                           «none»))
                               else
                                 if («shape» x3 x8 (leaf 31) (leaf 1)).label ≠ 0 then
                                   «bindO»
                                     («nth» x0 (Const.label x9))
                                     (fun (x13 : T) =>
                                       «bindO»
                                         («typeIn» x2 x6 («mk1» (leaf 23) x9))
                                         (fun (x14 : T) =>
                                           «some»
                                             («eqn»
                                               x14
                                               («mk1» (leaf 23) x9)
                                               («wk» («length» x6) x13))))
                                 else
                                   if («shape» x3 x8 (leaf 32) (leaf 3)).label ≠ 0 then
                                     «bindO»
                                       («typeIn» x2 x6 x10)
                                       (fun (x13 : T) =>
                                         if («hasType» x2 x6 x11 x13).label ≠ 0 then
                                           «some»
                                             («eqn»
                                               x13
                                               («mk3» (leaf 16) («mk1» (leaf 15) x9) x10 x11)
                                               (if (x9).label ≠ 0 then x10 else x11))
                                         else
                                           «none»)
                                   else
                                     if («and»
                                       (Const.eq x3 (leaf 33))
                                       (Const.lt (leaf 0) x8)).label ≠ 0 then
                                       «bindO»
                                         («nth» «axioms» (Const.label x9))
                                         («cite» x2 x6 («tail» x4))
                                     else
                                       if («shape» x3 x8 (leaf 34) (leaf 4)).label ≠ 0 then
                                         if («and»
                                           («isTy» x9)
                                           («and»
                                             («hasType» x2 x6 x10 («tyArrow» x9 x9))
                                             («and»
                                               («hasType» x2 x6 x11 x9)
                                               («hasType» x2 x6 x12 (leaf 0))))).label ≠ 0 then
                                           «some»
                                             («eqn»
                                               x9
                                               («app3» («mk1» (leaf 18) x9) x10 x11 x12)
                                               («app3»
                                                 («mk1» (leaf 18) x9)
                                                 x10
                                                 x11
                                                 («app» («mk1» (leaf 22) (leaf 0)) x12)))
                                         else
                                           «none»
                                       else
                                         if («shape» x3 x8 (leaf 35) (leaf 4)).label ≠ 0 then
                                           if («and»
                                             («isTy» x9)
                                             («and»
                                               («hasType» x2 x6 x10 (leaf 0))
                                               («and»
                                                 («hasType» x2 x6 x11 x9)
                                                 («hasType» x2 x6 x12 x9)))).label ≠ 0 then
                                             «some»
                                               («eqn»
                                                 x9
                                                 («mk3» (leaf 16) x10 x11 x12)
                                                 («app3»
                                                   («mk1» (leaf 18) x9)
                                                   («node2» (leaf 9) x9 («wk» (leaf 1) x11))
                                                   x12
                                                   x10))
                                           else
                                             «none»
                                         else
                                           if («and»
                                             (Const.eq x3 (leaf 36))
                                             (Const.lt (leaf 0) x8)).label ≠ 0 then
                                             «bindO»
                                               («nth» x1 (Const.label x9))
                                               («cite» x2 x6 («tail» x4))
                                           else
                                             if («shape» x3 x8 (leaf 37) (leaf 4)).label ≠ 0 then
                                               if («and»
                                                 («isTy» x9)
                                                 («and»
                                                   («hasType»
                                                     x2
                                                     x6
                                                     x10
                                                     («tyArrow»
                                                       (leaf 0)
                                                       («tyArrow» («tyList» x9) x9)))
                                                   («and»
                                                     («hasType» x2 x6 x11 (leaf 0))
                                                     («hasType»
                                                       x2
                                                       x6
                                                       x12
                                                       («tyList» (leaf 0)))))).label ≠ 0 then
                                                 «some»
                                                   («eqn»
                                                     x9
                                                     («app2»
                                                       («mk1» (leaf 25) x9)
                                                       x10
                                                       («app2» («mk1» (leaf 22) (leaf 3)) x11 x12))
                                                     («app2»
                                                       x10
                                                       («app2» («mk1» (leaf 22) (leaf 3)) x11 x12)
                                                       («mapBy»
                                                         (leaf 0)
                                                         x9
                                                         («app2»
                                                           («mk1» (leaf 25) x9)
                                                           («wk» (leaf 2) x10)
                                                           («var» (leaf 1)))
                                                         x12)))
                                               else
                                                 «none»
                                             else
                                               «none»);
    x8

def «checkCert» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := (Const.fold
      (α := T × (List T → List T → T))
      (fun (x6 : T) (x7 : List (T × (List T → List T → T))) =>
        let x8 : List T := «crTrees» x7;
        (Const.node x6 x8,
          fun (x9 : List T) (x10 : List T) =>
            if (Const.lt x6 (leaf 24)).label ≠ 0 then
              «checkCore» x0 x2 x6 x8 x7 x9 x10
            else
              «checkMore» x0 x1 x2 x6 x8 x7 x9 x10))
      x3).2
      x4
      x5;
    x6

end GebMirror.GoedelT

end
