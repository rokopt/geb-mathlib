module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebBoot

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

def «Serialize.deltaBits» :=
  fun (x0 : T) =>
    let x1 : T := Const.add x0 (leaf 1);
    let x2 : T := Const.add (Const.log2 x1) (leaf 1);
    let x3 : T := Const.log2 x2;
    «Prelude.append»
      («Prelude.replicate» x3 (leaf 0))
      ((leaf 1) ::
        («Prelude.append»
          («Prelude.digitsMsb» (leaf 2) x2 x3)
          («Prelude.digitsMsb» (leaf 2) x1 (Const.sub x2 (leaf 1)))))

def «Serialize.nodeBits» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.add x1 (leaf 1);
    «Prelude.append»
      («Prelude.replicate» x0 (leaf 1))
      ((leaf 0) ::
        («Prelude.append»
          («Serialize.deltaBits» (Const.log2 x2))
          («Prelude.digitsLsb» (leaf 2) x2 (Const.log2 x2))))

def «Serialize.treeBits» :=
  fun (x0 : T) =>
    Const.fold
      (α := List T → List T)
      (fun (x1 : T) (x2 : List (List T → List T)) =>
        let x3 : T ×
          (List T →
            List
              T) := Const.foldr
          (α := List T → List T)
          (β := T × (List T → List T))
          (fun (x3 : List T → List T) (x4 : T × (List T → List T)) =>
            (Const.add (x4).1 (leaf 1), fun (x5 : List T) => x3 ((x4).2 x5)))
          (leaf 0, fun (x3 : List T) => x3)
          x2;
        fun (x4 : List T) =>
          «Prelude.append» («Serialize.nodeBits» (x3).1 x1) ((x3).2 x4))
      x0
      ([] : List T)

def «Serialize.packBits» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (T ×
        List
          T) := Const.foldr
      (α := T)
      (β := (T × (T × List T)) → T × (T × List T))
      (fun (x1 : T)
         (x2 : (T × (T × List T)) → T × (T × List T))
         (x3 : T × (T × List T)) =>
        let x4 : T := Const.add (x3).1 (Const.mul x1 ((x3).2).1);
        x2
          (if (Const.eq ((x3).2).1 (leaf 128)).label ≠ 0 then
            (leaf 0, (leaf 1, (x4 :: ((x3).2).2)))
          else
            (x4, (Const.mul (leaf 2) ((x3).2).1, ((x3).2).2))))
      (fun (x1 : T × (T × List T)) => x1)
      x0
      (leaf 0, (leaf 1, ([] : List T)));
    «Prelude.reverse»
      (if (Const.eq ((x1).2).1 (leaf 1)).label ≠ 0 then
        ((x1).2).2
      else
        ((x1).1 :: ((x1).2).2))

def «Serialize.image» :=
  fun (x0 : T) =>
    let x1 : List T := «Serialize.treeBits» x0;
    Const.node
      (leaf 0)
      («Prelude.append»
        ((leaf 71) ::
          ((leaf 69) ::
            ((leaf 66) :: ((leaf 75) :: ((leaf 1) :: ([] : List T))))))
        («Prelude.append»
          («Prelude.digitsLsb» (leaf 256) («Prelude.length» x1) (leaf 8))
          («Serialize.packBits» x1)))

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

def «Typing.name» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Typing.sameName» :=
  fun (x0 : T) (x1 : T) => let x2 : T := Const.equal x0 x1; x2

def «Typing.tx0» := Const.node (leaf 0) ([] : List T)

def «Typing.tAtom» := fun (x0 : List T) => Const.node (leaf 1) x0

def «Typing.tList» := fun (x0 : List T) => Const.node (leaf 2) x0

def «Typing.tx3» := Const.node (leaf 3) ([] : List T)

def «Typing.tx4» := Const.node (leaf 4) ([] : List T)

def «Typing.tx5» := Const.node (leaf 5) ([] : List T)

def «Typing.tx6» := Const.node (leaf 6) ([] : List T)

def «Typing.tx7» := Const.node (leaf 7) ([] : List T)

def «Typing.tx8» := Const.node (leaf 8) ([] : List T)

def «Typing.tMarker» := fun (x0 : List T) => Const.node (leaf 9) x0

def «Typing.tData» :=
  fun (x0 : T) => Const.node (leaf 10) (x0 :: ([] : List T))

def «Typing.tAs» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 11) (x0 :: (x1 :: ([] : List T)))

def «Typing.tOf» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 12) (x0 :: (x1 :: ([] : List T)))

def «Typing.tx13» := Const.node (leaf 13) ([] : List T)

def «Typing.tx14» := Const.node (leaf 14) ([] : List T)

def «Typing.tGeneric» := fun (x0 : List T) => Const.node (leaf 15) x0

def «Typing.Tx.member» :=
  fun (x0 : T) =>
    Const.mod
      (Const.div
        (Const.fold
          (α := T)
          (fun (x1 : T) (x2 : List T) =>
            let x3 : T := Const.node (leaf 0) x2;
            Const.add
              (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                Const.eq (Const.arity x3) (leaf 0)
              else
                if (Const.eq x1 (leaf 1)).label ≠ 0 then
                  Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                else
                  if (Const.eq x1 (leaf 2)).label ≠ 0 then
                    if (Const.lt
                      (leaf 0)
                      (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                      Const.foldr
                        (α := T)
                        (β := T)
                        (fun (x4 : T) (x5 : T) =>
                          if (Const.mod (Const.div x4 (leaf 1)) (leaf 2)).label ≠ 0 then
                            x5
                          else
                            leaf 0)
                        (leaf 1)
                        (Const.iter
                          (α := List T)
                          (fun (x4 : List T) =>
                            Const.lcase
                              (α := T)
                              (β := List T)
                              x4
                              ([] : List T)
                              (fun (_ : T) (x6 : List T) => x6))
                          x2
                          (leaf 0))
                    else
                      leaf 0
                  else
                    if (Const.eq x1 (leaf 3)).label ≠ 0 then
                      Const.eq (Const.arity x3) (leaf 0)
                    else
                      if (Const.eq x1 (leaf 4)).label ≠ 0 then
                        Const.eq (Const.arity x3) (leaf 0)
                      else
                        if (Const.eq x1 (leaf 5)).label ≠ 0 then
                          Const.eq (Const.arity x3) (leaf 0)
                        else
                          if (Const.eq x1 (leaf 6)).label ≠ 0 then
                            Const.eq (Const.arity x3) (leaf 0)
                          else
                            if (Const.eq x1 (leaf 7)).label ≠ 0 then
                              Const.eq (Const.arity x3) (leaf 0)
                            else
                              if (Const.eq x1 (leaf 8)).label ≠ 0 then
                                Const.eq (Const.arity x3) (leaf 0)
                              else
                                if (Const.eq x1 (leaf 9)).label ≠ 0 then
                                  Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                                else
                                  if (Const.eq x1 (leaf 10)).label ≠ 0 then
                                    if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                                      Const.mod
                                        (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                        (leaf 2)
                                    else
                                      leaf 0
                                  else
                                    if (Const.eq x1 (leaf 11)).label ≠ 0 then
                                      if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                                        if (Const.mod
                                          (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                          (leaf 2)).label ≠ 0 then
                                          Const.mod
                                            (Const.div (Const.child x3 (leaf 1)) (leaf 1))
                                            (leaf 2)
                                        else
                                          leaf 0
                                      else
                                        leaf 0
                                    else
                                      if (Const.eq x1 (leaf 12)).label ≠ 0 then
                                        if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                                          if (Const.mod
                                            (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                            (leaf 2)).label ≠ 0 then
                                            Const.mod
                                              (Const.div (Const.child x3 (leaf 1)) (leaf 1))
                                              (leaf 2)
                                          else
                                            leaf 0
                                        else
                                          leaf 0
                                      else
                                        if (Const.eq x1 (leaf 13)).label ≠ 0 then
                                          Const.eq (Const.arity x3) (leaf 0)
                                        else
                                          if (Const.eq x1 (leaf 14)).label ≠ 0 then
                                            Const.eq (Const.arity x3) (leaf 0)
                                          else
                                            if (Const.eq x1 (leaf 15)).label ≠ 0 then
                                              if (Const.lt
                                                (leaf 0)
                                                (Const.add
                                                  (Const.arity x3)
                                                  (leaf 1))).label ≠ 0 then
                                                Const.foldr
                                                  (α := T)
                                                  (β := T)
                                                  (fun (x4 : T) (x5 : T) =>
                                                    if (Const.mod
                                                      (Const.div x4 (leaf 1))
                                                      (leaf 2)).label ≠ 0 then
                                                      x5
                                                    else
                                                      leaf 0)
                                                  (leaf 1)
                                                  (Const.iter
                                                    (α := List T)
                                                    (fun (x4 : List T) =>
                                                      Const.lcase
                                                        (α := T)
                                                        (β := List T)
                                                        x4
                                                        ([] : List T)
                                                        (fun (_ : T) (x6 : List T) => x6))
                                                    x2
                                                    (leaf 0))
                                              else
                                                leaf 0
                                            else
                                              leaf 0).label ≠ 0 then
                leaf 1
              else
                leaf 0)
              (leaf 0))
          x0)
        (leaf 1))
      (leaf 2)

def «Typing/Txs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Typing/Txs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/Txs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/Txs.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Typing/Txs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Typing/Txs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Typing/Txs.tail» x1 x0;
    x2

def «Typing/Txs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Typing/Txs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Typing.tyT» := Const.node (leaf 0) ([] : List T)

def «Typing.tyUnit» := Const.node (leaf 1) ([] : List T)

def «Typing.tyProd» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «Typing.tyArrow» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 3) (x0 :: (x1 :: ([] : List T)))

def «Typing.tyList» :=
  fun (x0 : T) => Const.node (leaf 4) (x0 :: ([] : List T))

def «Typing.tyData» :=
  fun (x0 : T) => Const.node (leaf 5) (x0 :: ([] : List T))

def «Typing.tySort» :=
  fun (x0 : T) => Const.node (leaf 6) (x0 :: ([] : List T))

def «Typing.sameTy» :=
  fun (x0 : T) (x1 : T) => let x2 : T := Const.equal x0 x1; x2

def «Typing/Tys.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Typing/Tys.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/Tys.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/Tys.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Typing/Tys.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Typing/Tys.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Typing/Tys.tail» x1 x0;
    x2

def «Typing/Tys.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Typing/Tys.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Typing/OTy.nothing» := Const.node (leaf 0) ([] : List T)

def «Typing/OTy.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Typing/OTy.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Typing/OTy.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Typing/OTy.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Typing/OTy.nothing»
      (fun (x2 : T) (_ : List T) => «Typing/OTy.just» x2);
    x2

def «Typing/OTy.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Typing/MTys.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Typing/MTys.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/MTys.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/MTys.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Typing/MTys.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Typing/MTys.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Typing/MTys.tail» x1 x0;
    x2

def «Typing/MTys.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Typing/MTys.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Typing.eraseTy» :=
  fun (x0 : T) =>
    let x1 : T := Const.para
      (α := Unit → T)
      (fun (x1 : T) (x2 : List (Unit → T)) (_ : Unit) =>
        if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
          «Typing.tyT»
        else
          if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
            «Typing.tyUnit»
          else
            if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
              let x4 : (Unit → T) ×
                List
                  (Unit →
                    T) := Const.lcase
                (α := Unit → T)
                (β := (Unit → T) × List (Unit → T))
                x2
                (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
              let x5 : T := (x4).1 ();
              let x6 : (Unit → T) ×
                List
                  (Unit →
                    T) := Const.lcase
                (α := Unit → T)
                (β := (Unit → T) × List (Unit → T))
                (x4).2
                (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                (fun (x6 : Unit → T) (x7 : List (Unit → T)) => (x6, x7));
              let x7 : T := (x6).1 (); «Typing.tyProd» x5 x7
            else
              if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
                let x4 : (Unit → T) ×
                  List
                    (Unit →
                      T) := Const.lcase
                  (α := Unit → T)
                  (β := (Unit → T) × List (Unit → T))
                  x2
                  (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                  (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
                let x5 : T := (x4).1 ();
                let x6 : (Unit → T) ×
                  List
                    (Unit →
                      T) := Const.lcase
                  (α := Unit → T)
                  (β := (Unit → T) × List (Unit → T))
                  (x4).2
                  (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                  (fun (x6 : Unit → T) (x7 : List (Unit → T)) => (x6, x7));
                let x7 : T := (x6).1 (); «Typing.tyArrow» x5 x7
              else
                if (Const.eq (Const.label x1) (leaf 4)).label ≠ 0 then
                  let x4 : (Unit → T) ×
                    List
                      (Unit →
                        T) := Const.lcase
                    (α := Unit → T)
                    (β := (Unit → T) × List (Unit → T))
                    x2
                    (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                    (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
                  let x5 : T := (x4).1 (); «Typing.tyList» x5
                else
                  if (Const.eq (Const.label x1) (leaf 5)).label ≠ 0 then
                    let _ : (Unit → T) ×
                      List
                        (Unit →
                          T) := Const.lcase
                      (α := Unit → T)
                      (β := (Unit → T) × List (Unit → T))
                      x2
                      (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                      (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
                    let _ : T := Const.child x1 (leaf 0); «Typing.tyT»
                  else
                    let _ : (Unit → T) ×
                      List
                        (Unit →
                          T) := Const.lcase
                      (α := Unit → T)
                      (β := (Unit → T) × List (Unit → T))
                      x2
                      (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
                      (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
                    let _ : T := Const.child x1 (leaf 0); «Typing.tyT»)
      x0
      ();
    x1

def «Typing.isData» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 5)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Typing.foldTyOf» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tyArrow»
      («Typing.tyArrow»
        «Typing.tyT»
        («Typing.tyArrow» («Typing.tyList» x0) x0))
      («Typing.tyArrow» «Typing.tyT» x0);
    x1

def «Typing.iterTyOf» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tyArrow»
      («Typing.tyArrow» x0 x0)
      («Typing.tyArrow» x0 («Typing.tyArrow» «Typing.tyT» x0));
    x1

def «Typing.foldrTyOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Typing.tyArrow»
      («Typing.tyArrow» x0 («Typing.tyArrow» x1 x1))
      («Typing.tyArrow» x1 («Typing.tyArrow» («Typing.tyList» x0) x1));
    x2

def «Typing.lcaseTyOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Typing.tyArrow»
      («Typing.tyList» x0)
      («Typing.tyArrow»
        x1
        («Typing.tyArrow»
          («Typing.tyArrow» x0 («Typing.tyArrow» («Typing.tyList» x0) x1))
          x1));
    x2

def «Typing.tt» := «Typing.tyArrow» «Typing.tyT» «Typing.tyT»

def «Typing.ttt» := «Typing.tyArrow» «Typing.tyT» «Typing.tt»

def «Typing.primTys» :=
  («Typing.tt» ::
    («Typing.tt» ::
      («Typing.ttt» ::
        ((«Typing.tyArrow»
          «Typing.tyT»
          («Typing.tyArrow» («Typing.tyList» «Typing.tyT») «Typing.tyT»)) ::
          ((«Typing.tyArrow» «Typing.tyT» («Typing.tyList» «Typing.tyT»)) ::
            («Typing.ttt» ::
              («Typing.ttt» ::
                («Typing.ttt» ::
                  («Typing.ttt» ::
                    («Typing.ttt» ::
                      («Typing.ttt» ::
                        («Typing.ttt» ::
                          («Typing.ttt» :: («Typing.tt» :: ([] : List T)))))))))))))))

def «Typing.abbr» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Typing/Abbrs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Typing/Abbrs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/Abbrs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/Abbrs.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Typing/Abbrs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Typing/Abbrs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Typing/Abbrs.tail» x1 x0;
    x2

def «Typing/Abbrs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Typing/Abbrs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Typing/Names.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Typing/Names.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/Names.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/Names.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Typing/Names.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Typing/Names.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Typing/Names.tail» x1 x0;
    x2

def «Typing/Names.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Typing/Names.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Typing.mkEnv» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : List T ×
      (List T ×
        (List T ×
          (List T × (List T × List T)))) := (x0,
      (x1, (x2, (x3, (x4, x5)))));
    x6

def «Typing.envAl» :=
  fun (x0 : List T ×
      (List T × (List T × (List T × (List T × List T))))) =>
    let x1 : List T := (x0).1; x1

def «Typing.envDefs» :=
  fun (x0 : List T ×
      (List T × (List T × (List T × (List T × List T))))) =>
    let x1 : List T := ((x0).2).1; x1

def «Typing.envNoms» :=
  fun (x0 : List T ×
      (List T × (List T × (List T × (List T × List T))))) =>
    let x1 : List T := (((x0).2).2).1; x1

def «Typing.envSorts» :=
  fun (x0 : List T ×
      (List T × (List T × (List T × (List T × List T))))) =>
    let x1 : List T := ((((x0).2).2).2).1; x1

def «Typing.envNums» :=
  fun (x0 : List T ×
      (List T × (List T × (List T × (List T × List T))))) =>
    let x1 : List T := (((((x0).2).2).2).2).1; x1

def «Typing.envMs» :=
  fun (x0 : List T ×
      (List T × (List T × (List T × (List T × List T))))) =>
    let x1 : List T := (((((x0).2).2).2).2).2; x1

def «Typing.env0» :=
  «Typing.mkEnv»
    ([] : List T)
    ([] : List T)
    ([] : List T)
    ([] : List T)
    ([] : List T)
    ([] : List T)

def «Typing.lookupName» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        let x5 : T := Const.child x4 (leaf 0);
        let x6 : T := Const.child x4 (leaf 1);
        if («Typing.sameName» x5 x0).label ≠ 0 then
          «Typing/OTy.just» x6
        else
          x3)
      «Typing/OTy.nothing»
      x1;
    x2

def «Typing.hasName» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» («Typing.sameName» x2 x0) x3)
      (leaf 0)
      x1;
    x2

def «Typing.atomName» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List
                       T := Const.iter
                       (α := List T)
                       (fun (x2 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x2
                           ([] : List T)
                           (fun (_ : T) (x4 : List T) => x4))
                       (Const.children x1)
                       (leaf 0);
                     «Typing.name» x2
                   else
                     «Typing.name» ([] : List T));
    x1

def «Typing.isAtomTx» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : List
                       T := Const.iter
                       (α := List T)
                       (fun (x2 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x2
                           ([] : List T)
                           (fun (_ : T) (x4 : List T) => x4))
                       (Const.children x1)
                       (leaf 0);
                     leaf 1
                   else
                     leaf 0);
    x1

def «Typing.namedTx» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «Reader.named» x0 x1; x2

def «Typing.kwRep» := mk 0 [leaf 114, leaf 101, leaf 112]

def «Typing.kwDecode» :=
  mk 0 [leaf 100, leaf 101, leaf 99, leaf 111, leaf 100, leaf 101]

def «Typing.kwDatum» :=
  mk 0 [leaf 100, leaf 97, leaf 116, leaf 117, leaf 109]

def «Typing.kwSort» :=
  mk 0 [leaf 37, leaf 115, leaf 111, leaf 114, leaf 116]

def «Typing.kwPostulate» :=
  mk 0 [leaf 37,
    leaf 112,
    leaf 111,
    leaf 115,
    leaf 116,
    leaf 117,
    leaf 108,
    leaf 97,
    leaf 116,
    leaf 101]

def «Typing/RT1s.single» :=
  fun (x0 : T × T) =>
    let x1 : List (T × T) := (x0 :: ([] : List (T × T))); x1

def «Typing/RT1s.length» :=
  fun (x0 : List (T × T)) =>
    let x1 : T := Const.foldr
      (α := T × T)
      (β := T)
      (fun (_ : T × T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/RT1s.append» :=
  fun (x0 : List (T × T)) (x1 : List (T × T)) =>
    let x2 : List
      (T ×
        T) := Const.foldr
      (α := T × T)
      (β := List (T × T))
      (fun (x2 : T × T) (x3 : List (T × T)) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/RT1s.reverse» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      (T ×
        T) := Const.foldr
      (α := T × T)
      (β := List (T × T) → List (T × T))
      (fun (x1 : T × T)
         (x2 : List (T × T) → List (T × T))
         (x3 : List (T × T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (T × T)) => x1)
      x0
      ([] : List (T × T));
    x1

def «Typing/RT1s.tail» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      (T ×
        T) := Const.lcase
      (α := T × T)
      (β := List (T × T))
      x0
      ([] : List (T × T))
      (fun (_ : T × T) (x2 : List (T × T)) => x2);
    x1

def «Typing/RT1s.drop» :=
  fun (x0 : T) (x1 : List (T × T)) =>
    let x2 : List
      (T × T) := Const.iter (α := List (T × T)) «Typing/RT1s.tail» x1 x0;
    x2

def «Typing/RT1s.atOr» :=
  fun (x0 : T × T) (x1 : List (T × T)) (x2 : T) =>
    let x3 : T ×
      T := Const.lcase
      (α := T × T)
      (β := T × T)
      («Typing/RT1s.drop» x2 x1)
      x0
      (fun (x3 : T × T) (_ : List (T × T)) => x3);
    x3

def «Typing.rtForms» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Typing.readTy» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : T) =>
    let x2 : T := (Const.para
      (α := Unit → T × T)
      (fun (x2 : T) (x3 : List (Unit → T × T)) (_ : Unit) =>
        if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
          let x5 : List
            T := Const.iter
            (α := List T)
            (fun (x5 : List T) =>
              Const.lcase
                (α := T)
                (β := List T)
                x5
                ([] : List T)
                (fun (_ : T) (x7 : List T) => x7))
            (Const.children x2)
            (leaf 0);
          («Typing.tAtom» x5,
            let x6 : T := «Typing.name» x5;
            if («Typing.namedTx» («Typing.tAtom» x5) «Reader.kwT»).label ≠ 0 then
              «Typing/OTy.just» «Typing.tyT»
            else
              if («Typing.namedTx»
                («Typing.tAtom» x5)
                «Reader.kwUnit»).label ≠ 0 then
                «Typing/OTy.just» «Typing.tyUnit»
              else
                let x7 : T := «Typing.lookupName» x6 («Typing.envAl» x0);
                if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                  let x8 : T := Const.child x7 (leaf 0); «Typing/OTy.just» x8
                else
                  if («Typing.hasName» x6 («Typing.envNoms» x0)).label ≠ 0 then
                    «Typing/OTy.just» («Typing.tyData» x6)
                  else
                    if («Typing.hasName» x6 («Typing.envSorts» x0)).label ≠ 0 then
                      «Typing/OTy.just» («Typing.tySort» x6)
                    else
                      «Typing/OTy.nothing»)
        else
          if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
            let x5 : List
              (T ×
                T) := Const.foldr
              (α := Unit → T × T)
              (β := List (T × T))
              (fun (x5 : Unit → T × T) (x6 : List (T × T)) => ((x5 ()) :: x6))
              ([] : List (T × T))
              x3;
            let x6 : List T := «Typing.rtForms» x5;
            let x7 : T := «Typing/RT1s.length» x5;
            let x8 : T := «Typing/Txs.atOr» «Typing.tx0» x6 (leaf 0);
            let x9 : T →
              T := (fun (x9 : T) =>
              («Typing/RT1s.atOr» («Typing.tx0», «Typing/OTy.nothing») x5 x9).2);
            («Typing.tList» x6,
              if («Prelude.and»
                («Typing.namedTx» x8 «Reader.kwProd»)
                (Const.eq x7 (leaf 3))).label ≠ 0 then
                let x10 : T := x9 (leaf 1);
                if (Const.eq (Const.label x10) (leaf 1)).label ≠ 0 then
                  let x11 : T := Const.child x10 (leaf 0);
                  let x12 : T := x9 (leaf 2);
                  if (Const.eq (Const.label x12) (leaf 1)).label ≠ 0 then
                    let x13 : T := Const.child x12 (leaf 0);
                    «Typing/OTy.just» («Typing.tyProd» x11 x13)
                  else
                    «Typing/OTy.nothing»
                else
                  «Typing/OTy.nothing»
              else
                if («Prelude.and»
                  («Typing.namedTx» x8 «Reader.kwArrow»)
                  (Const.eq x7 (leaf 3))).label ≠ 0 then
                  let x10 : T := x9 (leaf 1);
                  if (Const.eq (Const.label x10) (leaf 1)).label ≠ 0 then
                    let x11 : T := Const.child x10 (leaf 0);
                    let x12 : T := x9 (leaf 2);
                    if (Const.eq (Const.label x12) (leaf 1)).label ≠ 0 then
                      let x13 : T := Const.child x12 (leaf 0);
                      «Typing/OTy.just» («Typing.tyArrow» x11 x13)
                    else
                      «Typing/OTy.nothing»
                  else
                    «Typing/OTy.nothing»
                else
                  if («Prelude.and»
                    («Typing.namedTx» x8 «Reader.kwList»)
                    (Const.eq x7 (leaf 2))).label ≠ 0 then
                    let x10 : T := x9 (leaf 1);
                    if (Const.eq (Const.label x10) (leaf 1)).label ≠ 0 then
                      let x11 : T := Const.child x10 (leaf 0);
                      «Typing/OTy.just» («Typing.tyList» x11)
                    else
                      «Typing/OTy.nothing»
                  else
                    «Typing/OTy.nothing»)
          else
            («Typing.tx0», «Typing/OTy.nothing»))
      x1
      ()).2;
    x2

def «Typing/Tss.single» :=
  fun (x0 : List T) =>
    let x1 : List (List T) := (x0 :: ([] : List (List T))); x1

def «Typing/Tss.length» :=
  fun (x0 : List (List T)) =>
    let x1 : T := Const.foldr
      (α := List T)
      (β := T)
      (fun (_ : List T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/Tss.append» :=
  fun (x0 : List (List T)) (x1 : List (List T)) =>
    let x2 : List
      (List
        T) := Const.foldr
      (α := List T)
      (β := List (List T))
      (fun (x2 : List T) (x3 : List (List T)) => (x2 :: x3))
      x1
      x0;
    x2

def «Typing/Tss.reverse» :=
  fun (x0 : List (List T)) =>
    let x1 : List
      (List
        T) := Const.foldr
      (α := List T)
      (β := List (List T) → List (List T))
      (fun (x1 : List T)
         (x2 : List (List T) → List (List T))
         (x3 : List (List T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (List T)) => x1)
      x0
      ([] : List (List T));
    x1

def «Typing/Tss.tail» :=
  fun (x0 : List (List T)) =>
    let x1 : List
      (List
        T) := Const.lcase
      (α := List T)
      (β := List (List T))
      x0
      ([] : List (List T))
      (fun (_ : List T) (x2 : List (List T)) => x2);
    x1

def «Typing/Tss.drop» :=
  fun (x0 : T) (x1 : List (List T)) =>
    let x2 : List
      (List T) := Const.iter (α := List (List T)) «Typing/Tss.tail» x1 x0;
    x2

def «Typing/Tss.atOr» :=
  fun (x0 : List T) (x1 : List (List T)) (x2 : T) =>
    let x3 : List
      T := Const.lcase
      (α := List T)
      (β := List T)
      («Typing/Tss.drop» x2 x1)
      x0
      (fun (x3 : List T) (_ : List (List T)) => x3);
    x3

def «Typing.markerNames» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) => ((Const.child x1 (leaf 0)) :: x2))
      ([] : List T)
      x0;
    x1

def «Typing.fieldOk» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := (let x3 : T := «Reader.indexOf» x1 («Typing.markerNames» x0);
                   if («Prelude.isSome» x3).label ≠ 0 then
                     «Prelude.at» x2 («Prelude.get» x3)
                   else
                     leaf 1);
    x3

def «Typing.ctorOk» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : List (List T)) =>
    let x4 : T := (let x4 : List T := Const.children (Const.child x1 (leaf 1));
                   let x5 : T := «Prelude.length» x4;
                   let x6 : T := «Typing/Tss.length» x3;
                   «Prelude.and»
                     (Const.eq (Const.child x1 (leaf 0)) x2)
                     («Prelude.and»
                       (if (Const.child x1 (leaf 2)).label ≠ 0 then
                         Const.lt x5 (Const.add x6 (leaf 1))
                       else
                         Const.eq x6 x5)
                       («Prelude.and»
                         (Const.foldr
                           (α := T)
                           (β := T × T)
                           (fun (x7 : T) (x8 : T × T) =>
                             (Const.sub (x8).1 (leaf 1),
                               «Prelude.and»
                                 («Typing.fieldOk»
                                   x0
                                   x7
                                   («Typing/Tss.atOr» ([] : List T) x3 (Const.sub (x8).1 (leaf 1))))
                                 (x8).2))
                           (x5, leaf 1)
                           x4).2
                         (if (Const.child x1 (leaf 2)).label ≠ 0 then
                           Const.foldr
                             (α := List T)
                             (β := T)
                             (fun (x7 : List T) (x8 : T) =>
                               «Prelude.and» («Typing.fieldOk» x0 (Const.child x1 (leaf 3)) x7) x8)
                             (leaf 1)
                             («Typing/Tss.drop» x5 x3)
                         else
                           leaf 1))));
    x4

def «Typing.memberships» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List
      T := Const.fold
      (α := List T)
      (fun (x2 : T) (x3 : List (List T)) =>
        Const.foldr
          (α := T)
          (β := List T)
          (fun (x4 : T) (x5 : List T) =>
            ((Const.foldr
              (α := T)
              (β := T)
              (fun (x6 : T) (x7 : T) =>
                «Prelude.or» («Typing.ctorOk» x0 x6 x2 x3) x7)
              (leaf 0)
              («Prelude.tail» (Const.children x4))) ::
              x5))
          ([] : List T)
          x0)
      x1;
    x2

def «Typing.memberOf» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Reader.indexOf» x1 («Typing.markerNames» x0);
                   if («Prelude.isSome» x3).label ≠ 0 then
                     «Prelude.at» («Typing.memberships» x0 x2) («Prelude.get» x3)
                   else
                     leaf 0);
    x3

def «Typing/SRs.single» :=
  fun (x0 : T × (List T → T)) =>
    let x1 : List
      (T × (List T → T)) := (x0 :: ([] : List (T × (List T → T))));
    x1

def «Typing/SRs.length» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : T := Const.foldr
      (α := T × (List T → T))
      (β := T)
      (fun (_ : T × (List T → T)) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Typing/SRs.append» :=
  fun (x0 : List (T × (List T → T))) (x1 : List (T × (List T → T))) =>
    let x2 : List
      (T ×
        (List T →
          T)) := Const.foldr
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      (fun (x2 : T × (List T → T)) (x3 : List (T × (List T → T))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Typing/SRs.reverse» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : List
      (T ×
        (List T →
          T)) := Const.foldr
      (α := T × (List T → T))
      (β := List (T × (List T → T)) → List (T × (List T → T)))
      (fun (x1 : T × (List T → T))
         (x2 : List (T × (List T → T)) → List (T × (List T → T)))
         (x3 : List (T × (List T → T))) =>
        x2 (x1 :: x3))
      (fun (x1 : List (T × (List T → T))) => x1)
      x0
      ([] : List (T × (List T → T)));
    x1

def «Typing/SRs.tail» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : List
      (T ×
        (List T →
          T)) := Const.lcase
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      x0
      ([] : List (T × (List T → T)))
      (fun (_ : T × (List T → T)) (x2 : List (T × (List T → T))) => x2);
    x1

def «Typing/SRs.drop» :=
  fun (x0 : T) (x1 : List (T × (List T → T))) =>
    let x2 : List
      (T ×
        (List T →
          T)) := Const.iter
      (α := List (T × (List T → T)))
      «Typing/SRs.tail»
      x1
      x0;
    x2

def «Typing/SRs.atOr» :=
  fun (x0 : T × (List T → T)) (x1 : List (T × (List T → T))) (x2 : T) =>
    let x3 : T ×
      (List T →
        T) := Const.lcase
      (α := T × (List T → T))
      (β := T × (List T → T))
      («Typing/SRs.drop» x2 x1)
      x0
      (fun (x3 : T × (List T → T)) (_ : List (T × (List T → T))) => x3);
    x3

def «Typing.srForms» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x1 : T × (List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Typing.srAt» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    let x3 : T := («Typing/SRs.atOr»
      («Typing.tx0», fun (_ : List T) => «Typing/OTy.nothing»)
      x0
      x1).2
      x2;
    x3

def «Typing.srFrom» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x3 : T × (List T → T)) (x4 : List T) => (((x3).2 x2) :: x4))
      ([] : List T)
      («Typing/SRs.drop» x1 x0);
    x3

def «Typing.applyTy» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x3;
        if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          let x6 : T := x5;
          if (Const.eq (Const.label x6) (leaf 3)).label ≠ 0 then
            let x7 : T := Const.child x6 (leaf 0);
            let x8 : T := Const.child x6 (leaf 1);
            let x9 : T := x2;
            if (Const.eq (Const.label x9) (leaf 1)).label ≠ 0 then
              let x10 : T := Const.child x9 (leaf 0);
              if («Typing.sameTy» x7 x10).label ≠ 0 then
                «Typing/OTy.just» x8
              else
                «Typing/OTy.nothing»
            else
              «Typing/OTy.nothing»
          else
            «Typing/OTy.nothing»
        else
          «Typing/OTy.nothing»)
      x0
      («Typing/MTys.reverse» x1);
    x2

def «Typing/OAbbr.nothing» := Const.node (leaf 0) ([] : List T)

def «Typing/OAbbr.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Typing/OAbbr.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Typing/OAbbr.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Typing/OAbbr.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Typing/OAbbr.nothing»
      (fun (x2 : T) (_ : List T) => «Typing/OAbbr.just» x2);
    x2

def «Typing/OAbbr.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Typing.bindersOf» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : T) =>
    let x2 : T ×
      List
        T := (let x2 : List
                T := (let x2 : T := x1;
                      if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
                        let x3 : List
                          T := Const.iter
                          (α := List T)
                          (fun (x3 : List T) =>
                            Const.lcase
                              (α := T)
                              (β := List T)
                              x3
                              ([] : List T)
                              (fun (_ : T) (x5 : List T) => x5))
                          (Const.children x2)
                          (leaf 0);
                        if («Prelude.and»
                          (Const.eq («Typing/Txs.length» x3) (leaf 2))
                          («Typing.isAtomTx»
                            («Typing/Txs.atOr» «Typing.tx0» x3 (leaf 0)))).label ≠ 0 then
                          «Typing/Txs.single» x1
                        else
                          x3
                      else
                        ([] : List T));
              «Typing/OAbbr.allJust»
                (Const.foldr
                  (α := T)
                  (β := List T)
                  (fun (x3 : T) (x4 : List T) =>
                    ((let x5 : T := x3;
                      if (Const.eq (Const.label x5) (leaf 2)).label ≠ 0 then
                        let x6 : List
                          T := Const.iter
                          (α := List T)
                          (fun (x6 : List T) =>
                            Const.lcase
                              (α := T)
                              (β := List T)
                              x6
                              ([] : List T)
                              (fun (_ : T) (x8 : List T) => x8))
                          (Const.children x5)
                          (leaf 0);
                        if («Prelude.and»
                          (Const.eq («Typing/Txs.length» x6) (leaf 2))
                          («Typing.isAtomTx»
                            («Typing/Txs.atOr» «Typing.tx0» x6 (leaf 0)))).label ≠ 0 then
                          let x7 : T := «Typing.readTy»
                            x0
                            («Typing/Txs.atOr» «Typing.tx0» x6 (leaf 1));
                          if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                            let x8 : T := Const.child x7 (leaf 0);
                            «Typing/OAbbr.just»
                              («Typing.abbr»
                                («Typing.atomName» («Typing/Txs.atOr» «Typing.tx0» x6 (leaf 0)))
                                x8)
                          else
                            «Typing/OAbbr.nothing»
                        else
                          «Typing/OAbbr.nothing»
                      else
                        «Typing/OAbbr.nothing») ::
                      x4))
                  ([] : List T)
                  x2));
    x2

def «Typing.synAtom» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T)
    (x2 : List T) =>
    let x3 : T := (let x3 : T := «Typing.name» x1;
                   if («Prelude.isSome» («Reader.numeral» x1)).label ≠ 0 then
                     «Typing/OTy.just» «Typing.tyT»
                   else
                     if («Typing.hasName» x3 («Typing.envNums» x0)).label ≠ 0 then
                       «Typing/OTy.just» «Typing.tyT»
                     else
                       let x4 : T := «Typing.lookupName» x3 x2;
                       if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                         let x5 : T := Const.child x4 (leaf 0); «Typing/OTy.just» x5
                       else
                         let x5 : T := «Typing.lookupName» x3 («Typing.envDefs» x0);
                         if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                           let x6 : T := Const.child x5 (leaf 0); «Typing/OTy.just» x6
                         else
                           let x6 : T := «Reader.indexOf» x3 «Reader.primNames»;
                           if («Prelude.isSome» x6).label ≠ 0 then
                             «Typing/OTy.just»
                               («Typing/Tys.atOr» «Typing.tyT» «Typing.primTys» («Prelude.get» x6))
                           else
                             if («Typing.namedTx»
                               («Typing.tAtom» x1)
                               «Reader.kwUnitValue»).label ≠ 0 then
                               «Typing/OTy.just» «Typing.tyUnit»
                             else
                               «Typing/OTy.nothing»);
    x3

def «Typing.both2» :=
  fun (x0 : T) (x1 : T) (x2 : T → T → T) =>
    let x3 : T := (let x3 : T := x0;
                   if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
                     let x4 : T := Const.child x3 (leaf 0);
                     let x5 : T := x1;
                     if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                       let x6 : T := Const.child x5 (leaf 0); x2 x4 x6
                     else
                       «Typing/OTy.nothing»
                   else
                     «Typing/OTy.nothing»);
    x3

def «Typing.then1» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Typing/OTy.nothing»);
    x2

def «Typing.when» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (x0).label ≠ 0 then
      «Typing/OTy.just» x1
    else
      «Typing/OTy.nothing»);
    x2

def «Typing.synList» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T)
    (x2 : List (T × (List T → T)))
    (x3 : List T) =>
    let x4 : T := (let x4 : T := «Typing/SRs.length» x2;
                   let x5 : T := «Typing/Txs.atOr» «Typing.tx0» x1 (leaf 0);
                   let x6 : T →
                     T := (fun (x6 : T) => «Typing/Txs.atOr» «Typing.tx0» x1 x6);
                   let x7 : T → T := (fun (x7 : T) => «Typing.srAt» x2 x7 x3);
                   if (Const.eq x4 (leaf 0)).label ≠ 0 then
                     «Typing/OTy.nothing»
                   else
                     if («Prelude.and»
                       («Typing.namedTx» x5 «Reader.kwLam»)
                       (Const.eq x4 (leaf 3))).label ≠ 0 then
                       let x8 : T × List T := «Typing.bindersOf» x0 (x6 (leaf 1));
                       if («Prelude.and»
                         (x8).1
                         (Const.lt (leaf 0) («Typing/Abbrs.length» (x8).2))).label ≠ 0 then
                         «Typing.then1»
                           («Typing.srAt»
                             x2
                             (leaf 2)
                             («Typing/Abbrs.append» («Typing/Abbrs.reverse» (x8).2) x3))
                           (fun (x9 : T) =>
                             «Typing/OTy.just»
                               (Const.foldr
                                 (α := T)
                                 (β := T)
                                 (fun (x10 : T) (x11 : T) =>
                                   let x12 : T := x10;
                                   let _ : T := Const.child x12 (leaf 0);
                                   let x14 : T := Const.child x12 (leaf 1);
                                   «Typing.tyArrow» x14 x11)
                                 x9
                                 (x8).2))
                       else
                         «Typing/OTy.nothing»
                     else
                       if («Prelude.and»
                         («Typing.namedTx» x5 «Reader.kwLet»)
                         (Const.eq x4 (leaf 5))).label ≠ 0 then
                         «Typing.both2»
                           («Typing.readTy» x0 (x6 (leaf 2)))
                           (x7 (leaf 3))
                           (fun (x8 : T) (x9 : T) =>
                             if («Prelude.and»
                               («Typing.isAtomTx» (x6 (leaf 1)))
                               («Typing.sameTy» x8 x9)).label ≠ 0 then
                               «Typing.srAt»
                                 x2
                                 (leaf 4)
                                 ((«Typing.abbr» («Typing.atomName» (x6 (leaf 1))) x8) :: x3)
                             else
                               «Typing/OTy.nothing»)
                       else
                         if («Prelude.and»
                           («Typing.namedTx» x5 «Reader.kwPair»)
                           (Const.eq x4 (leaf 3))).label ≠ 0 then
                           «Typing.both2»
                             (x7 (leaf 1))
                             (x7 (leaf 2))
                             (fun (x8 : T) (x9 : T) => «Typing/OTy.just» («Typing.tyProd» x8 x9))
                         else
                           if («Prelude.and»
                             («Prelude.or»
                               («Typing.namedTx» x5 «Reader.kwFst»)
                               («Typing.namedTx» x5 «Reader.kwSnd»))
                             (Const.eq x4 (leaf 2))).label ≠ 0 then
                             «Typing.then1»
                               (x7 (leaf 1))
                               (fun (x8 : T) =>
                                 let x9 : T := x8;
                                 if (Const.eq (Const.label x9) (leaf 2)).label ≠ 0 then
                                   let x10 : T := Const.child x9 (leaf 0);
                                   let x11 : T := Const.child x9 (leaf 1);
                                   «Typing/OTy.just»
                                     (if («Typing.namedTx» x5 «Reader.kwFst»).label ≠ 0 then
                                       x10
                                     else
                                       x11)
                                 else
                                   «Typing/OTy.nothing»)
                           else
                             if («Prelude.and»
                               («Typing.namedTx» x5 «Reader.kwIf»)
                               (Const.eq x4 (leaf 4))).label ≠ 0 then
                               «Typing.then1»
                                 (x7 (leaf 1))
                                 (fun (x8 : T) =>
                                   «Typing.both2»
                                     (x7 (leaf 2))
                                     (x7 (leaf 3))
                                     (fun (x9 : T) (x10 : T) =>
                                       «Typing.when»
                                         («Prelude.and»
                                           («Typing.sameTy» x8 «Typing.tyT»)
                                           («Typing.sameTy» x9 x10))
                                         x9))
                             else
                               if («Prelude.and»
                                 («Typing.namedTx» x5 «Reader.kwCons»)
                                 (Const.eq x4 (leaf 3))).label ≠ 0 then
                                 «Typing.both2»
                                   (x7 (leaf 1))
                                   (x7 (leaf 2))
                                   (fun (x8 : T) (x9 : T) =>
                                     «Typing.when» («Typing.sameTy» («Typing.tyList» x8) x9) x9)
                               else
                                 if («Prelude.and»
                                   («Typing.namedTx» x5 «Reader.kwNil»)
                                   (Const.eq x4 (leaf 2))).label ≠ 0 then
                                   «Typing.then1»
                                     («Typing.readTy» x0 (x6 (leaf 1)))
                                     (fun (x8 : T) => «Typing/OTy.just» («Typing.tyList» x8))
                                 else
                                   if («Prelude.and»
                                     («Typing.namedTx» x5 «Reader.kwQuote»)
                                     (Const.eq x4 (leaf 2))).label ≠ 0 then
                                     «Typing/OTy.just» «Typing.tyT»
                                   else
                                     if («Prelude.and»
                                       («Typing.namedTx» x5 «Typing.kwDatum»)
                                       (Const.eq x4 (leaf 3))).label ≠ 0 then
                                       «Typing.then1»
                                         («Typing.readTy» x0 (x6 (leaf 1)))
                                         (fun (x8 : T) =>
                                           let x9 : T := «Reader.readDatum» (x6 (leaf 2));
                                           «Typing.when»
                                             («Prelude.and»
                                               («Typing.isData» x8)
                                               («Prelude.and»
                                                 («Prelude.isSome» x9)
                                                 («Typing.memberOf»
                                                   («Typing.envMs» x0)
                                                   (x6 (leaf 1))
                                                   («Prelude.get» x9))))
                                             x8)
                                     else
                                       if («Prelude.and»
                                         («Typing.namedTx» x5 «Typing.kwRep»)
                                         (Const.eq x4 (leaf 2))).label ≠ 0 then
                                         «Typing.then1»
                                           (x7 (leaf 1))
                                           (fun (x8 : T) =>
                                             «Typing.when» («Typing.isData» x8) «Typing.tyT»)
                                       else
                                         if («Prelude.and»
                                           («Typing.namedTx» x5 «Typing.kwDecode»)
                                           (Const.eq x4 (leaf 5))).label ≠ 0 then
                                           «Typing.then1»
                                             («Typing.readTy» x0 (x6 (leaf 1)))
                                             (fun (x8 : T) =>
                                               «Typing.then1»
                                                 (x7 (leaf 2))
                                                 (fun (x9 : T) =>
                                                   «Typing.both2»
                                                     (x7 (leaf 3))
                                                     (x7 (leaf 4))
                                                     (fun (x10 : T) (x11 : T) =>
                                                       «Typing.when»
                                                         («Prelude.and»
                                                           («Typing.isData» x8)
                                                           («Prelude.and»
                                                             («Typing.sameTy» x9 «Typing.tyT»)
                                                             («Typing.sameTy»
                                                               x10
                                                               («Typing.tyArrow» x8 x11))))
                                                         x11)))
                                         else
                                           if («Prelude.and»
                                             («Prelude.or»
                                               («Typing.namedTx» x5 «Reader.kwFold»)
                                               («Prelude.or»
                                                 («Typing.namedTx» x5 «Reader.kwPara»)
                                                 («Typing.namedTx» x5 «Reader.kwIter»)))
                                             (Const.lt (leaf 1) x4)).label ≠ 0 then
                                             «Typing.then1»
                                               («Typing.readTy» x0 (x6 (leaf 1)))
                                               (fun (x8 : T) =>
                                                 «Typing.applyTy»
                                                   («Typing/OTy.just»
                                                     (if («Typing.namedTx»
                                                       x5
                                                       «Reader.kwIter»).label ≠ 0 then
                                                       «Typing.iterTyOf» x8
                                                     else
                                                       «Typing.foldTyOf» x8))
                                                   («Typing.srFrom» x2 (leaf 2) x3))
                                           else
                                             if («Prelude.and»
                                               («Prelude.or»
                                                 («Typing.namedTx» x5 «Reader.kwFoldr»)
                                                 («Typing.namedTx» x5 «Reader.kwLcase»))
                                               (Const.lt (leaf 2) x4)).label ≠ 0 then
                                               «Typing.both2»
                                                 («Typing.readTy» x0 (x6 (leaf 1)))
                                                 («Typing.readTy» x0 (x6 (leaf 2)))
                                                 (fun (x8 : T) (x9 : T) =>
                                                   «Typing.applyTy»
                                                     («Typing/OTy.just»
                                                       (if («Typing.namedTx»
                                                         x5
                                                         «Reader.kwFoldr»).label ≠ 0 then
                                                         «Typing.foldrTyOf» x8 x9
                                                       else
                                                         «Typing.lcaseTyOf» x8 x9))
                                                     («Typing.srFrom» x2 (leaf 3) x3))
                                             else
                                               «Typing.applyTy»
                                                 (x7 (leaf 0))
                                                 («Typing.srFrom» x2 (leaf 1) x3));
    x4

def «Typing.synIn» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T)
    (x2 : T) =>
    let x3 : T := (Const.para
      (α := Unit → T × (List T → T))
      (fun (x3 : T) (x4 : List (Unit → T × (List T → T))) (_ : Unit) =>
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x6 : List
            T := Const.iter
            (α := List T)
            (fun (x6 : List T) =>
              Const.lcase
                (α := T)
                (β := List T)
                x6
                ([] : List T)
                (fun (_ : T) (x8 : List T) => x8))
            (Const.children x3)
            (leaf 0);
          («Typing.tAtom» x6, fun (x7 : List T) => «Typing.synAtom» x0 x6 x7)
        else
          if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
            let x6 : List
              (T ×
                (List T →
                  T)) := Const.foldr
              (α := Unit → T × (List T → T))
              (β := List (T × (List T → T)))
              (fun (x6 : Unit → T × (List T → T)) (x7 : List (T × (List T → T))) =>
                ((x6 ()) :: x7))
              ([] : List (T × (List T → T)))
              x4;
            let x7 : List T := «Typing.srForms» x6;
            («Typing.tList» x7, fun (x8 : List T) => «Typing.synList» x0 x7 x6 x8)
          else
            if (Const.eq (Const.label x3) (leaf 11)).label ≠ 0 then
              let x6 : (Unit → T × (List T → T)) ×
                List
                  (Unit →
                    T ×
                      (List T →
                        T)) := Const.lcase
                (α := Unit → T × (List T → T))
                (β := (Unit → T × (List T → T)) × List (Unit → T × (List T → T)))
                x4
                (fun (_ : Unit) => (leaf 0, fun (_ : List T) => leaf 0),
                  ([] : List (Unit → T × (List T → T))))
                (fun (x6 : Unit → T × (List T → T))
                   (x7 : List (Unit → T × (List T → T))) =>
                  (x6, x7));
              let x7 : T × (List T → T) := (x6).1 ();
              let x8 : (Unit → T × (List T → T)) ×
                List
                  (Unit →
                    T ×
                      (List T →
                        T)) := Const.lcase
                (α := Unit → T × (List T → T))
                (β := (Unit → T × (List T → T)) × List (Unit → T × (List T → T)))
                (x6).2
                (fun (_ : Unit) => (leaf 0, fun (_ : List T) => leaf 0),
                  ([] : List (Unit → T × (List T → T))))
                (fun (x8 : Unit → T × (List T → T))
                   (x9 : List (Unit → T × (List T → T))) =>
                  (x8, x9));
              let x9 : T × (List T → T) := (x8).1 ();
              («Typing.tAs» (x7).1 (x9).1,
                fun (x10 : List T) =>
                  «Typing.both2»
                    («Typing.readTy» x0 (x7).1)
                    ((x9).2 x10)
                    (fun (x11 : T) (x12 : T) =>
                      «Typing.when» («Typing.sameTy» («Typing.eraseTy» x11) x12) x11))
            else
              if (Const.eq (Const.label x3) (leaf 12)).label ≠ 0 then
                let x6 : (Unit → T × (List T → T)) ×
                  List
                    (Unit →
                      T ×
                        (List T →
                          T)) := Const.lcase
                  (α := Unit → T × (List T → T))
                  (β := (Unit → T × (List T → T)) × List (Unit → T × (List T → T)))
                  x4
                  (fun (_ : Unit) => (leaf 0, fun (_ : List T) => leaf 0),
                    ([] : List (Unit → T × (List T → T))))
                  (fun (x6 : Unit → T × (List T → T))
                     (x7 : List (Unit → T × (List T → T))) =>
                    (x6, x7));
                let x7 : T × (List T → T) := (x6).1 ();
                let x8 : (Unit → T × (List T → T)) ×
                  List
                    (Unit →
                      T ×
                        (List T →
                          T)) := Const.lcase
                  (α := Unit → T × (List T → T))
                  (β := (Unit → T × (List T → T)) × List (Unit → T × (List T → T)))
                  (x6).2
                  (fun (_ : Unit) => (leaf 0, fun (_ : List T) => leaf 0),
                    ([] : List (Unit → T × (List T → T))))
                  (fun (x8 : Unit → T × (List T → T))
                     (x9 : List (Unit → T × (List T → T))) =>
                    (x8, x9));
                let x9 : T × (List T → T) := (x8).1 ();
                («Typing.tOf» (x7).1 (x9).1,
                  fun (x10 : List T) =>
                    «Typing.both2»
                      («Typing.readTy» x0 (x7).1)
                      ((x9).2 x10)
                      (fun (x11 : T) (x12 : T) =>
                        «Typing.when» («Typing.sameTy» x11 x12) («Typing.eraseTy» x11)))
              else
                («Typing.tx0», fun (_ : List T) => «Typing/OTy.nothing»))
      x2
      ()).2
      x1;
    x3

def «Typing/OName.nothing» := Const.node (leaf 0) ([] : List T)

def «Typing/OName.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Typing/OName.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Typing/OName.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Typing/OName.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Typing/OName.nothing»
      (fun (x2 : T) (_ : List T) => «Typing/OName.just» x2);
    x2

def «Typing/OName.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Typing.withAl» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T) =>
    let x2 : List T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              List
                T)))) := «Typing.mkEnv»
      x1
      («Typing.envDefs» x0)
      («Typing.envNoms» x0)
      («Typing.envSorts» x0)
      («Typing.envNums» x0)
      («Typing.envMs» x0);
    x2

def «Typing.withDefs» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T) =>
    let x2 : List T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              List
                T)))) := «Typing.mkEnv»
      («Typing.envAl» x0)
      x1
      («Typing.envNoms» x0)
      («Typing.envSorts» x0)
      («Typing.envNums» x0)
      («Typing.envMs» x0);
    x2

def «Typing.withNoms» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T) =>
    let x2 : List T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              List
                T)))) := «Typing.mkEnv»
      («Typing.envAl» x0)
      («Typing.envDefs» x0)
      x1
      («Typing.envSorts» x0)
      («Typing.envNums» x0)
      («Typing.envMs» x0);
    x2

def «Typing.withSorts» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T) =>
    let x2 : List T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              List
                T)))) := «Typing.mkEnv»
      («Typing.envAl» x0)
      («Typing.envDefs» x0)
      («Typing.envNoms» x0)
      x1
      («Typing.envNums» x0)
      («Typing.envMs» x0);
    x2

def «Typing.withNums» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T) =>
    let x2 : List T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              List
                T)))) := «Typing.mkEnv»
      («Typing.envAl» x0)
      («Typing.envDefs» x0)
      («Typing.envNoms» x0)
      («Typing.envSorts» x0)
      x1
      («Typing.envMs» x0);
    x2

def «Typing.withMs» :=
  fun (x0 : List T × (List T × (List T × (List T × (List T × List T)))))
    (x1 : List T) =>
    let x2 : List T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              List
                T)))) := «Typing.mkEnv»
      («Typing.envAl» x0)
      («Typing.envDefs» x0)
      («Typing.envNoms» x0)
      («Typing.envSorts» x0)
      («Typing.envNums» x0)
      x1;
    x2

def «Typing.checkStep» :=
  fun (x0 : (List T ×
      (List T × (List T × (List T × (List T × List T))))) ×
      T)
    (x1 : T) =>
    let x2 : (List T ×
      (List T × (List T × (List T × (List T × List T))))) ×
      T := (let x2 : T := (x0).2;
            if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
              let _ : T := Const.child x2 (leaf 0); x0
            else
              let x3 : List T ×
                (List T × (List T × (List T × (List T × List T)))) := (x0).1;
              let x4 : (List T ×
                (List T × (List T × (List T × (List T × List T))))) →
                (List T × (List T × (List T × (List T × (List T × List T))))) ×
                  T := (fun (x4 : List T ×
                            (List T × (List T × (List T × (List T × List T))))) =>
                (x4, «Typing/OName.nothing»));
              let x5 : (List T ×
                (List T × (List T × (List T × (List T × List T))))) ×
                T := (x3,
                «Typing/OName.just»
                  (let x5 : T := x1;
                   if (Const.eq (Const.label x5) (leaf 2)).label ≠ 0 then
                     let x6 : List
                       T := Const.iter
                       (α := List T)
                       (fun (x6 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x6
                           ([] : List T)
                           (fun (_ : T) (x8 : List T) => x8))
                       (Const.children x5)
                       (leaf 0);
                     if (Const.lt (leaf 1) («Typing/Txs.length» x6)).label ≠ 0 then
                       «Typing.atomName» («Typing/Txs.atOr» «Typing.tx0» x6 (leaf 1))
                     else
                       «Typing.name» ([] : List T)
                   else
                     «Typing.name» ([] : List T)));
              let x6 : T := x1;
              if (Const.eq (Const.label x6) (leaf 10)).label ≠ 0 then
                let x7 : T := Const.child x6 (leaf 0);
                x4
                  («Typing.withNoms»
                    x3
                    («Typing/Names.append»
                      («Typing.envNoms» x3)
                      («Typing/Names.single» («Typing.atomName» x7))))
              else
                if (Const.eq (Const.label x6) (leaf 9)).label ≠ 0 then
                  let _ : List
                    T := Const.iter
                    (α := List T)
                    (fun (x7 : List T) =>
                      Const.lcase
                        (α := T)
                        (β := List T)
                        x7
                        ([] : List T)
                        (fun (_ : T) (x9 : List T) => x9))
                    (Const.children x6)
                    (leaf 0);
                  x4
                    («Typing.withMs»
                      x3
                      («Typing/Txs.append» («Typing.envMs» x3) («Typing/Txs.single» x1)))
                else
                  if (Const.eq (Const.label x6) (leaf 2)).label ≠ 0 then
                    let x7 : List
                      T := Const.iter
                      (α := List T)
                      (fun (x7 : List T) =>
                        Const.lcase
                          (α := T)
                          (β := List T)
                          x7
                          ([] : List T)
                          (fun (_ : T) (x9 : List T) => x9))
                      (Const.children x6)
                      (leaf 0);
                    let x8 : T := «Typing/Txs.atOr» «Typing.tx0» x7 (leaf 0);
                    let x9 : T := «Typing/Txs.atOr» «Typing.tx0» x7 (leaf 1);
                    let x10 : T := «Typing/Txs.length» x7;
                    if («Prelude.and»
                      («Typing.namedTx» x8 «Typing.kwSort»)
                      (Const.eq x10 (leaf 2))).label ≠ 0 then
                      x4
                        («Typing.withSorts»
                          x3
                          («Typing/Names.append»
                            («Typing.envSorts» x3)
                            («Typing/Names.single» («Typing.atomName» x9))))
                    else
                      if (Const.eq x10 (leaf 3)).label ≠ 0 then
                        let x11 : T := «Typing.atomName» x9;
                        let x12 : T := «Typing/Txs.atOr» «Typing.tx0» x7 (leaf 2);
                        let x13 : T →
                          (List T × (List T × (List T × (List T × (List T × List T))))) ×
                            T := (fun (x13 : T) =>
                          let x14 : T := x13;
                          if (Const.eq (Const.label x14) (leaf 1)).label ≠ 0 then
                            let x15 : T := Const.child x14 (leaf 0);
                            x4
                              («Typing.withDefs»
                                x3
                                («Typing/Abbrs.append»
                                  («Typing.envDefs» x3)
                                  («Typing/Abbrs.single» («Typing.abbr» x11 x15))))
                          else
                            x5);
                        if («Typing.namedTx» x8 «Reader.kwDef»).label ≠ 0 then
                          x13 («Typing.synIn» x3 ([] : List T) x12)
                        else
                          if («Typing.namedTx» x8 «Typing.kwPostulate»).label ≠ 0 then
                            x13 («Typing.readTy» x3 x12)
                          else
                            if («Typing.namedTx» x8 «Reader.kwDeftype»).label ≠ 0 then
                              let x14 : T := «Typing.readTy» x3 x12;
                              if (Const.eq (Const.label x14) (leaf 1)).label ≠ 0 then
                                let x15 : T := Const.child x14 (leaf 0);
                                x4
                                  («Typing.withAl»
                                    x3
                                    ((«Typing.abbr» x11 x15) :: («Typing.envAl» x3)))
                              else
                                x5
                            else
                              if («Typing.namedTx» x8 «Reader.kwDefnum»).label ≠ 0 then
                                x4
                                  («Typing.withNums»
                                    x3
                                    («Typing/Names.append»
                                      («Typing.envNums» x3)
                                      («Typing/Names.single» x11)))
                              else
                                x5
                      else
                        x5
                  else
                    x5);
    x2

def «Typing.checkRun» :=
  fun (x0 : (List T ×
      (List T × (List T × (List T × (List T × List T))))) ×
      T)
    (x1 : List T) =>
    let x2 : (List T ×
      (List T × (List T × (List T × (List T × List T))))) ×
      T := Const.foldr
      (α := T)
      (β := ((List T × (List T × (List T × (List T × (List T × List T))))) ×
        T) →
        (List T × (List T × (List T × (List T × (List T × List T))))) × T)
      (fun (x2 : T)
         (x3 : ((List T × (List T × (List T × (List T × (List T × List T))))) ×
           T) →
           (List T × (List T × (List T × (List T × (List T × List T))))) × T)
         (x4 : (List T × (List T × (List T × (List T × (List T × List T))))) ×
           T) =>
        x3 («Typing.checkStep» x4 x2))
      (fun (x2 : (List T ×
           (List T × (List T × (List T × (List T × List T))))) ×
           T) =>
        x2)
      x1
      x0;
    x2

def «Typing.checkForms» :=
  fun (x0 : List T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := ((List T × (List T × (List T × (List T × (List T × List T))))) ×
        T) →
        (List T × (List T × (List T × (List T × (List T × List T))))) × T)
      (fun (x1 : T)
         (x2 : ((List T × (List T × (List T × (List T × (List T × List T))))) ×
           T) →
           (List T × (List T × (List T × (List T × (List T × List T))))) × T)
         (x3 : (List T × (List T × (List T × (List T × (List T × List T))))) ×
           T) =>
        x2
          (let x4 : T := x1;
           if (Const.eq (Const.label x4) (leaf 15)).label ≠ 0 then
             let x5 : List
               T := Const.iter
               (α := List T)
               (fun (x5 : List T) =>
                 Const.lcase
                   (α := T)
                   (β := List T)
                   x5
                   ([] : List T)
                   (fun (_ : T) (x7 : List T) => x7))
               (Const.children x4)
               (leaf 0);
             let x6 : T := (x3).2;
             if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
               let _ : T := Const.child x6 (leaf 0); x3
             else
               ((x3).1, («Typing.checkRun» x3 x5).2)
           else
             «Typing.checkStep» x3 x1))
      (fun (x1 : (List T ×
           (List T × (List T × (List T × (List T × List T))))) ×
           T) =>
        x1)
      x0
      («Typing.env0», «Typing/OName.nothing»)).2;
    x1

def «Datatype/Txs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Datatype/Txs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Datatype/Txs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Datatype/Txs.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Datatype/Txs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Datatype/Txs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Datatype/Txs.tail» x1 x0;
    x2

def «Datatype/Txs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Datatype/Txs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Datatype/OTx.nothing» := Const.node (leaf 0) ([] : List T)

def «Datatype/OTx.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Datatype/OTx.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Datatype/OTx.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Datatype/OTx.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Datatype/OTx.nothing»
      (fun (x2 : T) (_ : List T) => «Datatype/OTx.just» x2);
    x2

def «Datatype/OTx.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Datatype/MTxs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Datatype/MTxs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Datatype/MTxs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Datatype/MTxs.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Datatype/MTxs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Datatype/MTxs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Datatype/MTxs.tail» x1 x0;
    x2

def «Datatype/MTxs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Datatype/MTxs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Datatype.sameName» :=
  fun (x0 : T) (x1 : T) => let x2 : T := Const.equal x0 x1; x2

def «Datatype.atomName» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List
                       T := Const.iter
                       (α := List T)
                       (fun (x2 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x2
                           ([] : List T)
                           (fun (_ : T) (x4 : List T) => x4))
                       (Const.children x1)
                       (leaf 0);
                     «Typing.name» x2
                   else
                     «Typing.name» ([] : List T));
    x1

def «Datatype.isAtomTx» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : List
                       T := Const.iter
                       (α := List T)
                       (fun (x2 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x2
                           ([] : List T)
                           (fun (_ : T) (x4 : List T) => x4))
                       (Const.children x1)
                       (leaf 0);
                     leaf 1
                   else
                     leaf 0);
    x1

def «Datatype.isListTx» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                     let _ : List
                       T := Const.iter
                       (α := List T)
                       (fun (x2 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x2
                           ([] : List T)
                           (fun (_ : T) (x4 : List T) => x4))
                       (Const.children x1)
                       (leaf 0);
                     leaf 1
                   else
                     leaf 0);
    x1

def «Datatype.namedTx» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «Reader.named» x0 x1; x2

def «Datatype.elems» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
              let x2 : List
                T := Const.iter
                (α := List T)
                (fun (x2 : List T) =>
                  Const.lcase
                    (α := T)
                    (β := List T)
                    x2
                    ([] : List T)
                    (fun (_ : T) (x4 : List T) => x4))
                (Const.children x1)
                (leaf 0);
              x2
            else
              ([] : List T));
    x1

def «Datatype.nthTx» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «Datatype/Txs.atOr» «Typing.tx0» x0 x1; x2

def «Datatype.sx1» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tList» («Datatype/Txs.single» x0); x1

def «Datatype.sx2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Typing.tList» (x0 :: («Datatype/Txs.single» x1)); x2

def «Datatype.sx3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Typing.tList»
      (x0 :: (x1 :: («Datatype/Txs.single» x2)));
    x3

def «Datatype.sx4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Typing.tList»
      (x0 :: (x1 :: (x2 :: («Datatype/Txs.single» x3))));
    x4

def «Datatype.sx5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Typing.tList»
      (x0 :: (x1 :: (x2 :: (x3 :: («Datatype/Txs.single» x4)))));
    x5

def «Datatype.sx6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «Typing.tList»
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: («Datatype/Txs.single» x5))))));
    x6

def «Datatype.aLet» := mk 1 [leaf 108, leaf 101, leaf 116]

def «Datatype.aIf» := mk 1 [leaf 105, leaf 102]

def «Datatype.aLam» := mk 1 [leaf 108, leaf 97, leaf 109]

def «Datatype.aPair» := mk 1 [leaf 112, leaf 97, leaf 105, leaf 114]

def «Datatype.aFst» := mk 1 [leaf 102, leaf 115, leaf 116]

def «Datatype.aSnd» := mk 1 [leaf 115, leaf 110, leaf 100]

def «Datatype.aCons» := mk 1 [leaf 99, leaf 111, leaf 110, leaf 115]

def «Datatype.aNil» := mk 1 [leaf 110, leaf 105, leaf 108]

def «Datatype.aIter» := mk 1 [leaf 105, leaf 116, leaf 101, leaf 114]

def «Datatype.aLcase» :=
  mk 1 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «Datatype.aFoldr» :=
  mk 1 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «Datatype.aPara» := mk 1 [leaf 112, leaf 97, leaf 114, leaf 97]

def «Datatype.aDef» := mk 1 [leaf 100, leaf 101, leaf 102]

def «Datatype.aDeftype» :=
  mk 1 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «Datatype.aUnitV» := mk 1 [leaf 117, leaf 110, leaf 105, leaf 116]

def «Datatype.aQuote» :=
  mk 1 [leaf 113, leaf 117, leaf 111, leaf 116, leaf 101]

def «Datatype.aLabel» :=
  mk 1 [leaf 108, leaf 97, leaf 98, leaf 101, leaf 108]

def «Datatype.aChild» :=
  mk 1 [leaf 99, leaf 104, leaf 105, leaf 108, leaf 100]

def «Datatype.aChildren» :=
  mk 1 [leaf 99,
    leaf 104,
    leaf 105,
    leaf 108,
    leaf 100,
    leaf 114,
    leaf 101,
    leaf 110]

def «Datatype.aNode» := mk 1 [leaf 110, leaf 111, leaf 100, leaf 101]

def «Datatype.aEq» := mk 1 [leaf 101, leaf 113]

def «Datatype.aT» := mk 1 [leaf 84]

def «Datatype.aUnit» := mk 1 [leaf 85, leaf 110, leaf 105, leaf 116]

def «Datatype.aProd» := mk 1 [leaf 80, leaf 114, leaf 111, leaf 100]

def «Datatype.aArrow» :=
  mk 1 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «Datatype.aList» := mk 1 [leaf 76, leaf 105, leaf 115, leaf 116]

def «Datatype.aZero» := mk 1 [leaf 48]

def «Datatype.aS» := mk 1 [leaf 37, leaf 115]

def «Datatype.aO» := mk 1 [leaf 37, leaf 111]

def «Datatype.aA» := mk 1 [leaf 37, leaf 97]

def «Datatype.aH» := mk 1 [leaf 37, leaf 104]

def «Datatype.aTl» := mk 1 [leaf 37, leaf 116]

def «Datatype.aX» := mk 1 [leaf 37, leaf 120]

def «Datatype.aU» := mk 1 [leaf 37, leaf 117]

def «Datatype.aR» := mk 1 [leaf 37, leaf 114]

def «Datatype.aD» := mk 1 [leaf 37, leaf 100]

def «Datatype.aRest» :=
  mk 1 [leaf 37, leaf 114, leaf 101, leaf 115, leaf 116]

def «Datatype.aK» := mk 1 [leaf 37, leaf 107]

def «Datatype.aE» := mk 1 [leaf 37, leaf 101]

def «Datatype.kwData» := mk 0 [leaf 100, leaf 97, leaf 116, leaf 97]

def «Datatype.kwTreeData» :=
  mk 0 [leaf 116,
    leaf 114,
    leaf 101,
    leaf 101,
    leaf 45,
    leaf 100,
    leaf 97,
    leaf 116,
    leaf 97]

def «Datatype.kwCase» := mk 0 [leaf 99, leaf 97, leaf 115, leaf 101]

def «Datatype.kwCata» := mk 0 [leaf 99, leaf 97, leaf 116, leaf 97]

def «Datatype.kwDefn» := mk 0 [leaf 100, leaf 101, leaf 102, leaf 110]

def «Datatype.kwElse» := mk 0 [leaf 101, leaf 108, leaf 115, leaf 101]

def «Datatype.kwRep» := mk 0 [leaf 114, leaf 101, leaf 112]

def «Datatype.kwDecode» :=
  mk 0 [leaf 100, leaf 101, leaf 99, leaf 111, leaf 100, leaf 101]

def «Datatype.kwDatum» :=
  mk 0 [leaf 100, leaf 97, leaf 116, leaf 117, leaf 109]

def «Datatype.kwGeneric» :=
  mk 0 [leaf 37,
    leaf 103,
    leaf 101,
    leaf 110,
    leaf 101,
    leaf 114,
    leaf 105,
    leaf 99]

def «Datatype.kwSort» :=
  mk 0 [leaf 37, leaf 115, leaf 111, leaf 114, leaf 116]

def «Datatype.kwPostulate» :=
  mk 0 [leaf 37,
    leaf 112,
    leaf 111,
    leaf 115,
    leaf 116,
    leaf 117,
    leaf 108,
    leaf 97,
    leaf 116,
    leaf 101]

def «Datatype.kwAmp» := mk 0 [leaf 38]

def «Datatype.decimalChars» :=
  fun (x0 : T) =>
    let x1 : List
      T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «Prelude.single» (leaf 48)
    else
      let x1 : T := (Const.iter
        (α := T × T)
        (fun (x1 : T × T) =>
          if (Const.eq (x1).2 (leaf 0)).label ≠ 0 then
            x1
          else
            (Const.add (x1).1 (leaf 1), Const.div (x1).2 (leaf 10)))
        (leaf 0, x0)
        (Const.add (Const.log2 x0) (leaf 1))).1;
      Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) => ((Const.add x2 (leaf 48)) :: x3))
        ([] : List T)
        («Prelude.digitsMsb» (leaf 10) x0 x1));
    x1

def «Datatype.numAtom» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tAtom» («Datatype.decimalChars» x0); x1

def «Datatype.memberName» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 1)
      («Prelude.append»
        (Const.children x0)
        (Const.children
          (mk 1 [leaf 46,
            leaf 109,
            leaf 101,
            leaf 109,
            leaf 98,
            leaf 101,
            leaf 114])));
    x1

def «Datatype.memberAtom» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tAtom»
      («Prelude.append»
        (Const.children x0)
        (Const.children
          (mk 1 [leaf 46,
            leaf 109,
            leaf 101,
            leaf 109,
            leaf 98,
            leaf 101,
            leaf 114])));
    x1

def «Datatype.fieldAtom» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tAtom»
      ((leaf 37) :: ((leaf 102) :: («Datatype.decimalChars» x0)));
    x1

def «Datatype.qAtom» :=
  fun (x0 : T) =>
    let x1 : T := «Typing.tAtom»
      ((leaf 37) :: ((leaf 113) :: («Datatype.decimalChars» x0)));
    x1

def «Datatype.sList» :=
  fun (x0 : T) => let x1 : T := «Datatype.sx2» «Datatype.aList» x0; x1

def «Datatype.sProd» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Datatype.sx3» «Datatype.aProd» x0 x1; x2

def «Datatype.sArrow» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Datatype.sx3» «Datatype.aArrow» x0 x1; x2

def «Datatype.sLet» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Datatype.sx5» «Datatype.aLet» x0 x1 x2 x3; x4

def «Datatype.sIf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Datatype.sx4» «Datatype.aIf» x0 x1 x2; x3

def «Datatype.sLam1» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Datatype.sx3»
      «Datatype.aLam»
      («Datatype.sx1» («Datatype.sx2» x0 x1))
      x2;
    x3

def «Datatype.sLam2» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «Datatype.sx3»
      «Datatype.aLam»
      («Datatype.sx2» («Datatype.sx2» x0 x1) («Datatype.sx2» x2 x3))
      x4;
    x5

def «Datatype.sTail» :=
  fun (x0 : T) =>
    let x1 : T := «Datatype.sLam1»
      «Datatype.aX»
      («Datatype.sList» x0)
      («Datatype.sx6»
        «Datatype.aLcase»
        x0
        («Datatype.sList» x0)
        «Datatype.aX»
        («Datatype.sx2» «Datatype.aNil» x0)
        («Datatype.sLam2»
          «Datatype.aH»
          x0
          «Datatype.aTl»
          («Datatype.sList» x0)
          «Datatype.aTl»));
    x1

def «Datatype.sDrop» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Datatype.sx5»
      «Datatype.aIter»
      («Datatype.sList» x0)
      («Datatype.sTail» x0)
      x1
      («Datatype.numAtom» x2);
    x3

def «Datatype.asTy» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «Typing.tAs» x0 x1; x2

def «Datatype.ofTy» :=
  fun (x0 : T) (x1 : T) => let x2 : T := «Typing.tOf» x0 x1; x2

def «Datatype.dropLast» :=
  fun (x0 : List T) =>
    let x1 : List
      T := «Datatype/Txs.reverse»
      («Datatype/Txs.tail» («Datatype/Txs.reverse» x0));
    x1

def «Datatype.allTrue» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) => «Prelude.and» x1 x2)
      (leaf 1)
      x0;
    x1

def «Datatype.ctorD» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «Datatype.dataD» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Datatype.aliasD» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «Datatype/Decls.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Datatype/Decls.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Datatype/Decls.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Datatype/Decls.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Datatype/Decls.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Datatype/Decls.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Datatype/Decls.tail» x1 x0;
    x2

def «Datatype/Decls.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Datatype/Decls.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Datatype/ODecl.nothing» := Const.node (leaf 0) ([] : List T)

def «Datatype/ODecl.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Datatype/ODecl.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Datatype/ODecl.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
    x2

def «Datatype/ODecl.nthOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.lcase
      (α := T)
      (β := T)
      (Const.iter
        (α := List T)
        (fun (x2 : List T) =>
          Const.lcase
            (α := T)
            (β := List T)
            x2
            ([] : List T)
            (fun (_ : T) (x4 : List T) => x4))
        x0
        x1)
      «Datatype/ODecl.nothing»
      (fun (x2 : T) (_ : List T) => «Datatype/ODecl.just» x2);
    x2

def «Datatype/ODecl.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Datatype.findCtor» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          let _ : T := Const.child x4 (leaf 1);
          let _ : T := Const.child x4 (leaf 2);
          let _ : T := Const.child x4 (leaf 3);
          let _ : T := Const.child x4 (leaf 4);
          let _ : T := Const.child x4 (leaf 5);
          if («Datatype.sameName» x5 x0).label ≠ 0 then
            «Datatype/ODecl.just» x2
          else
            x3
        else
          x3)
      «Datatype/ODecl.nothing»
      x1;
    x2

def «Datatype.isData» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          «Prelude.or» («Datatype.sameName» x5 x0) x3
        else
          x3)
      (leaf 0)
      x1;
    x2

def «Datatype.findAlias» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 2)).label ≠ 0 then
          let x5 : T := Const.child x4 (leaf 0);
          let x6 : T := Const.child x4 (leaf 1);
          if («Datatype.sameName» x5 x0).label ≠ 0 then
            «Datatype/OTx.just» x6
          else
            x3
        else
          x3)
      «Datatype/OTx.nothing»
      x1;
    x2

def «Datatype.ctorsOf» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := x2;
        if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
          let _ : T := Const.child x4 (leaf 0);
          let _ : T := Const.child x4 (leaf 1);
          let x7 : T := Const.child x4 (leaf 2);
          let _ : T := Const.child x4 (leaf 3);
          let _ : T := Const.child x4 (leaf 4);
          let _ : T := Const.child x4 (leaf 5);
          if («Datatype.sameName» x7 x0).label ≠ 0 then (x2 :: x3) else x3
        else
          x3)
      ([] : List T)
      x1;
    x2

def «Datatype.ctorName» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     let _ : T := Const.child x1 (leaf 1);
                     let _ : T := Const.child x1 (leaf 2);
                     let _ : T := Const.child x1 (leaf 3);
                     let _ : T := Const.child x1 (leaf 4);
                     let _ : T := Const.child x1 (leaf 5); x2
                   else
                     if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                       let x2 : T := Const.child x1 (leaf 0); x2
                     else
                       let x2 : T := Const.child x1 (leaf 0);
                       let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Datatype.ctorData» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0);
                     let _ : T := Const.child x1 (leaf 1);
                     let x4 : T := Const.child x1 (leaf 2);
                     let _ : T := Const.child x1 (leaf 3);
                     let _ : T := Const.child x1 (leaf 4);
                     let _ : T := Const.child x1 (leaf 5); x4
                   else
                     if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                       let x2 : T := Const.child x1 (leaf 0); x2
                     else
                       let x2 : T := Const.child x1 (leaf 0);
                       let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Datatype.expandAliases» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.para
      (α := Unit → T)
      (fun (x2 : T) (x3 : List (Unit → T)) (_ : Unit) =>
        if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
          let x5 : List
            T := Const.iter
            (α := List T)
            (fun (x5 : List T) =>
              Const.lcase
                (α := T)
                (β := List T)
                x5
                ([] : List T)
                (fun (_ : T) (x7 : List T) => x7))
            (Const.children x2)
            (leaf 0);
          let x6 : T := «Datatype.findAlias» («Typing.name» x5) x0;
          if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
            let x7 : T := Const.child x6 (leaf 0); x7
          else
            «Typing.tAtom» x5
        else
          if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
            let x5 : List
              T := Const.foldr
              (α := Unit → T)
              (β := List T)
              (fun (x5 : Unit → T) (x6 : List T) => ((x5 ()) :: x6))
              ([] : List T)
              x3;
            «Typing.tList» x5
          else
            «Typing.tx0»)
      x1
      ();
    x2

def «Datatype/TTs.single» :=
  fun (x0 : T × T) =>
    let x1 : List (T × T) := (x0 :: ([] : List (T × T))); x1

def «Datatype/TTs.length» :=
  fun (x0 : List (T × T)) =>
    let x1 : T := Const.foldr
      (α := T × T)
      (β := T)
      (fun (_ : T × T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Datatype/TTs.append» :=
  fun (x0 : List (T × T)) (x1 : List (T × T)) =>
    let x2 : List
      (T ×
        T) := Const.foldr
      (α := T × T)
      (β := List (T × T))
      (fun (x2 : T × T) (x3 : List (T × T)) => (x2 :: x3))
      x1
      x0;
    x2

def «Datatype/TTs.reverse» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      (T ×
        T) := Const.foldr
      (α := T × T)
      (β := List (T × T) → List (T × T))
      (fun (x1 : T × T)
         (x2 : List (T × T) → List (T × T))
         (x3 : List (T × T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (T × T)) => x1)
      x0
      ([] : List (T × T));
    x1

def «Datatype/TTs.tail» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      (T ×
        T) := Const.lcase
      (α := T × T)
      (β := List (T × T))
      x0
      ([] : List (T × T))
      (fun (_ : T × T) (x2 : List (T × T)) => x2);
    x1

def «Datatype/TTs.drop» :=
  fun (x0 : T) (x1 : List (T × T)) =>
    let x2 : List
      (T × T) := Const.iter (α := List (T × T)) «Datatype/TTs.tail» x1 x0;
    x2

def «Datatype/TTs.atOr» :=
  fun (x0 : T × T) (x1 : List (T × T)) (x2 : T) =>
    let x3 : T ×
      T := Const.lcase
      (α := T × T)
      (β := T × T)
      («Datatype/TTs.drop» x2 x1)
      x0
      (fun (x3 : T × T) (_ : List (T × T)) => x3);
    x3

def «Datatype.defaultOf» :=
  fun (x0 : T) =>
    let x1 : T := (Const.para
      (α := Unit → T × T)
      (fun (x1 : T) (x2 : List (Unit → T × T)) (_ : Unit) =>
        if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
          let x4 : List
            T := Const.iter
            (α := List T)
            (fun (x4 : List T) =>
              Const.lcase
                (α := T)
                (β := List T)
                x4
                ([] : List T)
                (fun (_ : T) (x6 : List T) => x6))
            (Const.children x1)
            (leaf 0);
          («Typing.tAtom» x4,
            if («Datatype.namedTx»
              («Typing.tAtom» x4)
              «Reader.kwUnit»).label ≠ 0 then
              «Datatype.aUnitV»
            else
              «Datatype.asTy» («Typing.tAtom» x4) «Datatype.aZero»)
        else
          if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
            let x4 : List
              (T ×
                T) := Const.foldr
              (α := Unit → T × T)
              (β := List (T × T))
              (fun (x4 : Unit → T × T) (x5 : List (T × T)) => ((x4 ()) :: x5))
              ([] : List (T × T))
              x2;
            let x5 : List
              T := Const.foldr
              (α := T × T)
              (β := List T)
              (fun (x5 : T × T) (x6 : List T) => ((x5).1 :: x6))
              ([] : List T)
              x4;
            let x6 : T →
              T := (fun (x6 : T) =>
              («Datatype/TTs.atOr» («Typing.tx0», «Datatype.aZero») x4 x6).2);
            let x7 : T := «Datatype.nthTx» x5 (leaf 0);
            («Typing.tList» x5,
              if («Datatype.namedTx» x7 «Reader.kwProd»).label ≠ 0 then
                «Datatype.sx3» «Datatype.aPair» (x6 (leaf 1)) (x6 (leaf 2))
              else
                if («Datatype.namedTx» x7 «Reader.kwArrow»).label ≠ 0 then
                  «Datatype.sLam1»
                    «Datatype.aD»
                    («Datatype.nthTx» x5 (leaf 1))
                    (x6 (leaf 2))
                else
                  if («Datatype.namedTx» x7 «Reader.kwList»).label ≠ 0 then
                    «Datatype.sx2» «Datatype.aNil» («Datatype.nthTx» x5 (leaf 1))
                  else
                    «Datatype.aZero»)
          else
            («Typing.tx0», «Datatype.aZero»))
      x0
      ()).2;
    x1

def «Datatype.bindWith» :=
  fun (x0 : T → T → T → T → T)
    (x1 : T → T → T → T → T)
    (x2 : T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : T := (let x5 : T := x2;
                   if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                     let _ : T := Const.child x5 (leaf 0);
                     let _ : T := Const.child x5 (leaf 1);
                     let _ : T := Const.child x5 (leaf 2);
                     let x9 : T := Const.child x5 (leaf 3);
                     let x10 : T := Const.child x5 (leaf 4);
                     let x11 : T := Const.child x5 (leaf 5);
                     let x12 : List T := «Datatype.elems» x9;
                     let x13 : T := «Datatype/Txs.length» x12;
                     let x14 : T := «Datatype/Txs.length» x3;
                     if («Prelude.and»
                       (Const.eq x14 (Const.add x13 x10))
                       («Datatype.allTrue»
                         (Const.foldr
                           (α := T)
                           (β := List T)
                           (fun (x15 : T) (x16 : List T) => ((«Datatype.isAtomTx» x15) :: x16))
                           ([] : List T)
                           x3))).label ≠ 0 then
                       «Datatype/OTx.just»
                         (Const.foldr
                           (α := T)
                           (β := T × T)
                           (fun (x15 : T) (x16 : T × T) =>
                             let x17 : T := Const.sub (Const.sub x14 (leaf 1)) (x16).1;
                             (Const.add (x16).1 (leaf 1),
                               if (Const.lt x17 x13).label ≠ 0 then
                                 x0 x17 («Datatype.nthTx» x12 x17) x15 (x16).2
                               else
                                 x1 x13 x11 x15 (x16).2))
                           (leaf 0, x4)
                           x3).2
                     else
                       «Datatype/OTx.nothing»
                   else
                     «Datatype/OTx.nothing»);
    x5

def «Datatype.clauseCtor» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Datatype.nthTx» («Datatype.elems» x1) (leaf 0);
                   if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
                     let x3 : List
                       T := Const.iter
                       (α := List T)
                       (fun (x3 : List T) =>
                         Const.lcase
                           (α := T)
                           (β := List T)
                           x3
                           ([] : List T)
                           (fun (_ : T) (x5 : List T) => x5))
                       (Const.children x2)
                       (leaf 0);
                     «Datatype.findCtor»
                       («Datatype.atomName» («Datatype.nthTx» x3 (leaf 0)))
                       x0
                   else
                     «Datatype/ODecl.nothing»);
    x2

def «Datatype.testChain» :=
  fun (x0 : T)
    (x1 : List (T × (T × T)))
    (x2 : T)
    (x3 : T → List T → T → T) =>
    let x4 : T := (let x4 : T ×
                     (T ×
                       T) := Const.foldr
                     (α := T × (T × T))
                     (β := T × (T × T))
                     (fun (x4 : T × (T × T)) (x5 : T × (T × T)) =>
                       let x6 : T := ((x4).2).1;
                       let x7 : T := x3
                         x6
                         («Datatype/Txs.tail»
                           («Datatype.elems»
                             («Datatype.nthTx» («Datatype.elems» (x4).1) (leaf 0))))
                         («Datatype.nthTx» («Datatype.elems» ((x4).2).2) (leaf 1));
                       if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                         let x8 : T := Const.child x7 (leaf 0);
                         if ((x5).1).label ≠ 0 then
                           (leaf 1,
                             (leaf 1,
                               if (((x5).2).1).label ≠ 0 then
                                 let x9 : T := x6;
                                 if (Const.eq (Const.label x9) (leaf 0)).label ≠ 0 then
                                   let _ : T := Const.child x9 (leaf 0);
                                   let x11 : T := Const.child x9 (leaf 1);
                                   let _ : T := Const.child x9 (leaf 2);
                                   let _ : T := Const.child x9 (leaf 3);
                                   let _ : T := Const.child x9 (leaf 4);
                                   let _ : T := Const.child x9 (leaf 5);
                                   «Datatype.sIf»
                                     («Datatype.sx3»
                                       «Datatype.aEq»
                                       («Datatype.sx2» «Datatype.aLabel» x0)
                                       («Datatype.numAtom» x11))
                                     x8
                                     ((x5).2).2
                                 else
                                   x8
                               else
                                 x8))
                         else
                           (leaf 0, (leaf 0, «Typing.tx0»))
                       else
                         (leaf 0, (leaf 0, «Typing.tx0»)))
                     (let x4 : T := x2;
                      if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                        let x5 : T := Const.child x4 (leaf 0); (leaf 1, (leaf 1, x5))
                      else
                        (leaf 1, (leaf 0, «Typing.tx0»)))
                     x1;
                   if («Prelude.and» (x4).1 ((x4).2).1).label ≠ 0 then
                     «Datatype/OTx.just» ((x4).2).2
                   else
                     «Datatype/OTx.nothing»);
    x4

def «Datatype/ODecls.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Datatype/ODecls.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Datatype/ODecls.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Datatype/ODecls.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «Datatype/ODecls.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Datatype/ODecls.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Datatype/ODecls.tail» x1 x0;
    x2

def «Datatype/ODecls.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Datatype/ODecls.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Datatype.clauseChain» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List T)
    (x3 : T × List T)
    (x4 : T)
    (x5 : T → List T → T → T) =>
    let x6 : T := (if («Prelude.and»
      (x3).1
      (Const.lt (leaf 0) («Datatype/Txs.length» x2))).label ≠ 0 then
      let x6 : List T := (x3).2;
      let x7 : T := «Datatype/Txs.length» x2;
      let x8 : T := «Datatype.nthTx» x2 (Const.sub x7 (leaf 1));
      let x9 : T := «Prelude.and»
        («Datatype.isListTx» x8)
        («Prelude.and»
          (Const.eq («Datatype/Txs.length» («Datatype.elems» x8)) (leaf 2))
          («Datatype.namedTx»
            («Datatype.nthTx» («Datatype.elems» x8) (leaf 0))
            «Datatype.kwElse»));
      let x10 : List
        T := (if (x9).label ≠ 0 then «Datatype.dropLast» x2 else x2);
      let x11 : List
        T := (if (x9).label ≠ 0 then «Datatype.dropLast» x6 else x6);
      let x12 : T := (if (x9).label ≠ 0 then
        «Datatype/OTx.just»
          («Datatype.nthTx»
            («Datatype.elems» («Datatype.nthTx» x6 (Const.sub x7 (leaf 1))))
            (leaf 1))
      else
        «Datatype/OTx.nothing»);
      let x13 : List
        T := Const.foldr
        (α := T)
        (β := List T)
        (fun (x13 : T) (x14 : List T) =>
          ((«Datatype.clauseCtor» x0 x13) :: x14))
        ([] : List T)
        x10;
      let x14 : T := (let x14 : T := x1;
                      if (Const.eq (Const.label x14) (leaf 1)).label ≠ 0 then
                        let x15 : T := Const.child x14 (leaf 0); x15
                      else
                        let x15 : T := «Datatype/ODecls.atOr»
                          «Datatype/ODecl.nothing»
                          x13
                          (leaf 0);
                        if (Const.eq (Const.label x15) (leaf 1)).label ≠ 0 then
                          let x16 : T := Const.child x15 (leaf 0); «Datatype.ctorData» x16
                        else
                          «Typing.name» ([] : List T));
      let x15 : T := «Datatype.allTrue»
        (Const.foldr
          (α := T)
          (β := List T)
          (fun (x15 : T) (x16 : List T) =>
            ((«Prelude.and»
              (Const.eq («Datatype/Txs.length» («Datatype.elems» x15)) (leaf 2))
              (let x17 : T := «Datatype.clauseCtor» x0 x15;
               if (Const.eq (Const.label x17) (leaf 1)).label ≠ 0 then
                 let x18 : T := Const.child x17 (leaf 0);
                 «Datatype.sameName» («Datatype.ctorData» x18) x14
               else
                 leaf 0)) ::
              x16))
          ([] : List T)
          x10);
      let x16 : List
        T := Const.foldr
        (α := T)
        (β := List T)
        (fun (x16 : T) (x17 : List T) =>
          let x18 : T := x16;
          if (Const.eq (Const.label x18) (leaf 1)).label ≠ 0 then
            let x19 : T := Const.child x18 (leaf 0);
            ((«Datatype.ctorName» x19) :: x17)
          else
            x17)
        ([] : List T)
        x13;
      let x17 : T := «Prelude.or»
        x9
        («Datatype.allTrue»
          (Const.foldr
            (α := T)
            (β := List T)
            (fun (x17 : T) (x18 : List T) =>
              ((Const.foldr
                (α := T)
                (β := T)
                (fun (x19 : T) (x20 : T) =>
                  «Prelude.or» («Datatype.sameName» x19 («Datatype.ctorName» x17)) x20)
                (leaf 0)
                x16) ::
                x18))
            ([] : List T)
            («Datatype.ctorsOf» x14 x0)));
      if («Prelude.and» x15 x17).label ≠ 0 then
        let x18 : T := «Datatype/Txs.length» x10;
        «Datatype.testChain»
          x4
          (Const.foldr
            (α := T)
            (β := T × List (T × (T × T)))
            (fun (x19 : T) (x20 : T × List (T × (T × T))) =>
              let x21 : T := Const.sub (Const.sub x18 (leaf 1)) (x20).1;
              (Const.add (x20).1 (leaf 1),
                let x22 : T := «Datatype/ODecls.atOr»
                  «Datatype/ODecl.nothing»
                  x13
                  x21;
                if (Const.eq (Const.label x22) (leaf 1)).label ≠ 0 then
                  let x23 : T := Const.child x22 (leaf 0);
                  ((x19, (x23, «Datatype.nthTx» x11 x21)) :: (x20).2)
                else
                  (x20).2))
            (leaf 0, ([] : List (T × (T × T))))
            x10).2
          x12
          x5
      else
        «Datatype/OTx.nothing»
    else
      «Datatype/OTx.nothing»);
    x6

def «Datatype/XRs.single» :=
  fun (x0 : T × (List T → T)) =>
    let x1 : List
      (T × (List T → T)) := (x0 :: ([] : List (T × (List T → T))));
    x1

def «Datatype/XRs.length» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : T := Const.foldr
      (α := T × (List T → T))
      (β := T)
      (fun (_ : T × (List T → T)) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Datatype/XRs.append» :=
  fun (x0 : List (T × (List T → T))) (x1 : List (T × (List T → T))) =>
    let x2 : List
      (T ×
        (List T →
          T)) := Const.foldr
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      (fun (x2 : T × (List T → T)) (x3 : List (T × (List T → T))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Datatype/XRs.reverse» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : List
      (T ×
        (List T →
          T)) := Const.foldr
      (α := T × (List T → T))
      (β := List (T × (List T → T)) → List (T × (List T → T)))
      (fun (x1 : T × (List T → T))
         (x2 : List (T × (List T → T)) → List (T × (List T → T)))
         (x3 : List (T × (List T → T))) =>
        x2 (x1 :: x3))
      (fun (x1 : List (T × (List T → T))) => x1)
      x0
      ([] : List (T × (List T → T)));
    x1

def «Datatype/XRs.tail» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : List
      (T ×
        (List T →
          T)) := Const.lcase
      (α := T × (List T → T))
      (β := List (T × (List T → T)))
      x0
      ([] : List (T × (List T → T)))
      (fun (_ : T × (List T → T)) (x2 : List (T × (List T → T))) => x2);
    x1

def «Datatype/XRs.drop» :=
  fun (x0 : T) (x1 : List (T × (List T → T))) =>
    let x2 : List
      (T ×
        (List T →
          T)) := Const.iter
      (α := List (T × (List T → T)))
      «Datatype/XRs.tail»
      x1
      x0;
    x2

def «Datatype/XRs.atOr» :=
  fun (x0 : T × (List T → T)) (x1 : List (T × (List T → T))) (x2 : T) =>
    let x3 : T ×
      (List T →
        T) := Const.lcase
      (α := T × (List T → T))
      (β := T × (List T → T))
      («Datatype/XRs.drop» x2 x1)
      x0
      (fun (x3 : T × (List T → T)) (_ : List (T × (List T → T))) => x3);
    x3

def «Datatype.xrForms» :=
  fun (x0 : List (T × (List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (List T → T))
      (β := List T)
      (fun (x1 : T × (List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Datatype.xrAt» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    let x3 : T := («Datatype/XRs.atOr»
      («Typing.tx0», fun (_ : List T) => «Datatype/OTx.nothing»)
      x0
      x1).2
      x2;
    x3

def «Datatype.xrFrom» :=
  fun (x0 : List (T × (List T → T))) (x1 : T) (x2 : List T) =>
    let x3 : T ×
      List
        T := «Datatype/OTx.allJust»
      (Const.foldr
        (α := T × (List T → T))
        (β := List T)
        (fun (x3 : T × (List T → T)) (x4 : List T) => (((x3).2 x2) :: x4))
        ([] : List T)
        («Datatype/XRs.drop» x1 x0));
    x3

def «Datatype.caseField» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Datatype.sLet»
      x2
      x1
      («Datatype.asTy»
        x1
        («Datatype.sx3»
          «Datatype.aChild»
          «Datatype.aS»
          («Datatype.numAtom» x0)))
      x3;
    x4

def «Datatype.caseRest» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Datatype.sLet»
      x2
      («Datatype.sList» x1)
      («Datatype.asTy»
        («Datatype.sList» x1)
        («Datatype.sDrop»
          «Datatype.aT»
          («Datatype.sx2» «Datatype.aChildren» «Datatype.aS»)
          x0))
      x3;
    x4

def «Datatype.expandCase» :=
  fun (x0 : List T) (x1 : List T) (x2 : List (T × (List T → T))) =>
    let x3 : T := (let x3 : List T := «Datatype/Txs.drop» (leaf 2) x1;
                   let x4 : T := «Datatype.clauseChain»
                     x0
                     «Typing/OName.nothing»
                     x3
                     («Datatype.xrFrom» x2 (leaf 2) x0)
                     «Datatype.aS»
                     («Datatype.bindWith» «Datatype.caseField» «Datatype.caseRest»);
                   let x5 : T := (let x5 : T := «Datatype.clauseCtor»
                                    x0
                                    («Datatype.nthTx» x3 (leaf 0));
                                  if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                                    let x6 : T := Const.child x5 (leaf 0);
                                    «Typing.tAtom» (Const.children («Datatype.ctorData» x6))
                                  else
                                    «Datatype.aT»);
                   let x6 : T := «Datatype.xrAt» x2 (leaf 1) x0;
                   if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
                     let x7 : T := Const.child x6 (leaf 0);
                     let x8 : T := x4;
                     if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                       let x9 : T := Const.child x8 (leaf 0);
                       «Datatype/OTx.just»
                         («Datatype.sLet»
                           «Datatype.aS»
                           «Datatype.aT»
                           («Datatype.ofTy» x5 x7)
                           x9)
                     else
                       «Datatype/OTx.nothing»
                   else
                     «Datatype/OTx.nothing»);
    x3

def «Datatype.thTy» :=
  fun (x0 : T) =>
    let x1 : T := «Datatype.sArrow» «Datatype.aUnit» x0; x1

def «Datatype.splitTy» :=
  fun (x0 : T) =>
    let x1 : T := «Datatype.sProd»
      («Datatype.thTy» x0)
      («Datatype.sList» («Datatype.thTy» x0));
    x1

def «Datatype.resultsAt» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      «Datatype.aK»
    else
      «Datatype.sx2»
        «Datatype.aSnd»
        («Datatype.qAtom» (Const.sub x0 (leaf 1))));
    x1

def «Datatype.cataField» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) (x6 : T) =>
    let x7 : T := «Datatype.sLet»
      («Datatype.qAtom» x3)
      («Datatype.splitTy» x1)
      («Datatype.sx6»
        «Datatype.aLcase»
        («Datatype.thTy» x1)
        («Datatype.splitTy» x1)
        («Datatype.resultsAt» x3)
        («Datatype.sx3»
          «Datatype.aPair»
          («Datatype.sLam1» «Datatype.aU» «Datatype.aUnit» x2)
          («Datatype.sx2» «Datatype.aNil» («Datatype.thTy» x1)))
        («Datatype.sLam2»
          «Datatype.aH»
          («Datatype.thTy» x1)
          «Datatype.aTl»
          («Datatype.sList» («Datatype.thTy» x1))
          («Datatype.sx3» «Datatype.aPair» «Datatype.aH» «Datatype.aTl»)))
      (if («Reader.named» x4 x0).label ≠ 0 then
        «Datatype.sLet»
          x5
          x1
          («Datatype.sx2»
            («Datatype.sx2» «Datatype.aFst» («Datatype.qAtom» x3))
            «Datatype.aUnitV»)
          x6
      else
        «Datatype.sLet»
          x5
          x4
          («Datatype.asTy»
            x4
            («Datatype.sx3»
              «Datatype.aChild»
              «Datatype.aO»
              («Datatype.numAtom» x3)))
          x6);
    x7

def «Datatype.cataRest» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := (if («Reader.named» x3 x0).label ≠ 0 then
      «Datatype.sLet»
        x4
        («Datatype.sList» x1)
        («Datatype.sx6»
          «Datatype.aFoldr»
          («Datatype.thTy» x1)
          («Datatype.sList» x1)
          («Datatype.sLam2»
            «Datatype.aH»
            («Datatype.thTy» x1)
            «Datatype.aA»
            («Datatype.sList» x1)
            («Datatype.sx3»
              «Datatype.aCons»
              («Datatype.sx2» «Datatype.aH» «Datatype.aUnitV»)
              «Datatype.aA»))
          («Datatype.sx2» «Datatype.aNil» x1)
          («Datatype.resultsAt» x2))
        x5
    else
      «Datatype.sLet»
        x4
        («Datatype.sList» x3)
        («Datatype.asTy»
          («Datatype.sList» x3)
          («Datatype.sDrop»
            «Datatype.aT»
            («Datatype.sx2» «Datatype.aChildren» «Datatype.aO»)
            x2))
        x5);
    x6

def «Datatype.expandCata» :=
  fun (x0 : List T) (x1 : List T) (x2 : List (T × (List T → T))) =>
    let x3 : T := (let x3 : T := «Datatype.atomName» («Datatype.nthTx» x1 (leaf 1));
                   let x4 : T := «Datatype.nthTx» x1 (leaf 2);
                   let x5 : T := (if («Prelude.and»
                     («Datatype.isAtomTx» («Datatype.nthTx» x1 (leaf 1)))
                     («Datatype.isData» x3 x0)).label ≠ 0 then
                     «Datatype.clauseChain»
                       x0
                       («Typing/OName.just» x3)
                       («Datatype/Txs.drop» (leaf 4) x1)
                       («Datatype.xrFrom» x2 (leaf 4) x0)
                       «Datatype.aO»
                       («Datatype.bindWith»
                         («Datatype.cataField»
                           x3
                           x4
                           («Datatype.defaultOf» («Datatype.expandAliases» x0 x4)))
                         («Datatype.cataRest» x3 x4))
                   else
                     «Datatype/OTx.nothing»);
                   let x6 : T := «Datatype.xrAt» x2 (leaf 3) x0;
                   if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
                     let x7 : T := Const.child x6 (leaf 0);
                     let x8 : T := x5;
                     if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                       let x9 : T := Const.child x8 (leaf 0);
                       «Datatype/OTx.just»
                         («Datatype.sx2»
                           («Datatype.sx4»
                             «Datatype.aPara»
                             («Datatype.thTy» x4)
                             («Datatype.sLam2»
                               «Datatype.aO»
                               «Datatype.aT»
                               «Datatype.aK»
                               («Datatype.sList» («Datatype.thTy» x4))
                               («Datatype.sLam1» «Datatype.aU» «Datatype.aUnit» x9))
                             («Datatype.ofTy» («Datatype.nthTx» x1 (leaf 1)) x7))
                           «Datatype.aUnitV»)
                     else
                       «Datatype/OTx.nothing»
                   else
                     «Datatype/OTx.nothing»);
    x3

def «Datatype.expandExpr» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.para
      (α := Unit → T × (List T → T))
      (fun (x2 : T) (x3 : List (Unit → T × (List T → T))) (_ : Unit) =>
        if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
          let x5 : List
            T := Const.iter
            (α := List T)
            (fun (x5 : List T) =>
              Const.lcase
                (α := T)
                (β := List T)
                x5
                ([] : List T)
                (fun (_ : T) (x7 : List T) => x7))
            (Const.children x2)
            (leaf 0);
          («Typing.tAtom» x5,
            fun (_ : List T) => «Datatype/OTx.just» («Typing.tAtom» x5))
        else
          if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
            let x5 : List
              (T ×
                (List T →
                  T)) := Const.foldr
              (α := Unit → T × (List T → T))
              (β := List (T × (List T → T)))
              (fun (x5 : Unit → T × (List T → T)) (x6 : List (T × (List T → T))) =>
                ((x5 ()) :: x6))
              ([] : List (T × (List T → T)))
              x3;
            let x6 : List T := «Datatype.xrForms» x5;
            («Typing.tList» x6,
              fun (x7 : List T) =>
                let x8 : T := «Datatype.nthTx» x6 (leaf 0);
                let x9 : T := «Datatype/XRs.length» x5;
                if («Prelude.and»
                  («Datatype.namedTx» x8 «Datatype.kwCase»)
                  (Const.lt (leaf 2) x9)).label ≠ 0 then
                  «Datatype.expandCase» x7 x6 x5
                else
                  if («Prelude.and»
                    («Datatype.namedTx» x8 «Datatype.kwCata»)
                    (Const.lt (leaf 4) x9)).label ≠ 0 then
                    «Datatype.expandCata» x7 x6 x5
                  else
                    let x10 : T × List T := «Datatype.xrFrom» x5 (leaf 0) x7;
                    if ((x10).1).label ≠ 0 then
                      «Datatype/OTx.just» («Typing.tList» (x10).2)
                    else
                      «Datatype/OTx.nothing»)
          else
            («Typing.tx0», fun (_ : List T) => «Datatype/OTx.just» «Typing.tx0»))
      x1
      ()).2
      x0;
    x2

def «Datatype.ctorDecl» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T ×
      (T ×
        T) := (let x3 : List T := «Datatype.elems» x2;
               let x4 : List T := «Datatype/Txs.tail» x3;
               let x5 : T := «Datatype/Txs.length» x4;
               let x6 : T := «Prelude.and»
                 (Const.lt (leaf 1) x5)
                 («Datatype.namedTx»
                   («Datatype.nthTx» x4 (Const.sub x5 (leaf 2)))
                   «Datatype.kwAmp»);
               let x7 : List
                 T := (if (x6).label ≠ 0 then
                 «Datatype.dropLast» («Datatype.dropLast» x4)
               else
                 x4);
               let x8 : T := «Datatype/Txs.length» x7;
               let x9 : T := (if (x6).label ≠ 0 then
                 «Datatype.nthTx» x4 (Const.sub x5 (leaf 1))
               else
                 «Typing.tx0»);
               let x10 : List
                 T := (Const.foldr
                 (α := T)
                 (β := T × List T)
                 (fun (x10 : T) (x11 : T × List T) =>
                   (Const.add (x11).1 (leaf 1),
                     ((«Datatype.sx2»
                       («Datatype.fieldAtom» (Const.sub (Const.sub x8 (leaf 1)) (x11).1))
                       x10) ::
                       (x11).2)))
                 (leaf 0, ([] : List T))
                 x7).2;
               let x11 : T := (Const.foldr
                 (α := T)
                 (β := T × T)
                 (fun (x11 : T) (x12 : T × T) =>
                   (Const.add (x12).1 (leaf 1),
                     «Datatype.sx3»
                       «Datatype.aCons»
                       («Datatype.ofTy»
                         x11
                         («Datatype.fieldAtom» (Const.sub (Const.sub x8 (leaf 1)) (x12).1)))
                       (x12).2))
                 (leaf 0,
                   if (x6).label ≠ 0 then
                     «Datatype.ofTy» («Datatype.sList» x9) «Datatype.aRest»
                   else
                     «Datatype.sx2» «Datatype.aNil» «Datatype.aT»)
                 x7).2;
               let x12 : List
                 T := (if (x6).label ≠ 0 then
                 «Datatype/Txs.append»
                   x10
                   («Datatype/Txs.single»
                     («Datatype.sx2» «Datatype.aRest» («Datatype.sList» x9)))
               else
                 x10);
               let x13 : T := «Datatype.asTy»
                 («Typing.tAtom» (Const.children x0))
                 («Datatype.sx3» «Datatype.aNode» («Datatype.numAtom» x1) x11);
               («Prelude.and»
                 («Datatype.isListTx» x2)
                 («Datatype.isAtomTx» («Datatype.nthTx» x3 (leaf 0))),
                 («Datatype.ctorD»
                   («Datatype.atomName» («Datatype.nthTx» x3 (leaf 0)))
                   x1
                   x0
                   («Typing.tList» x7)
                   x6
                   x9,
                   «Datatype.sx3»
                     «Datatype.aDef»
                     («Datatype.nthTx» x3 (leaf 0))
                     (if (Const.lt (leaf 0) («Datatype/Txs.length» x12)).label ≠ 0 then
                       «Datatype.sx3» «Datatype.aLam» («Typing.tList» x12) x13
                     else
                       x13))));
    x3

def «Datatype.dataDecl» :=
  fun (x0 : T) =>
    let x1 : T ×
      (List T ×
        List
          T) := (let x1 : List T := «Datatype.elems» x0;
                 let x2 : T := «Datatype.atomName» («Datatype.nthTx» x1 (leaf 1));
                 let x3 : List T := «Datatype/Txs.drop» (leaf 2) x1;
                 let x4 : T := «Datatype/Txs.length» x3;
                 let x5 : T ×
                   (T ×
                     (List T ×
                       List
                         T)) := Const.foldr
                   (α := T)
                   (β := T × (T × (List T × List T)))
                   (fun (x5 : T) (x6 : T × (T × (List T × List T))) =>
                     let x7 : T ×
                       (T ×
                         T) := «Datatype.ctorDecl»
                       x2
                       (Const.sub (Const.sub x4 (leaf 1)) (x6).1)
                       x5;
                     (Const.add (x6).1 (leaf 1),
                       («Prelude.and» (x7).1 ((x6).2).1,
                         ((((x7).2).1 :: (((x6).2).2).1), (((x7).2).2 :: (((x6).2).2).2)))))
                   (leaf 0, (leaf 1, (([] : List T), ([] : List T))))
                   x3;
                 («Prelude.and»
                   ((x5).2).1
                   («Datatype.isAtomTx» («Datatype.nthTx» x1 (leaf 1))),
                   (((«Datatype.dataD» x2) :: (((x5).2).2).1),
                     ((«Datatype.sx3»
                       «Datatype.aDeftype»
                       («Datatype.nthTx» x1 (leaf 1))
                       «Datatype.aT») ::
                       (((x5).2).2).2))));
    x1

def «Datatype.marker» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := «Typing.tMarker»
      (x1 ::
        (Const.foldr
          (α := T)
          (β := List T)
          (fun (x3 : T) (x4 : List T) =>
            let x5 : T := x3;
            if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
              let _ : T := Const.child x5 (leaf 0);
              let x7 : T := Const.child x5 (leaf 1);
              let _ : T := Const.child x5 (leaf 2);
              let x9 : T := Const.child x5 (leaf 3);
              let x10 : T := Const.child x5 (leaf 4);
              let x11 : T := Const.child x5 (leaf 5);
              ((Const.node
                (leaf 0)
                (x7 ::
                  ((Const.node
                    (leaf 0)
                    (Const.foldr
                      (α := T)
                      (β := List T)
                      (fun (x12 : T) (x13 : List T) =>
                        ((«Datatype.expandAliases» x0 x12) :: x13))
                      ([] : List T)
                      («Datatype.elems» x9))) ::
                    (x10 :: («Prelude.single» («Datatype.expandAliases» x0 x11)))))) ::
                x4)
            else
              x4)
          ([] : List T)
          x2));
    x3

def «Datatype.xpFail» := (leaf 0, (([] : List T), ([] : List T)))

def «Datatype.xpStep» :=
  fun (x0 : T × (List T × List T)) (x1 : T) =>
    let x2 : T ×
      (List T ×
        List
          T) := (if («Prelude.and»
      (x0).1
      («Datatype.isListTx» x1)).label ≠ 0 then
      let x2 : List T := ((x0).2).1;
      let x3 : List T := ((x0).2).2;
      let x4 : List T := «Datatype.elems» x1;
      let x5 : T := «Datatype.nthTx» x4 (leaf 0);
      let x6 : T := «Datatype/Txs.length» x4;
      if («Prelude.or»
        («Datatype.namedTx» x5 «Datatype.kwData»)
        («Datatype.namedTx» x5 «Datatype.kwTreeData»)).label ≠ 0 then
        let x7 : T × (List T × List T) := «Datatype.dataDecl» x1;
        if ((x7).1).label ≠ 0 then
          let x8 : List T := ((x7).2).1;
          let x9 : List T := ((x7).2).2;
          (leaf 1,
            («Datatype/Decls.append» x2 x8,
              «Datatype/Txs.append»
                («Datatype/Txs.reverse»
                  (if («Datatype.namedTx» x5 «Datatype.kwData»).label ≠ 0 then
                    «Datatype/Txs.append»
                      ((«Typing.tData» («Datatype.nthTx» x4 (leaf 1))) ::
                        («Datatype/Txs.tail» x9))
                      («Datatype/Txs.single»
                        («Datatype.marker» x2 («Datatype.nthTx» x4 (leaf 1)) x8))
                  else
                    x9))
                x3))
        else
          «Datatype.xpFail»
      else
        if («Prelude.and»
          («Datatype.namedTx» x5 «Datatype.kwDefn»)
          (Const.eq x6 (leaf 5))).label ≠ 0 then
          let x7 : T := «Datatype.expandExpr» x2 («Datatype.nthTx» x4 (leaf 4));
          if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
            let x8 : T := Const.child x7 (leaf 0);
            let x9 : T := «Datatype.sLet»
              «Datatype.aR»
              («Datatype.nthTx» x4 (leaf 3))
              x8
              «Datatype.aR»;
            (leaf 1,
              (x2,
                ((«Datatype.sx3»
                  «Datatype.aDef»
                  («Datatype.nthTx» x4 (leaf 1))
                  (if (Const.eq
                    («Datatype/Txs.length»
                      («Datatype.elems» («Datatype.nthTx» x4 (leaf 2))))
                    (leaf 0)).label ≠ 0 then
                    x9
                  else
                    «Datatype.sx3» «Datatype.aLam» («Datatype.nthTx» x4 (leaf 2)) x9)) ::
                  x3)))
          else
            «Datatype.xpFail»
        else
          if («Prelude.and»
            («Datatype.namedTx» x5 «Reader.kwDef»)
            (Const.eq x6 (leaf 3))).label ≠ 0 then
            let x7 : T := «Datatype.expandExpr» x2 («Datatype.nthTx» x4 (leaf 2));
            if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
              let x8 : T := Const.child x7 (leaf 0);
              (leaf 1,
                (x2,
                  ((«Datatype.sx3» «Datatype.aDef» («Datatype.nthTx» x4 (leaf 1)) x8) ::
                    x3)))
            else
              «Datatype.xpFail»
          else
            if («Prelude.and»
              («Datatype.namedTx» x5 «Reader.kwDeftype»)
              (Const.eq x6 (leaf 3))).label ≠ 0 then
              (leaf 1,
                («Datatype/Decls.append»
                  x2
                  («Datatype/Decls.single»
                    («Datatype.aliasD»
                      («Datatype.atomName» («Datatype.nthTx» x4 (leaf 1)))
                      («Datatype.expandAliases» x2 («Datatype.nthTx» x4 (leaf 2))))),
                  (x1 :: x3)))
            else
              if («Prelude.and»
                («Datatype.namedTx» x5 «Reader.kwDefnum»)
                (Const.eq x6 (leaf 3))).label ≠ 0 then
                (leaf 1, (x2, (x1 :: x3)))
              else
                «Datatype.xpFail»
    else
      «Datatype.xpFail»);
    x2

def «Datatype.genericStep» :=
  fun (x0 : T × (List T × List T)) (x1 : T) =>
    let x2 : T ×
      (List T ×
        List
          T) := (if ((x0).1).label ≠ 0 then
      let x2 : T ×
        (List T ×
          List
            T) := Const.foldr
        (α := T)
        (β := (T × (List T × List T)) → T × (List T × List T))
        (fun (x2 : T)
           (x3 : (T × (List T × List T)) → T × (List T × List T))
           (x4 : T × (List T × List T)) =>
          x3
            (if («Prelude.and» (x4).1 («Datatype.isListTx» x2)).label ≠ 0 then
              let x5 : T := «Datatype.nthTx» («Datatype.elems» x2) (leaf 0);
              if («Prelude.or»
                («Datatype.namedTx» x5 «Datatype.kwSort»)
                («Datatype.namedTx» x5 «Datatype.kwPostulate»)).label ≠ 0 then
                (leaf 1, (((x4).2).1, (x2 :: ((x4).2).2)))
              else
                if («Datatype.namedTx» x5 «Datatype.kwGeneric»).label ≠ 0 then
                  «Datatype.xpFail»
                else
                  «Datatype.xpStep» x4 x2
            else
              «Datatype.xpFail»))
        (fun (x2 : T × (List T × List T)) => x2)
        («Datatype/Txs.tail» («Datatype.elems» x1))
        (leaf 1, (((x0).2).1, ([] : List T)));
      if ((x2).1).label ≠ 0 then
        (leaf 1,
          (((x0).2).1,
            ((«Typing.tGeneric» («Datatype/Txs.reverse» ((x2).2).2)) ::
              ((x0).2).2)))
      else
        «Datatype.xpFail»
    else
      x0);
    x2

def «Datatype.expandTyped» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := (let x1 : T ×
                (List T ×
                  List
                    T) := Const.foldr
                (α := T)
                (β := (T × (List T × List T)) → T × (List T × List T))
                (fun (x1 : T)
                   (x2 : (T × (List T × List T)) → T × (List T × List T))
                   (x3 : T × (List T × List T)) =>
                  x2
                    (if («Prelude.and»
                      («Datatype.isListTx» x1)
                      («Datatype.namedTx»
                        («Datatype.nthTx» («Datatype.elems» x1) (leaf 0))
                        «Datatype.kwGeneric»)).label ≠ 0 then
                      «Datatype.genericStep» x3 x1
                    else
                      «Datatype.xpStep» x3 x1))
                (fun (x1 : T × (List T × List T)) => x1)
                x0
                (leaf 1, (([] : List T), ([] : List T)));
              ((x1).1, «Datatype/Txs.reverse» ((x1).2).2));
    x1

def «Datatype.eraseExpr» :=
  fun (x0 : T) =>
    let x1 : T := Const.para
      (α := Unit → T)
      (fun (x1 : T) (x2 : List (Unit → T)) (_ : Unit) =>
        if (Const.eq (Const.label x1) (leaf 11)).label ≠ 0 then
          let x4 : (Unit → T) ×
            List
              (Unit →
                T) := Const.lcase
            (α := Unit → T)
            (β := (Unit → T) × List (Unit → T))
            x2
            (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
            (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
          let _ : T := (x4).1 ();
          let x6 : (Unit → T) ×
            List
              (Unit →
                T) := Const.lcase
            (α := Unit → T)
            (β := (Unit → T) × List (Unit → T))
            (x4).2
            (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
            (fun (x6 : Unit → T) (x7 : List (Unit → T)) => (x6, x7));
          let x7 : T := (x6).1 (); x7
        else
          if (Const.eq (Const.label x1) (leaf 12)).label ≠ 0 then
            let x4 : (Unit → T) ×
              List
                (Unit →
                  T) := Const.lcase
              (α := Unit → T)
              (β := (Unit → T) × List (Unit → T))
              x2
              (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
              (fun (x4 : Unit → T) (x5 : List (Unit → T)) => (x4, x5));
            let _ : T := (x4).1 ();
            let x6 : (Unit → T) ×
              List
                (Unit →
                  T) := Const.lcase
              (α := Unit → T)
              (β := (Unit → T) × List (Unit → T))
              (x4).2
              (fun (_ : Unit) => leaf 0, ([] : List (Unit → T)))
              (fun (x6 : Unit → T) (x7 : List (Unit → T)) => (x6, x7));
            let x7 : T := (x6).1 (); x7
          else
            if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
              let x4 : List
                T := Const.iter
                (α := List T)
                (fun (x4 : List T) =>
                  Const.lcase
                    (α := T)
                    (β := List T)
                    x4
                    ([] : List T)
                    (fun (_ : T) (x6 : List T) => x6))
                (Const.children x1)
                (leaf 0);
              «Typing.tAtom» x4
            else
              if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                let x4 : List
                  T := Const.foldr
                  (α := Unit → T)
                  (β := List T)
                  (fun (x4 : Unit → T) (x5 : List T) => ((x4 ()) :: x5))
                  ([] : List T)
                  x2;
                let x5 : T := «Datatype/Txs.length» x4;
                let x6 : T := «Datatype.nthTx» x4 (leaf 0);
                if («Prelude.and»
                  («Datatype.namedTx» x6 «Datatype.kwRep»)
                  (Const.eq x5 (leaf 2))).label ≠ 0 then
                  «Datatype.nthTx» x4 (leaf 1)
                else
                  if («Prelude.and»
                    («Datatype.namedTx» x6 «Datatype.kwDecode»)
                    (Const.eq x5 (leaf 5))).label ≠ 0 then
                    «Datatype.sLet»
                      «Datatype.aE»
                      «Datatype.aT»
                      («Datatype.nthTx» x4 (leaf 2))
                      («Datatype.sIf»
                        («Datatype.sx2»
                          («Datatype.memberAtom» («Datatype.nthTx» x4 (leaf 1)))
                          «Datatype.aE»)
                        («Datatype.sx2» («Datatype.nthTx» x4 (leaf 3)) «Datatype.aE»)
                        («Datatype.nthTx» x4 (leaf 4)))
                  else
                    if («Prelude.and»
                      («Datatype.namedTx» x6 «Datatype.kwDatum»)
                      (Const.eq x5 (leaf 3))).label ≠ 0 then
                      «Datatype.sx2» «Datatype.aQuote» («Datatype.nthTx» x4 (leaf 2))
                    else
                      «Typing.tList» x4
              else
                «Typing.tx0»)
      x0
      ();
    x1

def «Datatype.eraseForm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 10)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     «Datatype.sx3» «Datatype.aDeftype» x2 «Datatype.aT»
                   else
                     if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                       let x2 : List
                         T := Const.iter
                         (α := List T)
                         (fun (x2 : List T) =>
                           Const.lcase
                             (α := T)
                             (β := List T)
                             x2
                             ([] : List T)
                             (fun (_ : T) (x4 : List T) => x4))
                         (Const.children x1)
                         (leaf 0);
                       if («Prelude.and»
                         (Const.eq («Datatype/Txs.length» x2) (leaf 3))
                         («Datatype.namedTx»
                           («Datatype.nthTx» x2 (leaf 0))
                           «Reader.kwDef»)).label ≠ 0 then
                         «Datatype.sx3»
                           («Datatype.nthTx» x2 (leaf 0))
                           («Datatype.nthTx» x2 (leaf 1))
                           («Datatype.eraseExpr» («Datatype.nthTx» x2 (leaf 2)))
                       else
                         x0
                     else
                       x0);
    x1

def «Datatype.expandChecked» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T × List T := «Datatype.expandTyped» x0;
                   if ((x1).1).label ≠ 0 then
                     let x2 : T := «Typing.checkForms» (x1).2;
                     if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                       let _ : T := Const.child x2 (leaf 0); «Datatype/OTx.nothing»
                     else
                       «Datatype/OTx.just»
                         («Typing.tList»
                           (Const.foldr
                             (α := T)
                             (β := List T)
                             (fun (x3 : T) (x4 : List T) =>
                               let x5 : T := x3;
                               if (Const.eq (Const.label x5) (leaf 15)).label ≠ 0 then
                                 let _ : List
                                   T := Const.iter
                                   (α := List T)
                                   (fun (x6 : List T) =>
                                     Const.lcase
                                       (α := T)
                                       (β := List T)
                                       x6
                                       ([] : List T)
                                       (fun (_ : T) (x8 : List T) => x8))
                                   (Const.children x5)
                                   (leaf 0);
                                 x4
                               else
                                 ((«Datatype.eraseForm» x3) :: x4))
                             ([] : List T)
                             (x1).2))
                   else
                     «Datatype/OTx.nothing»);
    x1

def «Datatype.expandProgram» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T := Const.node (leaf 2) x0;
                   if («Typing.Tx.member» x1).label ≠ 0 then
                     let x2 : T := x1;
                     let x3 : T := «Datatype.expandChecked» («Datatype.elems» x2);
                     if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
                       let x4 : T := Const.child x3 (leaf 0);
                       «Prelude.some» (Const.node (leaf 0) (Const.children x4))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x1

def «Datatype.typeErrorOfForms» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T := Const.node (leaf 2) x0;
                   if («Typing.Tx.member» x1).label ≠ 0 then
                     let x2 : T := x1;
                     let x3 : T × List T := «Datatype.expandTyped» («Datatype.elems» x2);
                     if ((x3).1).label ≠ 0 then
                       let x4 : T := «Typing.checkForms» (x3).2;
                       if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                         let x5 : T := Const.child x4 (leaf 0); x5
                       else
                         Const.node (leaf 0) ([] : List T)
                     else
                       Const.node (leaf 0) ([] : List T)
                   else
                     Const.node (leaf 0) ([] : List T));
    x1

def «Datatype.typeErrorOf» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Reader.readSExps» (Const.children x0);
                   if («Prelude.isSome» x1).label ≠ 0 then
                     «Datatype.typeErrorOfForms» (Const.children («Prelude.get» x1))
                   else
                     Const.node (leaf 0) ([] : List T));
    x1

def «Modules.kwModule» :=
  mk 0 [leaf 109, leaf 111, leaf 100, leaf 117, leaf 108, leaf 101]

def «Modules.kwParameter» :=
  mk 0 [leaf 112,
    leaf 97,
    leaf 114,
    leaf 97,
    leaf 109,
    leaf 101,
    leaf 116,
    leaf 101,
    leaf 114]

def «Modules.kwImport» :=
  mk 0 [leaf 105, leaf 109, leaf 112, leaf 111, leaf 114, leaf 116]

def «Modules.kwExport» :=
  mk 0 [leaf 101, leaf 120, leaf 112, leaf 111, leaf 114, leaf 116]

def «Modules.kwInterface» :=
  mk 0 [leaf 105,
    leaf 110,
    leaf 116,
    leaf 101,
    leaf 114,
    leaf 102,
    leaf 97,
    leaf 99,
    leaf 101]

def «Modules.kwAs» := mk 0 [leaf 97, leaf 115]

def «Modules.moduleKeywords» :=
  («Modules.kwModule» ::
    («Modules.kwParameter» ::
      («Modules.kwImport» ::
        («Modules.kwExport» :: («Prelude.single» «Modules.kwInterface»)))))

def «Modules.concat» :=
  fun (x0 : List (List T)) =>
    Const.foldr
      (α := List T)
      (β := List T)
      «Prelude.append»
      ([] : List T)
      x0

def «Modules.mkList» := fun (x0 : List T) => Const.node (leaf 2) x0

def «Modules.atomOf» :=
  fun (x0 : T) => Const.node (leaf 1) (Const.children x0)

def «Modules.nameCat» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node
      (leaf 0)
      («Prelude.append» (Const.children x0) (x1 :: (Const.children x2)))

def «Modules.hasDot» :=
  fun (x0 : T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) => «Prelude.or» (Const.eq x1 (leaf 46)) x2)
      (leaf 0)
      (Const.children x0)

def «Modules.flatName» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «Reader.lookupAbbrev» x1 x0;
    if («Prelude.isSome» x2).label ≠ 0 then
      «Prelude.get» x2
    else
      if («Modules.hasDot» x1).label ≠ 0 then «Reader.kwHole» else x1

def «Modules.boundBy» :=
  fun (x0 : T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) =>
        if («Reader.nonEmpty» (Const.children x1)).label ≠ 0 then
          if («Reader.isAtom» (Const.child x1 (leaf 0))).label ≠ 0 then
            ((«Reader.nameOf» (Const.child x1 (leaf 0))) :: x2)
          else
            x2
        else
          x2)
      ([] : List T)
      («Reader.binders» x0)

def «Modules.patternVars» :=
  fun (x0 : T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) =>
        if («Reader.isAtom» x1).label ≠ 0 then
          ((«Reader.nameOf» x1) :: x2)
        else
          x2)
      ([] : List T)
      («Prelude.drop» (leaf 1) (Const.children x0))

def «Modules.renPattern» :=
  fun (x0 : List T) (x1 : T) =>
    Const.lcase
      (α := T)
      (β := T)
      (Const.children x1)
      x1
      (fun (x2 : T) (x3 : List T) =>
        «Modules.mkList»
          ((if («Reader.isAtom» x2).label ≠ 0 then
            «Modules.atomOf» («Modules.flatName» x0 («Reader.nameOf» x2))
          else
            Const.node (leaf 1) ([] : List T)) ::
            x3))

def «Modules.rkDrop» :=
  fun (x0 : T) (x1 : List (T → List T → T)) =>
    Const.iter
      (α := List (T → List T → T))
      (fun (x2 : List (T → List T → T)) =>
        Const.lcase
          (α := T → List T → T)
          (β := List (T → List T → T))
          x2
          x2
          (fun (_ : T → List T → T) (x4 : List (T → List T → T)) => x4))
      x1
      x0

def «Modules.rkAt» :=
  fun (x0 : List (T → List T → T)) (x1 : T) (x2 : T) (x3 : List T) =>
    Const.lcase
      (α := T → List T → T)
      (β := T → List T → T)
      («Modules.rkDrop» x1 x0)
      (fun (_ : T) (_ : List T) => leaf 0)
      (fun (x4 : T → List T → T) (_ : List (T → List T → T)) => x4)
      x2
      x3

def «Modules.rkAll» :=
  fun (x0 : List (T → List T → T)) (x1 : T) (x2 : List T) =>
    Const.foldr
      (α := T → List T → T)
      (β := List T)
      (fun (x3 : T → List T → T) (x4 : List T) => ((x3 x1 x2) :: x4))
      ([] : List T)
      x0

def «Modules.renTermList» :=
  fun (_ : List T)
    (x1 : T)
    (x2 : List (T → List T → T))
    (x3 : List T) =>
    let x4 : List T := Const.children x1;
    let x5 : T := Const.arity x1;
    let x6 : T := «Prelude.at» x4 (leaf 0);
    if (Const.eq x5 (leaf 0)).label ≠ 0 then
      x1
    else
      if («Prelude.or»
        («Reader.named» x6 «Reader.kwQuote»)
        («Reader.named» x6 «Reader.kwHole»)).label ≠ 0 then
        x1
      else
        if («Reader.named» x6 «Datatype.kwDatum»).label ≠ 0 then
          if (Const.eq x5 (leaf 3)).label ≠ 0 then
            «Modules.mkList»
              (x6 ::
                ((«Modules.rkAt» x2 (leaf 1) (leaf 1) ([] : List T)) ::
                  («Prelude.single» («Prelude.at» x4 (leaf 2)))))
          else
            x1
        else
          if («Reader.named» x6 «Datatype.kwDecode»).label ≠ 0 then
            if (Const.lt (leaf 1) x5).label ≠ 0 then
              «Modules.mkList»
                (x6 ::
                  ((«Modules.rkAt» x2 (leaf 1) (leaf 1) ([] : List T)) ::
                    («Modules.rkAll» («Modules.rkDrop» (leaf 2) x2) (leaf 0) x3)))
            else
              x1
          else
            if («Reader.named» x6 «Reader.kwLam»).label ≠ 0 then
              if (Const.eq x5 (leaf 3)).label ≠ 0 then
                «Modules.mkList»
                  (x6 ::
                    ((«Modules.rkAt» x2 (leaf 1) (leaf 3) ([] : List T)) ::
                      («Prelude.single»
                        («Modules.rkAt»
                          x2
                          (leaf 2)
                          (leaf 0)
                          («Prelude.append»
                            («Modules.boundBy» («Prelude.at» x4 (leaf 1)))
                            x3)))))
              else
                x1
            else
              if («Reader.named» x6 «Reader.kwLet»).label ≠ 0 then
                if (Const.eq x5 (leaf 5)).label ≠ 0 then
                  let x7 : T := «Prelude.at» x4 (leaf 1);
                  «Modules.mkList»
                    (x6 ::
                      (x7 ::
                        ((«Modules.rkAt» x2 (leaf 2) (leaf 1) ([] : List T)) ::
                          ((«Modules.rkAt» x2 (leaf 3) (leaf 0) x3) ::
                            («Prelude.single»
                              («Modules.rkAt»
                                x2
                                (leaf 4)
                                (leaf 0)
                                (if («Reader.isAtom» x7).label ≠ 0 then
                                  ((«Reader.nameOf» x7) :: x3)
                                else
                                  x3)))))))
                else
                  x1
              else
                if («Reader.named» x6 «Reader.kwNil»).label ≠ 0 then
                  «Modules.mkList»
                    (x6 ::
                      («Modules.rkAll»
                        («Modules.rkDrop» (leaf 1) x2)
                        (leaf 1)
                        ([] : List T)))
                else
                  if («Prelude.or»
                    («Reader.named» x6 «Reader.kwFold»)
                    («Prelude.or»
                      («Reader.named» x6 «Reader.kwPara»)
                      («Reader.named» x6 «Reader.kwIter»))).label ≠ 0 then
                    if (Const.lt (leaf 1) x5).label ≠ 0 then
                      «Modules.mkList»
                        (x6 ::
                          ((«Modules.rkAt» x2 (leaf 1) (leaf 1) ([] : List T)) ::
                            («Modules.rkAll» («Modules.rkDrop» (leaf 2) x2) (leaf 0) x3)))
                    else
                      x1
                  else
                    if («Prelude.or»
                      («Reader.named» x6 «Reader.kwFoldr»)
                      («Reader.named» x6 «Reader.kwLcase»)).label ≠ 0 then
                      if (Const.lt (leaf 2) x5).label ≠ 0 then
                        «Modules.mkList»
                          (x6 ::
                            ((«Modules.rkAt» x2 (leaf 1) (leaf 1) ([] : List T)) ::
                              ((«Modules.rkAt» x2 (leaf 2) (leaf 1) ([] : List T)) ::
                                («Modules.rkAll» («Modules.rkDrop» (leaf 3) x2) (leaf 0) x3))))
                      else
                        x1
                    else
                      if («Reader.named» x6 «Datatype.kwCase»).label ≠ 0 then
                        if (Const.lt (leaf 1) x5).label ≠ 0 then
                          «Modules.mkList»
                            (x6 ::
                              ((«Modules.rkAt» x2 (leaf 1) (leaf 0) x3) ::
                                («Modules.rkAll» («Modules.rkDrop» (leaf 2) x2) (leaf 2) x3)))
                        else
                          x1
                      else
                        if («Reader.named» x6 «Datatype.kwCata»).label ≠ 0 then
                          if (Const.lt (leaf 3) x5).label ≠ 0 then
                            «Modules.mkList»
                              (x6 ::
                                ((«Modules.rkAt» x2 (leaf 1) (leaf 1) ([] : List T)) ::
                                  ((«Modules.rkAt» x2 (leaf 2) (leaf 1) ([] : List T)) ::
                                    ((«Modules.rkAt» x2 (leaf 3) (leaf 0) x3) ::
                                      («Modules.rkAll»
                                        («Modules.rkDrop» (leaf 4) x2)
                                        (leaf 2)
                                        x3)))))
                          else
                            x1
                        else
                          «Modules.mkList» («Modules.rkAll» x2 (leaf 0) x3)

def «Modules.renStep» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T → List T → T))
    (x3 : T)
    (x4 : List T) =>
    let x5 : List T := Const.children x1;
    let x6 : T := Const.arity x1;
    if (Const.eq x3 (leaf 4)).label ≠ 0 then
      x1
    else
      if («Reader.isAtom» x1).label ≠ 0 then
        if (Const.eq x3 (leaf 1)).label ≠ 0 then
          «Modules.atomOf» («Modules.flatName» x0 («Reader.nameOf» x1))
        else
          if (Const.eq x3 (leaf 0)).label ≠ 0 then
            if («Prelude.isSome»
              («Reader.indexOf» («Reader.nameOf» x1) x4)).label ≠ 0 then
              x1
            else
              «Modules.atomOf» («Modules.flatName» x0 («Reader.nameOf» x1))
          else
            x1
      else
        if (Const.eq x3 (leaf 1)).label ≠ 0 then
          «Modules.mkList» («Modules.rkAll» x2 (leaf 1) ([] : List T))
        else
          if (Const.eq x3 (leaf 3)).label ≠ 0 then
            if (Const.eq x6 (leaf 0)).label ≠ 0 then
              x1
            else
              if («Reader.isAtom» («Prelude.at» x5 (leaf 0))).label ≠ 0 then
                «Modules.mkList»
                  ((«Prelude.at» x5 (leaf 0)) ::
                    («Modules.rkAll»
                      («Modules.rkDrop» (leaf 1) x2)
                      (leaf 1)
                      ([] : List T)))
              else
                «Modules.mkList» («Modules.rkAll» x2 (leaf 3) ([] : List T))
          else
            if (Const.eq x3 (leaf 2)).label ≠ 0 then
              if (Const.eq x6 (leaf 2)).label ≠ 0 then
                let x7 : T := «Prelude.at» x5 (leaf 0);
                if («Reader.isAtom» x7).label ≠ 0 then
                  «Modules.mkList»
                    (x7 :: («Prelude.single» («Modules.rkAt» x2 (leaf 1) (leaf 0) x4)))
                else
                  «Modules.mkList»
                    ((«Modules.renPattern» x0 x7) ::
                      («Prelude.single»
                        («Modules.rkAt»
                          x2
                          (leaf 1)
                          (leaf 0)
                          («Prelude.append» («Modules.patternVars» x7) x4))))
              else
                x1
            else
              «Modules.renTermList» x0 x1 x2 x4

def «Modules.rename» :=
  fun (x0 : List T) (x1 : T) (x2 : T) (x3 : List T) =>
    Const.para
      (α := T → List T → T)
      (fun (x4 : T) (x5 : List (T → List T → T)) (x6 : T) (x7 : List T) =>
        «Modules.renStep» x0 x4 x5 x6 x7)
      x1
      x2
      x3

def «Modules.mkSt» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T) =>
    (leaf 1, (x0, (x1, (x2, (x3, (x4, x5))))))

def «Modules.stFail» :=
  (leaf 0,
    («Modules.mkSt»
      ([] : List T)
      ([] : List T)
      ([] : List T)
      ([] : List T)
      ([] : List T)
      ([] : List T)).2)

def «Modules.stVis» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    ((x0).2).1

def «Modules.stOut» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    (((x0).2).2).1

def «Modules.stReg» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    ((((x0).2).2).2).1

def «Modules.stEx» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    (((((x0).2).2).2).2).1

def «Modules.stMem» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    ((((((x0).2).2).2).2).2).1

def «Modules.stMods» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    ((((((x0).2).2).2).2).2).2

def «Modules.withVis» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : List T) =>
    if ((x0).1).label ≠ 0 then
      «Modules.mkSt»
        x1
        («Modules.stOut» x0)
        («Modules.stReg» x0)
        («Modules.stEx» x0)
        («Modules.stMem» x0)
        («Modules.stMods» x0)
    else
      x0

def «Modules.emitTo» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : T)
    (x2 : List T) =>
    if ((x0).1).label ≠ 0 then
      «Modules.mkSt»
        («Modules.stVis» x0)
        («Prelude.append» («Modules.stOut» x0) («Prelude.single» x1))
        («Modules.stReg» x0)
        («Modules.stEx» x0)
        («Prelude.append» («Modules.stMem» x0) x2)
        («Modules.stMods» x0)
    else
      x0

def «Modules.memberDecl» :=
  fun (x0 : T) => Const.node (leaf 0) («Prelude.single» x0)

def «Modules.memberSub» :=
  fun (x0 : T) => Const.node (leaf 1) («Prelude.single» x0)

def «Modules.modNode» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    Const.node
      (leaf 0)
      (x0 ::
        ((Const.node (leaf 0) x1) ::
          («Prelude.single» (Const.node (leaf 0) x2))))

def «Modules.qualify» :=
  fun (x0 : T) (x1 : T) =>
    if («Reader.nonEmpty» (Const.children x0)).label ≠ 0 then
      «Modules.nameCat» x0 (leaf 46) x1
    else
      x1

def «Modules.declare» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : T)
    (x2 : T) =>
    if ((x0).1).label ≠ 0 then
      if («Prelude.isSome»
        («Reader.lookupAbbrev» x1 («Modules.stVis» x0))).label ≠ 0 then
        «Modules.stFail»
      else
        if («Prelude.isSome»
          («Reader.indexOf» x1 «Reader.reservedNames»)).label ≠ 0 then
          «Modules.stFail»
        else
          if («Prelude.isSome»
            («Reader.indexOf» x1 «Modules.moduleKeywords»)).label ≠ 0 then
            «Modules.stFail»
          else
            «Modules.withVis»
              x0
              («Prelude.append»
                («Modules.stVis» x0)
                («Prelude.single» («Reader.node2» (leaf 0) x1 x2)))
    else
      x0

def «Modules.declareAll» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := (T ×
        (List T × (List T × (List T × (List T × (List T × List T)))))) →
        T × (List T × (List T × (List T × (List T × (List T × List T))))))
      (fun (x2 : T)
         (x3 : (T ×
           (List T × (List T × (List T × (List T × (List T × List T)))))) →
           T × (List T × (List T × (List T × (List T × (List T × List T))))))
         (x4 : T ×
           (List T × (List T × (List T × (List T × (List T × List T)))))) =>
        x3
          («Modules.declare»
            x4
            (Const.child x2 (leaf 0))
            (Const.child x2 (leaf 1))))
      (fun (x2 : T ×
           (List T × (List T × (List T × (List T × (List T × List T)))))) =>
        x2)
      x1
      x0

def «Modules.exportsOf» :=
  fun (x0 : T ×
      (List T × (List T × (List T × (List T × (List T × List T)))))) =>
    «Reader.allSome»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x1 : T) (x2 : List T) =>
          ((let x3 : T := «Reader.lookupAbbrev» x1 («Modules.stVis» x0);
            if («Prelude.isSome» x3).label ≠ 0 then
              «Prelude.some» («Reader.node2» (leaf 0) x1 («Prelude.get» x3))
            else
              «Prelude.none») ::
            x2))
        ([] : List T)
        («Modules.stEx» x0))

def «Modules.headed» :=
  fun (x0 : T) (x1 : T) =>
    if («Reader.isList» x1).label ≠ 0 then
      if («Reader.nonEmpty» (Const.children x1)).label ≠ 0 then
        «Reader.named» (Const.child x1 (leaf 0)) x0
      else
        leaf 0
    else
      leaf 0

def «Modules.withHead» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        if («Modules.headed» x0 x2).label ≠ 0 then (x2 :: x3) else x3)
      ([] : List T)
      x1

def «Modules.withoutHead» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        if («Modules.headed» x0 x2).label ≠ 0 then x3 else (x2 :: x3))
      ([] : List T)
      x1

def «Modules.atomNames» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) =>
        if («Reader.isAtom» x1).label ≠ 0 then
          ((«Reader.nameOf» x1) :: x2)
        else
          x2)
      ([] : List T)
      x0

def «Modules.aDeftypeM» :=
  mk 1 [leaf 100,
    leaf 101,
    leaf 102,
    leaf 116,
    leaf 121,
    leaf 112,
    leaf 101]

def «Modules.aDefM» := mk 1 [leaf 100, leaf 101, leaf 102]

def «Modules.aLetM» := mk 1 [leaf 108, leaf 101, leaf 116]

def «Modules.aLamM» := mk 1 [leaf 108, leaf 97, leaf 109]

def «Modules.aResultM» := mk 1 [leaf 37, leaf 114]

def «Modules.paramVar» :=
  fun (x0 : T) =>
    Const.node
      (leaf 1)
      ((leaf 37) :: ((leaf 109) :: («Datatype.decimalChars» x0)))

def «Modules.paramVars» :=
  fun (x0 : List T) =>
    (Const.foldr
      (α := T)
      (β := T × List T)
      (fun (_ : T) (x2 : T × List T) =>
        (Const.sub (x2).1 (leaf 1),
          ((«Modules.paramVar» (Const.sub (x2).1 (leaf 1))) :: (x2).2)))
      («Prelude.length» x0, ([] : List T))
      x0).2

def «Modules.zipWith2» :=
  fun (x0 : T → T → T) (x1 : List T) (x2 : List T) =>
    (Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x3 : T) (x4 : T × List T) =>
        (Const.sub (x4).1 (leaf 1),
          ((x0 x3 («Prelude.at» x2 (Const.sub (x4).1 (leaf 1)))) :: (x4).2)))
      («Prelude.length» x1, ([] : List T))
      x1).2

def «Modules.bindParam» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x3 : T)
    (x4 : T) =>
    if (if ((x2).1).label ≠ 0 then
      Const.eq (Const.arity x3) (leaf 2)
    else
      leaf 0).label ≠ 0 then
      let x5 : T := Const.child x3 (leaf 1);
      if («Reader.isAtom» x5).label ≠ 0 then
        let x6 : T := «Modules.qualify» x0 («Reader.nameOf» x5);
        «Modules.emitTo»
          («Modules.declare» x2 («Reader.nameOf» x5) x6)
          («Modules.mkList»
            («Modules.aDeftypeM» ::
              ((«Modules.atomOf» x6) ::
                («Prelude.single» («Modules.rename» x1 x4 (leaf 1) ([] : List T))))))
          ([] : List T)
      else
        if (if (Const.eq (Const.arity x5) (leaf 3)).label ≠ 0 then
          «Reader.isAtom» (Const.child x5 (leaf 0))
        else
          leaf 0).label ≠ 0 then
          let x6 : T := «Reader.nameOf» (Const.child x5 (leaf 0));
          let x7 : T := «Modules.qualify» x0 x6;
          let x8 : List T := Const.children (Const.child x5 (leaf 1));
          let x9 : List T := «Modules.paramVars» x8;
          let x10 : T := «Modules.rename» x1 x4 (leaf 0) ([] : List T);
          let x11 : T := (if («Reader.nonEmpty» x9).label ≠ 0 then
            «Modules.mkList» (x10 :: x9)
          else
            x10);
          let x12 : T := «Modules.mkList»
            («Modules.aLetM» ::
              («Modules.aResultM» ::
                ((«Modules.rename»
                  («Modules.stVis» x2)
                  (Const.child x5 (leaf 2))
                  (leaf 1)
                  ([] : List T)) ::
                  (x11 :: («Prelude.single» «Modules.aResultM»)))));
          let x13 : T := (if («Reader.nonEmpty» x9).label ≠ 0 then
            «Modules.mkList»
              («Modules.aLamM» ::
                ((«Modules.mkList»
                  («Modules.zipWith2»
                    (fun (x13 : T) (x14 : T) =>
                      «Modules.mkList»
                        (x14 ::
                          («Prelude.single»
                            («Modules.rename» («Modules.stVis» x2) x13 (leaf 1) ([] : List T)))))
                    x8
                    x9)) ::
                  («Prelude.single» x12)))
          else
            x12);
          «Modules.emitTo»
            («Modules.declare» x2 x6 x7)
            («Modules.mkList»
              («Modules.aDefM» ::
                ((«Modules.atomOf» x7) :: («Prelude.single» x13))))
            («Prelude.single» («Modules.memberDecl» x7))
        else
          «Modules.stFail»
    else
      «Modules.stFail»

def «Modules.elabDecl» :=
  fun (x0 : T)
    (x1 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x2 : T) =>
    let x3 : List T := Const.children x2;
    let x4 : T := Const.arity x2;
    let x5 : T := «Prelude.at» x3 (leaf 0);
    let x6 : T := «Prelude.at» x3 (leaf 1);
    if (if (Const.lt (leaf 1) x4).label ≠ 0 then
      «Reader.isAtom» x6
    else
      leaf 0).label ≠ 0 then
      let x7 : T := «Reader.nameOf» x6;
      let x8 : T := «Modules.qualify» x0 x7;
      let x9 : List T := «Modules.stVis» x1;
      let x10 : List T →
        T := (fun (x10 : List T) =>
        «Modules.mkList» (x5 :: ((«Modules.atomOf» x8) :: x10)));
      if («Reader.named» x5 «Reader.kwDef»).label ≠ 0 then
        if (Const.eq x4 (leaf 3)).label ≠ 0 then
          «Modules.emitTo»
            («Modules.declare» x1 x7 x8)
            (x10
              («Prelude.single»
                («Modules.rename»
                  x9
                  («Prelude.at» x3 (leaf 2))
                  (leaf 0)
                  ([] : List T))))
            («Prelude.single» («Modules.memberDecl» x8))
        else
          «Modules.stFail»
      else
        if («Prelude.or»
          («Reader.named» x5 «Reader.kwDeftype»)
          («Reader.named» x5 «Reader.kwDefnum»)).label ≠ 0 then
          if (Const.eq x4 (leaf 3)).label ≠ 0 then
            «Modules.emitTo»
              («Modules.declare» x1 x7 x8)
              (x10
                («Prelude.single»
                  («Modules.rename»
                    x9
                    («Prelude.at» x3 (leaf 2))
                    (leaf 1)
                    ([] : List T))))
              ([] : List T)
          else
            «Modules.stFail»
        else
          if («Reader.named» x5 «Datatype.kwDefn»).label ≠ 0 then
            if (Const.eq x4 (leaf 5)).label ≠ 0 then
              «Modules.emitTo»
                («Modules.declare» x1 x7 x8)
                (x10
                  ((«Modules.rename»
                    x9
                    («Prelude.at» x3 (leaf 2))
                    (leaf 3)
                    ([] : List T)) ::
                    ((«Modules.rename»
                      x9
                      («Prelude.at» x3 (leaf 3))
                      (leaf 1)
                      ([] : List T)) ::
                      («Prelude.single»
                        («Modules.rename»
                          x9
                          («Prelude.at» x3 (leaf 4))
                          (leaf 0)
                          («Modules.boundBy» («Prelude.at» x3 (leaf 2))))))))
                («Prelude.single» («Modules.memberDecl» x8))
            else
              «Modules.stFail»
          else
            if («Prelude.or»
              («Reader.named» x5 «Datatype.kwData»)
              («Reader.named» x5 «Datatype.kwTreeData»)).label ≠ 0 then
              let x11 : List T := «Prelude.drop» (leaf 2) x3;
              if (Const.foldr
                (α := T)
                (β := T)
                (fun (x12 : T) (x13 : T) =>
                  «Prelude.and»
                    (if («Reader.isList» x12).label ≠ 0 then
                      if («Reader.nonEmpty» (Const.children x12)).label ≠ 0 then
                        «Reader.isAtom» (Const.child x12 (leaf 0))
                      else
                        leaf 0
                    else
                      leaf 0)
                    x13)
                (leaf 1)
                x11).label ≠ 0 then
                let x12 : T ×
                  (List T ×
                    (List T ×
                      (List T ×
                        (List T × (List T × List T))))) := «Modules.declare» x1 x7 x8;
                let x13 : T ×
                  (List T ×
                    (List T ×
                      (List T ×
                        (List T ×
                          (List T ×
                            List
                              T))))) := «Modules.declareAll»
                  x12
                  (Const.foldr
                    (α := T)
                    (β := List T)
                    (fun (x13 : T) (x14 : List T) =>
                      ((«Reader.node2»
                        (leaf 0)
                        («Reader.nameOf» (Const.child x13 (leaf 0)))
                        («Modules.qualify»
                          x0
                          («Reader.nameOf» (Const.child x13 (leaf 0))))) ::
                        x14))
                    ([] : List T)
                    x11);
                if ((x13).1).label ≠ 0 then
                  «Modules.mkSt»
                    («Modules.stVis» x13)
                    («Prelude.append»
                      («Modules.stOut» x1)
                      («Prelude.single»
                        (x10
                          (Const.foldr
                            (α := T)
                            (β := List T)
                            (fun (x14 : T) (x15 : List T) =>
                              ((«Modules.mkList»
                                ((«Modules.atomOf»
                                  («Modules.qualify»
                                    x0
                                    («Reader.nameOf» (Const.child x14 (leaf 0))))) ::
                                  (Const.foldr
                                    (α := T)
                                    (β := List T)
                                    (fun (x16 : T) (x17 : List T) =>
                                      ((«Modules.rename»
                                        («Modules.stVis» x12)
                                        x16
                                        (leaf 1)
                                        ([] : List T)) ::
                                        x17))
                                    ([] : List T)
                                    («Prelude.drop» (leaf 1) (Const.children x14))))) ::
                                x15))
                            ([] : List T)
                            x11))))
                    («Modules.stReg» x13)
                    («Modules.stEx» x13)
                    («Prelude.append»
                      («Modules.stMem» x1)
                      (Const.foldr
                        (α := T)
                        (β := List T)
                        (fun (x14 : T) (x15 : List T) =>
                          ((«Modules.memberDecl»
                            («Modules.qualify»
                              x0
                              («Reader.nameOf» (Const.child x14 (leaf 0))))) ::
                            x15))
                        ([] : List T)
                        x11))
                    («Modules.stMods» x13)
                else
                  «Modules.stFail»
              else
                «Modules.stFail»
            else
              «Modules.stFail»
    else
      «Modules.stFail»

def «Modules.importSpec» :=
  fun (x0 : T) =>
    let x1 : List T := Const.children x0;
    let x2 : T := Const.arity x0;
    let x3 : T := «Prelude.at» x1 (leaf 1);
    let x4 : T := (if («Reader.isAtom» x3).label ≠ 0 then
      «Prelude.some»
        («Reader.node2»
          (leaf 0)
          («Reader.nameOf» x3)
          (Const.node (leaf 0) ([] : List T)))
    else
      if (if («Reader.isList» x3).label ≠ 0 then
        if («Reader.nonEmpty» (Const.children x3)).label ≠ 0 then
          «Reader.isAtom» (Const.child x3 (leaf 0))
        else
          leaf 0
      else
        leaf 0).label ≠ 0 then
        «Prelude.some»
          («Reader.node2»
            (leaf 0)
            («Reader.nameOf» (Const.child x3 (leaf 0)))
            (Const.node (leaf 0) («Prelude.drop» (leaf 1) (Const.children x3))))
      else
        «Prelude.none»);
    if («Prelude.isSome» x4).label ≠ 0 then
      if (Const.eq x2 (leaf 2)).label ≠ 0 then
        «Prelude.some»
          (Const.node
            (leaf 0)
            ((Const.child («Prelude.get» x4) (leaf 0)) ::
              ((Const.child («Prelude.get» x4) (leaf 1)) ::
                («Prelude.single» «Prelude.none»))))
      else
        if (if (Const.eq x2 (leaf 4)).label ≠ 0 then
          if («Reader.named»
            («Prelude.at» x1 (leaf 2))
            «Modules.kwAs»).label ≠ 0 then
            «Reader.isAtom» («Prelude.at» x1 (leaf 3))
          else
            leaf 0
        else
          leaf 0).label ≠ 0 then
          «Prelude.some»
            (Const.node
              (leaf 0)
              ((Const.child («Prelude.get» x4) (leaf 0)) ::
                ((Const.child («Prelude.get» x4) (leaf 1)) ::
                  («Prelude.single»
                    («Prelude.some» («Reader.nameOf» («Prelude.at» x1 (leaf 3))))))))
        else
          «Prelude.none»
    else
      «Prelude.none»

def «Modules.importAs» :=
  fun (x0 : T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        ((«Reader.node2»
          (leaf 0)
          (if («Prelude.isSome» x0).label ≠ 0 then
            «Modules.nameCat»
              («Prelude.get» x0)
              (leaf 46)
              (Const.child x2 (leaf 0))
          else
            Const.child x2 (leaf 0))
          (Const.child x2 (leaf 1))) ::
          x3))
      ([] : List T)
      x1

def «Modules.elabForms» :=
  fun (x0 : T →
      (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
        T → T × (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : T)
    (x2 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x3 : List T) =>
    Const.foldr
      (α := T)
      (β := (T ×
        (List T × (List T × (List T × (List T × (List T × List T)))))) →
        T × (List T × (List T × (List T × (List T × (List T × List T))))))
      (fun (x4 : T)
         (x5 : (T ×
           (List T × (List T × (List T × (List T × (List T × List T)))))) →
           T × (List T × (List T × (List T × (List T × (List T × List T))))))
         (x6 : T ×
           (List T × (List T × (List T × (List T × (List T × List T)))))) =>
        x5 (x0 x1 x6 x4))
      (fun (x4 : T ×
           (List T × (List T × (List T × (List T × (List T × List T)))))) =>
        x4)
      x3
      x2

def «Modules.instantiate» :=
  fun (x0 : T →
      (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
        T → T × (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x2 : T)
    (x3 : T)
    (x4 : List T) =>
    «Modules.elabForms»
      x0
      x3
      (Const.foldr
        (α := T)
        (β := T →
          (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
            T × (List T × (List T × (List T × (List T × (List T × List T))))))
        (fun (x5 : T)
           (x6 : T →
             (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
               T × (List T × (List T × (List T × (List T × (List T × List T))))))
           (x7 : T)
           (x8 : T ×
             (List T × (List T × (List T × (List T × (List T × List T)))))) =>
          x6
            (Const.add x7 (leaf 1))
            («Modules.bindParam»
              x3
              («Modules.stVis» x1)
              x8
              x5
              («Prelude.at» x4 x7)))
        (fun (_ : T)
           (x6 : T ×
             (List T × (List T × (List T × (List T × (List T × List T)))))) =>
          x6)
        (Const.children (Const.child x2 (leaf 0)))
        (leaf 0)
        («Modules.mkSt»
          (Const.children (Const.child x2 (leaf 3)))
          («Modules.stOut» x1)
          («Modules.stReg» x1)
          (Const.children (Const.child x2 (leaf 1)))
          ([] : List T)
          («Modules.stMods» x1)))
      (Const.children (Const.child x2 (leaf 2)))

def «Modules.aGeneric» :=
  mk 1 [leaf 37,
    leaf 103,
    leaf 101,
    leaf 110,
    leaf 101,
    leaf 114,
    leaf 105,
    leaf 99]

def «Modules.aSort» :=
  mk 1 [leaf 37, leaf 115, leaf 111, leaf 114, leaf 116]

def «Modules.aPostulate» :=
  mk 1 [leaf 37,
    leaf 112,
    leaf 111,
    leaf 115,
    leaf 116,
    leaf 117,
    leaf 108,
    leaf 97,
    leaf 116,
    leaf 101]

def «Modules.aArrowM» :=
  mk 1 [leaf 65, leaf 114, leaf 114, leaf 111, leaf 119]

def «Modules.freshArg» :=
  fun (x0 : T) (x1 : T) =>
    Const.node
      (leaf 1)
      ((leaf 37) :: (x0 :: («Datatype.decimalChars» x1)))

def «Modules.genericArgs» :=
  fun (x0 : List T) =>
    (Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        (Const.sub (x2).1 (leaf 1),
          ((«Modules.freshArg»
            (if («Reader.isAtom» (Const.child x1 (leaf 1))).label ≠ 0 then
              leaf 115
            else
              leaf 112)
            (Const.sub (x2).1 (leaf 1))) ::
            (x2).2)))
      («Prelude.length» x0, ([] : List T))
      x0).2

def «Modules.genericOf» :=
  fun (x0 : T →
      (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
        T → T × (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x2 : T)
    (x3 : T) =>
    let x4 : List T := Const.children (Const.child x2 (leaf 0));
    let x5 : List T := «Modules.genericArgs» x4;
    let x6 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x6 : T) (x7 : List T) =>
        if («Reader.isAtom»
          (Const.child (Const.child x6 (leaf 0)) (leaf 1))).label ≠ 0 then
          ((«Reader.node2»
            (leaf 0)
            («Reader.nameOf» (Const.child (Const.child x6 (leaf 0)) (leaf 1)))
            («Reader.nameOf» (Const.child x6 (leaf 1)))) ::
            x7)
        else
          x7)
      ([] : List T)
      («Modules.zipWith2»
        (fun (x6 : T) (x7 : T) => «Reader.node2» (leaf 0) x6 x7)
        x4
        x5);
    let x7 : List
      T := «Prelude.append» x6 (Const.children (Const.child x2 (leaf 3)));
    let x8 : List
      T := «Modules.zipWith2»
      (fun (x8 : T) (x9 : T) =>
        let x10 : T := Const.child x8 (leaf 1);
        if («Reader.isAtom» x10).label ≠ 0 then
          «Modules.mkList» («Modules.aSort» :: («Prelude.single» x9))
        else
          «Modules.mkList»
            («Modules.aPostulate» ::
              (x9 ::
                («Prelude.single»
                  (Const.foldr
                    (α := T)
                    (β := T)
                    (fun (x11 : T) (x12 : T) =>
                      «Modules.mkList»
                        («Modules.aArrowM» ::
                          ((«Modules.rename» x7 x11 (leaf 1) ([] : List T)) ::
                            («Prelude.single» x12))))
                    («Modules.rename»
                      x7
                      (Const.child x10 (leaf 2))
                      (leaf 1)
                      ([] : List T))
                    (Const.children (Const.child x10 (leaf 1))))))))
      x4
      x5;
    let x9 : T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              (List T ×
                List
                  T))))) := «Modules.instantiate»
      x0
      («Modules.mkSt»
        («Modules.stVis» x1)
        ([] : List T)
        («Modules.stReg» x1)
        («Modules.stEx» x1)
        («Modules.stMem» x1)
        («Modules.stMods» x1))
      x2
      («Modules.nameCat»
        x3
        (leaf 37)
        (mk 0 [leaf 103,
          leaf 101,
          leaf 110,
          leaf 101,
          leaf 114,
          leaf 105,
          leaf 99]))
      x5;
    if ((x9).1).label ≠ 0 then
      «Prelude.some»
        («Modules.mkList»
          («Modules.aGeneric» :: («Prelude.append» x8 («Modules.stOut» x9))))
    else
      «Prelude.none»

def «Modules.elabStep» :=
  fun (x0 : T →
      (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
        T → T × (List T × (List T × (List T × (List T × (List T × List T))))))
    (x1 : T)
    (x2 : T ×
      (List T × (List T × (List T × (List T × (List T × List T))))))
    (x3 : T) =>
    if (if ((x2).1).label ≠ 0 then
      if («Reader.isList» x3).label ≠ 0 then
        «Reader.nonEmpty» (Const.children x3)
      else
        leaf 0
    else
      leaf 0).label ≠ 0 then
      let x4 : List T := Const.children x3;
      let x5 : T := «Prelude.at» x4 (leaf 0);
      if («Reader.named» x5 «Modules.kwExport»).label ≠ 0 then
        «Modules.mkSt»
          («Modules.stVis» x2)
          («Modules.stOut» x2)
          («Modules.stReg» x2)
          («Prelude.append»
            («Modules.stEx» x2)
            («Modules.atomNames» («Prelude.drop» (leaf 1) x4)))
          («Modules.stMem» x2)
          («Modules.stMods» x2)
      else
        if («Reader.named» x5 «Modules.kwImport»).label ≠ 0 then
          let x6 : T := «Modules.importSpec» x3;
          if («Prelude.isSome» x6).label ≠ 0 then
            let x7 : T := Const.child («Prelude.get» x6) (leaf 0);
            let x8 : List
              T := Const.children (Const.child («Prelude.get» x6) (leaf 1));
            let x9 : T := Const.child («Prelude.get» x6) (leaf 2);
            let x10 : T := «Reader.lookupAbbrev» x7 («Modules.stReg» x2);
            if («Prelude.isSome» x10).label ≠ 0 then
              let x11 : T := «Prelude.get» x10;
              if (Const.eq (Const.label x11) (leaf 0)).label ≠ 0 then
                if («Reader.nonEmpty» x8).label ≠ 0 then
                  «Modules.stFail»
                else
                  «Modules.declareAll»
                    x2
                    («Modules.importAs» x9 (Const.children (Const.child x11 (leaf 0))))
              else
                let x12 : List T := Const.children (Const.child x11 (leaf 0));
                if (Const.eq
                  («Prelude.length» x12)
                  («Prelude.length» x8)).label ≠ 0 then
                  let x13 : T := «Modules.nameCat»
                    x1
                    (leaf 47)
                    (if («Prelude.isSome» x9).label ≠ 0 then «Prelude.get» x9 else x7);
                  let x14 : T ×
                    (List T ×
                      (List T ×
                        (List T ×
                          (List T ×
                            (List T × List T))))) := «Modules.instantiate»
                    x0
                    x2
                    x11
                    x13
                    x8;
                  let x15 : T := (if ((x14).1).label ≠ 0 then
                    «Modules.exportsOf» x14
                  else
                    «Prelude.none»);
                  if («Prelude.isSome» x15).label ≠ 0 then
                    «Modules.declareAll»
                      («Modules.mkSt»
                        («Modules.stVis» x2)
                        («Modules.stOut» x14)
                        («Modules.stReg» x14)
                        («Modules.stEx» x2)
                        («Prelude.append»
                          («Modules.stMem» x2)
                          («Prelude.single» («Modules.memberSub» x13)))
                        («Prelude.append»
                          («Modules.stMods» x14)
                          («Prelude.single»
                            («Modules.modNode»
                              x13
                              («Modules.stMem» x14)
                              (Const.children («Prelude.get» x15))))))
                      («Modules.importAs» x9 (Const.children («Prelude.get» x15)))
                  else
                    «Modules.stFail»
                else
                  «Modules.stFail»
            else
              «Modules.stFail»
          else
            «Modules.stFail»
        else
          if («Reader.named» x5 «Modules.kwModule»).label ≠ 0 then
            if (if (Const.lt (leaf 1) («Prelude.length» x4)).label ≠ 0 then
              «Reader.isAtom» («Prelude.at» x4 (leaf 1))
            else
              leaf 0).label ≠ 0 then
              let x6 : T := «Reader.nameOf» («Prelude.at» x4 (leaf 1));
              let x7 : T := «Modules.qualify» x1 x6;
              let x8 : List T := «Prelude.drop» (leaf 2) x4;
              let x9 : List T := «Modules.withHead» «Modules.kwParameter» x8;
              if («Reader.nonEmpty» x9).label ≠ 0 then
                let x10 : List T := «Modules.withoutHead» «Modules.kwParameter» x8;
                let x11 : T := Const.node
                  (leaf 1)
                  ((Const.node (leaf 0) x9) ::
                    ((Const.node
                      (leaf 0)
                      («Modules.concat»
                        (Const.foldr
                          (α := T)
                          (β := List (List T))
                          (fun (x11 : T) (x12 : List (List T)) =>
                            ((«Modules.atomNames»
                              («Prelude.drop» (leaf 1) (Const.children x11))) ::
                              x12))
                          ([] : List (List T))
                          («Modules.withHead» «Modules.kwExport» x10)))) ::
                      ((Const.node
                        (leaf 0)
                        («Modules.withoutHead» «Modules.kwExport» x10)) ::
                        («Prelude.single» (Const.node (leaf 0) («Modules.stVis» x2))))));
                let x12 : T := «Modules.genericOf» x0 x2 x11 x7;
                if («Prelude.isSome» x12).label ≠ 0 then
                  «Modules.mkSt»
                    («Modules.stVis» x2)
                    («Prelude.append»
                      («Modules.stOut» x2)
                      («Prelude.single» («Prelude.get» x12)))
                    («Prelude.append»
                      («Modules.stReg» x2)
                      («Prelude.single» («Reader.node2» (leaf 0) x7 x11)))
                    («Modules.stEx» x2)
                    («Modules.stMem» x2)
                    («Modules.stMods» x2)
                else
                  «Modules.stFail»
              else
                let x10 : T ×
                  (List T ×
                    (List T ×
                      (List T ×
                        (List T ×
                          (List T ×
                            List
                              T))))) := «Modules.elabForms»
                  x0
                  x7
                  («Modules.mkSt»
                    («Modules.stVis» x2)
                    («Modules.stOut» x2)
                    («Modules.stReg» x2)
                    ([] : List T)
                    ([] : List T)
                    («Modules.stMods» x2))
                  x8;
                let x11 : T := (if ((x10).1).label ≠ 0 then
                  «Modules.exportsOf» x10
                else
                  «Prelude.none»);
                if («Prelude.isSome» x11).label ≠ 0 then
                  «Modules.declareAll»
                    («Modules.mkSt»
                      («Modules.stVis» x2)
                      («Modules.stOut» x10)
                      («Prelude.append»
                        («Modules.stReg» x10)
                        («Prelude.single»
                          («Reader.node2»
                            (leaf 0)
                            x7
                            (Const.node (leaf 0) («Prelude.single» («Prelude.get» x11))))))
                      («Modules.stEx» x2)
                      («Prelude.append»
                        («Modules.stMem» x2)
                        («Prelude.single» («Modules.memberSub» x7)))
                      («Prelude.append»
                        («Modules.stMods» x10)
                        («Prelude.single»
                          («Modules.modNode»
                            x7
                            («Modules.stMem» x10)
                            (Const.children («Prelude.get» x11))))))
                    («Modules.importAs»
                      («Prelude.some» x6)
                      (Const.children («Prelude.get» x11)))
                else
                  «Modules.stFail»
            else
              «Modules.stFail»
          else
            «Modules.elabDecl» x1 x2 x3
    else
      «Modules.stFail»

def «Modules.elabAt» :=
  fun (x0 : T) =>
    Const.iter
      (α := T →
        (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
          T → T × (List T × (List T × (List T × (List T × (List T × List T))))))
      (fun (x1 : T →
           (T × (List T × (List T × (List T × (List T × (List T × List T)))))) →
             T → T × (List T × (List T × (List T × (List T × (List T × List T))))))
         (x2 : T)
         (x3 : T ×
           (List T × (List T × (List T × (List T × (List T × List T))))))
         (x4 : T) =>
        «Modules.elabStep» x1 x2 x3 x4)
      (fun (_ : T)
         (_ : T ×
           (List T × (List T × (List T × (List T × (List T × List T))))))
         (_ : T) =>
        «Modules.stFail»)
      x0

def «Modules.moduleCount» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        Const.add
          x2
          (Const.para
            (α := T)
            (fun (x3 : T) (x4 : List T) =>
              Const.foldr
                (α := T)
                (β := T)
                Const.add
                (if («Reader.named» x3 «Modules.kwModule»).label ≠ 0 then
                  leaf 1
                else
                  leaf 0)
                x4)
            x1))
      (leaf 0)
      x0

def «Modules.expandModulesTree» :=
  fun (x0 : List T) =>
    let x1 : T ×
      (List T ×
        (List T ×
          (List T ×
            (List T ×
              (List T ×
                List
                  T))))) := «Modules.elabForms»
      («Modules.elabAt» (Const.add («Modules.moduleCount» x0) (leaf 1)))
      (Const.node (leaf 0) ([] : List T))
      («Modules.mkSt»
        ([] : List T)
        ([] : List T)
        ([] : List T)
        ([] : List T)
        ([] : List T)
        ([] : List T))
      x0;
    if ((x1).1).label ≠ 0 then
      if («Reader.nonEmpty» («Modules.stEx» x1)).label ≠ 0 then
        «Prelude.none»
      else
        «Prelude.some»
          («Reader.node2»
            (leaf 0)
            (Const.node (leaf 0) («Modules.stOut» x1))
            (Const.node
              (leaf 0)
              («Prelude.append»
                («Modules.stMods» x1)
                («Prelude.single»
                  («Modules.modNode»
                    (Const.node (leaf 0) ([] : List T))
                    («Modules.stMem» x1)
                    ([] : List T))))))
    else
      «Prelude.none»

def «Modules.expandModules» :=
  fun (x0 : List T) =>
    let x1 : T := «Modules.expandModulesTree» x0;
    if («Prelude.isSome» x1).label ≠ 0 then
      «Prelude.some» (Const.child («Prelude.get» x1) (leaf 0))
    else
      «Prelude.none»

def «Recognize.sx» := fun (x0 : List T) => Const.node (leaf 2) x0

def «Recognize.s2» :=
  fun (x0 : T) (x1 : T) => «Recognize.sx» (x0 :: («Prelude.single» x1))

def «Recognize.s3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    «Recognize.sx» (x0 :: (x1 :: («Prelude.single» x2)))

def «Recognize.s4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    «Recognize.sx» (x0 :: (x1 :: (x2 :: («Prelude.single» x3))))

def «Recognize.num» :=
  fun (x0 : T) => Const.node (leaf 1) («Datatype.decimalChars» x0)

def «Recognize.pow2» :=
  fun (x0 : T) =>
    Const.iter
      (α := T)
      (fun (x1 : T) => Const.mul x1 (leaf 2))
      (leaf 1)
      x0

def «Recognize.rT» := mk 1 [leaf 84]

def «Recognize.rList» := mk 1 [leaf 76, leaf 105, leaf 115, leaf 116]

def «Recognize.rLam» := mk 1 [leaf 108, leaf 97, leaf 109]

def «Recognize.rLet» := mk 1 [leaf 108, leaf 101, leaf 116]

def «Recognize.rIf» := mk 1 [leaf 105, leaf 102]

def «Recognize.rDef» := mk 1 [leaf 100, leaf 101, leaf 102]

def «Recognize.rFold» := mk 1 [leaf 102, leaf 111, leaf 108, leaf 100]

def «Recognize.rFoldr» :=
  mk 1 [leaf 102, leaf 111, leaf 108, leaf 100, leaf 114]

def «Recognize.rIter» := mk 1 [leaf 105, leaf 116, leaf 101, leaf 114]

def «Recognize.rLcase» :=
  mk 1 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101]

def «Recognize.rNil» := mk 1 [leaf 110, leaf 105, leaf 108]

def «Recognize.rNode» := mk 1 [leaf 110, leaf 111, leaf 100, leaf 101]

def «Recognize.rChild» :=
  mk 1 [leaf 99, leaf 104, leaf 105, leaf 108, leaf 100]

def «Recognize.rArity» :=
  mk 1 [leaf 97, leaf 114, leaf 105, leaf 116, leaf 121]

def «Recognize.rEq» := mk 1 [leaf 101, leaf 113]

def «Recognize.rLt» := mk 1 [leaf 108, leaf 116]

def «Recognize.rAdd» := mk 1 [leaf 97, leaf 100, leaf 100]

def «Recognize.rDiv» := mk 1 [leaf 100, leaf 105, leaf 118]

def «Recognize.rMod» := mk 1 [leaf 109, leaf 111, leaf 100]

def «Recognize.vT» := mk 1 [leaf 37, leaf 116]

def «Recognize.vL» := mk 1 [leaf 37, leaf 108]

def «Recognize.vR» := mk 1 [leaf 37, leaf 114]

def «Recognize.vN» := mk 1 [leaf 37, leaf 110]

def «Recognize.vC» := mk 1 [leaf 37, leaf 99]

def «Recognize.vA» := mk 1 [leaf 37, leaf 97]

def «Recognize.vX» := mk 1 [leaf 37, leaf 120]

def «Recognize.vH» := mk 1 [leaf 37, leaf 104]

def «Recognize.vU» := mk 1 [leaf 37, leaf 117]

def «Recognize.zero» := mk 1 [leaf 48]

def «Recognize.one» := mk 1 [leaf 49]

def «Recognize.tList» :=
  «Recognize.s2» «Recognize.rList» «Recognize.rT»

def «Recognize.bind1» :=
  fun (x0 : T) (x1 : T) =>
    «Recognize.sx» («Prelude.single» («Recognize.s2» x0 x1))

def «Recognize.bind2» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    «Recognize.sx»
      ((«Recognize.s2» x0 x1) :: («Prelude.single» («Recognize.s2» x2 x3)))

def «Recognize.conj» :=
  fun (x0 : T) (x1 : T) =>
    if (Const.equal x0 «Recognize.one»).label ≠ 0 then
      x1
    else
      if (Const.equal x1 «Recognize.one»).label ≠ 0 then
        x0
      else
        «Recognize.s4» «Recognize.rIf» x0 x1 «Recognize.zero»

def «Recognize.bitOf» :=
  fun (x0 : T) (x1 : T) =>
    «Recognize.s3»
      «Recognize.rMod»
      («Recognize.s3»
        «Recognize.rDiv»
        x0
        («Recognize.num» («Recognize.pow2» x1)))
      («Recognize.num» (leaf 2))

def «Recognize.tailE» :=
  «Recognize.s3»
    «Recognize.rLam»
    («Recognize.bind1» «Recognize.vX» «Recognize.tList»)
    («Recognize.sx»
      («Recognize.rLcase» ::
        («Recognize.rT» ::
          («Recognize.tList» ::
            («Recognize.vX» ::
              ((«Recognize.s2» «Recognize.rNil» «Recognize.rT») ::
                («Prelude.single»
                  («Recognize.s3»
                    «Recognize.rLam»
                    («Recognize.bind2»
                      «Recognize.vH»
                      «Recognize.rT»
                      «Recognize.vU»
                      «Recognize.tList»)
                    «Recognize.vU»))))))))

def «Recognize.dropE» :=
  fun (x0 : T) =>
    «Recognize.sx»
      («Recognize.rIter» ::
        («Recognize.tList» ::
          («Recognize.tailE» ::
            («Recognize.vR» :: («Prelude.single» («Recognize.num» x0))))))

def «Recognize.markers» :=
  fun (x0 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x1 : T) (x2 : List T) =>
        if (Const.eq (Const.label x1) (leaf 9)).label ≠ 0 then
          (x1 :: x2)
        else
          x2)
      ([] : List T)
      x0

def «Recognize.markerOf» :=
  fun (x0 : List T) (x1 : T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        if (Const.equal (Const.child x2 (leaf 0)) x1).label ≠ 0 then
          «Prelude.some» x2
        else
          x3)
      «Prelude.none»
      x0

def «Recognize.fieldTypes» :=
  fun (x0 : T) =>
    if (Const.child x0 (leaf 2)).label ≠ 0 then
      «Prelude.append»
        (Const.children (Const.child x0 (leaf 1)))
        («Prelude.single» (Const.child x0 (leaf 3)))
    else
      Const.children (Const.child x0 (leaf 1))

def «Recognize.depsOf» :=
  fun (x0 : List T) (x1 : T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        Const.foldr
          (α := T)
          (β := List T)
          (fun (x4 : T) (x5 : List T) =>
            if («Prelude.isSome» («Recognize.markerOf» x0 x4)).label ≠ 0 then
              (x4 :: x5)
            else
              x5)
          x3
          («Recognize.fieldTypes» x2))
      ([] : List T)
      («Prelude.tail» (Const.children x1))

def «Recognize.addNew» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        if («Prelude.isSome» («Reader.indexOf» x2 x3)).label ≠ 0 then
          x3
        else
          «Prelude.append» x3 («Prelude.single» x2))
      x1
      («Prelude.reverse» x0)

def «Recognize.closure» :=
  fun (x0 : List T) (x1 : T) =>
    Const.iter
      (α := List T)
      (fun (x2 : List T) =>
        Const.foldr
          (α := T)
          (β := List T)
          (fun (x3 : T) (x4 : List T) =>
            let x5 : T := «Recognize.markerOf» x0 x3;
            if («Prelude.isSome» x5).label ≠ 0 then
              «Recognize.addNew» («Recognize.depsOf» x0 («Prelude.get» x5)) x4
            else
              x4)
          x2
          x2)
      («Prelude.single» x1)
      («Prelude.length» x0)

def «Recognize.fieldTest» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    if («Reader.named» x1 «Reader.kwT»).label ≠ 0 then
      «Prelude.some» «Recognize.one»
    else
      let x3 : T := «Reader.indexOf» x1 x0;
      if («Prelude.isSome» x3).label ≠ 0 then
        «Prelude.some» («Recognize.bitOf» x2 («Prelude.get» x3))
      else
        «Prelude.none»

def «Recognize.ctorTest» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List T := Const.children (Const.child x1 (leaf 1));
    let x3 : T := «Prelude.length» x2;
    let x4 : T := (if (Const.child x1 (leaf 2)).label ≠ 0 then
      «Recognize.s3»
        «Recognize.rLt»
        («Recognize.num» x3)
        («Recognize.s3»
          «Recognize.rAdd»
          («Recognize.s2» «Recognize.rArity» «Recognize.vN»)
          «Recognize.one»)
    else
      «Recognize.s3»
        «Recognize.rEq»
        («Recognize.s2» «Recognize.rArity» «Recognize.vN»)
        («Recognize.num» x3));
    let x5 : T := «Reader.allSome»
      (Const.foldr
        (α := T)
        (β := T × List T)
        (fun (x5 : T) (x6 : T × List T) =>
          (Const.sub (x6).1 (leaf 1),
            ((«Recognize.fieldTest»
              x0
              x5
              («Recognize.s3»
                «Recognize.rChild»
                «Recognize.vN»
                («Recognize.num» (Const.sub (x6).1 (leaf 1))))) ::
              (x6).2)))
        (x3, ([] : List T))
        x2).2;
    let x6 : T := (if (Const.child x1 (leaf 2)).label ≠ 0 then
      let x6 : T := «Recognize.fieldTest»
        x0
        (Const.child x1 (leaf 3))
        «Recognize.vC»;
      if («Prelude.isSome» x6).label ≠ 0 then
        if (Const.equal («Prelude.get» x6) «Recognize.one»).label ≠ 0 then
          x6
        else
          «Prelude.some»
            («Recognize.sx»
              («Recognize.rFoldr» ::
                («Recognize.rT» ::
                  («Recognize.rT» ::
                    ((«Recognize.s3»
                      «Recognize.rLam»
                      («Recognize.bind2»
                        «Recognize.vC»
                        «Recognize.rT»
                        «Recognize.vA»
                        «Recognize.rT»)
                      («Recognize.s4»
                        «Recognize.rIf»
                        («Prelude.get» x6)
                        «Recognize.vA»
                        «Recognize.zero»)) ::
                      («Recognize.one» :: («Prelude.single» («Recognize.dropE» x3))))))))
      else
        «Prelude.none»
    else
      «Prelude.some» «Recognize.one»);
    if («Reader.both» x5 x6).label ≠ 0 then
      «Prelude.some»
        («Recognize.conj»
          x4
          (Const.foldr
            (α := T)
            (β := T)
            «Recognize.conj»
            («Prelude.get» x6)
            (Const.children («Prelude.get» x5))))
    else
      «Prelude.none»

def «Recognize.dataTest» :=
  fun (x0 : List T) (x1 : T) =>
    Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := «Recognize.ctorTest» x0 x2;
        if («Reader.both» x4 x3).label ≠ 0 then
          «Prelude.some»
            («Recognize.s4»
              «Recognize.rIf»
              («Recognize.s3»
                «Recognize.rEq»
                «Recognize.vL»
                («Recognize.num» (Const.child x2 (leaf 0))))
              («Prelude.get» x4)
              («Prelude.get» x3))
        else
          «Prelude.none»)
      («Prelude.some» «Recognize.zero»)
      («Prelude.tail» (Const.children x1))

def «Recognize.recognizer» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List T := «Recognize.closure» x0 (Const.child x1 (leaf 0));
    let x3 : T := «Reader.allSome»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x3 : T) (x4 : List T) =>
          let x5 : T := «Recognize.markerOf» x0 x3;
          ((if («Prelude.isSome» x5).label ≠ 0 then
            let x6 : T := «Recognize.dataTest» x2 («Prelude.get» x5);
            if («Prelude.isSome» x6).label ≠ 0 then
              «Prelude.some»
                («Recognize.s4»
                  «Recognize.rIf»
                  («Prelude.get» x6)
                  («Recognize.num»
                    («Recognize.pow2» («Prelude.get» («Reader.indexOf» x3 x2))))
                  «Recognize.zero»)
            else
              «Prelude.none»
          else
            «Prelude.none») ::
            x4))
        ([] : List T)
        x2);
    if («Prelude.isSome» x3).label ≠ 0 then
      let x4 : T := «Recognize.s3»
        «Recognize.rLam»
        («Recognize.bind2»
          «Recognize.vL»
          «Recognize.rT»
          «Recognize.vR»
          «Recognize.tList»)
        («Recognize.sx»
          («Recognize.rLet» ::
            («Recognize.vN» ::
              («Recognize.rT» ::
                ((«Recognize.s3» «Recognize.rNode» «Recognize.zero» «Recognize.vR») ::
                  («Prelude.single»
                    (Const.foldr
                      (α := T)
                      (β := T)
                      (fun (x4 : T) (x5 : T) => «Recognize.s3» «Recognize.rAdd» x4 x5)
                      «Recognize.zero»
                      (Const.children («Prelude.get» x3)))))))));
      «Prelude.some»
        («Recognize.s3»
          «Recognize.rDef»
          («Datatype.memberName» (Const.child x1 (leaf 0)))
          («Recognize.s3»
            «Recognize.rLam»
            («Recognize.bind1» «Recognize.vT» «Recognize.rT»)
            («Recognize.bitOf»
              («Recognize.s4» «Recognize.rFold» «Recognize.rT» x4 «Recognize.vT»)
              (leaf 0))))
    else
      «Prelude.none»

def «Recognize.occurs» :=
  fun (x0 : T) (x1 : T) =>
    Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        if (Const.equal x2 x0).label ≠ 0 then
          leaf 1
        else
          Const.foldr (α := T) (β := T) «Prelude.or» (leaf 0) x3)
      x1

def «Recognize.insertRecognizers» :=
  fun (x0 : List T) =>
    let x1 : List T := «Recognize.markers» x0;
    let x2 : T := «Reader.allSome»
      (Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) =>
          ((if (Const.eq (Const.label x2) (leaf 9)).label ≠ 0 then
            if (Const.foldr
              (α := T)
              (β := T)
              (fun (x4 : T) (x5 : T) =>
                «Prelude.or»
                  («Recognize.occurs»
                    («Datatype.memberName» (Const.child x2 (leaf 0)))
                    x4)
                  x5)
              (leaf 0)
              x0).label ≠ 0 then
              let x4 : T := «Recognize.recognizer» x1 x2;
              if («Prelude.isSome» x4).label ≠ 0 then
                «Prelude.some»
                  (Const.node (leaf 0) («Prelude.single» («Prelude.get» x4)))
              else
                «Prelude.none»
            else
              «Prelude.some» (Const.node (leaf 0) ([] : List T))
          else
            «Prelude.some» (Const.node (leaf 0) («Prelude.single» x2))) ::
            x3))
        ([] : List T)
        x0);
    if («Prelude.isSome» x2).label ≠ 0 then
      «Prelude.some»
        (Const.node
          (leaf 0)
          (Const.foldr
            (α := T)
            (β := List T)
            (fun (x3 : T) (x4 : List T) =>
              «Prelude.append» (Const.children x3) x4)
            ([] : List T)
            (Const.children («Prelude.get» x2))))
    else
      «Prelude.none»

def «Compile.bundleOf» :=
  fun (x0 : T) =>
    let x1 : T := «Reader.readSExps» (Const.children x0);
    let x2 : T := (if («Prelude.isSome» x1).label ≠ 0 then
      «Modules.expandModules» (Const.children («Prelude.get» x1))
    else
      «Prelude.none»);
    let x3 : T := (if («Prelude.isSome» x2).label ≠ 0 then
      «Datatype.expandProgram» (Const.children («Prelude.get» x2))
    else
      «Prelude.none»);
    let x4 : T := (if («Prelude.isSome» x3).label ≠ 0 then
      «Recognize.insertRecognizers» (Const.children («Prelude.get» x3))
    else
      «Prelude.none»);
    if («Prelude.isSome» x4).label ≠ 0 then
      «Reader.readProgram» (Const.children («Prelude.get» x4))
    else
      «Prelude.none»

def «Compile.compileWith» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := «Compile.bundleOf» x1;
    if («Prelude.isSome» x2).label ≠ 0 then
      if («Prelude.isSome»
        («Check.checkProgram»
          (Const.children
            (Const.child («Prelude.get» x2) (leaf 0))))).label ≠ 0 then
        x0 («Prelude.get» x2)
      else
        Const.node (leaf 0) ([] : List T)
    else
      Const.node (leaf 0) ([] : List T)

def «Compile.compile» :=
  fun (x0 : T) => «Compile.compileWith» «Serialize.image» x0

def «main» := fun (x0 : T) => «Compile.compile» x0

def «LeanBackend.bytes» := fun (x0 : List T) => Const.node (leaf 0) x0

def «LeanBackend.txt» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.cat» := fun (x0 : List T) => Const.node (leaf 1) x0

def «LeanBackend.nest» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «LeanBackend.line» := Const.node (leaf 3) ([] : List T)

def «LeanBackend.grp» :=
  fun (x0 : T) => Const.node (leaf 4) (x0 :: ([] : List T))

def «LeanBackend.align» :=
  fun (x0 : T) => Const.node (leaf 5) (x0 :: ([] : List T))

def «LeanBackend/Docs.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «LeanBackend/Docs.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «LeanBackend/Docs.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «LeanBackend/Docs.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «LeanBackend/Docs.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «LeanBackend/Docs.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «LeanBackend/Docs.tail» x1 x0;
    x2

def «LeanBackend/Docs.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («LeanBackend/Docs.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «LeanBackend.cols» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        if («Prelude.and»
          (Const.lt (leaf 127) x1)
          (Const.lt x1 (leaf 192))).label ≠ 0 then
          x2
        else
          Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «LeanBackend.text» :=
  fun (x0 : List T) =>
    let x1 : T := «LeanBackend.txt»
      («LeanBackend.cols» x0)
      («LeanBackend.bytes» x0);
    x1

def «LeanBackend.cat2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «LeanBackend.cat»
      (x0 :: («LeanBackend/Docs.single» x1));
    x2

def «LeanBackend.cat3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «LeanBackend.cat»
      (x0 :: (x1 :: («LeanBackend/Docs.single» x2)));
    x3

def «LeanBackend.cat5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := «LeanBackend.cat»
      (x0 :: (x1 :: (x2 :: (x3 :: («LeanBackend/Docs.single» x4)))));
    x5

def «LeanBackend.indented» :=
  fun (x0 : T) =>
    let x1 : T := «LeanBackend.nest»
      («LeanBackend.cat2» «LeanBackend.line» x0);
    x1

def «LeanBackend.joinWith» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «LeanBackend.cat»
      (Const.lcase
        (α := T)
        (β := List T)
        x1
        ([] : List T)
        (fun (x2 : T) (x3 : List T) =>
          (x2 ::
            (Const.foldr
              (α := T)
              (β := List T)
              (fun (x4 : T) (x5 : List T) => (x0 :: (x4 :: x5)))
              ([] : List T)
              x3))));
    x2

def «LeanBackend.tLp» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 40]))

def «LeanBackend.tRp» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 41]))

def «LeanBackend.tComma» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 44]))

def «LeanBackend.tColon» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 32, leaf 58, leaf 32]))

def «LeanBackend.tUnder» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 95]))

def «LeanBackend.tFun» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 102, leaf 117, leaf 110, leaf 32]))

def «LeanBackend.tDoubleArrow» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 32, leaf 61, leaf 62]))

def «LeanBackend.tT» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 84]))

def «LeanBackend.tUnitTy» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 85, leaf 110, leaf 105, leaf 116]))

def «LeanBackend.tTimes» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 32, leaf 195, leaf 151]))

def «LeanBackend.tTo» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 32, leaf 226, leaf 134, leaf 146]))

def «LeanBackend.tList» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 76, leaf 105, leaf 115, leaf 116]))

def «LeanBackend.tLet» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 108, leaf 101, leaf 116, leaf 32]))

def «LeanBackend.tSemi» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 59]))

def «LeanBackend.tUnitV» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 40, leaf 41]))

def «LeanBackend.tDot1» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 41, leaf 46, leaf 49]))

def «LeanBackend.tDot2» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 41, leaf 46, leaf 50]))

def «LeanBackend.tIf» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 105, leaf 102, leaf 32, leaf 40]))

def «LeanBackend.tThen» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 41,
        leaf 46,
        leaf 108,
        leaf 97,
        leaf 98,
        leaf 101,
        leaf 108,
        leaf 32,
        leaf 226,
        leaf 137,
        leaf 160,
        leaf 32,
        leaf 48,
        leaf 32,
        leaf 116,
        leaf 104,
        leaf 101,
        leaf 110]))

def «LeanBackend.tElse» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 101, leaf 108, leaf 115, leaf 101]))

def «LeanBackend.tFold» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 102,
        leaf 111,
        leaf 108,
        leaf 100]))

def «LeanBackend.tIter» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 105,
        leaf 116,
        leaf 101,
        leaf 114]))

def «LeanBackend.tFoldr» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 102,
        leaf 111,
        leaf 108,
        leaf 100,
        leaf 114]))

def «LeanBackend.tLcase» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 108,
        leaf 99,
        leaf 97,
        leaf 115,
        leaf 101]))

def «LeanBackend.tPara» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 67,
        leaf 111,
        leaf 110,
        leaf 115,
        leaf 116,
        leaf 46,
        leaf 112,
        leaf 97,
        leaf 114,
        leaf 97]))

def «LeanBackend.tConstDot» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 67, leaf 111, leaf 110, leaf 115, leaf 116, leaf 46]))

def «LeanBackend.tAlpha» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 206, leaf 177]))

def «LeanBackend.tBeta» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 206, leaf 178]))

def «LeanBackend.tColonEq» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 32, leaf 58, leaf 61, leaf 32]))

def «LeanBackend.tNilLp» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 40,
        leaf 91,
        leaf 93,
        leaf 32,
        leaf 58,
        leaf 32,
        leaf 76,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 32]))

def «LeanBackend.tConsOp» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 32, leaf 58, leaf 58]))

def «LeanBackend.tLeaf» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 108, leaf 101, leaf 97, leaf 102, leaf 32]))

def «LeanBackend.tMk» :=
  «LeanBackend.text»
    (Const.children (mk 0 [leaf 109, leaf 107, leaf 32]))

def «LeanBackend.tSpLb» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 32, leaf 91]))

def «LeanBackend.tRb» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 93]))

def «LeanBackend.tLg» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 194, leaf 171]))

def «LeanBackend.tRg» :=
  «LeanBackend.text» (Const.children (mk 0 [leaf 194, leaf 187]))

def «LeanBackend.tDef» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 100, leaf 101, leaf 102, leaf 32, leaf 194, leaf 171]))

def «LeanBackend.tAssign» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 194, leaf 187, leaf 32, leaf 58, leaf 61]))

def «LeanBackend.tHeader» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 109,
        leaf 111,
        leaf 100,
        leaf 117,
        leaf 108,
        leaf 101,
        leaf 10,
        leaf 10,
        leaf 112,
        leaf 117,
        leaf 98,
        leaf 108,
        leaf 105,
        leaf 99,
        leaf 32,
        leaf 105,
        leaf 109,
        leaf 112,
        leaf 111,
        leaf 114,
        leaf 116,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 46,
        leaf 80,
        leaf 114,
        leaf 111,
        leaf 116,
        leaf 111,
        leaf 116,
        leaf 121,
        leaf 112,
        leaf 101,
        leaf 115,
        leaf 46,
        leaf 75,
        leaf 101,
        leaf 114,
        leaf 110,
        leaf 101,
        leaf 108,
        leaf 46,
        leaf 82,
        leaf 101,
        leaf 97,
        leaf 100,
        leaf 101,
        leaf 114,
        leaf 10,
        leaf 10,
        leaf 47,
        leaf 45,
        leaf 33,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 110,
        leaf 101,
        leaf 114,
        leaf 97,
        leaf 116,
        leaf 101,
        leaf 100,
        leaf 32,
        leaf 102,
        leaf 114,
        leaf 111,
        leaf 109,
        leaf 32,
        leaf 97,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 32,
        leaf 112,
        leaf 114,
        leaf 111,
        leaf 103,
        leaf 114,
        leaf 97,
        leaf 109,
        leaf 32,
        leaf 98,
        leaf 121,
        leaf 32,
        leaf 96,
        leaf 98,
        leaf 111,
        leaf 111,
        leaf 116,
        leaf 115,
        leaf 116,
        leaf 114,
        leaf 97,
        leaf 112,
        leaf 47,
        leaf 115,
        leaf 116,
        leaf 97,
        leaf 103,
        leaf 101,
        leaf 49,
        leaf 47,
        leaf 108,
        leaf 101,
        leaf 97,
        leaf 110,
        leaf 46,
        leaf 103,
        leaf 101,
        leaf 98,
        leaf 96,
        leaf 46,
        leaf 32,
        leaf 45,
        leaf 47,
        leaf 10,
        leaf 10,
        leaf 64,
        leaf 91,
        leaf 101,
        leaf 120,
        leaf 112,
        leaf 111,
        leaf 115,
        leaf 101,
        leaf 93,
        leaf 32,
        leaf 112,
        leaf 117,
        leaf 98,
        leaf 108,
        leaf 105,
        leaf 99,
        leaf 32,
        leaf 115,
        leaf 101,
        leaf 99,
        leaf 116,
        leaf 105,
        leaf 111,
        leaf 110,
        leaf 10,
        leaf 10,
        leaf 111,
        leaf 112,
        leaf 101,
        leaf 110,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 46,
        leaf 75,
        leaf 101,
        leaf 114,
        leaf 110,
        leaf 101,
        leaf 108,
        leaf 10,
        leaf 111,
        leaf 112,
        leaf 101,
        leaf 110,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 46,
        leaf 75,
        leaf 101,
        leaf 114,
        leaf 110,
        leaf 101,
        leaf 108,
        leaf 32,
        leaf 114,
        leaf 101,
        leaf 110,
        leaf 97,
        leaf 109,
        leaf 105,
        leaf 110,
        leaf 103,
        leaf 32,
        leaf 84,
        leaf 114,
        leaf 101,
        leaf 101,
        leaf 32,
        leaf 226,
        leaf 134,
        leaf 146,
        leaf 32,
        leaf 84,
        leaf 10,
        leaf 10,
        leaf 110,
        leaf 97,
        leaf 109,
        leaf 101,
        leaf 115,
        leaf 112,
        leaf 97,
        leaf 99,
        leaf 101,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 66,
        leaf 111,
        leaf 111,
        leaf 116]))

def «LeanBackend.tFooter» :=
  «LeanBackend.text»
    (Const.children
      (mk 0 [leaf 10,
        leaf 10,
        leaf 101,
        leaf 110,
        leaf 100,
        leaf 32,
        leaf 71,
        leaf 101,
        leaf 98,
        leaf 66,
        leaf 111,
        leaf 111,
        leaf 116,
        leaf 10,
        leaf 10,
        leaf 101,
        leaf 110,
        leaf 100,
        leaf 10]))

def «LeanBackend.wOf» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x1 : T := ((x0).1).1; x1

def «LeanBackend.hbOf» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x1 : T := (((x0).1).2).1; x1

def «LeanBackend.ldOf» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x1 : T := (((x0).1).2).2; x1

def «LeanBackend.ms» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T × (T × T) := (x0, (x1, x2)); x3

def «LeanBackend.revOnto» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x2 : T) (x3 : List T → List T) (x4 : List T) => x3 (x2 :: x4))
      (fun (x2 : List T) => x2)
      x0
      x1;
    x2

def «LeanBackend.catWP» :=
  fun (x0 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
    (x1 : (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) =>
    let x2 : (T × (T × T)) ×
      (T →
        T →
          T →
            (T × List T) →
              T ×
                List
                  T) := («LeanBackend.ms»
      (Const.add («LeanBackend.wOf» x0) («LeanBackend.wOf» x1))
      («Prelude.or» («LeanBackend.hbOf» x0) («LeanBackend.hbOf» x1))
      (if («LeanBackend.hbOf» x0).label ≠ 0 then
        «LeanBackend.ldOf» x0
      else
        Const.add («LeanBackend.wOf» x0) («LeanBackend.ldOf» x1)),
      fun (x2 : T) (x3 : T) (x4 : T) (x5 : T × List T) =>
        (x1).2
          x2
          x3
          x4
          ((x0).2
            x2
            x3
            (Const.add
              («LeanBackend.ldOf» x1)
              (if («LeanBackend.hbOf» x1).label ≠ 0 then leaf 0 else x4))
            x5));
    x2

def «LeanBackend.layout» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : (T × (T × T)) ×
                     (T →
                       T →
                         T →
                           (T × List T) →
                             T ×
                               List
                                 T) := Const.para
                     (α := Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                     (fun (x1 : T)
                        (x2 : List
                          (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                        (_ : Unit) =>
                       if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                         let x4 : (Unit →
                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                           List
                             (Unit →
                               (T × (T × T)) ×
                                 (T →
                                   T →
                                     T →
                                       (T × List T) →
                                         T ×
                                           List
                                             T)) := Const.lcase
                           (α := Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                           (β := (Unit →
                             (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                             List (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                           x2
                           (fun (_ : Unit) =>
                             ((leaf 0, (leaf 0, leaf 0)),
                               fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                 (leaf 0, ([] : List T))),
                             ([] : List (Unit →
                               (T × (T × T)) × (T → T → T → (T × List T) → T × List T))))
                           (fun (x4 : Unit →
                                (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                              (x5 : List
                                (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))) =>
                             (x4, x5));
                         let x5 : T := Const.child x1 (leaf 0);
                         let _ : (Unit →
                           (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                           List
                             (Unit →
                               (T × (T × T)) ×
                                 (T →
                                   T →
                                     T →
                                       (T × List T) →
                                         T ×
                                           List
                                             T)) := Const.lcase
                           (α := Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                           (β := (Unit →
                             (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                             List (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                           (x4).2
                           (fun (_ : Unit) =>
                             ((leaf 0, (leaf 0, leaf 0)),
                               fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                 (leaf 0, ([] : List T))),
                             ([] : List (Unit →
                               (T × (T × T)) × (T → T → T → (T × List T) → T × List T))))
                           (fun (x6 : Unit →
                                (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                              (x7 : List
                                (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))) =>
                             (x6, x7));
                         let x7 : T := Const.child x1 (leaf 1);
                         («LeanBackend.ms» x5 (leaf 0) x5,
                           fun (_ : T) (_ : T) (_ : T) (x11 : T × List T) =>
                             (Const.add (x11).1 x5,
                               «LeanBackend.revOnto»
                                 (let x12 : T := x7;
                                  let x13 : List
                                    T := Const.iter
                                    (α := List T)
                                    (fun (x13 : List T) =>
                                      Const.lcase
                                        (α := T)
                                        (β := List T)
                                        x13
                                        ([] : List T)
                                        (fun (_ : T) (x15 : List T) => x15))
                                    (Const.children x12)
                                    (leaf 0);
                                  x13)
                                 (x11).2))
                       else
                         if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                           let x4 : List
                             ((T × (T × T)) ×
                               (T →
                                 T →
                                   T →
                                     (T × List T) →
                                       T ×
                                         List
                                           T)) := Const.foldr
                             (α := Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                             (β := List ((T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                             (fun (x4 : Unit →
                                  (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                (x5 : List
                                  ((T × (T × T)) × (T → T → T → (T × List T) → T × List T))) =>
                               ((x4 ()) :: x5))
                             ([] : List ((T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                             x2;
                           Const.foldr
                             (α := (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                             (β := (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                             «LeanBackend.catWP»
                             («LeanBackend.ms» (leaf 0) (leaf 0) (leaf 0),
                               fun (_ : T) (_ : T) (_ : T) (x8 : T × List T) => x8)
                             x4
                         else
                           if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                             let x4 : (Unit →
                               (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                               List
                                 (Unit →
                                   (T × (T × T)) ×
                                     (T →
                                       T →
                                         T →
                                           (T × List T) →
                                             T ×
                                               List
                                                 T)) := Const.lcase
                               (α := Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                               (β := (Unit →
                                 (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                                 List
                                   (Unit → (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                               x2
                               (fun (_ : Unit) =>
                                 ((leaf 0, (leaf 0, leaf 0)),
                                   fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                     (leaf 0, ([] : List T))),
                                 ([] : List (Unit →
                                   (T × (T × T)) × (T → T → T → (T × List T) → T × List T))))
                               (fun (x4 : Unit →
                                    (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                  (x5 : List
                                    (Unit →
                                      (T × (T × T)) × (T → T → T → (T × List T) → T × List T))) =>
                                 (x4, x5));
                             let x5 : (T × (T × T)) ×
                               (T → T → T → (T × List T) → T × List T) := (x4).1 ();
                             ((x5).1,
                               fun (x6 : T) (x7 : T) (x8 : T) (x9 : T × List T) =>
                                 (x5).2 (Const.add x6 (leaf 2)) x7 x8 x9)
                           else
                             if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
                               («LeanBackend.ms» (leaf 1) (leaf 1) (leaf 0),
                                 fun (x4 : T) (x5 : T) (_ : T) (x7 : T × List T) =>
                                   if (x5).label ≠ 0 then
                                     (Const.add (x7).1 (leaf 1), ((leaf 32) :: (x7).2))
                                   else
                                     (x4,
                                       «LeanBackend.revOnto»
                                         («Prelude.replicate» x4 (leaf 32))
                                         ((leaf 10) :: (x7).2)))
                             else
                               if (Const.eq (Const.label x1) (leaf 4)).label ≠ 0 then
                                 let x4 : (Unit →
                                   (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                                   List
                                     (Unit →
                                       (T × (T × T)) ×
                                         (T →
                                           T →
                                             T →
                                               (T × List T) →
                                                 T ×
                                                   List
                                                     T)) := Const.lcase
                                   (α := Unit →
                                     (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                   (β := (Unit →
                                     (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                                     List
                                       (Unit →
                                         (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                   x2
                                   (fun (_ : Unit) =>
                                     ((leaf 0, (leaf 0, leaf 0)),
                                       fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                         (leaf 0, ([] : List T))),
                                     ([] : List (Unit →
                                       (T × (T × T)) × (T → T → T → (T × List T) → T × List T))))
                                   (fun (x4 : Unit →
                                        (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                      (x5 : List
                                        (Unit →
                                          (T × (T × T)) ×
                                            (T → T → T → (T × List T) → T × List T))) =>
                                     (x4, x5));
                                 let x5 : (T × (T × T)) ×
                                   (T → T → T → (T × List T) → T × List T) := (x4).1 ();
                                 («LeanBackend.ms»
                                   («LeanBackend.wOf» x5)
                                   (leaf 0)
                                   («LeanBackend.wOf» x5),
                                   fun (x6 : T) (x7 : T) (x8 : T) (x9 : T × List T) =>
                                     (x5).2
                                       x6
                                       («Prelude.or»
                                         x7
                                         («Prelude.and»
                                           (Const.lt
                                             (Const.add
                                               (x9).1
                                               (Const.add («LeanBackend.wOf» x5) x8))
                                             (leaf 101))
                                           (Const.lt
                                             (Const.add
                                               (Const.sub (x9).1 x6)
                                               (Const.add («LeanBackend.wOf» x5) x8))
                                             (leaf 71))))
                                       x8
                                       x9)
                               else
                                 let x4 : (Unit →
                                   (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                                   List
                                     (Unit →
                                       (T × (T × T)) ×
                                         (T →
                                           T →
                                             T →
                                               (T × List T) →
                                                 T ×
                                                   List
                                                     T)) := Const.lcase
                                   (α := Unit →
                                     (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                   (β := (Unit →
                                     (T × (T × T)) × (T → T → T → (T × List T) → T × List T)) ×
                                     List
                                       (Unit →
                                         (T × (T × T)) × (T → T → T → (T × List T) → T × List T)))
                                   x2
                                   (fun (_ : Unit) =>
                                     ((leaf 0, (leaf 0, leaf 0)),
                                       fun (_ : T) (_ : T) (_ : T) (_ : T × List T) =>
                                         (leaf 0, ([] : List T))),
                                     ([] : List (Unit →
                                       (T × (T × T)) × (T → T → T → (T × List T) → T × List T))))
                                   (fun (x4 : Unit →
                                        (T × (T × T)) × (T → T → T → (T × List T) → T × List T))
                                      (x5 : List
                                        (Unit →
                                          (T × (T × T)) ×
                                            (T → T → T → (T × List T) → T × List T))) =>
                                     (x4, x5));
                                 let x5 : (T × (T × T)) ×
                                   (T → T → T → (T × List T) → T × List T) := (x4).1 ();
                                 ((x5).1,
                                   fun (_ : T) (x7 : T) (x8 : T) (x9 : T × List T) =>
                                     (x5).2 (x9).1 x7 x8 x9))
                     x0
                     ();
                   Const.node
                     (leaf 0)
                     («Prelude.reverse»
                       ((x1).2 (leaf 0) (leaf 0) (leaf 0) (leaf 0, ([] : List T))).2));
    x1

def «LeanBackend.param» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.params» :=
  fun (x0 : List T) => Const.node (leaf 0) x0

def «LeanBackend/Ps.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «LeanBackend/Ps.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «LeanBackend/Ps.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «LeanBackend/Ps.reverse» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x1 : T) (x2 : List T → List T) (x3 : List T) => x2 (x1 :: x3))
      (fun (x1 : List T) => x1)
      x0
      ([] : List T);
    x1

def «LeanBackend/Ps.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «LeanBackend/Ps.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «LeanBackend/Ps.tail» x1 x0;
    x2

def «LeanBackend/Ps.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («LeanBackend/Ps.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «LeanBackend.atomic» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «LeanBackend.compound» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «LeanBackend.fn» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.ap» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 3) (x0 :: x1)

def «LeanBackend.binderDocs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List
                     T := Const.iter
                     (α := List T)
                     (fun (x2 : List T) =>
                       Const.lcase
                         (α := T)
                         (β := List T)
                         x2
                         ([] : List T)
                         (fun (_ : T) (x4 : List T) => x4))
                     (Const.children x1)
                     (leaf 0);
                   «LeanBackend.joinWith»
                     «LeanBackend.line»
                     (Const.foldr
                       (α := T)
                       (β := List T)
                       (fun (x3 : T) (x4 : List T) =>
                         let x5 : T := x3;
                         let x6 : T := Const.child x5 (leaf 0);
                         let x7 : T := Const.child x5 (leaf 1);
                         ((«LeanBackend.cat5»
                           «LeanBackend.tLp»
                           x6
                           «LeanBackend.tColon»
                           x7
                           «LeanBackend.tRp») ::
                           x4))
                       ([] : List T)
                       x2));
    x1

def «LeanBackend.shDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); x2
                   else
                     if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                       let x2 : T := Const.child x1 (leaf 0); x2
                     else
                       if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                         let x2 : T := Const.child x1 (leaf 0);
                         let x3 : T := Const.child x1 (leaf 1);
                         «LeanBackend.grp»
                           («LeanBackend.cat2»
                             («LeanBackend.align»
                               («LeanBackend.grp»
                                 («LeanBackend.cat3»
                                   «LeanBackend.tFun»
                                   («LeanBackend.nest» («LeanBackend.binderDocs» x2))
                                   «LeanBackend.tDoubleArrow»)))
                             («LeanBackend.indented» x3))
                       else
                         let x2 : T := Const.child x1 (leaf 0);
                         let x3 : List
                           T := Const.iter
                           (α := List T)
                           (fun (x3 : List T) =>
                             Const.lcase
                               (α := T)
                               (β := List T)
                               x3
                               ([] : List T)
                               (fun (_ : T) (x5 : List T) => x5))
                           (Const.children x1)
                           (leaf 1);
                         «LeanBackend.grp»
                           («LeanBackend.cat2»
                             x2
                             («LeanBackend.nest»
                               («LeanBackend.cat»
                                 (Const.foldr
                                   (α := T)
                                   (β := List T)
                                   (fun (x4 : T) (x5 : List T) =>
                                     («LeanBackend.line» :: (x4 :: x5)))
                                   ([] : List T)
                                   x3)))));
    x1

def «LeanBackend.argDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); x2
                   else
                     «LeanBackend.cat3»
                       «LeanBackend.tLp»
                       («LeanBackend.shDoc» x0)
                       «LeanBackend.tRp»);
    x1

def «LeanBackend.valDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); x2
                   else
                     if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
                       let _ : T := Const.child x1 (leaf 0);
                       let _ : List
                         T := Const.iter
                         (α := List T)
                         (fun (x3 : List T) =>
                           Const.lcase
                             (α := T)
                             (β := List T)
                             x3
                             ([] : List T)
                             (fun (_ : T) (x5 : List T) => x5))
                         (Const.children x1)
                         (leaf 1);
                       «LeanBackend.shDoc» x0
                     else
                       «LeanBackend.cat3»
                         «LeanBackend.tLp»
                         («LeanBackend.shDoc» x0)
                         «LeanBackend.tRp»);
    x1

def «LeanBackend.opDoc» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     «LeanBackend.cat3» «LeanBackend.tLp» x2 «LeanBackend.tRp»
                   else
                     «LeanBackend.shDoc» x0);
    x1

def «LeanBackend.ktT» := Const.node (leaf 0) ([] : List T)

def «LeanBackend.ktUnit» := Const.node (leaf 1) ([] : List T)

def «LeanBackend.ktProd» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.ktArrow» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 3) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.ktList» :=
  fun (x0 : T) => Const.node (leaf 4) (x0 :: ([] : List T))

def «LeanBackend.kt5» := Const.node (leaf 5) ([] : List T)

def «LeanBackend.kt6» := Const.node (leaf 6) ([] : List T)

def «LeanBackend.kt7» := Const.node (leaf 7) ([] : List T)

def «LeanBackend.kVar» :=
  fun (x0 : T) => Const.node (leaf 8) (x0 :: ([] : List T))

def «LeanBackend.kLam» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 9) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.kApp» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 10) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.kUnit» := Const.node (leaf 11) ([] : List T)

def «LeanBackend.kPair» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 12) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.kFst» :=
  fun (x0 : T) => Const.node (leaf 13) (x0 :: ([] : List T))

def «LeanBackend.kSnd» :=
  fun (x0 : T) => Const.node (leaf 14) (x0 :: ([] : List T))

def «LeanBackend.kQuote» :=
  fun (x0 : T) => Const.node (leaf 15) (x0 :: ([] : List T))

def «LeanBackend.kIf» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 16) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «LeanBackend.kFold» :=
  fun (x0 : T) => Const.node (leaf 17) (x0 :: ([] : List T))

def «LeanBackend.kIter» :=
  fun (x0 : T) => Const.node (leaf 18) (x0 :: ([] : List T))

def «LeanBackend.kNil» :=
  fun (x0 : T) => Const.node (leaf 19) (x0 :: ([] : List T))

def «LeanBackend.kCons» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 20) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.kFoldr» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 21) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.kPrim» :=
  fun (x0 : T) => Const.node (leaf 22) (x0 :: ([] : List T))

def «LeanBackend.kRef» :=
  fun (x0 : T) => Const.node (leaf 23) (x0 :: ([] : List T))

def «LeanBackend.kLcase» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 24) (x0 :: (x1 :: ([] : List T)))

def «LeanBackend.kPara» :=
  fun (x0 : T) => Const.node (leaf 25) (x0 :: ([] : List T))

def «LeanBackend.Kt.member» :=
  fun (x0 : T) =>
    Const.mod
      (Const.div
        (Const.fold
          (α := T)
          (fun (x1 : T) (x2 : List T) =>
            let x3 : T := Const.node (leaf 0) x2;
            Const.add
              (if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                Const.eq (Const.arity x3) (leaf 0)
              else
                if (Const.eq x1 (leaf 1)).label ≠ 0 then
                  Const.eq (Const.arity x3) (leaf 0)
                else
                  if (Const.eq x1 (leaf 2)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                      if (Const.mod
                        (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                        (leaf 2)).label ≠ 0 then
                        Const.mod (Const.div (Const.child x3 (leaf 1)) (leaf 1)) (leaf 2)
                      else
                        leaf 0
                    else
                      leaf 0
                  else
                    if (Const.eq x1 (leaf 3)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                        if (Const.mod
                          (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                          (leaf 2)).label ≠ 0 then
                          Const.mod (Const.div (Const.child x3 (leaf 1)) (leaf 1)) (leaf 2)
                        else
                          leaf 0
                      else
                        leaf 0
                    else
                      if (Const.eq x1 (leaf 4)).label ≠ 0 then
                        if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                          Const.mod (Const.div (Const.child x3 (leaf 0)) (leaf 1)) (leaf 2)
                        else
                          leaf 0
                      else
                        if (Const.eq x1 (leaf 5)).label ≠ 0 then
                          Const.eq (Const.arity x3) (leaf 0)
                        else
                          if (Const.eq x1 (leaf 6)).label ≠ 0 then
                            Const.eq (Const.arity x3) (leaf 0)
                          else
                            if (Const.eq x1 (leaf 7)).label ≠ 0 then
                              Const.eq (Const.arity x3) (leaf 0)
                            else
                              if (Const.eq x1 (leaf 8)).label ≠ 0 then
                                Const.eq (Const.arity x3) (leaf 1)
                              else
                                if (Const.eq x1 (leaf 9)).label ≠ 0 then
                                  if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                                    if (Const.mod
                                      (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                      (leaf 2)).label ≠ 0 then
                                      Const.mod
                                        (Const.div (Const.child x3 (leaf 1)) (leaf 1))
                                        (leaf 2)
                                    else
                                      leaf 0
                                  else
                                    leaf 0
                                else
                                  if (Const.eq x1 (leaf 10)).label ≠ 0 then
                                    if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                                      if (Const.mod
                                        (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                        (leaf 2)).label ≠ 0 then
                                        Const.mod
                                          (Const.div (Const.child x3 (leaf 1)) (leaf 1))
                                          (leaf 2)
                                      else
                                        leaf 0
                                    else
                                      leaf 0
                                  else
                                    if (Const.eq x1 (leaf 11)).label ≠ 0 then
                                      Const.eq (Const.arity x3) (leaf 0)
                                    else
                                      if (Const.eq x1 (leaf 12)).label ≠ 0 then
                                        if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                                          if (Const.mod
                                            (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                            (leaf 2)).label ≠ 0 then
                                            Const.mod
                                              (Const.div (Const.child x3 (leaf 1)) (leaf 1))
                                              (leaf 2)
                                          else
                                            leaf 0
                                        else
                                          leaf 0
                                      else
                                        if (Const.eq x1 (leaf 13)).label ≠ 0 then
                                          if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                                            Const.mod
                                              (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                              (leaf 2)
                                          else
                                            leaf 0
                                        else
                                          if (Const.eq x1 (leaf 14)).label ≠ 0 then
                                            if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                                              Const.mod
                                                (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                                (leaf 2)
                                            else
                                              leaf 0
                                          else
                                            if (Const.eq x1 (leaf 15)).label ≠ 0 then
                                              Const.eq (Const.arity x3) (leaf 1)
                                            else
                                              if (Const.eq x1 (leaf 16)).label ≠ 0 then
                                                if (Const.eq
                                                  (Const.arity x3)
                                                  (leaf 3)).label ≠ 0 then
                                                  if (Const.mod
                                                    (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                                    (leaf 2)).label ≠ 0 then
                                                    if (Const.mod
                                                      (Const.div (Const.child x3 (leaf 1)) (leaf 1))
                                                      (leaf 2)).label ≠ 0 then
                                                      Const.mod
                                                        (Const.div
                                                          (Const.child x3 (leaf 2))
                                                          (leaf 1))
                                                        (leaf 2)
                                                    else
                                                      leaf 0
                                                  else
                                                    leaf 0
                                                else
                                                  leaf 0
                                              else
                                                if (Const.eq x1 (leaf 17)).label ≠ 0 then
                                                  if (Const.eq
                                                    (Const.arity x3)
                                                    (leaf 1)).label ≠ 0 then
                                                    Const.mod
                                                      (Const.div (Const.child x3 (leaf 0)) (leaf 1))
                                                      (leaf 2)
                                                  else
                                                    leaf 0
                                                else
                                                  if (Const.eq x1 (leaf 18)).label ≠ 0 then
                                                    if (Const.eq
                                                      (Const.arity x3)
                                                      (leaf 1)).label ≠ 0 then
                                                      Const.mod
                                                        (Const.div
                                                          (Const.child x3 (leaf 0))
                                                          (leaf 1))
                                                        (leaf 2)
                                                    else
                                                      leaf 0
                                                  else
                                                    if (Const.eq x1 (leaf 19)).label ≠ 0 then
                                                      if (Const.eq
                                                        (Const.arity x3)
                                                        (leaf 1)).label ≠ 0 then
                                                        Const.mod
                                                          (Const.div
                                                            (Const.child x3 (leaf 0))
                                                            (leaf 1))
                                                          (leaf 2)
                                                      else
                                                        leaf 0
                                                    else
                                                      if (Const.eq x1 (leaf 20)).label ≠ 0 then
                                                        if (Const.eq
                                                          (Const.arity x3)
                                                          (leaf 2)).label ≠ 0 then
                                                          if (Const.mod
                                                            (Const.div
                                                              (Const.child x3 (leaf 0))
                                                              (leaf 1))
                                                            (leaf 2)).label ≠ 0 then
                                                            Const.mod
                                                              (Const.div
                                                                (Const.child x3 (leaf 1))
                                                                (leaf 1))
                                                              (leaf 2)
                                                          else
                                                            leaf 0
                                                        else
                                                          leaf 0
                                                      else
                                                        if (Const.eq x1 (leaf 21)).label ≠ 0 then
                                                          if (Const.eq
                                                            (Const.arity x3)
                                                            (leaf 2)).label ≠ 0 then
                                                            if (Const.mod
                                                              (Const.div
                                                                (Const.child x3 (leaf 0))
                                                                (leaf 1))
                                                              (leaf 2)).label ≠ 0 then
                                                              Const.mod
                                                                (Const.div
                                                                  (Const.child x3 (leaf 1))
                                                                  (leaf 1))
                                                                (leaf 2)
                                                            else
                                                              leaf 0
                                                          else
                                                            leaf 0
                                                        else
                                                          if (Const.eq x1 (leaf 22)).label ≠ 0 then
                                                            Const.eq (Const.arity x3) (leaf 1)
                                                          else
                                                            if (Const.eq
                                                              x1
                                                              (leaf 23)).label ≠ 0 then
                                                              Const.eq (Const.arity x3) (leaf 1)
                                                            else
                                                              if (Const.eq
                                                                x1
                                                                (leaf 24)).label ≠ 0 then
                                                                if (Const.eq
                                                                  (Const.arity x3)
                                                                  (leaf 2)).label ≠ 0 then
                                                                  if (Const.mod
                                                                    (Const.div
                                                                      (Const.child x3 (leaf 0))
                                                                      (leaf 1))
                                                                    (leaf 2)).label ≠ 0 then
                                                                    Const.mod
                                                                      (Const.div
                                                                        (Const.child x3 (leaf 1))
                                                                        (leaf 1))
                                                                      (leaf 2)
                                                                  else
                                                                    leaf 0
                                                                else
                                                                  leaf 0
                                                              else
                                                                if (Const.eq
                                                                  x1
                                                                  (leaf 25)).label ≠ 0 then
                                                                  if (Const.eq
                                                                    (Const.arity x3)
                                                                    (leaf 1)).label ≠ 0 then
                                                                    Const.mod
                                                                      (Const.div
                                                                        (Const.child x3 (leaf 0))
                                                                        (leaf 1))
                                                                      (leaf 2)
                                                                  else
                                                                    leaf 0
                                                                else
                                                                  leaf 0).label ≠ 0 then
                leaf 1
              else
                leaf 0)
              (leaf 0))
          x0)
        (leaf 1))
      (leaf 2)

def «LeanBackend.orList» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x2 : T) (x3 : List T → List T) (x4 : List T) =>
        Const.lcase
          (α := T)
          (β := List T)
          x4
          (x2 :: (x3 ([] : List T)))
          (fun (x5 : T) (x6 : List T) => ((«Prelude.or» x2 x5) :: (x3 x6))))
      (fun (x2 : List T) => x2)
      x0
      x1;
    x2

def «LeanBackend.closedSh» :=
  fun (x0 : T) =>
    let x1 : List T × (T → T) := (([] : List T), fun (_ : T) => x0); x1

def «LeanBackend.closed» :=
  fun (x0 : T) =>
    let x1 : List T ×
      (T → T) := «LeanBackend.closedSh» («LeanBackend.atomic» x0);
    x1

def «LeanBackend.tyDoc» :=
  fun (x0 : List T × (T → T)) =>
    let x1 : T := «LeanBackend.shDoc» ((x0).2 (leaf 0)); x1

def «LeanBackend.varDoc» :=
  fun (x0 : T) =>
    let x1 : T := «LeanBackend.text»
      ((leaf 120) :: («Datatype.decimalChars» x0));
    x1

def «LeanBackend.namedArg» :=
  fun (x0 : T) (x1 : List T × (T → T)) =>
    let x2 : T := «LeanBackend.cat5»
      «LeanBackend.tLp»
      x0
      «LeanBackend.tColonEq»
      («LeanBackend.tyDoc» x1)
      «LeanBackend.tRp»;
    x2

def «LeanBackend.quoteDoc» :=
  fun (x0 : T) =>
    let x1 : T := Const.fold
      (α := T)
      (fun (x1 : T) (x2 : List T) =>
        if (Const.lt (leaf 0) («LeanBackend/Docs.length» x2)).label ≠ 0 then
          «LeanBackend.grp»
            («LeanBackend.cat»
              («LeanBackend.tMk» ::
                ((«LeanBackend.text» («Datatype.decimalChars» x1)) ::
                  («LeanBackend.tSpLb» ::
                    ((«LeanBackend.nest»
                      («LeanBackend.joinWith»
                        («LeanBackend.cat2» «LeanBackend.tComma» «LeanBackend.line»)
                        x2)) ::
                      («LeanBackend/Docs.single» «LeanBackend.tRb»))))))
        else
          «LeanBackend.cat2»
            «LeanBackend.tLeaf»
            («LeanBackend.text» («Datatype.decimalChars» x1)))
      x0;
    x1

def «LeanBackend.letDoc» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : List T := «LeanBackend/Ps.tail» x0;
                   let x4 : T := «LeanBackend/Ps.atOr»
                     («LeanBackend.param» «LeanBackend.tUnder» «LeanBackend.tUnder»)
                     x0
                     (leaf 0);
                   let x5 : T := Const.child x4 (leaf 0);
                   let x6 : T := Const.child x4 (leaf 1);
                   «LeanBackend.align»
                     («LeanBackend.grp»
                       («LeanBackend.cat»
                         («LeanBackend.tLet» ::
                           (x5 ::
                             («LeanBackend.tColon» ::
                               (x6 ::
                                 («LeanBackend.tColonEq» ::
                                   ((«LeanBackend.valDoc» x2) ::
                                     («LeanBackend.tSemi» ::
                                       («LeanBackend.line» ::
                                         («LeanBackend/Docs.single»
                                           (if (Const.lt
                                             (leaf 0)
                                             («LeanBackend/Ps.length» x3)).label ≠ 0 then
                                             «LeanBackend.shDoc»
                                               («LeanBackend.fn» («LeanBackend.params» x3) x1)
                                           else
                                             x1)))))))))))));
    x3

def «LeanBackend.emTerm» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T ×
      (T →
        T) := Const.para
      (α := Unit → List T × (T → T))
      (fun (x2 : T) (x3 : List (Unit → List T × (T → T))) (_ : Unit) =>
        if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
          «LeanBackend.closed» «LeanBackend.tT»
        else
          if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
            «LeanBackend.closed» «LeanBackend.tUnitTy»
          else
            if (Const.eq (Const.label x2) (leaf 2)).label ≠ 0 then
              let x5 : (Unit → List T × (T → T)) ×
                List
                  (Unit →
                    List T ×
                      (T →
                        T)) := Const.lcase
                (α := Unit → List T × (T → T))
                (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                x3
                (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                  ([] : List (Unit → List T × (T → T))))
                (fun (x5 : Unit → List T × (T → T))
                   (x6 : List (Unit → List T × (T → T))) =>
                  (x5, x6));
              let x6 : List T × (T → T) := (x5).1 ();
              let x7 : (Unit → List T × (T → T)) ×
                List
                  (Unit →
                    List T ×
                      (T →
                        T)) := Const.lcase
                (α := Unit → List T × (T → T))
                (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                (x5).2
                (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                  ([] : List (Unit → List T × (T → T))))
                (fun (x7 : Unit → List T × (T → T))
                   (x8 : List (Unit → List T × (T → T))) =>
                  (x7, x8));
              let x8 : List T × (T → T) := (x7).1 ();
              «LeanBackend.closedSh»
                («LeanBackend.compound»
                  («LeanBackend.grp»
                    («LeanBackend.cat3»
                      («LeanBackend.opDoc» ((x6).2 (leaf 0)))
                      «LeanBackend.tTimes»
                      («LeanBackend.indented» («LeanBackend.opDoc» ((x8).2 (leaf 0)))))))
            else
              if (Const.eq (Const.label x2) (leaf 3)).label ≠ 0 then
                let x5 : (Unit → List T × (T → T)) ×
                  List
                    (Unit →
                      List T ×
                        (T →
                          T)) := Const.lcase
                  (α := Unit → List T × (T → T))
                  (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                  x3
                  (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                    ([] : List (Unit → List T × (T → T))))
                  (fun (x5 : Unit → List T × (T → T))
                     (x6 : List (Unit → List T × (T → T))) =>
                    (x5, x6));
                let x6 : List T × (T → T) := (x5).1 ();
                let x7 : (Unit → List T × (T → T)) ×
                  List
                    (Unit →
                      List T ×
                        (T →
                          T)) := Const.lcase
                  (α := Unit → List T × (T → T))
                  (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                  (x5).2
                  (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                    ([] : List (Unit → List T × (T → T))))
                  (fun (x7 : Unit → List T × (T → T))
                     (x8 : List (Unit → List T × (T → T))) =>
                    (x7, x8));
                let x8 : List T × (T → T) := (x7).1 ();
                «LeanBackend.closedSh»
                  («LeanBackend.compound»
                    («LeanBackend.grp»
                      («LeanBackend.cat3»
                        («LeanBackend.opDoc» ((x6).2 (leaf 0)))
                        «LeanBackend.tTo»
                        («LeanBackend.indented» («LeanBackend.tyDoc» x8)))))
              else
                if (Const.eq (Const.label x2) (leaf 4)).label ≠ 0 then
                  let x5 : (Unit → List T × (T → T)) ×
                    List
                      (Unit →
                        List T ×
                          (T →
                            T)) := Const.lcase
                    (α := Unit → List T × (T → T))
                    (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                    x3
                    (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                      ([] : List (Unit → List T × (T → T))))
                    (fun (x5 : Unit → List T × (T → T))
                       (x6 : List (Unit → List T × (T → T))) =>
                      (x5, x6));
                  let x6 : List T × (T → T) := (x5).1 ();
                  «LeanBackend.closedSh»
                    («LeanBackend.ap»
                      «LeanBackend.tList»
                      («LeanBackend/Docs.single» («LeanBackend.argDoc» ((x6).2 (leaf 0)))))
                else
                  if (Const.eq (Const.label x2) (leaf 8)).label ≠ 0 then
                    let _ : (Unit → List T × (T → T)) ×
                      List
                        (Unit →
                          List T ×
                            (T →
                              T)) := Const.lcase
                      (α := Unit → List T × (T → T))
                      (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                      x3
                      (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                        ([] : List (Unit → List T × (T → T))))
                      (fun (x5 : Unit → List T × (T → T))
                         (x6 : List (Unit → List T × (T → T))) =>
                        (x5, x6));
                    let x6 : T := Const.child x2 (leaf 0);
                    («Prelude.append»
                      («Prelude.replicate» (Const.label x6) (leaf 0))
                      («Prelude.single» (leaf 1)),
                      fun (x7 : T) =>
                        «LeanBackend.atomic»
                          («LeanBackend.varDoc»
                            (Const.sub (Const.sub x7 (leaf 1)) (Const.label x6))))
                  else
                    if (Const.eq (Const.label x2) (leaf 9)).label ≠ 0 then
                      let x5 : (Unit → List T × (T → T)) ×
                        List
                          (Unit →
                            List T ×
                              (T →
                                T)) := Const.lcase
                        (α := Unit → List T × (T → T))
                        (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                        x3
                        (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                          ([] : List (Unit → List T × (T → T))))
                        (fun (x5 : Unit → List T × (T → T))
                           (x6 : List (Unit → List T × (T → T))) =>
                          (x5, x6));
                      let x6 : List T × (T → T) := (x5).1 ();
                      let x7 : (Unit → List T × (T → T)) ×
                        List
                          (Unit →
                            List T ×
                              (T →
                                T)) := Const.lcase
                        (α := Unit → List T × (T → T))
                        (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                        (x5).2
                        (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                          ([] : List (Unit → List T × (T → T))))
                        (fun (x7 : Unit → List T × (T → T))
                           (x8 : List (Unit → List T × (T → T))) =>
                          (x7, x8));
                      let x8 : List T × (T → T) := (x7).1 ();
                      («Prelude.tail» (x8).1,
                        fun (x9 : T) =>
                          let x10 : T := Const.lcase
                            (α := T)
                            (β := T)
                            (x8).1
                            (leaf 0)
                            (fun (x10 : T) (_ : List T) => x10);
                          let x11 : T := «LeanBackend.param»
                            (if (x10).label ≠ 0 then
                              «LeanBackend.varDoc» x9
                            else
                              «LeanBackend.tUnder»)
                            («LeanBackend.tyDoc» x6);
                          let x12 : T := (x8).2 (Const.add x9 (leaf 1));
                          let x13 : T := x12;
                          if (Const.eq (Const.label x13) (leaf 2)).label ≠ 0 then
                            let x14 : T := Const.child x13 (leaf 0);
                            let x15 : T := Const.child x13 (leaf 1);
                            let x16 : T := x14;
                            let x17 : List
                              T := Const.iter
                              (α := List T)
                              (fun (x17 : List T) =>
                                Const.lcase
                                  (α := T)
                                  (β := List T)
                                  x17
                                  ([] : List T)
                                  (fun (_ : T) (x19 : List T) => x19))
                              (Const.children x16)
                              (leaf 0);
                            «LeanBackend.fn» («LeanBackend.params» (x11 :: x17)) x15
                          else
                            «LeanBackend.fn»
                              («LeanBackend.params» («LeanBackend/Ps.single» x11))
                              («LeanBackend.shDoc» x12))
                    else
                      if (Const.eq (Const.label x2) (leaf 10)).label ≠ 0 then
                        let x5 : (Unit → List T × (T → T)) ×
                          List
                            (Unit →
                              List T ×
                                (T →
                                  T)) := Const.lcase
                          (α := Unit → List T × (T → T))
                          (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                          x3
                          (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                            ([] : List (Unit → List T × (T → T))))
                          (fun (x5 : Unit → List T × (T → T))
                             (x6 : List (Unit → List T × (T → T))) =>
                            (x5, x6));
                        let x6 : List T × (T → T) := (x5).1 ();
                        let x7 : (Unit → List T × (T → T)) ×
                          List
                            (Unit →
                              List T ×
                                (T →
                                  T)) := Const.lcase
                          (α := Unit → List T × (T → T))
                          (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                          (x5).2
                          (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                            ([] : List (Unit → List T × (T → T))))
                          (fun (x7 : Unit → List T × (T → T))
                             (x8 : List (Unit → List T × (T → T))) =>
                            (x7, x8));
                        let x8 : List T × (T → T) := (x7).1 ();
                        («LeanBackend.orList» (x6).1 (x8).1,
                          fun (x9 : T) =>
                            let x10 : T := (x6).2 x9;
                            let x11 : T := (x8).2 x9;
                            let x12 : T := x10;
                            if (Const.eq (Const.label x12) (leaf 3)).label ≠ 0 then
                              let x13 : T := Const.child x12 (leaf 0);
                              let x14 : List
                                T := Const.iter
                                (α := List T)
                                (fun (x14 : List T) =>
                                  Const.lcase
                                    (α := T)
                                    (β := List T)
                                    x14
                                    ([] : List T)
                                    (fun (_ : T) (x16 : List T) => x16))
                                (Const.children x12)
                                (leaf 1);
                              «LeanBackend.ap»
                                x13
                                («LeanBackend/Docs.append»
                                  x14
                                  («LeanBackend/Docs.single» («LeanBackend.argDoc» x11)))
                            else
                              if (Const.eq (Const.label x12) (leaf 2)).label ≠ 0 then
                                let x13 : T := Const.child x12 (leaf 0);
                                let x14 : T := Const.child x12 (leaf 1);
                                «LeanBackend.compound»
                                  (let x15 : T := x13;
                                   let x16 : List
                                     T := Const.iter
                                     (α := List T)
                                     (fun (x16 : List T) =>
                                       Const.lcase
                                         (α := T)
                                         (β := List T)
                                         x16
                                         ([] : List T)
                                         (fun (_ : T) (x18 : List T) => x18))
                                     (Const.children x15)
                                     (leaf 0);
                                   «LeanBackend.letDoc» x16 x14 x11)
                              else
                                «LeanBackend.ap»
                                  («LeanBackend.argDoc» x10)
                                  («LeanBackend/Docs.single» («LeanBackend.argDoc» x11)))
                      else
                        if (Const.eq (Const.label x2) (leaf 11)).label ≠ 0 then
                          «LeanBackend.closed» «LeanBackend.tUnitV»
                        else
                          if (Const.eq (Const.label x2) (leaf 12)).label ≠ 0 then
                            let x5 : (Unit → List T × (T → T)) ×
                              List
                                (Unit →
                                  List T ×
                                    (T →
                                      T)) := Const.lcase
                              (α := Unit → List T × (T → T))
                              (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                              x3
                              (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                ([] : List (Unit → List T × (T → T))))
                              (fun (x5 : Unit → List T × (T → T))
                                 (x6 : List (Unit → List T × (T → T))) =>
                                (x5, x6));
                            let x6 : List T × (T → T) := (x5).1 ();
                            let x7 : (Unit → List T × (T → T)) ×
                              List
                                (Unit →
                                  List T ×
                                    (T →
                                      T)) := Const.lcase
                              (α := Unit → List T × (T → T))
                              (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                              (x5).2
                              (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                ([] : List (Unit → List T × (T → T))))
                              (fun (x7 : Unit → List T × (T → T))
                                 (x8 : List (Unit → List T × (T → T))) =>
                                (x7, x8));
                            let x8 : List T × (T → T) := (x7).1 ();
                            («LeanBackend.orList» (x6).1 (x8).1,
                              fun (x9 : T) =>
                                «LeanBackend.atomic»
                                  («LeanBackend.grp»
                                    («LeanBackend.cat5»
                                      «LeanBackend.tLp»
                                      («LeanBackend.shDoc» ((x6).2 x9))
                                      «LeanBackend.tComma»
                                      («LeanBackend.indented» («LeanBackend.shDoc» ((x8).2 x9)))
                                      «LeanBackend.tRp»)))
                          else
                            if (Const.eq (Const.label x2) (leaf 13)).label ≠ 0 then
                              let x5 : (Unit → List T × (T → T)) ×
                                List
                                  (Unit →
                                    List T ×
                                      (T →
                                        T)) := Const.lcase
                                (α := Unit → List T × (T → T))
                                (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                                x3
                                (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                  ([] : List (Unit → List T × (T → T))))
                                (fun (x5 : Unit → List T × (T → T))
                                   (x6 : List (Unit → List T × (T → T))) =>
                                  (x5, x6));
                              let x6 : List T × (T → T) := (x5).1 ();
                              ((x6).1,
                                fun (x7 : T) =>
                                  «LeanBackend.atomic»
                                    («LeanBackend.cat3»
                                      «LeanBackend.tLp»
                                      («LeanBackend.shDoc» ((x6).2 x7))
                                      «LeanBackend.tDot1»))
                            else
                              if (Const.eq (Const.label x2) (leaf 14)).label ≠ 0 then
                                let x5 : (Unit → List T × (T → T)) ×
                                  List
                                    (Unit →
                                      List T ×
                                        (T →
                                          T)) := Const.lcase
                                  (α := Unit → List T × (T → T))
                                  (β := (Unit → List T × (T → T)) × List (Unit → List T × (T → T)))
                                  x3
                                  (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                    ([] : List (Unit → List T × (T → T))))
                                  (fun (x5 : Unit → List T × (T → T))
                                     (x6 : List (Unit → List T × (T → T))) =>
                                    (x5, x6));
                                let x6 : List T × (T → T) := (x5).1 ();
                                ((x6).1,
                                  fun (x7 : T) =>
                                    «LeanBackend.atomic»
                                      («LeanBackend.cat3»
                                        «LeanBackend.tLp»
                                        («LeanBackend.shDoc» ((x6).2 x7))
                                        «LeanBackend.tDot2»))
                              else
                                if (Const.eq (Const.label x2) (leaf 15)).label ≠ 0 then
                                  let _ : (Unit → List T × (T → T)) ×
                                    List
                                      (Unit →
                                        List T ×
                                          (T →
                                            T)) := Const.lcase
                                    (α := Unit → List T × (T → T))
                                    (β := (Unit → List T × (T → T)) ×
                                      List (Unit → List T × (T → T)))
                                    x3
                                    (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                      ([] : List (Unit → List T × (T → T))))
                                    (fun (x5 : Unit → List T × (T → T))
                                       (x6 : List (Unit → List T × (T → T))) =>
                                      (x5, x6));
                                  let x6 : T := Const.child x2 (leaf 0);
                                  (([] : List T),
                                    fun (_ : T) =>
                                      «LeanBackend.compound» («LeanBackend.quoteDoc» x6))
                                else
                                  if (Const.eq (Const.label x2) (leaf 16)).label ≠ 0 then
                                    let x5 : (Unit → List T × (T → T)) ×
                                      List
                                        (Unit →
                                          List T ×
                                            (T →
                                              T)) := Const.lcase
                                      (α := Unit → List T × (T → T))
                                      (β := (Unit → List T × (T → T)) ×
                                        List (Unit → List T × (T → T)))
                                      x3
                                      (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                        ([] : List (Unit → List T × (T → T))))
                                      (fun (x5 : Unit → List T × (T → T))
                                         (x6 : List (Unit → List T × (T → T))) =>
                                        (x5, x6));
                                    let x6 : List T × (T → T) := (x5).1 ();
                                    let x7 : (Unit → List T × (T → T)) ×
                                      List
                                        (Unit →
                                          List T ×
                                            (T →
                                              T)) := Const.lcase
                                      (α := Unit → List T × (T → T))
                                      (β := (Unit → List T × (T → T)) ×
                                        List (Unit → List T × (T → T)))
                                      (x5).2
                                      (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                        ([] : List (Unit → List T × (T → T))))
                                      (fun (x7 : Unit → List T × (T → T))
                                         (x8 : List (Unit → List T × (T → T))) =>
                                        (x7, x8));
                                    let x8 : List T × (T → T) := (x7).1 ();
                                    let x9 : (Unit → List T × (T → T)) ×
                                      List
                                        (Unit →
                                          List T ×
                                            (T →
                                              T)) := Const.lcase
                                      (α := Unit → List T × (T → T))
                                      (β := (Unit → List T × (T → T)) ×
                                        List (Unit → List T × (T → T)))
                                      (x7).2
                                      (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                        ([] : List (Unit → List T × (T → T))))
                                      (fun (x9 : Unit → List T × (T → T))
                                         (x10 : List (Unit → List T × (T → T))) =>
                                        (x9, x10));
                                    let x10 : List T × (T → T) := (x9).1 ();
                                    («LeanBackend.orList»
                                      (x6).1
                                      («LeanBackend.orList» (x8).1 (x10).1),
                                      fun (x11 : T) =>
                                        «LeanBackend.compound»
                                          («LeanBackend.grp»
                                            («LeanBackend.cat»
                                              («LeanBackend.tIf» ::
                                                ((«LeanBackend.shDoc» ((x6).2 x11)) ::
                                                  («LeanBackend.tThen» ::
                                                    ((«LeanBackend.indented»
                                                      («LeanBackend.shDoc» ((x8).2 x11))) ::
                                                      («LeanBackend.line» ::
                                                        («LeanBackend.tElse» ::
                                                          («LeanBackend/Docs.single»
                                                            («LeanBackend.indented»
                                                              («LeanBackend.shDoc»
                                                                ((x10).2 x11)))))))))))))
                                  else
                                    if (Const.eq (Const.label x2) (leaf 17)).label ≠ 0 then
                                      let x5 : (Unit → List T × (T → T)) ×
                                        List
                                          (Unit →
                                            List T ×
                                              (T →
                                                T)) := Const.lcase
                                        (α := Unit → List T × (T → T))
                                        (β := (Unit → List T × (T → T)) ×
                                          List (Unit → List T × (T → T)))
                                        x3
                                        (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                          ([] : List (Unit → List T × (T → T))))
                                        (fun (x5 : Unit → List T × (T → T))
                                           (x6 : List (Unit → List T × (T → T))) =>
                                          (x5, x6));
                                      let x6 : List T × (T → T) := (x5).1 ();
                                      (([] : List T),
                                        fun (_ : T) =>
                                          «LeanBackend.ap»
                                            «LeanBackend.tFold»
                                            («LeanBackend/Docs.single»
                                              («LeanBackend.namedArg» «LeanBackend.tAlpha» x6)))
                                    else
                                      if (Const.eq (Const.label x2) (leaf 18)).label ≠ 0 then
                                        let x5 : (Unit → List T × (T → T)) ×
                                          List
                                            (Unit →
                                              List T ×
                                                (T →
                                                  T)) := Const.lcase
                                          (α := Unit → List T × (T → T))
                                          (β := (Unit → List T × (T → T)) ×
                                            List (Unit → List T × (T → T)))
                                          x3
                                          (fun (_ : Unit) => (([] : List T), fun (_ : T) => leaf 0),
                                            ([] : List (Unit → List T × (T → T))))
                                          (fun (x5 : Unit → List T × (T → T))
                                             (x6 : List (Unit → List T × (T → T))) =>
                                            (x5, x6));
                                        let x6 : List T × (T → T) := (x5).1 ();
                                        (([] : List T),
                                          fun (_ : T) =>
                                            «LeanBackend.ap»
                                              «LeanBackend.tIter»
                                              («LeanBackend/Docs.single»
                                                («LeanBackend.namedArg» «LeanBackend.tAlpha» x6)))
                                      else
                                        if (Const.eq (Const.label x2) (leaf 19)).label ≠ 0 then
                                          let x5 : (Unit → List T × (T → T)) ×
                                            List
                                              (Unit →
                                                List T ×
                                                  (T →
                                                    T)) := Const.lcase
                                            (α := Unit → List T × (T → T))
                                            (β := (Unit → List T × (T → T)) ×
                                              List (Unit → List T × (T → T)))
                                            x3
                                            (fun (_ : Unit) =>
                                              (([] : List T), fun (_ : T) => leaf 0),
                                              ([] : List (Unit → List T × (T → T))))
                                            (fun (x5 : Unit → List T × (T → T))
                                               (x6 : List (Unit → List T × (T → T))) =>
                                              (x5, x6));
                                          let x6 : List T × (T → T) := (x5).1 ();
                                          «LeanBackend.closed»
                                            («LeanBackend.cat3»
                                              «LeanBackend.tNilLp»
                                              («LeanBackend.argDoc» ((x6).2 (leaf 0)))
                                              «LeanBackend.tRp»)
                                        else
                                          if (Const.eq (Const.label x2) (leaf 20)).label ≠ 0 then
                                            let x5 : (Unit → List T × (T → T)) ×
                                              List
                                                (Unit →
                                                  List T ×
                                                    (T →
                                                      T)) := Const.lcase
                                              (α := Unit → List T × (T → T))
                                              (β := (Unit → List T × (T → T)) ×
                                                List (Unit → List T × (T → T)))
                                              x3
                                              (fun (_ : Unit) =>
                                                (([] : List T), fun (_ : T) => leaf 0),
                                                ([] : List (Unit → List T × (T → T))))
                                              (fun (x5 : Unit → List T × (T → T))
                                                 (x6 : List (Unit → List T × (T → T))) =>
                                                (x5, x6));
                                            let x6 : List T × (T → T) := (x5).1 ();
                                            let x7 : (Unit → List T × (T → T)) ×
                                              List
                                                (Unit →
                                                  List T ×
                                                    (T →
                                                      T)) := Const.lcase
                                              (α := Unit → List T × (T → T))
                                              (β := (Unit → List T × (T → T)) ×
                                                List (Unit → List T × (T → T)))
                                              (x5).2
                                              (fun (_ : Unit) =>
                                                (([] : List T), fun (_ : T) => leaf 0),
                                                ([] : List (Unit → List T × (T → T))))
                                              (fun (x7 : Unit → List T × (T → T))
                                                 (x8 : List (Unit → List T × (T → T))) =>
                                                (x7, x8));
                                            let x8 : List T × (T → T) := (x7).1 ();
                                            («LeanBackend.orList» (x6).1 (x8).1,
                                              fun (x9 : T) =>
                                                «LeanBackend.atomic»
                                                  («LeanBackend.grp»
                                                    («LeanBackend.cat5»
                                                      «LeanBackend.tLp»
                                                      («LeanBackend.argDoc» ((x6).2 x9))
                                                      «LeanBackend.tConsOp»
                                                      («LeanBackend.indented»
                                                        («LeanBackend.argDoc» ((x8).2 x9)))
                                                      «LeanBackend.tRp»)))
                                          else
                                            if (Const.eq (Const.label x2) (leaf 21)).label ≠ 0 then
                                              let x5 : (Unit → List T × (T → T)) ×
                                                List
                                                  (Unit →
                                                    List T ×
                                                      (T →
                                                        T)) := Const.lcase
                                                (α := Unit → List T × (T → T))
                                                (β := (Unit → List T × (T → T)) ×
                                                  List (Unit → List T × (T → T)))
                                                x3
                                                (fun (_ : Unit) =>
                                                  (([] : List T), fun (_ : T) => leaf 0),
                                                  ([] : List (Unit → List T × (T → T))))
                                                (fun (x5 : Unit → List T × (T → T))
                                                   (x6 : List (Unit → List T × (T → T))) =>
                                                  (x5, x6));
                                              let x6 : List T × (T → T) := (x5).1 ();
                                              let x7 : (Unit → List T × (T → T)) ×
                                                List
                                                  (Unit →
                                                    List T ×
                                                      (T →
                                                        T)) := Const.lcase
                                                (α := Unit → List T × (T → T))
                                                (β := (Unit → List T × (T → T)) ×
                                                  List (Unit → List T × (T → T)))
                                                (x5).2
                                                (fun (_ : Unit) =>
                                                  (([] : List T), fun (_ : T) => leaf 0),
                                                  ([] : List (Unit → List T × (T → T))))
                                                (fun (x7 : Unit → List T × (T → T))
                                                   (x8 : List (Unit → List T × (T → T))) =>
                                                  (x7, x8));
                                              let x8 : List T × (T → T) := (x7).1 ();
                                              (([] : List T),
                                                fun (_ : T) =>
                                                  «LeanBackend.ap»
                                                    «LeanBackend.tFoldr»
                                                    ((«LeanBackend.namedArg»
                                                      «LeanBackend.tAlpha»
                                                      x6) ::
                                                      («LeanBackend/Docs.single»
                                                        («LeanBackend.namedArg»
                                                          «LeanBackend.tBeta»
                                                          x8))))
                                            else
                                              if (Const.eq
                                                (Const.label x2)
                                                (leaf 22)).label ≠ 0 then
                                                let _ : (Unit → List T × (T → T)) ×
                                                  List
                                                    (Unit →
                                                      List T ×
                                                        (T →
                                                          T)) := Const.lcase
                                                  (α := Unit → List T × (T → T))
                                                  (β := (Unit → List T × (T → T)) ×
                                                    List (Unit → List T × (T → T)))
                                                  x3
                                                  (fun (_ : Unit) =>
                                                    (([] : List T), fun (_ : T) => leaf 0),
                                                    ([] : List (Unit → List T × (T → T))))
                                                  (fun (x5 : Unit → List T × (T → T))
                                                     (x6 : List (Unit → List T × (T → T))) =>
                                                    (x5, x6));
                                                let x6 : T := Const.child x2 (leaf 0);
                                                «LeanBackend.closed»
                                                  («LeanBackend.cat2»
                                                    «LeanBackend.tConstDot»
                                                    («LeanBackend.text»
                                                      (Const.children
                                                        («Prelude.at»
                                                          «Reader.primNames»
                                                          (Const.label x6)))))
                                              else
                                                if (Const.eq
                                                  (Const.label x2)
                                                  (leaf 23)).label ≠ 0 then
                                                  let _ : (Unit → List T × (T → T)) ×
                                                    List
                                                      (Unit →
                                                        List T ×
                                                          (T →
                                                            T)) := Const.lcase
                                                    (α := Unit → List T × (T → T))
                                                    (β := (Unit → List T × (T → T)) ×
                                                      List (Unit → List T × (T → T)))
                                                    x3
                                                    (fun (_ : Unit) =>
                                                      (([] : List T), fun (_ : T) => leaf 0),
                                                      ([] : List (Unit → List T × (T → T))))
                                                    (fun (x5 : Unit → List T × (T → T))
                                                       (x6 : List (Unit → List T × (T → T))) =>
                                                      (x5, x6));
                                                  let x6 : T := Const.child x2 (leaf 0);
                                                  «LeanBackend.closed»
                                                    («LeanBackend.cat3»
                                                      «LeanBackend.tLg»
                                                      («LeanBackend.text»
                                                        (Const.children
                                                          (Const.child x0 (Const.label x6))))
                                                      «LeanBackend.tRg»)
                                                else
                                                  if (Const.eq
                                                    (Const.label x2)
                                                    (leaf 24)).label ≠ 0 then
                                                    let x5 : (Unit → List T × (T → T)) ×
                                                      List
                                                        (Unit →
                                                          List T ×
                                                            (T →
                                                              T)) := Const.lcase
                                                      (α := Unit → List T × (T → T))
                                                      (β := (Unit → List T × (T → T)) ×
                                                        List (Unit → List T × (T → T)))
                                                      x3
                                                      (fun (_ : Unit) =>
                                                        (([] : List T), fun (_ : T) => leaf 0),
                                                        ([] : List (Unit → List T × (T → T))))
                                                      (fun (x5 : Unit → List T × (T → T))
                                                         (x6 : List (Unit → List T × (T → T))) =>
                                                        (x5, x6));
                                                    let x6 : List T × (T → T) := (x5).1 ();
                                                    let x7 : (Unit → List T × (T → T)) ×
                                                      List
                                                        (Unit →
                                                          List T ×
                                                            (T →
                                                              T)) := Const.lcase
                                                      (α := Unit → List T × (T → T))
                                                      (β := (Unit → List T × (T → T)) ×
                                                        List (Unit → List T × (T → T)))
                                                      (x5).2
                                                      (fun (_ : Unit) =>
                                                        (([] : List T), fun (_ : T) => leaf 0),
                                                        ([] : List (Unit → List T × (T → T))))
                                                      (fun (x7 : Unit → List T × (T → T))
                                                         (x8 : List (Unit → List T × (T → T))) =>
                                                        (x7, x8));
                                                    let x8 : List T × (T → T) := (x7).1 ();
                                                    (([] : List T),
                                                      fun (_ : T) =>
                                                        «LeanBackend.ap»
                                                          «LeanBackend.tLcase»
                                                          ((«LeanBackend.namedArg»
                                                            «LeanBackend.tAlpha»
                                                            x6) ::
                                                            («LeanBackend/Docs.single»
                                                              («LeanBackend.namedArg»
                                                                «LeanBackend.tBeta»
                                                                x8))))
                                                  else
                                                    if (Const.eq
                                                      (Const.label x2)
                                                      (leaf 25)).label ≠ 0 then
                                                      let x5 : (Unit → List T × (T → T)) ×
                                                        List
                                                          (Unit →
                                                            List T ×
                                                              (T →
                                                                T)) := Const.lcase
                                                        (α := Unit → List T × (T → T))
                                                        (β := (Unit → List T × (T → T)) ×
                                                          List (Unit → List T × (T → T)))
                                                        x3
                                                        (fun (_ : Unit) =>
                                                          (([] : List T), fun (_ : T) => leaf 0),
                                                          ([] : List (Unit → List T × (T → T))))
                                                        (fun (x5 : Unit → List T × (T → T))
                                                           (x6 : List (Unit → List T × (T → T))) =>
                                                          (x5, x6));
                                                      let x6 : List T × (T → T) := (x5).1 ();
                                                      (([] : List T),
                                                        fun (_ : T) =>
                                                          «LeanBackend.ap»
                                                            «LeanBackend.tPara»
                                                            («LeanBackend/Docs.single»
                                                              («LeanBackend.namedArg»
                                                                «LeanBackend.tAlpha»
                                                                x6)))
                                                    else
                                                      «LeanBackend.closed» «LeanBackend.tUnder»)
      x1
      ();
    x2

def «LeanBackend.defDoc» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «LeanBackend.cat3»
      «LeanBackend.line»
      «LeanBackend.line»
      («LeanBackend.grp»
        («LeanBackend.cat»
          («LeanBackend.tDef» ::
            ((«LeanBackend.text» (Const.children x0)) ::
              («LeanBackend.tAssign» ::
                («LeanBackend/Docs.single» («LeanBackend.indented» x1)))))));
    x2

def «LeanBackend.emitLean» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.child x0 (leaf 1);
                   let x2 : List T := Const.children (Const.child x0 (leaf 0));
                   let x3 : T := «Prelude.length» x2;
                   «LeanBackend.layout»
                     («LeanBackend.cat»
                       («LeanBackend.tHeader» ::
                         («LeanBackend/Docs.append»
                           (Const.foldr
                             (α := T)
                             (β := T × List T)
                             (fun (x4 : T) (x5 : T × List T) =>
                               (Const.add (x5).1 (leaf 1),
                                 ((«LeanBackend.defDoc»
                                   (Const.child x1 (Const.sub (Const.sub x3 (leaf 1)) (x5).1))
                                   (let x6 : T := x4;
                                    if («LeanBackend.Kt.member» x6).label ≠ 0 then
                                      let x7 : T := x6;
                                      «LeanBackend.shDoc» ((«LeanBackend.emTerm» x1 x7).2 (leaf 0))
                                    else
                                      «LeanBackend.tUnder»)) ::
                                   (x5).2)))
                             (leaf 0, ([] : List T))
                             x2).2
                           («LeanBackend/Docs.single» «LeanBackend.tFooter»)))));
    x1

def «mainLean» :=
  fun (x0 : T) =>
    let x1 : T := «Compile.compileWith» «LeanBackend.emitLean» x0;
    x1

end GebBoot

end
