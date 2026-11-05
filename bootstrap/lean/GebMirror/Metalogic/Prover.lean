module

public import GebMirror.Metalogic.Translation

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Prover.dNode» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «Language.mNode» x0 x1 x2; x3

def «Prover.mark» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Prover.mDeriv» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let x3 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   x3);
    x1

def «Prover.mFlag» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   x5);
    x1

def «Prover/EachMarked.all» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «Prover/EachMarked.any» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «Prover/EachMarked.isEmpty» :=
  fun (x0 : List T) =>
    let x1 : T := Const.eq
      (Const.foldr
        (α := T)
        (β := T)
        (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
        (leaf 0)
        x0)
      (leaf 0);
    x1

def «Prover/EachMarked.take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := Const.foldr
              (α := T)
              (β := T)
              (fun (_ : T) (x3 : T) => Const.add x3 (leaf 1))
              (leaf 0)
              x1;
            (Const.foldr
              (α := T)
              (β := T × List T)
              (fun (x3 : T) (x4 : T × List T) =>
                (Const.add (x4).1 (leaf 1),
                  if (Const.lt
                    (Const.sub (Const.sub x2 (x4).1) (leaf 1))
                    x0).label ≠ 0 then
                    (x3 :: (x4).2)
                  else
                    (x4).2))
              (leaf 0, ([] : List T))
              x1).2);
    x2

def «Prover/MarkedOut.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover/MarkedF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Prover/MarkedF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Prover/MarkedF.l2» x1 x2)); x3

def «Prover/MarkedF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Prover/MarkedF.l3» x1 x2 x3)); x4

def «Prover/MarkedF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Prover/MarkedF.l4» x1 x2 x3 x4)); x5

def «Prover/MarkedF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Prover/MarkedF.l5» x1 x2 x3 x4 x5)); x6

def «Prover/MarkedAt.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.dRefl» :=
  «Prover.mark»
    («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))
    (leaf 0)

def «Prover.dTrans» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Prover.mFlag» x0).label ≠ 0 then
      if («Prover.mFlag» x1).label ≠ 0 then
        «Prover.mark»
          («Prover.dNode»
            (leaf 1)
            ([] : List T)
            («Theory.l2» («Prover.mDeriv» x0) («Prover.mDeriv» x1)))
          (leaf 1)
      else
        x0
    else
      x1);
    x2

def «Prover.dCong» :=
  fun (x0 : List T) =>
    let x1 : T := (if («Prover/EachMarked.any»
      «Prover.mFlag»
      x0).label ≠ 0 then
      «Prover.mark»
        («Prover.dNode»
          (leaf 2)
          ([] : List T)
          («Prover/MarkedOut.map» «Prover.mDeriv» x0))
        (leaf 1)
    else
      «Prover.dRefl»);
    x1

def «Prover.sameShape» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := Const.label x0;
                   if (Const.eq x2 (leaf 0)).label ≠ 0 then
                     leaf 1
                   else
                     if (Const.eq (Const.label x1) x2).label ≠ 0 then
                       if («Prelude.or»
                         (Const.eq x2 (leaf 7))
                         (Const.eq x2 (leaf 11))).label ≠ 0 then
                         Const.eq («Language.mD» x0 (leaf 0)) («Language.mD» x1 (leaf 0))
                       else
                         leaf 1
                     else
                       leaf 0);
    x2

def «Prover.setAt» :=
  fun (x0 : List T) (x1 : T) (x2 : T) =>
    let x3 : List
      T := «Base.mapT»
      (fun (x3 : T) =>
        if (Const.eq x3 x1).label ≠ 0 then x2 else «Prelude.at» x0 x3)
      («Base.range» («Prelude.length» x0));
    x3

def «Prover.assign» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Prover/OAssign.nothing» := Const.node (leaf 0) ([] : List T)

def «Prover/OAssign.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Prover/OAssign.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Prover/OAssign.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Prover/OAssign.nthOf» :=
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
      «Prover/OAssign.nothing»
      (fun (x2 : T) (_ : List T) => «Prover/OAssign.just» x2);
    x2

def «Prover/OAssign.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Prover.assigned» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1; let x3 : List T := x2; x3);
    x1

def «Prover.bindAA» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prover/OAssign.nothing»);
    x2

def «Prover/Mts.tail» :=
  fun (x0 : List (T → T → List T → T)) =>
    Const.lcase
      (α := T → T → List T → T)
      (β := List (T → T → List T → T))
      x0
      ([] : List (T → T → List T → T))
      (fun (_ : T → T → List T → T) (x2 : List (T → T → List T → T)) => x2)

def «Prover.matchVar» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) =>
    let x4 : T := (if (Const.lt x0 x1).label ≠ 0 then
      if (Const.equal x2 («Language.var» x0)).label ≠ 0 then
        «Prover/OAssign.just» («Prover.assign» x3)
      else
        «Prover/OAssign.nothing»
    else
      let x4 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
        x2
      else
        «Language.rename» x2 (fun (x4 : T) => Const.sub x4 x1));
      if («Prelude.or»
        (Const.eq x1 (leaf 0))
        (Const.equal
          («Language.rename» x4 (fun (x5 : T) => Const.add x5 x1))
          x2)).label ≠ 0 then
        let x5 : T := «Prelude.nth» x3 (Const.sub x0 x1);
        if («Prelude.isSome» x5).label ≠ 0 then
          if («Prelude.isSome» («Prelude.get» x5)).label ≠ 0 then
            if (Const.equal («Prelude.get» («Prelude.get» x5)) x4).label ≠ 0 then
              «Prover/OAssign.just» («Prover.assign» x3)
            else
              «Prover/OAssign.nothing»
          else
            «Prover/OAssign.just»
              («Prover.assign»
                («Prover.setAt» x3 (Const.sub x0 x1) («Prelude.some» x4)))
        else
          if (Const.equal x4 («Language.var» (Const.sub x0 x1))).label ≠ 0 then
            «Prover/OAssign.just» («Prover.assign» x3)
          else
            «Prover/OAssign.nothing»
      else
        «Prover/OAssign.nothing»);
    x4

def «Prover.matchAll» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List (T → T → List T → T)) =>
    let x4 : T →
      T →
        List T →
          T →
            T := Const.foldr
      (α := T → T → List T → T)
      (β := T → T → List T → T → T)
      (fun (x4 : T → T → List T → T)
         (x5 : T → T → List T → T → T)
         (x6 : T)
         (x7 : T)
         (x8 : List T)
         (x9 : T) =>
        Const.lcase
          (α := T)
          (β := T)
          x8
          x9
          (fun (x10 : T) (x11 : List T) =>
            x5
              x6
              (Const.add x7 (leaf 1))
              x11
              (if («Prelude.and»
                («Prelude.and» (Const.eq x1 (leaf 10)) (Const.eq x2 (leaf 2)))
                (Const.eq x7 (leaf 0))).label ≠ 0 then
                if (Const.equal («Language.mArg» x0 (leaf 0)) x10).label ≠ 0 then
                  x9
                else
                  «Prover/OAssign.nothing»
              else
                «Prover.bindAA»
                  x9
                  (fun (x12 : T) =>
                    x4
                      (Const.add x6 («Language.childBound» x1 x2 x7))
                      x10
                      («Prover.assigned» x12)))))
      (fun (_ : T) (_ : T) (_ : List T) (x7 : T) => x7)
      («Prover/Mts.tail» x3);
    x4

def «Prover.matchStep» :=
  fun (x0 : T) (x1 : List (T → T → List T → T)) =>
    let x2 : T →
      T →
        List T →
          T := (let x2 : T := Const.label x0;
                let x3 : T →
                  T →
                    List T →
                      T →
                        T := «Prover.matchAll»
                  x0
                  x2
                  («Prelude.length» («Language.mArgs» x0))
                  x1;
                fun (x4 : T) (x5 : T) (x6 : List T) =>
                  if (Const.eq x2 (leaf 0)).label ≠ 0 then
                    «Prover.matchVar» («Language.mD» x0 (leaf 0)) x4 x5 x6
                  else
                    let x7 : List T := «Language.mArgs» x5;
                    if («Prelude.and»
                      («Prelude.and»
                        (Const.eq x2 (Const.label x5))
                        (Const.equal (Const.child x0 (leaf 0)) (Const.child x5 (leaf 0))))
                      (Const.eq
                        («Prelude.length» («Language.mArgs» x0))
                        («Prelude.length» x7))).label ≠ 0 then
                      x3 x4 (leaf 0) x7 («Prover/OAssign.just» («Prover.assign» x6))
                    else
                      «Prover/OAssign.nothing»);
    x2

def «Prover.matchTerm» :=
  fun (x0 : T) =>
    let x1 : T →
      T →
        List T →
          T := Const.para (α := T → T → List T → T) «Prover.matchStep» x0;
    x1

def «Prover.nrRule» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Prover.nrDelta» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Prover.nrBelow» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: ([] : List T)))

def «Prover.nrUnit» := Const.node (leaf 3) ([] : List T)

def «Prover.nrThm» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 4) (x0 :: (x1 :: ([] : List T)))

def «Prover.nrThmAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 5) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Prover.nrHyp» :=
  fun (x0 : T) => Const.node (leaf 6) (x0 :: ([] : List T))

def «Prover.bindP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prelude.none»);
    x2

def «Prover.bindAP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Language/OTPair.nothing»);
    x2

def «Prover.bindHP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Language/OTPair.nothing»);
    x2

def «Prover.mapTP» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x1).label ≠ 0 then
      «Language/OTPair.just» (x0 («Prelude.get» x1))
    else
      «Language/OTPair.nothing»);
    x2

def «Prover.termsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1; let x3 : List T := x2; x3);
    x1

def «Prover.objsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1; let x3 : List T := x2; x3);
    x1

def «Prover.thmRewrite» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T)
    (x7 : T → T → List T → T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := «Prover.bindAP»
      (x7 (leaf 0) x9 («Prelude.replicate» x8 «Prelude.none»))
      (fun (x10 : T) =>
        «Language.bindTP»
          («Base.allSomeT» («Prover.assigned» x10))
          (fun (x11 : T) =>
            let x12 : List
              T := «Theory.l4» x5 (Const.node (leaf 0) x6) x11 (leaf 0);
            «Prover.mapTP»
              (fun (x13 : T) =>
                «Language.pr» x13 («Prover.dNode» (leaf 16) x12 ([] : List T)))
              («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 16) x12 x9)));
    x10

def «Prover.tryRule» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := x5;
                   if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
                     let x8 : List T := Const.children x7;
                     let x9 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x8
                       (leaf 0)
                       (fun (x9 : T) (_ : List T) => x9);
                     let x10 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : List T := «Prover.termsOf» x11;
                     «Prover.mapTP»
                       (fun (x14 : T) =>
                         «Language.pr» x14 («Prover.dNode» x9 x13 ([] : List T)))
                       («Derivation.rootStep» x0 x1 x2 x3 x4 x9 x13 x6)
                   else
                     if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                       let x8 : List T := Const.children x7;
                       let x9 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x8
                         (leaf 0)
                         (fun (x9 : T) (_ : List T) => x9);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x8
                         ([] : List T)
                         (fun (_ : T) (x11 : List T) => x11);
                       if («Prelude.and»
                         (Const.eq (Const.label x6) (leaf 11))
                         (Const.eq («Language.mD» x6 (leaf 0)) x9)).label ≠ 0 then
                         «Prover.mapTP»
                           (fun (x11 : T) =>
                             «Language.pr»
                               x11
                               («Prover.dNode» (leaf 8) ([] : List T) ([] : List T)))
                           («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 8) ([] : List T) x6)
                       else
                         «Language/OTPair.nothing»
                     else
                       if (Const.eq (Const.label x7) (leaf 2)).label ≠ 0 then
                         let x8 : List T := Const.children x7;
                         let x9 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x8
                           (leaf 0)
                           (fun (x9 : T) (_ : List T) => x9);
                         let x10 : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x8
                           ([] : List T)
                           (fun (_ : T) (x11 : List T) => x11);
                         let x11 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x10
                           (leaf 0)
                           (fun (x11 : T) (_ : List T) => x11);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x10
                           ([] : List T)
                           (fun (_ : T) (x13 : List T) => x13);
                         if («Prelude.and»
                           (Const.eq (Const.label x6) (leaf 11))
                           («Prelude.and»
                             (Const.lt («Language.mD» x6 (leaf 0)) x9)
                             («Base.not»
                               («Base.anyT»
                                 (fun (x13 : T) => Const.eq x13 («Language.mD» x6 (leaf 0)))
                                 («Prover.termsOf» x11))))).label ≠ 0 then
                           «Prover.mapTP»
                             (fun (x13 : T) =>
                               «Language.pr»
                                 x13
                                 («Prover.dNode» (leaf 8) ([] : List T) ([] : List T)))
                             («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 8) ([] : List T) x6)
                         else
                           «Language/OTPair.nothing»
                       else
                         if (Const.eq (Const.label x7) (leaf 3)).label ≠ 0 then
                           let _ : List T := Const.children x7;
                           if («Prelude.and»
                             (Const.eq (Const.label x6) (leaf 0))
                             (Const.equal
                               («Prelude.nth» x3 («Language.mD» x6 (leaf 0)))
                               («Prelude.some» «Theory.one»))).label ≠ 0 then
                             «Prover.mapTP»
                               (fun (x9 : T) =>
                                 «Language.pr»
                                   x9
                                   («Prover.dNode» (leaf 7) ([] : List T) ([] : List T)))
                               («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 7) ([] : List T) x6)
                           else
                             «Language/OTPair.nothing»
                         else
                           if (Const.eq (Const.label x7) (leaf 4)).label ≠ 0 then
                             let x8 : List T := Const.children x7;
                             let x9 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x8
                               (leaf 0)
                               (fun (x9 : T) (_ : List T) => x9);
                             let x10 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x8
                               ([] : List T)
                               (fun (_ : T) (x11 : List T) => x11);
                             let x11 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x10
                               (leaf 0)
                               (fun (x11 : T) (_ : List T) => x11);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x10
                               ([] : List T)
                               (fun (_ : T) (x13 : List T) => x13);
                             let x13 : List T := «Prover.objsOf» x11;
                             «Prover.bindHP»
                               («Derivation.thmAt» x1 x9)
                               (fun (x14 : T) =>
                                 «Language.bindPP»
                                   («Derivation.eqParts» («Derivation.thConcl» x14))
                                   (fun (x15 : T) =>
                                     if («Prover.sameShape» («Language.p1» x15) x6).label ≠ 0 then
                                       «Prover.thmRewrite»
                                         x0
                                         x1
                                         x2
                                         x3
                                         x4
                                         x9
                                         x13
                                         («Prover.matchTerm»
                                           (if («Base.isEmpty» x13).label ≠ 0 then
                                             «Language.p1» x15
                                           else
                                             «Language.osubst» x13 («Language.p1» x15)))
                                         («Prelude.length» («Derivation.thCtx» x14))
                                         x6
                                     else
                                       «Language/OTPair.nothing»))
                           else
                             if (Const.eq (Const.label x7) (leaf 5)).label ≠ 0 then
                               let x8 : List T := Const.children x7;
                               let x9 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x8
                                 (leaf 0)
                                 (fun (x9 : T) (_ : List T) => x9);
                               let x10 : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x8
                                 ([] : List T)
                                 (fun (_ : T) (x11 : List T) => x11);
                               let x11 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x10
                                 (leaf 0)
                                 (fun (x11 : T) (_ : List T) => x11);
                               let x12 : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x10
                                 ([] : List T)
                                 (fun (_ : T) (x13 : List T) => x13);
                               let x13 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x12
                                 (leaf 0)
                                 (fun (x13 : T) (_ : List T) => x13);
                               let x14 : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x12
                                 ([] : List T)
                                 (fun (_ : T) (x15 : List T) => x15);
                               let x15 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x14
                                 (leaf 0)
                                 (fun (x15 : T) (_ : List T) => x15);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x14
                                 ([] : List T)
                                 (fun (_ : T) (x17 : List T) => x17);
                               if («Prover.sameShape» x13 x6).label ≠ 0 then
                                 «Prover.thmRewrite»
                                   x0
                                   x1
                                   x2
                                   x3
                                   x4
                                   x9
                                   («Prover.objsOf» x11)
                                   («Prover.matchTerm» x13)
                                   x15
                                   x6
                               else
                                 «Language/OTPair.nothing»
                             else
                               let x8 : List T := Const.children x7;
                               let x9 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x8
                                 (leaf 0)
                                 (fun (x9 : T) (_ : List T) => x9);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x8
                                 ([] : List T)
                                 (fun (_ : T) (x11 : List T) => x11);
                               let x11 : List T := «Theory.l2» x9 (leaf 0);
                               «Prover.mapTP»
                                 (fun (x12 : T) =>
                                   «Language.pr» x12 («Prover.dNode» (leaf 17) x11 ([] : List T)))
                                 («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 17) x11 x6));
    x7

def «Prover.rootRewrite» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := Const.foldr
      (α := T)
      (β := T → T)
      (fun (x7 : T) (x8 : T → T) (x9 : T) =>
        let x10 : T := «Prover.tryRule» x0 x1 x2 x4 x5 x7 x9;
        if («Language/OTPair.isJust» x10).label ≠ 0 then x10 else x8 x9)
      (fun (_ : T) => «Language/OTPair.nothing»)
      x3
      x6;
    x7

def «Prover.pr0» := «Language.pr» (leaf 0) (leaf 0)

def «Prover.thm0» :=
  «Derivation.mkThm»
    (leaf 0)
    («Language.objs» ([] : List T))
    («Derivation.terms» ([] : List T))
    (leaf 0)

def «Prover.prepareRule» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 4)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let x5 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     let x6 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     let x8 : List T := «Prover.objsOf» x6;
                     let x9 : T := «Derivation.thmAt» x0 x4;
                     let x10 : T := «Prover.bindHP»
                       x9
                       (fun (x10 : T) => «Derivation.eqParts» («Derivation.thConcl» x10));
                     if («Language/OTPair.isJust» x10).label ≠ 0 then
                       let x11 : T := (if («Base.isEmpty» x8).label ≠ 0 then
                         «Language.p1» («Language/OTPair.fromMaybe» «Prover.pr0» x10)
                       else
                         «Language.osubst»
                           x8
                           («Language.p1» («Language/OTPair.fromMaybe» «Prover.pr0» x10)));
                       «Prover.nrThmAt»
                         x4
                         x6
                         x11
                         («Prelude.length»
                           («Derivation.thCtx» («Derivation/OThm.fromMaybe» «Prover.thm0» x9)))
                     else
                       x1
                   else
                     x1);
    x2

def «Prover.prepareRules» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((«Prover.prepareRule» x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.nfr» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Prover.nfTerm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let x3 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   x3);
    x1

def «Prover.nfMarked» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   x5);
    x1

def «Prover/ONFR.nothing» := Const.node (leaf 0) ([] : List T)

def «Prover/ONFR.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Prover/ONFR.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Prover/ONFR.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Prover/ONFR.nthOf» :=
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
      «Prover/ONFR.nothing»
      (fun (x2 : T) (_ : List T) => «Prover/ONFR.just» x2);
    x2

def «Prover/ONFR.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Prover/EachNFR.all» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «Prover/EachNFR.any» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «Prover/EachNFR.isEmpty» :=
  fun (x0 : List T) =>
    let x1 : T := Const.eq
      (Const.foldr
        (α := T)
        (β := T)
        (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
        (leaf 0)
        x0)
      (leaf 0);
    x1

def «Prover/EachNFR.take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := Const.foldr
              (α := T)
              (β := T)
              (fun (_ : T) (x3 : T) => Const.add x3 (leaf 1))
              (leaf 0)
              x1;
            (Const.foldr
              (α := T)
              (β := T × List T)
              (fun (x3 : T) (x4 : T × List T) =>
                (Const.add (x4).1 (leaf 1),
                  if (Const.lt
                    (Const.sub (Const.sub x2 (x4).1) (leaf 1))
                    x0).label ≠ 0 then
                    (x3 :: (x4).2)
                  else
                    (x4).2))
              (leaf 0, ([] : List T))
              x1).2);
    x2

def «Prover/NFRTerm.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover/NFRMarked.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.nfrs» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Prover/ONFRList.nothing» := Const.node (leaf 0) ([] : List T)

def «Prover/ONFRList.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Prover/ONFRList.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     leaf 1
                   else
                     let _ : List T := Const.children x1; leaf 0);
    x1

def «Prover/ONFRList.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x4
                   else
                     let _ : List T := Const.children x2; x0);
    x2

def «Prover/ONFRList.nthOf» :=
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
      «Prover/ONFRList.nothing»
      (fun (x2 : T) (_ : List T) => «Prover/ONFRList.just» x2);
    x2

def «Prover/ONFRList.allJust» :=
  fun (x0 : List T) =>
    let x1 : T ×
      List
        T := Const.foldr
      (α := T)
      (β := T × List T)
      (fun (x1 : T) (x2 : T × List T) =>
        let x3 : T := x1;
        if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
          let x4 : List T := Const.children x3;
          let x5 : T := Const.lcase
            (α := T)
            (β := T)
            x4
            (leaf 0)
            (fun (x5 : T) (_ : List T) => x5);
          let _ : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x4
            ([] : List T)
            (fun (_ : T) (x7 : List T) => x7);
          ((x2).1, (x5 :: (x2).2))
        else
          let _ : List T := Const.children x3; (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Prover.nfrsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1; let x3 : List T := x2; x3);
    x1

def «Prover.bindNT» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prelude.none»);
    x2

def «Prover.bindNN» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prover/ONFR.nothing»);
    x2

def «Prover.mapNN» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     «Prover/ONFR.just» (x0 x4)
                   else
                     let _ : List T := Const.children x2; «Prover/ONFR.nothing»);
    x2

def «Prover.bindTN» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (if («Prelude.isSome» x0).label ≠ 0 then
      x1 («Prelude.get» x0)
    else
      «Prover/ONFR.nothing»);
    x2

def «Prover.bindSN» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prover/ONFR.nothing»);
    x2

def «Prover.allSomeN» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T × List T := «Prover/ONFR.allJust» x0;
                   if ((x1).1).label ≠ 0 then
                     «Prover/ONFRList.just» («Prover.nfrs» (x1).2)
                   else
                     «Prover/ONFRList.nothing»);
    x1

def «Prover.bindLN» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prover/ONFR.nothing»);
    x2

def «Prover.bindHT» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     x1 x4
                   else
                     let _ : List T := Const.children x2; «Prelude.none»);
    x2

def «Prover.rebuild» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.node
      (Const.label x0)
      ((Const.child x0 (leaf 0)) ::
        («Prover/NFRTerm.map» «Prover.nfTerm» x1));
    x2

def «Prover.marked» :=
  fun (x0 : List T) =>
    let x1 : T := «Prover/EachNFR.any»
      (fun (x1 : T) => «Prover.mFlag» («Prover.nfMarked» x1))
      x0;
    x1

def «Prover.scopeTerm» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Prover/ScopeTerms.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Prover/ScopeTerms.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Prover/ScopeTerms.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Prover/ScopeTerms.reverse» :=
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

def «Prover/ScopeTerms.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Prover/ScopeTerms.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Prover/ScopeTerms.tail» x1 x0;
    x2

def «Prover/ScopeTerms.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Prover/ScopeTerms.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Prover.scopeOf» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let x3 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   x3);
    x1

def «Prover.termOf» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let x5 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   x5);
    x1

def «Prover.zipTs» :=
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
          ([] : List T)
          (fun (x5 : T) (x6 : List T) =>
            ((«Prover.scopeTerm» x2 x5) :: (x3 x6))))
      (fun (_ : List T) => ([] : List T))
      x0
      x1;
    x2

def «Prover.job» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Prover.jobs» := fun (x0 : List T) => Const.node (leaf 0) x0

def «Prover.jobsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1; let x3 : List T := x2; x3);
    x1

def «Prover/JobL.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Prover/JobL.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Prover/JobL.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Prover/JobL.reverse» :=
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

def «Prover/JobL.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Prover/JobL.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Prover/JobL.tail» x1 x0;
    x2

def «Prover/JobL.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Prover/JobL.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Prover/JobAt.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.jobDp» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let x3 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x3);
    x1

def «Prover.jobCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1;
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x2
              (leaf 0)
              (fun (x3 : T) (_ : List T) => x3);
            let x4 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x2
              ([] : List T)
              (fun (_ : T) (x5 : List T) => x5);
            let x5 : T := Const.lcase
              (α := T)
              (β := T)
              x4
              (leaf 0)
              (fun (x5 : T) (_ : List T) => x5);
            let x6 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x4
              ([] : List T)
              (fun (_ : T) (x7 : List T) => x7);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x7 : T) (_ : List T) => x7);
            let x8 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x6
              ([] : List T)
              (fun (_ : T) (x9 : List T) => x9);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x8
              (leaf 0)
              (fun (x9 : T) (_ : List T) => x9);
            let x10 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x8
              ([] : List T)
              (fun (_ : T) (x11 : List T) => x11);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x10
              (leaf 0)
              (fun (x11 : T) (_ : List T) => x11);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x10
              ([] : List T)
              (fun (_ : T) (x13 : List T) => x13);
            let x13 : T := x5;
            let x14 : List T := Const.children x13; let x15 : List T := x14; x15);
    x1

def «Prover.jobNum» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let x7 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x7);
    x1

def «Prover.jobHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : List T := Const.children x1;
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x2
              (leaf 0)
              (fun (x3 : T) (_ : List T) => x3);
            let x4 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x2
              ([] : List T)
              (fun (_ : T) (x5 : List T) => x5);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x4
              (leaf 0)
              (fun (x5 : T) (_ : List T) => x5);
            let x6 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x4
              ([] : List T)
              (fun (_ : T) (x7 : List T) => x7);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x7 : T) (_ : List T) => x7);
            let x8 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x6
              ([] : List T)
              (fun (_ : T) (x9 : List T) => x9);
            let x9 : T := Const.lcase
              (α := T)
              (β := T)
              x8
              (leaf 0)
              (fun (x9 : T) (_ : List T) => x9);
            let x10 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x8
              ([] : List T)
              (fun (_ : T) (x11 : List T) => x11);
            let _ : T := Const.lcase
              (α := T)
              (β := T)
              x10
              (leaf 0)
              (fun (x11 : T) (_ : List T) => x11);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x10
              ([] : List T)
              (fun (_ : T) (x13 : List T) => x13);
            «Prover.termsOf» x9);
    x1

def «Prover.jobTerm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : List T := Const.children x1;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x2
                     (leaf 0)
                     (fun (x3 : T) (_ : List T) => x3);
                   let x4 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x2
                     ([] : List T)
                     (fun (_ : T) (x5 : List T) => x5);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   x11);
    x1

def «Prover.jobAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := x0;
                   let x4 : List T := Const.children x3;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x4
                     (leaf 0)
                     (fun (x5 : T) (_ : List T) => x5);
                   let x6 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x4
                     ([] : List T)
                     (fun (_ : T) (x7 : List T) => x7);
                   let x7 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x6
                     (leaf 0)
                     (fun (x7 : T) (_ : List T) => x7);
                   let x8 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x6
                     ([] : List T)
                     (fun (_ : T) (x9 : List T) => x9);
                   let x9 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x8
                     (leaf 0)
                     (fun (x9 : T) (_ : List T) => x9);
                   let x10 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x10
                     (leaf 0)
                     (fun (x11 : T) (_ : List T) => x11);
                   let x12 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x10
                     ([] : List T)
                     (fun (_ : T) (x13 : List T) => x13);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x12
                     (leaf 0)
                     (fun (x13 : T) (_ : List T) => x13);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x12
                     ([] : List T)
                     (fun (_ : T) (x15 : List T) => x15);
                   «Prover.job» x1 x7 x9 x11 x2);
    x3

def «Prover.firstR» :=
  fun (x0 : List T) =>
    let x1 : T := Const.lcase
      (α := T)
      (β := T)
      x0
      «Prover/ONFR.nothing»
      (fun (x1 : T) (_ : List T) => x1);
    x1

def «Prover.splitRs» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List T ×
      List
        T := Const.foldr
      (α := T)
      (β := List T → List T × List T)
      (fun (_ : T) (x3 : List T → List T × List T) (x4 : List T) =>
        Const.lcase
          (α := T)
          (β := List T × List T)
          x4
          (([] : List T), ([] : List T))
          (fun (x5 : T) (x6 : List T) =>
            let x7 : List T × List T := x3 x6; ((x5 :: (x7).1), (x7).2)))
      (fun (x2 : List T) => (([] : List T), x2))
      x0
      x1;
    x2

def «Prover/NormJob.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.nsDone» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Prover.nsKids» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «Prover.nsTail» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 2) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Prover/NsAt.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover/NsOut.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.nsResult» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let x3 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     x3
                   else
                     «Prover/ONFR.nothing»);
    x1

def «Prover.nsNeed» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
              let x2 : List T := Const.children x1;
              let _ : T := Const.lcase
                (α := T)
                (β := T)
                x2
                (leaf 0)
                (fun (x3 : T) (_ : List T) => x3);
              let _ : List
                T := Const.lcase
                (α := T)
                (β := List T)
                x2
                ([] : List T)
                (fun (_ : T) (x5 : List T) => x5);
              ([] : List T)
            else
              if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                let x2 : List T := Const.children x1;
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x2
                  (leaf 0)
                  (fun (x3 : T) (_ : List T) => x3);
                let x4 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x2
                  ([] : List T)
                  (fun (_ : T) (x5 : List T) => x5);
                let x5 : T := Const.lcase
                  (α := T)
                  (β := T)
                  x4
                  (leaf 0)
                  (fun (x5 : T) (_ : List T) => x5);
                let _ : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x4
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7);
                «Prover.jobsOf» x5
              else
                let x2 : List T := Const.children x1;
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x2
                  (leaf 0)
                  (fun (x3 : T) (_ : List T) => x3);
                let x4 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x2
                  ([] : List T)
                  (fun (_ : T) (x5 : List T) => x5);
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x4
                  (leaf 0)
                  (fun (x5 : T) (_ : List T) => x5);
                let x6 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x4
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7);
                let x7 : T := Const.lcase
                  (α := T)
                  (β := T)
                  x6
                  (leaf 0)
                  (fun (x7 : T) (_ : List T) => x7);
                let _ : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x6
                  ([] : List T)
                  (fun (_ : T) (x9 : List T) => x9);
                «Prover/JobL.single» x7);
    x1

def «Prover.nsStart» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Prover.jobTerm» x2;
                   let x4 : T := «Derivation.childCtxs»
                     x0
                     x1
                     x3
                     («Prover.jobCtx» x2)
                     («Prover.jobHyps» x2);
                   if (Const.eq (Const.label x4) (leaf 1)).label ≠ 0 then
                     let x5 : List T := Const.children x4;
                     let x6 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     «Prover.nsKids»
                       x2
                       («Prover.jobs»
                         («Prover/NormJob.map»
                           (fun (x8 : T) =>
                             let x9 : T := «Prover.scopeOf» x8;
                             «Prover.job»
                               (leaf 0)
                               («Language.objs» («Derivation.scopeCtx» x9))
                               (leaf 0)
                               («Derivation.terms» («Derivation.scopeHyps» x9))
                               («Prover.termOf» x8))
                           («Prover.zipTs» («Derivation.scopesOf» x6) («Language.mArgs» x3))))
                   else
                     let _ : List T := Const.children x4;
                     «Prover.nsDone» «Prover/ONFR.nothing»);
    x3

def «Prover.nsAdv» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := (let x6 : T := x4;
                   if (Const.eq (Const.label x6) (leaf 0)).label ≠ 0 then
                     let x7 : List T := Const.children x6;
                     let x8 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x7
                       (leaf 0)
                       (fun (x8 : T) (_ : List T) => x8);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x7
                       ([] : List T)
                       (fun (_ : T) (x10 : List T) => x10);
                     «Prover.nsDone» x8
                   else
                     if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
                       let x7 : List T := Const.children x6;
                       let x8 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x7
                         (leaf 0)
                         (fun (x8 : T) (_ : List T) => x8);
                       let x9 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x7
                         ([] : List T)
                         (fun (_ : T) (x10 : List T) => x10);
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x9
                         (leaf 0)
                         (fun (x10 : T) (_ : List T) => x10);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x9
                         ([] : List T)
                         (fun (_ : T) (x12 : List T) => x12);
                       let x12 : T := «Prover.allSomeN» x5;
                       if (Const.eq (Const.label x12) (leaf 1)).label ≠ 0 then
                         let x13 : List T := Const.children x12;
                         let x14 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x13
                           (leaf 0)
                           (fun (x14 : T) (_ : List T) => x14);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x13
                           ([] : List T)
                           (fun (_ : T) (x16 : List T) => x16);
                         let x16 : List T := «Prover.nfrsOf» x14;
                         let x17 : T := «Prover.rebuild» («Prover.jobTerm» x8) x16;
                         let x18 : T := (if («Prover.marked» x16).label ≠ 0 then
                           «Prover.mark»
                             («Prover.dNode»
                               (leaf 2)
                               ([] : List T)
                               («Prover/NFRTerm.map»
                                 (fun (x18 : T) => «Prover.mDeriv» («Prover.nfMarked» x18))
                                 x16))
                             (leaf 1)
                         else
                           «Prover.dRefl»);
                         let x19 : T := «Prover.rootRewrite»
                           x0
                           x1
                           x2
                           x3
                           («Prover.jobCtx» x8)
                           («Prover.jobHyps» x8)
                           x17;
                         if («Language/OTPair.isJust» x19).label ≠ 0 then
                           let x20 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x19;
                           «Prover.nsTail»
                             x18
                             («Prover.mark» («Language.p2» x20) (leaf 1))
                             («Prover.jobAt» x8 (leaf 0) («Language.p1» x20))
                         else
                           «Prover.nsDone» («Prover/ONFR.just» («Prover.nfr» x17 x18))
                       else
                         let _ : List T := Const.children x12;
                         «Prover.nsDone» «Prover/ONFR.nothing»
                     else
                       let x7 : List T := Const.children x6;
                       let x8 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x7
                         (leaf 0)
                         (fun (x8 : T) (_ : List T) => x8);
                       let x9 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x7
                         ([] : List T)
                         (fun (_ : T) (x10 : List T) => x10);
                       let x10 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x9
                         (leaf 0)
                         (fun (x10 : T) (_ : List T) => x10);
                       let x11 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x9
                         ([] : List T)
                         (fun (_ : T) (x12 : List T) => x12);
                       let _ : T := Const.lcase
                         (α := T)
                         (β := T)
                         x11
                         (leaf 0)
                         (fun (x12 : T) (_ : List T) => x12);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x11
                         ([] : List T)
                         (fun (_ : T) (x14 : List T) => x14);
                       let x14 : T := «Prover.firstR» x5;
                       if (Const.eq (Const.label x14) (leaf 1)).label ≠ 0 then
                         let x15 : List T := Const.children x14;
                         let x16 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x15
                           (leaf 0)
                           (fun (x16 : T) (_ : List T) => x16);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x15
                           ([] : List T)
                           (fun (_ : T) (x18 : List T) => x18);
                         «Prover.nsDone»
                           («Prover/ONFR.just»
                             («Prover.nfr»
                               («Prover.nfTerm» x16)
                               («Prover.dTrans» x8 («Prover.dTrans» x10 («Prover.nfMarked» x16)))))
                       else
                         let _ : List T := Const.children x14;
                         «Prover.nsDone» «Prover/ONFR.nothing»);
    x6

def «Prover.nsRound» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T → List T)
    (x5 : List T) =>
    let x6 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x6 : T) (x7 : List T → List T) (x8 : List T) =>
        let x9 : List T × List T := «Prover.splitRs» («Prover.nsNeed» x6) x8;
        ((«Prover.nsAdv» x0 x1 x2 x3 x6 (x9).1) :: (x7 (x9).2)))
      (fun (_ : List T) => ([] : List T))
      x5
      (x4
        (Const.foldr
          (α := T)
          (β := List T)
          (fun (x6 : T) (x7 : List T) =>
            «Prover/JobL.append» («Prover.nsNeed» x6) x7)
          ([] : List T)
          x5));
    x6

def «Prover.normStepB» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T → List T) =>
    let x5 : List T →
      List
        T := (fun (x5 : List T) =>
      Const.lcase
        (α := T)
        (β := List T)
        x5
        ([] : List T)
        (fun (_ : T) (_ : List T) =>
          «Prover/NsOut.map»
            «Prover.nsResult»
            («Prover.nsRound»
              x0
              x1
              x2
              x3
              x4
              («Prover.nsRound»
                x0
                x1
                x2
                x3
                x4
                («Prover/NsAt.map»
                  (fun (x8 : T) => «Prover.nsStart» x0 x2 x8)
                  x5)))));
    x5

def «Prover.normB» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : List T →
      List
        T := Const.iter
      (α := List T → List T)
      («Prover.normStepB» x0 x1 x2 x3)
      (fun (x5 : List T) =>
        «Prover/NsOut.map»
          «Prover.nsResult»
          («Prover/NsAt.map»
            (fun (x6 : T) =>
              «Prover.nsDone»
                («Prover/ONFR.just»
                  («Prover.nfr» («Prover.jobTerm» x6) «Prover.dRefl»)))
            x5))
      x4;
    x5

def «Prover.normalize» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : List T →
      List T →
        T →
          T := (fun (x5 : List T) (x6 : List T) (x7 : T) =>
      «Prover.firstR»
        («Prover.normB»
          x0
          x1
          x2
          x3
          x4
          («Prover/JobL.single»
            («Prover.job»
              (leaf 0)
              («Language.objs» x5)
              (leaf 0)
              («Derivation.terms» x6)
              x7))));
    x5

def «Prover.joinBy» :=
  fun (x0 : List T → List T → T → T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : T) =>
    let x5 : T := «Prover.bindNT»
      (x0 x1 x2 x3)
      (fun (x5 : T) =>
        «Prover.bindNT»
          (x0 x1 x2 x4)
          (fun (x6 : T) =>
            if (Const.equal
              («Prover.nfTerm» x5)
              («Prover.nfTerm» x6)).label ≠ 0 then
              «Prelude.some»
                («Prover.dNode»
                  (leaf 18)
                  ([] : List T)
                  («Theory.l2»
                    («Prover.mDeriv» («Prover.nfMarked» x5))
                    («Prover.mDeriv» («Prover.nfMarked» x6))))
            else
              «Prelude.none»));
    x5

def «Prover.byNorm» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «Prover.joinBy»
      («Prover.normalize» x0 x1 x2 x3 x4)
      x5
      x6
      x7
      x8;
    x9

def «Prover.instAt» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Language.subst»
      x2
      («Derivation.instVar» («Language.mArr» x0 x1 «Language.mStar»));
    x3

def «Prover.byNatInd» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : List T)
    (x7 : T)
    (x8 : List T)
    (x9 : List T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := Const.lcase
      (α := T)
      (β := T)
      x8
      «Prelude.none»
      (fun (_ : T) (x13 : List T) =>
        «Prover.bindHT»
          («Derivation.lowerHyps» x0 x2 x13 x9)
          (fun (x14 : T) =>
            let x15 : List T := «Prover.termsOf» x14;
            «Base.bindO»
              («Prover.byNorm»
                x0
                x1
                x2
                x6
                x7
                x13
                x15
                («Prover.instAt» x3 ([] : List T) x10)
                («Prover.instAt» x3 ([] : List T) x11))
              (fun (x16 : T) =>
                «Base.bindO»
                  («Prover.byNorm»
                    x0
                    x1
                    x2
                    x6
                    x7
                    x8
                    x9
                    («Derivation.natSuccAt» x4 x10)
                    («Language.subst» x5 («Derivation.atVar0» x10)))
                  (fun (x17 : T) =>
                    «Base.mapO»
                      (fun (x18 : T) =>
                        «Prover.dNode»
                          (leaf 19)
                          («Theory.l3» x3 x4 x5)
                          («Theory.l3» x16 x17 x18))
                      («Prover.byNorm»
                        x0
                        x1
                        x2
                        x6
                        x7
                        x8
                        x9
                        («Derivation.natSuccAt» x4 x11)
                        («Language.subst» x5 («Derivation.atVar0» x11)))))));
    x12

def «Prover.byListInd» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : List T)
    (x7 : T)
    (x8 : List T)
    (x9 : List T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := Const.lcase
      (α := T)
      (β := T)
      x8
      «Prelude.none»
      (fun (x12 : T) (x13 : List T) =>
        «Base.bindO»
          («Language.listPart» x12)
          (fun (x14 : T) =>
            «Prover.bindHT»
              («Derivation.lowerHyps» x0 x2 x13 x9)
              (fun (x15 : T) =>
                let x16 : List T := «Prover.termsOf» x15;
                let x17 : List T := (x12 :: (x14 :: x13));
                let x18 : List T := «Base.mapT» «Derivation.weaken2» x16;
                «Base.bindO»
                  («Prover.byNorm»
                    x0
                    x1
                    x2
                    x6
                    x7
                    x13
                    x16
                    («Prover.instAt» x3 («Prelude.single» x14) x10)
                    («Prover.instAt» x3 («Prelude.single» x14) x11))
                  (fun (x19 : T) =>
                    «Base.bindO»
                      («Prover.byNorm»
                        x0
                        x1
                        x2
                        x6
                        x7
                        x17
                        x18
                        («Derivation.listConsAt» x4 x14 x10)
                        («Language.subst»
                          x5
                          («Derivation.atVar0» («Derivation.weakenElem» x10))))
                      (fun (x20 : T) =>
                        «Base.mapO»
                          (fun (x21 : T) =>
                            «Prover.dNode»
                              (leaf 20)
                              («Theory.l3» x3 x4 x5)
                              («Theory.l3» x19 x20 x21))
                          («Prover.byNorm»
                            x0
                            x1
                            x2
                            x6
                            x7
                            x17
                            x18
                            («Derivation.listConsAt» x4 x14 x11)
                            («Language.subst»
                              x5
                              («Derivation.atVar0» («Derivation.weakenElem» x11)))))))));
    x12

def «Prover.withHyp» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      ((«Prover.nrHyp» x1) :: ([] : List T))
      x0;
    x2

def «Prover.byNatIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List T)
    (x6 : T)
    (x7 : List T)
    (x8 : List T)
    (x9 : T)
    (x10 : T) =>
    let x11 : T := Const.lcase
      (α := T)
      (β := T)
      x7
      «Prelude.none»
      (fun (_ : T) (x12 : List T) =>
        «Prover.bindHT»
          («Derivation.lowerHyps» x0 x2 x12 x8)
          (fun (x13 : T) =>
            let x14 : List T := «Prover.termsOf» x13;
            «Base.bindO»
              («Prover.byNorm»
                x0
                x1
                x2
                x5
                x6
                x12
                x14
                («Prover.instAt» x3 ([] : List T) x9)
                («Prover.instAt» x3 ([] : List T) x10))
              (fun (x15 : T) =>
                let x16 : List
                  T := «Prelude.append» x8 («Prelude.single» («Language.mEq» x9 x10));
                «Prover.bindNT»
                  («Prover.normalize» x0 x1 x2 x5 x6 x7 x16 («Language.mEq» x9 x10))
                  (fun (x17 : T) =>
                    let x18 : T := «Prover.nfTerm» x17;
                    «Base.bindO»
                      («Prover.byNorm»
                        x0
                        x1
                        x2
                        («Prover.withHyp» x5 («Prelude.length» x16))
                        x6
                        x7
                        («Prelude.append» x16 («Prelude.single» x18))
                        («Derivation.natSuccAt» x4 x9)
                        («Derivation.natSuccAt» x4 x10))
                      (fun (x19 : T) =>
                        let x20 : T := «Prover.dNode»
                          (leaf 24)
                          («Prelude.single» («Language.mEq» x9 x10))
                          («Theory.l2»
                            («Prover.mDeriv» («Prover.nfMarked» x17))
                            («Prover.dNode»
                              (leaf 21)
                              («Prelude.single» («Prelude.length» x8))
                              ([] : List T)));
                        «Prelude.some»
                          («Prover.dNode»
                            (leaf 28)
                            («Theory.l2» x3 x4)
                            («Theory.l2»
                              x15
                              («Prover.dNode»
                                (leaf 22)
                                («Prelude.single» x18)
                                («Theory.l2» x20 x19)))))))));
    x11

def «Prover.byListIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List T)
    (x6 : T)
    (x7 : List T)
    (x8 : List T)
    (x9 : T)
    (x10 : T) =>
    let x11 : T := Const.lcase
      (α := T)
      (β := T)
      x7
      «Prelude.none»
      (fun (x11 : T) (x12 : List T) =>
        «Base.bindO»
          («Language.listPart» x11)
          (fun (x13 : T) =>
            «Prover.bindHT»
              («Derivation.lowerHyps» x0 x2 x12 x8)
              (fun (x14 : T) =>
                let x15 : List T := «Prover.termsOf» x14;
                «Base.bindO»
                  («Prover.byNorm»
                    x0
                    x1
                    x2
                    x5
                    x6
                    x12
                    x15
                    («Prover.instAt» x3 («Prelude.single» x13) x9)
                    («Prover.instAt» x3 («Prelude.single» x13) x10))
                  (fun (x16 : T) =>
                    let x17 : List T := (x11 :: (x13 :: x12));
                    let x18 : T := «Derivation.weakenElem» («Language.mEq» x9 x10);
                    let x19 : List
                      T := «Prelude.append»
                      («Base.mapT» «Derivation.weaken2» x15)
                      («Prelude.single» x18);
                    «Prover.bindNT»
                      («Prover.normalize» x0 x1 x2 x5 x6 x17 x19 x18)
                      (fun (x20 : T) =>
                        let x21 : T := «Prover.nfTerm» x20;
                        «Base.bindO»
                          («Prover.byNorm»
                            x0
                            x1
                            x2
                            («Prover.withHyp» x5 («Prelude.length» x19))
                            x6
                            x17
                            («Prelude.append» x19 («Prelude.single» x21))
                            («Derivation.listConsAt» x4 x13 x9)
                            («Derivation.listConsAt» x4 x13 x10))
                          (fun (x22 : T) =>
                            let x23 : T := «Prover.dNode»
                              (leaf 24)
                              («Prelude.single» x18)
                              («Theory.l2»
                                («Prover.mDeriv» («Prover.nfMarked» x20))
                                («Prover.dNode»
                                  (leaf 21)
                                  («Prelude.single» («Prelude.length» x15))
                                  ([] : List T)));
                            «Prelude.some»
                              («Prover.dNode»
                                (leaf 29)
                                («Theory.l2» x3 x4)
                                («Theory.l2»
                                  x16
                                  («Prover.dNode»
                                    (leaf 22)
                                    («Prelude.single» x21)
                                    («Theory.l2» x23 x22))))))))));
    x11

def «Prover.headChild» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.or»
      («Language.mIs» (leaf 3) (leaf 1) x0)
      («Language.mIs» (leaf 4) (leaf 1) x0)).label ≠ 0 then
      «Prelude.some» (leaf 0)
    else
      if («Prelude.or»
        («Language.mIs» (leaf 8) (leaf 3) x0)
        («Language.mIs» (leaf 9) (leaf 3) x0)).label ≠ 0 then
        «Prelude.some» (leaf 2)
      else
        if («Language.mIs» (leaf 10) (leaf 2) x0).label ≠ 0 then
          «Prelude.some» (leaf 1)
        else
          «Prelude.none»);
    x1

def «Prover.keepsFold» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Prelude.or»
      (Const.eq x0 (leaf 8))
      (Const.eq x0 (leaf 9))).label ≠ 0 then
      Const.lt x1 (leaf 2)
    else
      if (Const.eq x0 (leaf 10)).label ≠ 0 then
        Const.eq x1 (leaf 0)
      else
        leaf 0);
    x2

def «Prover.keepsWeak» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x0 (leaf 5)).label ≠ 0 then
      leaf 1
    else
      «Prover.keepsFold» x0 x1);
    x2

def «Prover/UFs.tail» :=
  fun (x0 : List (T → T)) =>
    Const.lcase
      (α := T → T)
      (β := List (T → T))
      x0
      ([] : List (T → T))
      (fun (_ : T → T) (x2 : List (T → T)) => x2)

def «Prover.usesStep» :=
  fun (x0 : T) (x1 : List (T → T)) =>
    let x2 : T →
      T := (let x2 : T := Const.label x0;
            let x3 : T := «Prelude.length» («Language.mArgs» x0);
            let x4 : T →
              T →
                T := Const.foldr
              (α := T → T)
              (β := T → T → T)
              (fun (x4 : T → T) (x5 : T → T → T) (x6 : T) (x7 : T) =>
                let x8 : T := (if (Const.eq x2 (leaf 5)).label ≠ 0 then
                  leaf 1
                else
                  «Language.childBound» x2 x3 x7);
                Const.add
                  (Const.mul
                    (if (Const.eq x8 (leaf 0)).label ≠ 0 then leaf 1 else leaf 2)
                    (x4 (Const.add x6 x8)))
                  (x5 x6 (Const.add x7 (leaf 1))))
              (fun (_ : T) (_ : T) => leaf 0)
              («Prover/UFs.tail» x1);
            fun (x5 : T) =>
              if (Const.eq x2 (leaf 0)).label ≠ 0 then
                if (Const.eq («Language.mD» x0 (leaf 0)) x5).label ≠ 0 then
                  leaf 1
                else
                  leaf 0
              else
                x4 x5 (leaf 0));
    x2

def «Prover.uses» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.para (α := T → T) «Prover.usesStep» x0 x1; x2

def «Prover.rootKey» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := Const.label x0;
                   if (Const.eq x1 (leaf 7)).label ≠ 0 then
                     Const.add (leaf 11) (Const.mul (leaf 2) («Language.mD» x0 (leaf 0)))
                   else
                     if (Const.eq x1 (leaf 11)).label ≠ 0 then
                       Const.add (leaf 12) (Const.mul (leaf 2) («Language.mD» x0 (leaf 0)))
                     else
                       if (Const.eq x1 (leaf 8)).label ≠ 0 then
                         leaf 7
                       else
                         if (Const.eq x1 (leaf 9)).label ≠ 0 then
                           leaf 8
                         else
                           if (Const.eq x1 (leaf 10)).label ≠ 0 then
                             leaf 9
                           else
                             if (Const.eq x1 (leaf 12)).label ≠ 0 then leaf 10 else x1);
    x1

def «Prover.patternKey» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq (Const.label x0) (leaf 0)).label ≠ 0 then
      «Prelude.none»
    else
      «Prelude.some» («Prover.rootKey» x0));
    x1

def «Prover.ruleKey» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.or»
      (Const.eq x0 (leaf 3))
      («Prelude.or»
        (Const.eq x0 (leaf 14))
        (Const.eq x0 (leaf 15)))).label ≠ 0 then
      «Prelude.some» (leaf 6)
    else
      if (Const.eq x0 (leaf 4)).label ≠ 0 then
        «Prelude.some» (leaf 3)
      else
        if (Const.eq x0 (leaf 5)).label ≠ 0 then
          «Prelude.some» (leaf 4)
        else
          if (Const.eq x0 (leaf 6)).label ≠ 0 then
            «Prelude.some» (leaf 2)
          else
            if («Prelude.or»
              (Const.eq x0 (leaf 9))
              (Const.eq x0 (leaf 10))).label ≠ 0 then
              «Prelude.some» (leaf 7)
            else
              if («Prelude.or»
                (Const.eq x0 (leaf 11))
                (Const.eq x0 (leaf 12))).label ≠ 0 then
                «Prelude.some» (leaf 8)
              else
                if (Const.eq x0 (leaf 13)).label ≠ 0 then
                  «Prelude.some» (leaf 9)
                else
                  «Prelude.none»);
    x1

def «Prover.nrKey» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let x3 : List T := Const.children x2;
                     let x4 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x3
                       (leaf 0)
                       (fun (x4 : T) (_ : List T) => x4);
                     let x5 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x3
                       ([] : List T)
                       (fun (_ : T) (x6 : List T) => x6);
                     let _ : T := Const.lcase
                       (α := T)
                       (β := T)
                       x5
                       (leaf 0)
                       (fun (x6 : T) (_ : List T) => x6);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x5
                       ([] : List T)
                       (fun (_ : T) (x8 : List T) => x8);
                     «Prover.ruleKey» x4
                   else
                     if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                       let x3 : List T := Const.children x2;
                       let x4 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x3
                         (leaf 0)
                         (fun (x4 : T) (_ : List T) => x4);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x3
                         ([] : List T)
                         (fun (_ : T) (x6 : List T) => x6);
                       «Prelude.some» (Const.add (leaf 12) (Const.mul (leaf 2) x4))
                     else
                       if (Const.eq (Const.label x2) (leaf 3)).label ≠ 0 then
                         let _ : List T := Const.children x2; «Prelude.some» (leaf 0)
                       else
                         if (Const.eq (Const.label x2) (leaf 4)).label ≠ 0 then
                           let x3 : List T := Const.children x2;
                           let x4 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x3
                             (leaf 0)
                             (fun (x4 : T) (_ : List T) => x4);
                           let x5 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x3
                             ([] : List T)
                             (fun (_ : T) (x6 : List T) => x6);
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x5
                             (leaf 0)
                             (fun (x6 : T) (_ : List T) => x6);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x5
                             ([] : List T)
                             (fun (_ : T) (x8 : List T) => x8);
                           let x8 : T := «Derivation.thmAt» x0 x4;
                           if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                             let x9 : List T := Const.children x8;
                             let x10 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x9
                               (leaf 0)
                               (fun (x10 : T) (_ : List T) => x10);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x9
                               ([] : List T)
                               (fun (_ : T) (x12 : List T) => x12);
                             let x12 : T := «Derivation.eqParts» («Derivation.thConcl» x10);
                             if (Const.eq (Const.label x12) (leaf 1)).label ≠ 0 then
                               let x13 : List T := Const.children x12;
                               let x14 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x13
                                 (leaf 0)
                                 (fun (x14 : T) (_ : List T) => x14);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x13
                                 ([] : List T)
                                 (fun (_ : T) (x16 : List T) => x16);
                               «Prover.patternKey» («Language.p1» x14)
                             else
                               let _ : List T := Const.children x12; «Prelude.none»
                           else
                             let _ : List T := Const.children x8; «Prelude.none»
                         else
                           if (Const.eq (Const.label x2) (leaf 5)).label ≠ 0 then
                             let x3 : List T := Const.children x2;
                             let _ : T := Const.lcase
                               (α := T)
                               (β := T)
                               x3
                               (leaf 0)
                               (fun (x4 : T) (_ : List T) => x4);
                             let x5 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x3
                               ([] : List T)
                               (fun (_ : T) (x6 : List T) => x6);
                             let _ : T := Const.lcase
                               (α := T)
                               (β := T)
                               x5
                               (leaf 0)
                               (fun (x6 : T) (_ : List T) => x6);
                             let x7 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x5
                               ([] : List T)
                               (fun (_ : T) (x8 : List T) => x8);
                             let x8 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x7
                               (leaf 0)
                               (fun (x8 : T) (_ : List T) => x8);
                             let x9 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x7
                               ([] : List T)
                               (fun (_ : T) (x10 : List T) => x10);
                             let _ : T := Const.lcase
                               (α := T)
                               (β := T)
                               x9
                               (leaf 0)
                               (fun (x10 : T) (_ : List T) => x10);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x9
                               ([] : List T)
                               (fun (_ : T) (x12 : List T) => x12);
                             «Prover.patternKey» x8
                           else
                             «Prelude.none»);
    x2

def «Prover.keyFits» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x1).label ≠ 0 then
      Const.eq («Prelude.get» x1) x0
    else
      leaf 1);
    x2

def «Prover.bucketOf» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x3 : T) (x4 : List T) =>
        if («Prover.keyFits» x2 («Prover.nrKey» x0 x3)).label ≠ 0 then
          (x3 :: x4)
        else
          x4)
      ([] : List T)
      x1;
    x3

def «Prover.ruleKeys» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := «Prover.nrKey» x0 x2;
        if («Prelude.and»
          («Prelude.isSome» x4)
          («Base.not»
            («Base.anyT»
              (fun (x5 : T) => Const.eq x5 («Prelude.get» x4))
              x3))).label ≠ 0 then
          ((«Prelude.get» x4) :: x3)
        else
          x3)
      ([] : List T)
      x1;
    x2

def «Prover.indexRules» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List (T × List T) ×
      List
        T := (Const.foldr
      (α := T)
      (β := List (T × List T))
      (fun (x2 : T) (x3 : List (T × List T)) =>
        ((x2, «Prover.bucketOf» x0 x1 x2) :: x3))
      ([] : List (T × List T))
      («Prover.ruleKeys» x0 x1),
      Const.foldr
        (α := T)
        (β := List T)
        (fun (x2 : T) (x3 : List T) =>
          if («Prelude.isSome» («Prover.nrKey» x0 x2)).label ≠ 0 then
            x3
          else
            (x2 :: x3))
        ([] : List T)
        x1);
    x2

def «Prover.ruleBucket» :=
  fun (x0 : List (T × List T) × List T) (x1 : T) =>
    let x2 : List
      T := Const.foldr
      (α := T × List T)
      (β := List T)
      (fun (x2 : T × List T) (x3 : List T) =>
        if (Const.eq (x2).1 x1).label ≠ 0 then (x2).2 else x3)
      (x0).2
      (x0).1;
    x2

def «Prover/RTs.tail» :=
  fun (x0 : List ((T → T) → T → T)) =>
    Const.lcase
      (α := (T → T) → T → T)
      (β := List ((T → T) → T → T))
      x0
      ([] : List ((T → T) → T → T))
      (fun (_ : (T → T) → T → T) (x2 : List ((T → T) → T → T)) => x2)

def «Prover.childRen» :=
  fun (x0 : T) (x1 : T) (x2 : T → T) (x3 : T) =>
    let x4 : T →
      T := (if («Prelude.and»
      (Const.eq x0 (leaf 5))
      (Const.eq x1 (leaf 1))).label ≠ 0 then
      fun (x4 : T) => «Language.liftR» x2 x4
    else
      if («Prelude.and»
        (Const.eq x0 (leaf 8))
        (Const.eq x1 (leaf 3))).label ≠ 0 then
        if (Const.eq x3 (leaf 1)).label ≠ 0 then
          fun (x4 : T) => «Language.liftR» x2 x4
        else
          x2
      else
        if («Prelude.and»
          (Const.eq x0 (leaf 9))
          (Const.eq x1 (leaf 3))).label ≠ 0 then
          if (Const.eq x3 (leaf 1)).label ≠ 0 then
            fun (x4 : T) =>
              «Language.liftR» (fun (x5 : T) => «Language.liftR» x2 x5) x4
          else
            x2
        else
          if («Prelude.and»
            (Const.eq x0 (leaf 10))
            (Const.eq x1 (leaf 2))).label ≠ 0 then
            if (Const.eq x3 (leaf 0)).label ≠ 0 then
              fun (x4 : T) => «Language.liftR» x2 x4
            else
              x2
          else
            x2);
    x4

def «Prover.holdAll» :=
  fun (x0 : T) (x1 : T) (x2 : List ((T → T) → T → T)) =>
    let x3 : (T → T) →
      T →
        List T →
          T := Const.foldr
      (α := (T → T) → T → T)
      (β := (T → T) → T → List T → T)
      (fun (x3 : (T → T) → T → T)
         (x4 : (T → T) → T → List T → T)
         (x5 : T → T)
         (x6 : T)
         (x7 : List T) =>
        Const.lcase
          (α := T)
          (β := T)
          x7
          (leaf 0)
          (fun (x8 : T) (x9 : List T) =>
            «Prelude.and»
              (x3 («Prover.childRen» x0 x1 x5 x6) x8)
              (x4 x5 (Const.add x6 (leaf 1)) x9)))
      (fun (_ : T → T) (_ : T) (x5 : List T) => «Base.isEmpty» x5)
      x2;
    x3

def «Prover.isRenameStep» :=
  fun (x0 : T) (x1 : List ((T → T) → T → T)) =>
    let x2 : (T → T) →
      T →
        T := (let x2 : (T → T) →
                T →
                  List T →
                    T := «Prover.holdAll»
                (Const.label x0)
                («Prelude.length» («Language.mArgs» x0))
                («Prover/RTs.tail» x1);
              fun (x3 : T → T) (x4 : T) =>
                if (Const.eq (Const.label x0) (leaf 0)).label ≠ 0 then
                  «Prelude.and»
                    (Const.eq (Const.label x4) (leaf 0))
                    («Prelude.and»
                      (Const.eq
                        («Language.mD» x4 (leaf 0))
                        (x3 («Language.mD» x0 (leaf 0))))
                      («Base.isEmpty» («Language.mArgs» x4)))
                else
                  «Prelude.and»
                    (Const.eq (Const.label x4) (Const.label x0))
                    («Prelude.and»
                      (Const.equal (Const.child x4 (leaf 0)) (Const.child x0 (leaf 0)))
                      (x2 x3 (leaf 0) («Language.mArgs» x4))));
    x2

def «Prover.isRename» :=
  fun (x0 : T) =>
    let x1 : (T → T) →
      T → T := Const.para (α := (T → T) → T → T) «Prover.isRenameStep» x0;
    x1

def «Prover/PHs.tail» :=
  fun (x0 : List (T × (T × (T × ((T → T) → T → T))))) =>
    Const.lcase
      (α := T × (T × (T × ((T → T) → T → T))))
      (β := List (T × (T × (T × ((T → T) → T → T)))))
      x0
      ([] : List (T × (T × (T × ((T → T) → T → T)))))
      (fun (_ : T × (T × (T × ((T → T) → T → T))))
         (x2 : List (T × (T × (T × ((T → T) → T → T))))) =>
        x2)

def «Prover.ph0» :=
  (leaf 0, (leaf 0, (leaf 0, fun (_ : T → T) (_ : T) => leaf 0)))

def «Prover.prepareHyps» :=
  fun (x0 : List T) =>
    let x1 : List
      (T ×
        (T ×
          (T ×
            ((T → T) →
              T →
                T)))) := Const.foldr
      (α := T)
      (β := List (T × (T × (T × ((T → T) → T → T)))))
      (fun (x1 : T) (x2 : List (T × (T × (T × ((T → T) → T → T))))) =>
        ((let x3 : T := «Derivation.eqParts» x1;
          if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
            let x4 : List T := Const.children x3;
            let x5 : T := Const.lcase
              (α := T)
              (β := T)
              x4
              (leaf 0)
              (fun (x5 : T) (_ : List T) => x5);
            let _ : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x4
              ([] : List T)
              (fun (_ : T) (x7 : List T) => x7);
            (leaf 1,
              («Language.p1» x5,
                («Language.p2» x5, «Prover.isRename» («Language.p1» x5))))
          else
            let _ : List T := Const.children x3; «Prover.ph0») ::
          x2))
      ([] : List (T × (T × (T × ((T → T) → T → T)))))
      x0;
    x1

def «Prover.phAt» :=
  fun (x0 : List (T × (T × (T × ((T → T) → T → T))))) (x1 : T) =>
    let x2 : T ×
      (T ×
        (T ×
          ((T → T) →
            T →
              T))) := Const.lcase
      (α := T × (T × (T × ((T → T) → T → T))))
      (β := T × (T × (T × ((T → T) → T → T))))
      (Const.iter
        (α := List (T × (T × (T × ((T → T) → T → T)))))
        «Prover/PHs.tail»
        x0
        x1)
      «Prover.ph0»
      (fun (x2 : T × (T × (T × ((T → T) → T → T))))
         (_ : List (T × (T × (T × ((T → T) → T → T))))) =>
        x2);
    x2

def «Prover.tryRuleK» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : List (T × (T × (T × ((T → T) → T → T)))))
    (x7 : T)
    (x8 : T) =>
    let x9 : T := (let x9 : T := x7;
                   if (Const.eq (Const.label x9) (leaf 0)).label ≠ 0 then
                     let x10 : List T := Const.children x9;
                     let x11 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x10
                       (leaf 0)
                       (fun (x11 : T) (_ : List T) => x11);
                     let x12 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x10
                       ([] : List T)
                       (fun (_ : T) (x13 : List T) => x13);
                     let x13 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x12
                       (leaf 0)
                       (fun (x13 : T) (_ : List T) => x13);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x12
                       ([] : List T)
                       (fun (_ : T) (x15 : List T) => x15);
                     let x15 : List T := «Prover.termsOf» x13;
                     «Prover.mapTP»
                       (fun (x16 : T) =>
                         «Language.pr» x16 («Prover.dNode» x11 x15 ([] : List T)))
                       («Derivation.rootStepK» x0 x1 x2 x3 x4 x5 x11 x15 x8)
                   else
                     if (Const.eq (Const.label x9) (leaf 6)).label ≠ 0 then
                       let x10 : List T := Const.children x9;
                       let x11 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x10
                         (leaf 0)
                         (fun (x11 : T) (_ : List T) => x11);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x10
                         ([] : List T)
                         (fun (_ : T) (x13 : List T) => x13);
                       let x13 : T × (T × (T × ((T → T) → T → T))) := «Prover.phAt» x6 x11;
                       if («Prelude.and»
                         (x13).1
                         (if (Const.eq x4 (leaf 0)).label ≠ 0 then
                           Const.equal x8 ((x13).2).1
                         else
                           (((x13).2).2).2
                             (fun (x14 : T) => Const.add x14 x4)
                             x8)).label ≠ 0 then
                         «Language/OTPair.just»
                           («Language.pr»
                             («Derivation.weakenBy» x4 (((x13).2).2).1)
                             («Prover.dNode» (leaf 17) («Theory.l2» x11 (leaf 0)) ([] : List T)))
                       else
                         «Language/OTPair.nothing»
                     else
                       «Prover.tryRule» x0 x1 x2 x3 ([] : List T) x7 x8);
    x9

def «Prover.rootRewriteK» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × List T) × List T)
    (x4 : List (T × (T × (T × ((T → T) → T → T))))) =>
    let x5 : List T →
      T →
        List T →
          T →
            T := (fun (x5 : List T) (x6 : T) (x7 : List T) (x8 : T) =>
      Const.foldr
        (α := T)
        (β := T → T)
        (fun (x9 : T) (x10 : T → T) (x11 : T) =>
          let x12 : T := «Prover.tryRuleK» x0 x1 x2 x5 x6 x7 x4 x9 x11;
          if («Language/OTPair.isJust» x12).label ≠ 0 then x12 else x10 x11)
        (fun (_ : T) => «Language/OTPair.nothing»)
        («Prover.ruleBucket» x3 («Prover.rootKey» x8))
        x8);
    x5

def «Prover.jobRw» :=
  fun (x0 : List T → T → List T → T → T) (x1 : T) (x2 : T) =>
    let x3 : T := x0
      («Prover.jobCtx» x1)
      («Prover.jobNum» x1)
      («Prover.jobHyps» x1)
      x2;
    x3

def «Prover.stDone» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Prover.stTail» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 1)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Prover.stFun» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «Prover.stArg» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 3) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Prover.stChild» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 4) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Prover.stKids» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 5) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Prover/StAt.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover/StOut.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.stResult» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : List T := Const.children x1;
                     let x3 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x2
                       (leaf 0)
                       (fun (x3 : T) (_ : List T) => x3);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x2
                       ([] : List T)
                       (fun (_ : T) (x5 : List T) => x5);
                     x3
                   else
                     «Prover/ONFR.nothing»);
    x1

def «Prover.stNeed» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
              let x2 : List T := Const.children x1;
              let _ : T := Const.lcase
                (α := T)
                (β := T)
                x2
                (leaf 0)
                (fun (x3 : T) (_ : List T) => x3);
              let _ : List
                T := Const.lcase
                (α := T)
                (β := List T)
                x2
                ([] : List T)
                (fun (_ : T) (x5 : List T) => x5);
              ([] : List T)
            else
              if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                let x2 : List T := Const.children x1;
                let x3 : T := Const.lcase
                  (α := T)
                  (β := T)
                  x2
                  (leaf 0)
                  (fun (x3 : T) (_ : List T) => x3);
                let x4 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x2
                  ([] : List T)
                  (fun (_ : T) (x5 : List T) => x5);
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x4
                  (leaf 0)
                  (fun (x5 : T) (_ : List T) => x5);
                let x6 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x4
                  ([] : List T)
                  (fun (_ : T) (x7 : List T) => x7);
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x6
                  (leaf 0)
                  (fun (x7 : T) (_ : List T) => x7);
                let x8 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x6
                  ([] : List T)
                  (fun (_ : T) (x9 : List T) => x9);
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x8
                  (leaf 0)
                  (fun (x9 : T) (_ : List T) => x9);
                let x10 : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x8
                  ([] : List T)
                  (fun (_ : T) (x11 : List T) => x11);
                let _ : T := Const.lcase
                  (α := T)
                  (β := T)
                  x10
                  (leaf 0)
                  (fun (x11 : T) (_ : List T) => x11);
                let _ : List
                  T := Const.lcase
                  (α := T)
                  (β := List T)
                  x10
                  ([] : List T)
                  (fun (_ : T) (x13 : List T) => x13);
                «Prover/JobL.single» x3
              else
                if (Const.eq (Const.label x1) (leaf 2)).label ≠ 0 then
                  let x2 : List T := Const.children x1;
                  let x3 : T := Const.lcase
                    (α := T)
                    (β := T)
                    x2
                    (leaf 0)
                    (fun (x3 : T) (_ : List T) => x3);
                  let _ : List
                    T := Const.lcase
                    (α := T)
                    (β := List T)
                    x2
                    ([] : List T)
                    (fun (_ : T) (x5 : List T) => x5);
                  «Prover/JobL.single»
                    («Prover.jobAt»
                      x3
                      (leaf 0)
                      («Language.mArg» («Prover.jobTerm» x3) (leaf 0)))
                else
                  if (Const.eq (Const.label x1) (leaf 3)).label ≠ 0 then
                    let x2 : List T := Const.children x1;
                    let _ : T := Const.lcase
                      (α := T)
                      (β := T)
                      x2
                      (leaf 0)
                      (fun (x3 : T) (_ : List T) => x3);
                    let x4 : List
                      T := Const.lcase
                      (α := T)
                      (β := List T)
                      x2
                      ([] : List T)
                      (fun (_ : T) (x5 : List T) => x5);
                    let _ : T := Const.lcase
                      (α := T)
                      (β := T)
                      x4
                      (leaf 0)
                      (fun (x5 : T) (_ : List T) => x5);
                    let x6 : List
                      T := Const.lcase
                      (α := T)
                      (β := List T)
                      x4
                      ([] : List T)
                      (fun (_ : T) (x7 : List T) => x7);
                    let x7 : T := Const.lcase
                      (α := T)
                      (β := T)
                      x6
                      (leaf 0)
                      (fun (x7 : T) (_ : List T) => x7);
                    let _ : List
                      T := Const.lcase
                      (α := T)
                      (β := List T)
                      x6
                      ([] : List T)
                      (fun (_ : T) (x9 : List T) => x9);
                    «Prover/JobL.single» x7
                  else
                    if (Const.eq (Const.label x1) (leaf 4)).label ≠ 0 then
                      let x2 : List T := Const.children x1;
                      let x3 : T := Const.lcase
                        (α := T)
                        (β := T)
                        x2
                        (leaf 0)
                        (fun (x3 : T) (_ : List T) => x3);
                      let x4 : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x2
                        ([] : List T)
                        (fun (_ : T) (x5 : List T) => x5);
                      let _ : T := Const.lcase
                        (α := T)
                        (β := T)
                        x4
                        (leaf 0)
                        (fun (x5 : T) (_ : List T) => x5);
                      let x6 : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x4
                        ([] : List T)
                        (fun (_ : T) (x7 : List T) => x7);
                      let x7 : T := Const.lcase
                        (α := T)
                        (β := T)
                        x6
                        (leaf 0)
                        (fun (x7 : T) (_ : List T) => x7);
                      let _ : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x6
                        ([] : List T)
                        (fun (_ : T) (x9 : List T) => x9);
                      «Prover/JobL.single» («Prover.jobAt» x3 (leaf 0) x7)
                    else
                      let x2 : List T := Const.children x1;
                      let _ : T := Const.lcase
                        (α := T)
                        (β := T)
                        x2
                        (leaf 0)
                        (fun (x3 : T) (_ : List T) => x3);
                      let x4 : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x2
                        ([] : List T)
                        (fun (_ : T) (x5 : List T) => x5);
                      let _ : T := Const.lcase
                        (α := T)
                        (β := T)
                        x4
                        (leaf 0)
                        (fun (x5 : T) (_ : List T) => x5);
                      let x6 : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x4
                        ([] : List T)
                        (fun (_ : T) (x7 : List T) => x7);
                      let _ : T := Const.lcase
                        (α := T)
                        (β := T)
                        x6
                        (leaf 0)
                        (fun (x7 : T) (_ : List T) => x7);
                      let x8 : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x6
                        ([] : List T)
                        (fun (_ : T) (x9 : List T) => x9);
                      let x9 : T := Const.lcase
                        (α := T)
                        (β := T)
                        x8
                        (leaf 0)
                        (fun (x9 : T) (_ : List T) => x9);
                      let _ : List
                        T := Const.lcase
                        (α := T)
                        (β := List T)
                        x8
                        ([] : List T)
                        (fun (_ : T) (x11 : List T) => x11);
                      «Prover.jobsOf» x9);
    x1

def «Prover.stDeep» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := «Prover.nfTerm» x4;
                   let x6 : T := Const.label x5;
                   let x7 : List T := «Language.mArgs» x5;
                   if (Const.eq x2 (leaf 1)).label ≠ 0 then
                     «Prover.stKids»
                       («Prover.jobAt» x3 (leaf 1) x5)
                       x5
                       («Prover.nfMarked» x4)
                       («Prover.jobs»
                         («Prover/JobAt.map»
                           (fun (x8 : T) =>
                             «Prover.jobAt»
                               x3
                               (if («Prover.keepsWeak» x6 x8).label ≠ 0 then leaf 4 else leaf 1)
                               («Prelude.at» x7 x8))
                           («Base.range» («Prelude.length» x7))))
                   else
                     let x8 : T := «Derivation.childBinders» x0 x1 x5 («Prover.jobCtx» x3);
                     if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                       let x9 : List T := Const.children x8;
                       let x10 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x9
                         (leaf 0)
                         (fun (x10 : T) (_ : List T) => x10);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x9
                         ([] : List T)
                         (fun (_ : T) (x12 : List T) => x12);
                       let x12 : List T := «Derivation.bindersOf» x10;
                       let x13 : T := (if (Const.lt
                         («Derivation/BinderL.length» x12)
                         («Prelude.length» x7)).label ≠ 0 then
                         «Derivation/BinderL.length» x12
                       else
                         «Prelude.length» x7);
                       «Prover.stKids»
                         («Prover.jobAt» x3 x2 x5)
                         x5
                         («Prover.nfMarked» x4)
                         («Prover.jobs»
                           («Prover/JobAt.map»
                             (fun (x14 : T) =>
                               let x15 : T := «Derivation/BinderL.atOr»
                                 «Derivation.binder0»
                                 x12
                                 x14;
                               let x16 : T := «Prelude.at» x7 x14;
                               if («Prelude.and»
                                 (Const.eq x2 (leaf 2))
                                 («Prover.keepsFold» x6 x14)).label ≠ 0 then
                                 «Prover.jobAt» x3 (leaf 4) x16
                               else
                                 «Prover.job»
                                   x2
                                   («Language.objs» («Derivation.binderCtx» x15))
                                   (Const.add («Prover.jobNum» x3) («Derivation.binderNum» x15))
                                   («Derivation.terms» («Prover.jobHyps» x3))
                                   x16)
                             («Base.range» x13)))
                     else
                       let _ : List T := Const.children x8;
                       «Prover.stDone» «Prover/ONFR.nothing»);
    x5

def «Prover.stAfter» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (if (Const.eq x2 (leaf 0)).label ≠ 0 then
      «Prover.stDone» («Prover/ONFR.just» x4)
    else
      «Prover.stDeep» x0 x1 x2 x3 x4);
    x5

def «Prover.stRoot» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → T → List T → T → T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T)
    (x7 : T) =>
    let x8 : T := (let x8 : T := «Prover.jobRw» x2 x5 x6;
                   if («Language/OTPair.isJust» x8).label ≠ 0 then
                     let x9 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x8;
                     «Prover.stTail»
                       («Prover.jobAt» x5 x3 («Language.p1» x9))
                       «Prover.dRefl»
                       x7
                       («Prover.mark» («Language.p2» x9) (leaf 1))
                       x4
                   else
                     «Prover.stAfter» x0 x1 x4 x5 («Prover.nfr» x6 x7));
    x8

def «Prover.stStart» :=
  fun (x0 : T) (x1 : T) (x2 : List T → T → List T → T → T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Prover.jobDp» x3;
                   let x5 : T := «Prover.jobTerm» x3;
                   if (Const.eq x4 (leaf 4)).label ≠ 0 then
                     «Prover.stDone» («Prover/ONFR.just» («Prover.nfr» x5 «Prover.dRefl»))
                   else
                     if («Language.mIs» (leaf 6) (leaf 2) x5).label ≠ 0 then
                       «Prover.stFun» x3
                     else
                       let x6 : T := «Prover.jobRw» x2 x3 x5;
                       if («Language/OTPair.isJust» x6).label ≠ 0 then
                         let x7 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x6;
                         «Prover.stTail»
                           («Prover.jobAt» x3 (leaf 0) («Language.p1» x7))
                           «Prover.dRefl»
                           «Prover.dRefl»
                           («Prover.mark» («Language.p2» x7) (leaf 1))
                           x4
                       else
                         let x7 : T := «Prover.headChild» x5;
                         if («Prelude.isSome» x7).label ≠ 0 then
                           let x8 : T := «Prelude.nth» («Language.mArgs» x5) («Prelude.get» x7);
                           if («Prelude.isSome» x8).label ≠ 0 then
                             «Prover.stChild» x3 («Prelude.get» x7) («Prelude.get» x8)
                           else
                             «Prover.stDone» «Prover/ONFR.nothing»
                         else
                           «Prover.stAfter» x0 x1 x4 x3 («Prover.nfr» x5 «Prover.dRefl»));
    x4

def «Prover.stAdv» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → T → List T → T → T)
    (x3 : T)
    (x4 : List T) =>
    let x5 : T := (let x5 : T := x3;
                   if (Const.eq (Const.label x5) (leaf 0)).label ≠ 0 then
                     let x6 : List T := Const.children x5;
                     let x7 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x6
                       (leaf 0)
                       (fun (x7 : T) (_ : List T) => x7);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x6
                       ([] : List T)
                       (fun (_ : T) (x9 : List T) => x9);
                     «Prover.stDone» x7
                   else
                     if (Const.eq (Const.label x5) (leaf 1)).label ≠ 0 then
                       let x6 : List T := Const.children x5;
                       let x7 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x6
                         (leaf 0)
                         (fun (x7 : T) (_ : List T) => x7);
                       let x8 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x6
                         ([] : List T)
                         (fun (_ : T) (x9 : List T) => x9);
                       let x9 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x8
                         (leaf 0)
                         (fun (x9 : T) (_ : List T) => x9);
                       let x10 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x8
                         ([] : List T)
                         (fun (_ : T) (x11 : List T) => x11);
                       let x11 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x10
                         (leaf 0)
                         (fun (x11 : T) (_ : List T) => x11);
                       let x12 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x10
                         ([] : List T)
                         (fun (_ : T) (x13 : List T) => x13);
                       let x13 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x12
                         (leaf 0)
                         (fun (x13 : T) (_ : List T) => x13);
                       let x14 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x12
                         ([] : List T)
                         (fun (_ : T) (x15 : List T) => x15);
                       let x15 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x14
                         (leaf 0)
                         (fun (x15 : T) (_ : List T) => x15);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x14
                         ([] : List T)
                         (fun (_ : T) (x17 : List T) => x17);
                       let x17 : T := «Prover.firstR» x4;
                       if (Const.eq (Const.label x17) (leaf 1)).label ≠ 0 then
                         let x18 : List T := Const.children x17;
                         let x19 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x18
                           (leaf 0)
                           (fun (x19 : T) (_ : List T) => x19);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x18
                           ([] : List T)
                           (fun (_ : T) (x21 : List T) => x21);
                         «Prover.stAfter»
                           x0
                           x1
                           x15
                           x7
                           («Prover.nfr»
                             («Prover.nfTerm» x19)
                             («Prover.dTrans»
                               x9
                               («Prover.dTrans» x11 («Prover.dTrans» x13 («Prover.nfMarked» x19)))))
                       else
                         let _ : List T := Const.children x17;
                         «Prover.stDone» «Prover/ONFR.nothing»
                     else
                       if (Const.eq (Const.label x5) (leaf 2)).label ≠ 0 then
                         let x6 : List T := Const.children x5;
                         let x7 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x6
                           (leaf 0)
                           (fun (x7 : T) (_ : List T) => x7);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x6
                           ([] : List T)
                           (fun (_ : T) (x9 : List T) => x9);
                         let x9 : T := «Prover.firstR» x4;
                         if (Const.eq (Const.label x9) (leaf 1)).label ≠ 0 then
                           let x10 : List T := Const.children x9;
                           let x11 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x10
                             (leaf 0)
                             (fun (x11 : T) (_ : List T) => x11);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x10
                             ([] : List T)
                             (fun (_ : T) (x13 : List T) => x13);
                           let x13 : T := «Prover.nfTerm» x11;
                           let x14 : T := «Language.mArg» («Prover.jobTerm» x7) (leaf 1);
                           «Prover.stArg»
                             x7
                             x11
                             (if («Language.mIs» (leaf 5) (leaf 1) x13).label ≠ 0 then
                               «Prover.jobAt»
                                 x7
                                 (if (Const.lt
                                   («Prover.uses» («Language.mArg» x13 (leaf 0)) (leaf 0))
                                   (leaf 2)).label ≠ 0 then
                                   leaf 4
                                 else
                                   leaf 1)
                                 x14
                             else
                               «Prover.jobAt» x7 (leaf 0) x14)
                         else
                           let _ : List T := Const.children x9;
                           «Prover.stDone» «Prover/ONFR.nothing»
                       else
                         if (Const.eq (Const.label x5) (leaf 3)).label ≠ 0 then
                           let x6 : List T := Const.children x5;
                           let x7 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x6
                             (leaf 0)
                             (fun (x7 : T) (_ : List T) => x7);
                           let x8 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x6
                             ([] : List T)
                             (fun (_ : T) (x9 : List T) => x9);
                           let x9 : T := Const.lcase
                             (α := T)
                             (β := T)
                             x8
                             (leaf 0)
                             (fun (x9 : T) (_ : List T) => x9);
                           let x10 : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x8
                             ([] : List T)
                             (fun (_ : T) (x11 : List T) => x11);
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x10
                             (leaf 0)
                             (fun (x11 : T) (_ : List T) => x11);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x10
                             ([] : List T)
                             (fun (_ : T) (x13 : List T) => x13);
                           let x13 : T := «Prover.firstR» x4;
                           if (Const.eq (Const.label x13) (leaf 1)).label ≠ 0 then
                             let x14 : List T := Const.children x13;
                             let x15 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x14
                               (leaf 0)
                               (fun (x15 : T) (_ : List T) => x15);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x14
                               ([] : List T)
                               (fun (_ : T) (x17 : List T) => x17);
                             «Prover.stRoot»
                               x0
                               x1
                               x2
                               (leaf 0)
                               («Prover.jobDp» x7)
                               x7
                               («Language.app» («Prover.nfTerm» x9) («Prover.nfTerm» x15))
                               («Prover.dCong»
                                 («Prover/MarkedF.l2»
                                   («Prover.nfMarked» x9)
                                   («Prover.nfMarked» x15)))
                           else
                             let _ : List T := Const.children x13;
                             «Prover.stDone» «Prover/ONFR.nothing»
                         else
                           if (Const.eq (Const.label x5) (leaf 4)).label ≠ 0 then
                             let x6 : List T := Const.children x5;
                             let x7 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x6
                               (leaf 0)
                               (fun (x7 : T) (_ : List T) => x7);
                             let x8 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x6
                               ([] : List T)
                               (fun (_ : T) (x9 : List T) => x9);
                             let x9 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x8
                               (leaf 0)
                               (fun (x9 : T) (_ : List T) => x9);
                             let x10 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x8
                               ([] : List T)
                               (fun (_ : T) (x11 : List T) => x11);
                             let _ : T := Const.lcase
                               (α := T)
                               (β := T)
                               x10
                               (leaf 0)
                               (fun (x11 : T) (_ : List T) => x11);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x10
                               ([] : List T)
                               (fun (_ : T) (x13 : List T) => x13);
                             let x13 : T := «Prover.firstR» x4;
                             if (Const.eq (Const.label x13) (leaf 1)).label ≠ 0 then
                               let x14 : List T := Const.children x13;
                               let x15 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x14
                                 (leaf 0)
                                 (fun (x15 : T) (_ : List T) => x15);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x14
                                 ([] : List T)
                                 (fun (_ : T) (x17 : List T) => x17);
                               let x17 : T := «Prover.jobTerm» x7;
                               if («Prover.mFlag» («Prover.nfMarked» x15)).label ≠ 0 then
                                 let x18 : List T := «Language.mArgs» x17;
                                 «Prover.stRoot»
                                   x0
                                   x1
                                   x2
                                   (leaf 0)
                                   («Prover.jobDp» x7)
                                   x7
                                   (Const.node
                                     (Const.label x17)
                                     ((Const.child x17 (leaf 0)) ::
                                       («Prover.setAt» x18 x9 («Prover.nfTerm» x15))))
                                   («Prover.dCong»
                                     («Prover/MarkedAt.map»
                                       (fun (x19 : T) =>
                                         if (Const.eq x19 x9).label ≠ 0 then
                                           «Prover.nfMarked» x15
                                         else
                                           «Prover.dRefl»)
                                       («Base.range» («Prelude.length» x18))))
                               else
                                 «Prover.stAfter»
                                   x0
                                   x1
                                   («Prover.jobDp» x7)
                                   x7
                                   («Prover.nfr» x17 «Prover.dRefl»)
                             else
                               let _ : List T := Const.children x13;
                               «Prover.stDone» «Prover/ONFR.nothing»
                           else
                             let x6 : List T := Const.children x5;
                             let x7 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x6
                               (leaf 0)
                               (fun (x7 : T) (_ : List T) => x7);
                             let x8 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x6
                               ([] : List T)
                               (fun (_ : T) (x9 : List T) => x9);
                             let x9 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x8
                               (leaf 0)
                               (fun (x9 : T) (_ : List T) => x9);
                             let x10 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x8
                               ([] : List T)
                               (fun (_ : T) (x11 : List T) => x11);
                             let x11 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x10
                               (leaf 0)
                               (fun (x11 : T) (_ : List T) => x11);
                             let x12 : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x10
                               ([] : List T)
                               (fun (_ : T) (x13 : List T) => x13);
                             let _ : T := Const.lcase
                               (α := T)
                               (β := T)
                               x12
                               (leaf 0)
                               (fun (x13 : T) (_ : List T) => x13);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x12
                               ([] : List T)
                               (fun (_ : T) (x15 : List T) => x15);
                             let x15 : T := «Prover.allSomeN» x4;
                             if (Const.eq (Const.label x15) (leaf 1)).label ≠ 0 then
                               let x16 : List T := Const.children x15;
                               let x17 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x16
                                 (leaf 0)
                                 (fun (x17 : T) (_ : List T) => x17);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x16
                                 ([] : List T)
                                 (fun (_ : T) (x19 : List T) => x19);
                               let x19 : List T := «Prover.nfrsOf» x17;
                               let x20 : T := «Prover.rebuild» x9 x19;
                               if (Const.eq («Prover.jobDp» x7) (leaf 3)).label ≠ 0 then
                                 let x21 : T := «Prover.dCong»
                                   («Prover/NFRMarked.map» «Prover.nfMarked» x19);
                                 let x22 : T := «Prover.jobRw» x2 x7 x20;
                                 if («Language/OTPair.isJust» x22).label ≠ 0 then
                                   let x23 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x22;
                                   «Prover.stTail»
                                     («Prover.jobAt» x7 (leaf 3) («Language.p1» x23))
                                     x11
                                     x21
                                     («Prover.mark» («Language.p2» x23) (leaf 1))
                                     (leaf 0)
                                 else
                                   «Prover.stDone»
                                     («Prover/ONFR.just»
                                       («Prover.nfr» x20 («Prover.dTrans» x11 x21)))
                               else
                                 let x21 : T := «Prover.dTrans»
                                   x11
                                   («Prover.dCong» («Prover/NFRMarked.map» «Prover.nfMarked» x19));
                                 if («Prover.marked» x19).label ≠ 0 then
                                   «Prover.stRoot» x0 x1 x2 («Prover.jobDp» x7) (leaf 0) x7 x20 x21
                                 else
                                   «Prover.stDone» («Prover/ONFR.just» («Prover.nfr» x20 x21))
                             else
                               let _ : List T := Const.children x15;
                               «Prover.stDone» «Prover/ONFR.nothing»);
    x5

def «Prover.stRound» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → T → List T → T → T)
    (x3 : List T → List T)
    (x4 : List T) =>
    let x5 : List
      T := Const.foldr
      (α := T)
      (β := List T → List T)
      (fun (x5 : T) (x6 : List T → List T) (x7 : List T) =>
        let x8 : List T × List T := «Prover.splitRs» («Prover.stNeed» x5) x7;
        ((«Prover.stAdv» x0 x1 x2 x5 (x8).1) :: (x6 (x8).2)))
      (fun (_ : List T) => ([] : List T))
      x4
      (x3
        (Const.foldr
          (α := T)
          (β := List T)
          (fun (x5 : T) (x6 : List T) =>
            «Prover/JobL.append» («Prover.stNeed» x5) x6)
          ([] : List T)
          x4));
    x5

def «Prover.evalStepB» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T → T → List T → T → T)
    (x3 : List T → List T) =>
    let x4 : List T →
      List
        T := (fun (x4 : List T) =>
      Const.lcase
        (α := T)
        (β := List T)
        x4
        ([] : List T)
        (fun (_ : T) (_ : List T) =>
          «Prover/StOut.map»
            «Prover.stResult»
            («Prover.stRound»
              x0
              x1
              x2
              x3
              («Prover.stRound»
                x0
                x1
                x2
                x3
                («Prover.stRound»
                  x0
                  x1
                  x2
                  x3
                  («Prover.stRound»
                    x0
                    x1
                    x2
                    x3
                    («Prover.stRound»
                      x0
                      x1
                      x2
                      x3
                      («Prover/StAt.map»
                        (fun (x7 : T) => «Prover.stStart» x0 x1 x2 x7)
                        x4))))))));
    x4

def «Prover.evalB» :=
  fun (x0 : T) (x1 : T) (x2 : List T → T → List T → T → T) (x3 : T) =>
    let x4 : List T →
      List
        T := Const.iter
      (α := List T → List T)
      («Prover.evalStepB» x0 x1 x2)
      (fun (x4 : List T) =>
        «Prover/StOut.map»
          «Prover.stResult»
          («Prover/StAt.map»
            (fun (x5 : T) =>
              «Prover.stDone»
                («Prover/ONFR.just»
                  («Prover.nfr» («Prover.jobTerm» x5) «Prover.dRefl»)))
            x4))
      x3;
    x4

def «Prover.evalK» :=
  fun (x0 : T) (x1 : T) (x2 : List T → T → List T → T → T) (x3 : T) =>
    let x4 : T →
      List T →
        T →
          List T →
            T →
              T := (fun (x4 : T) (x5 : List T) (x6 : T) (x7 : List T) (x8 : T) =>
      «Prover.firstR»
        («Prover.evalB»
          x0
          x1
          x2
          x3
          («Prover/JobL.single»
            («Prover.job»
              x4
              («Language.objs» x5)
              x6
              («Derivation.terms» x7)
              x8))));
    x4

def «Prover.eval» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : T →
      List T →
        List T →
          T →
            T := (let x5 : List (T × List T) × List T := «Prover.indexRules» x1 x3;
                  fun (x6 : T) (x7 : List T) (x8 : List T) (x9 : T) =>
                    «Prover.evalK»
                      x0
                      x2
                      («Prover.rootRewriteK» x0 x1 x2 x5 («Prover.prepareHyps» x8))
                      x4
                      x6
                      x7
                      (leaf 0)
                      x8
                      x9);
    x5

def «Prover.whnf» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : List T →
      List T → T → T := «Prover.eval» x0 x1 x2 x3 x4 (leaf 0);
    x5

def «Prover.normalizeW» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : List T →
      List T → T → T := «Prover.eval» x0 x1 x2 x3 x4 (leaf 3);
    x5

def «Prover.byNormW» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T) =>
    let x9 : T := «Prover.joinBy»
      («Prover.normalizeW» x0 x1 x2 x3 x4)
      x5
      x6
      x7
      x8;
    x9

def «Prover.abstractVar» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mLam»
      x1
      («Language.subst»
        («Derivation.weaken1» x2)
        (fun (x3 : T) =>
          if (Const.eq x3 (Const.add x0 (leaf 1))).label ≠ 0 then
            «Language.var» (leaf 0)
          else
            «Language.var» x3));
    x3

def «Prover.byFunExt» :=
  fun (x0 : T) (x1 : T) (x2 : List T → List T → T → T → T) =>
    let x3 : List T →
      List T →
        T →
          T →
            T := (fun (x3 : List T) (x4 : List T) (x5 : T) (x6 : T) =>
      «Derivation.bindPT»
        («Language.bindTP»
          («Derivation.typeIn» x0 x1 x3 x5)
          «Language.expParts»)
        (fun (x7 : T) =>
          «Base.mapO»
            (fun (x8 : T) =>
              «Prover.dNode» (leaf 26) ([] : List T) («Prelude.single» x8))
            (x2
              ((«Language.p1» x7) :: x3)
              («Base.mapT» «Derivation.weaken1» x4)
              («Language.app» («Derivation.weaken1» x5) («Language.var» (leaf 0)))
              («Language.app»
                («Derivation.weaken1» x6)
                («Language.var» (leaf 0))))));
    x3

def «Prover.bySplit» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
      «Base.bindO»
        («Prelude.nth» x4 x2)
        (fun (x8 : T) =>
          «Prover.bindP»
            («Language.coprodParts» x8)
            (fun (x9 : T) =>
              let x10 : T := «Language.p1» x9;
              let x11 : T := «Language.p2» x9;
              let x12 : T := «Prover.abstractVar» x2 x8 x6;
              let x13 : T := «Prover.abstractVar» x2 x8 x7;
              let x14 : T →
                T →
                  T := (fun (x14 : T) (x15 : T) =>
                «Language.app»
                  («Derivation.weaken1» x15)
                  («Language.mArr»
                    x14
                    («Theory.l2» x10 x11)
                    («Language.var» (leaf 0))));
              «Base.bindO»
                (x3
                  (x10 :: x4)
                  («Base.mapT» «Derivation.weaken1» x5)
                  (x14 x0 x12)
                  (x14 x0 x13))
                (fun (x15 : T) =>
                  «Base.bindO»
                    (x3
                      (x11 :: x4)
                      («Base.mapT» «Derivation.weaken1» x5)
                      (x14 x1 x12)
                      (x14 x1 x13))
                    (fun (x16 : T) =>
                      let x17 : T := «Prover.dNode»
                        (leaf 26)
                        ([] : List T)
                        («Prelude.single»
                          («Prover.dNode» (leaf 34) («Theory.l2» x0 x1) («Theory.l2» x15 x16)));
                      let x18 : T := «Prover.dNode»
                        (leaf 2)
                        ([] : List T)
                        («Theory.l2»
                          («Prover.dNode» (leaf 3) ([] : List T) ([] : List T))
                          («Prover.dNode» (leaf 3) ([] : List T) ([] : List T)));
                      let x19 : T := «Prover.dNode»
                        (leaf 18)
                        ([] : List T)
                        («Theory.l2»
                          («Prover.dNode»
                            (leaf 2)
                            ([] : List T)
                            («Theory.l2»
                              («Prover.dNode»
                                (leaf 17)
                                («Theory.l2» («Prelude.length» x5) (leaf 0))
                                ([] : List T))
                              («Prover.dNode» (leaf 0) ([] : List T) ([] : List T))))
                          («Prover.dNode» (leaf 0) ([] : List T) ([] : List T)));
                      let x20 : T := «Language.mEq»
                        («Language.app» x12 («Language.var» x2))
                        («Language.app» x13 («Language.var» x2));
                      «Prelude.some»
                        («Prover.dNode»
                          (leaf 22)
                          («Prelude.single» («Language.mEq» x12 x13))
                          («Theory.l2»
                            x17
                            («Prover.dNode»
                              (leaf 24)
                              («Prelude.single» x20)
                              («Theory.l2» x18 x19)))))))));
    x4

def «Prover.byListIndWith» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : T)
    (x4 : List T → List T → T → T → T)
    (x5 : List T → List T → T → T → T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      Const.lcase
        (α := T)
        (β := T)
        x6
        «Prelude.none»
        (fun (x10 : T) (x11 : List T) =>
          «Base.bindO»
            («Language.listPart» x10)
            (fun (x12 : T) =>
              «Prover.bindHT»
                («Derivation.lowerHyps» x0 x1 x11 x7)
                (fun (x13 : T) =>
                  let x14 : List T := «Prover.termsOf» x13;
                  «Base.bindO»
                    (x4
                      x11
                      x14
                      («Prover.instAt» x2 («Prelude.single» x12) x8)
                      («Prover.instAt» x2 («Prelude.single» x12) x9))
                    (fun (x15 : T) =>
                      «Base.mapO»
                        (fun (x16 : T) =>
                          «Prover.dNode» (leaf 29) («Theory.l2» x2 x3) («Theory.l2» x15 x16))
                        (x5
                          (x10 :: (x12 :: x11))
                          («Prelude.append»
                            («Base.mapT» «Derivation.weaken2» x14)
                            («Prelude.single» («Derivation.weakenElem» («Language.mEq» x8 x9))))
                          («Derivation.listConsAt» x3 x12 x8)
                          («Derivation.listConsAt» x3 x12 x9)))))));
    x6

def «Prover.byRoseInd» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : T)
    (x6 : T)
    (x7 : List T)
    (x8 : T)
    (x9 : List T)
    (x10 : T)
    (x11 : T) =>
    let x12 : T := (if (Const.eq
      («Prelude.length» x9)
      (leaf 1)).label ≠ 0 then
      let x12 : T := «Prelude.at» x9 (leaf 0);
      «Base.bindO»
        («Language.roseLabel» x12)
        (fun (x13 : T) =>
          «Base.bindO»
            («Derivation.typeIn» x0 x2 x9 x10)
            (fun (x14 : T) =>
              let x15 : List T := «Theory.l2» («Theory.list» x12) x13;
              «Base.bindO»
                («Prover.byNorm»
                  x0
                  x1
                  x2
                  x7
                  x8
                  x15
                  ([] : List T)
                  («Derivation.roseNodeAt» x3 x12 x13 x10)
                  («Language.subst»
                    x6
                    («Derivation.atVar0» («Derivation.roseMapAt» x4 x5 x14 x10))))
                (fun (x16 : T) =>
                  «Base.mapO»
                    (fun (x17 : T) =>
                      «Prover.dNode»
                        (leaf 32)
                        («Theory.l4» x3 x4 x5 x6)
                        («Theory.l2» x16 x17))
                    («Prover.byNorm»
                      x0
                      x1
                      x2
                      x7
                      x8
                      x15
                      ([] : List T)
                      («Derivation.roseNodeAt» x3 x12 x13 x11)
                      («Language.subst»
                        x6
                        («Derivation.atVar0» («Derivation.roseMapAt» x4 x5 x14 x11)))))))
    else
      «Prelude.none»);
    x12

def «Prover.byRoseIndHyp» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T → List T → T → T → T) =>
    let x4 : List T →
      List T →
        T →
          T →
            T := (fun (x4 : List T) (x5 : List T) (x6 : T) (x7 : T) =>
      if («Prelude.and»
        («Base.not» («Base.isEmpty» x4))
        («Base.isEmpty» x5)).label ≠ 0 then
        let x8 : T := «Prelude.at» x4 (leaf 0);
        «Base.bindO»
          («Language.roseLabel» x8)
          (fun (x9 : T) =>
            «Base.mapO»
              (fun (x10 : T) =>
                «Prover.dNode»
                  (leaf 33)
                  («Theory.l3» x0 x1 x2)
                  («Prelude.single» x10))
              (x3
                ((«Theory.list» x8) :: (x9 :: («Prelude.tail» x4)))
                («Prelude.single» («Derivation.roseHyp» x1 x2 («Language.mEq» x6 x7)))
                («Derivation.roseNodeAt» x0 x8 x9 x6)
                («Derivation.roseNodeAt» x0 x8 x9 x7)))
      else
        «Prelude.none»);
    x4

end GebMirror.Metalogic

end
