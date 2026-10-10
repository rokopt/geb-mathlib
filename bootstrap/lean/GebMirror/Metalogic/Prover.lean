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
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Prover.mFlag» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
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
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Prover/OAssign.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
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
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Prover.assigned» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
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
            x2);
    x1

def «Prover.bindAA» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prover/OAssign.nothing»);
    x2

def «Prover/Mts.tail» :=
  fun (x0 : List (T → T → List T → T)) =>
    Const.lcase
      (α := T → T → List T → T)
      (β := List (T → T → List T → T))
      x0
      ([] : List (T → T → List T → T))
      (fun (_ : T → T → List T → T) (x2 : List (T → T → List T → T)) => x2)

def «Prover.mtAt» :=
  fun (x0 : List (T → T → List T → T)) (x1 : T) =>
    let x2 : T →
      T →
        List T →
          T := Const.lcase
      (α := T → T → List T → T)
      (β := T → T → List T → T)
      (Const.iter (α := List (T → T → List T → T)) «Prover/Mts.tail» x0 x1)
      (fun (_ : T) (_ : T) (_ : List T) => «Prover/OAssign.nothing»)
      (fun (x2 : T → T → List T → T) (_ : List (T → T → List T → T)) => x2);
    x2

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
  fun (x0 : List (T → T → List T → T))
    (x1 : T)
    (x2 : List T)
    (x3 : List T) =>
    let x4 : T := Const.foldr
      (α := T → T → List T → T)
      (β := List T → T → T)
      (fun (x4 : T → T → List T → T)
         (x5 : List T → T → T)
         (x6 : List T)
         (x7 : T) =>
        Const.lcase
          (α := T)
          (β := T)
          x6
          x7
          (fun (x8 : T) (x9 : List T) =>
            x5
              x9
              («Prover.bindAA»
                x7
                (fun (x10 : T) => x4 x1 x8 («Prover.assigned» x10)))))
      (fun (_ : List T) (x5 : T) => x5)
      («Prover/Mts.tail» x0)
      x2
      («Prover/OAssign.just» («Prover.assign» x3));
    x4

def «Prover.matchStep» :=
  fun (x0 : T) (x1 : List (T → T → List T → T)) =>
    let x2 : T →
      T →
        List T →
          T := (fun (x2 : T) (x3 : T) (x4 : List T) =>
      let x5 : T := Const.label x0;
      if (Const.eq x5 (leaf 0)).label ≠ 0 then
        «Prover.matchVar» («Language.mD» x0 (leaf 0)) x2 x3 x4
      else
        let x6 : List T := «Language.mArgs» x3;
        let x7 : T := «Prelude.length» x6;
        if («Prelude.and»
          («Prelude.and»
            (Const.eq x5 (Const.label x3))
            (Const.equal (Const.child x0 (leaf 0)) (Const.child x3 (leaf 0))))
          (Const.eq («Prelude.length» («Language.mArgs» x0)) x7)).label ≠ 0 then
          if («Prelude.and»
            (Const.eq x5 (leaf 5))
            (Const.eq x7 (leaf 1))).label ≠ 0 then
            «Prover.mtAt»
              x1
              (leaf 1)
              (Const.add x2 (leaf 1))
              («Prelude.at» x6 (leaf 0))
              x4
          else
            if («Prelude.and»
              («Prelude.or» (Const.eq x5 (leaf 8)) (Const.eq x5 (leaf 9)))
              (Const.eq x7 (leaf 3))).label ≠ 0 then
              «Prover.bindAA»
                («Prover.bindAA»
                  («Prover.mtAt» x1 (leaf 1) x2 («Prelude.at» x6 (leaf 0)) x4)
                  (fun (x8 : T) =>
                    «Prover.mtAt»
                      x1
                      (leaf 2)
                      (Const.add
                        x2
                        (if (Const.eq x5 (leaf 8)).label ≠ 0 then leaf 1 else leaf 2))
                      («Prelude.at» x6 (leaf 1))
                      («Prover.assigned» x8)))
                (fun (x8 : T) =>
                  «Prover.mtAt»
                    x1
                    (leaf 3)
                    x2
                    («Prelude.at» x6 (leaf 2))
                    («Prover.assigned» x8))
            else
              if («Prelude.and»
                (Const.eq x5 (leaf 10))
                (Const.eq x7 (leaf 2))).label ≠ 0 then
                if (Const.equal
                  («Language.mArg» x0 (leaf 0))
                  («Prelude.at» x6 (leaf 0))).label ≠ 0 then
                  «Prover.mtAt» x1 (leaf 2) x2 («Prelude.at» x6 (leaf 1)) x4
                else
                  «Prover/OAssign.nothing»
              else
                «Prover.matchAll» x1 x2 x6 x4
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

def «Prover.noMatch» :=
  fun (_ : T) (_ : T) (_ : List T) => «Prover/OAssign.nothing»

def «Prover.bindP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prelude.none»);
    x2

def «Prover.bindAP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Language/OTPair.nothing»);
    x2

def «Prover.bindHP» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Language/OTPair.nothing»);
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
            x2);
    x1

def «Prover.objsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
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
            x2);
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
    (x5 : T × (T → T → List T → T))
    (x6 : T) =>
    let x7 : T := (let x7 : T := (x5).1;
                   if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
                     let x8 : T := Const.child x7 (leaf 0);
                     let x9 : T := Const.child x7 (leaf 1);
                     let x10 : List T := «Prover.termsOf» x9;
                     «Prover.mapTP»
                       (fun (x11 : T) =>
                         «Language.pr» x11 («Prover.dNode» x8 x10 ([] : List T)))
                       («Derivation.rootStep» x0 x1 x2 x3 x4 x8 x10 x6)
                   else
                     if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                       let x8 : T := Const.child x7 (leaf 0);
                       if («Prelude.and»
                         (Const.eq (Const.label x6) (leaf 11))
                         (Const.eq («Language.mD» x6 (leaf 0)) x8)).label ≠ 0 then
                         «Prover.mapTP»
                           (fun (x9 : T) =>
                             «Language.pr»
                               x9
                               («Prover.dNode» (leaf 8) ([] : List T) ([] : List T)))
                           («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 8) ([] : List T) x6)
                       else
                         «Language/OTPair.nothing»
                     else
                       if (Const.eq (Const.label x7) (leaf 2)).label ≠ 0 then
                         let x8 : T := Const.child x7 (leaf 0);
                         let x9 : T := Const.child x7 (leaf 1);
                         if («Prelude.and»
                           (Const.eq (Const.label x6) (leaf 11))
                           («Prelude.and»
                             (Const.lt («Language.mD» x6 (leaf 0)) x8)
                             («Base.not»
                               («Base.anyT»
                                 (fun (x10 : T) => Const.eq x10 («Language.mD» x6 (leaf 0)))
                                 («Prover.termsOf» x9))))).label ≠ 0 then
                           «Prover.mapTP»
                             (fun (x10 : T) =>
                               «Language.pr»
                                 x10
                                 («Prover.dNode» (leaf 8) ([] : List T) ([] : List T)))
                             («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 8) ([] : List T) x6)
                         else
                           «Language/OTPair.nothing»
                       else
                         if (Const.eq (Const.label x7) (leaf 3)).label ≠ 0 then
                           if («Prelude.and»
                             (Const.eq (Const.label x6) (leaf 0))
                             (Const.equal
                               («Prelude.nth» x3 («Language.mD» x6 (leaf 0)))
                               («Prelude.some» «Theory.one»))).label ≠ 0 then
                             «Prover.mapTP»
                               (fun (x8 : T) =>
                                 «Language.pr»
                                   x8
                                   («Prover.dNode» (leaf 7) ([] : List T) ([] : List T)))
                               («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 7) ([] : List T) x6)
                           else
                             «Language/OTPair.nothing»
                         else
                           if (Const.eq (Const.label x7) (leaf 4)).label ≠ 0 then
                             let x8 : T := Const.child x7 (leaf 0);
                             let x9 : T := Const.child x7 (leaf 1);
                             let x10 : List T := «Prover.objsOf» x9;
                             «Prover.bindHP»
                               («Derivation.thmAt» x1 x8)
                               (fun (x11 : T) =>
                                 «Language.bindPP»
                                   («Derivation.eqParts» («Derivation.thConcl» x11))
                                   (fun (x12 : T) =>
                                     if («Prover.sameShape» («Language.p1» x12) x6).label ≠ 0 then
                                       «Prover.thmRewrite»
                                         x0
                                         x1
                                         x2
                                         x3
                                         x4
                                         x8
                                         x10
                                         («Prover.matchTerm»
                                           (if («Base.isEmpty» x10).label ≠ 0 then
                                             «Language.p1» x12
                                           else
                                             «Language.osubst» x10 («Language.p1» x12)))
                                         («Prelude.length» («Derivation.thCtx» x11))
                                         x6
                                     else
                                       «Language/OTPair.nothing»))
                           else
                             if (Const.eq (Const.label x7) (leaf 5)).label ≠ 0 then
                               let x8 : T := Const.child x7 (leaf 0);
                               let x9 : T := Const.child x7 (leaf 1);
                               let x10 : T := Const.child x7 (leaf 2);
                               let x11 : T := Const.child x7 (leaf 3);
                               if («Prover.sameShape» x10 x6).label ≠ 0 then
                                 «Prover.thmRewrite»
                                   x0
                                   x1
                                   x2
                                   x3
                                   x4
                                   x8
                                   («Prover.objsOf» x9)
                                   (x5).2
                                   x11
                                   x6
                               else
                                 «Language/OTPair.nothing»
                             else
                               let x8 : T := Const.child x7 (leaf 0);
                               let x9 : List T := «Theory.l2» x8 (leaf 0);
                               «Prover.mapTP»
                                 (fun (x10 : T) =>
                                   «Language.pr» x10 («Prover.dNode» (leaf 17) x9 ([] : List T)))
                                 («Derivation.rootStep» x0 x1 x2 x3 x4 (leaf 17) x9 x6));
    x7

def «Prover.rootRewrite» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := Const.foldr
      (α := T × (T → T → List T → T))
      (β := T → T)
      (fun (x7 : T × (T → T → List T → T)) (x8 : T → T) (x9 : T) =>
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
    let x2 : T ×
      (T →
        T →
          List T →
            T) := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 4)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0);
                     let x4 : T := Const.child x2 (leaf 1);
                     let x5 : List T := «Prover.objsOf» x4;
                     let x6 : T := «Derivation.thmAt» x0 x3;
                     let x7 : T := «Prover.bindHP»
                       x6
                       (fun (x7 : T) => «Derivation.eqParts» («Derivation.thConcl» x7));
                     if («Language/OTPair.isJust» x7).label ≠ 0 then
                       let x8 : T := (if («Base.isEmpty» x5).label ≠ 0 then
                         «Language.p1» («Language/OTPair.fromMaybe» «Prover.pr0» x7)
                       else
                         «Language.osubst»
                           x5
                           («Language.p1» («Language/OTPair.fromMaybe» «Prover.pr0» x7)));
                       («Prover.nrThmAt»
                         x3
                         x4
                         x8
                         («Prelude.length»
                           («Derivation.thCtx» («Derivation/OThm.fromMaybe» «Prover.thm0» x6))),
                         «Prover.matchTerm» x8)
                     else
                       (x1, «Prover.noMatch»)
                   else
                     (x1, «Prover.noMatch»));
    x2

def «Prover.prepareRules» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      (T ×
        (T →
          T →
            List T →
              T)) := Const.foldr
      (α := T)
      (β := List (T × (T → T → List T → T)))
      (fun (x2 : T) (x3 : List (T × (T → T → List T → T))) =>
        ((«Prover.prepareRule» x0 x2) :: x3))
      ([] : List (T × (T → T → List T → T)))
      x1;
    x2

def «Prover.nfr» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Prover.nfTerm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Prover.nfMarked» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «Prover/ONFR.nothing» := Const.node (leaf 0) ([] : List T)

def «Prover/ONFR.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Prover/ONFR.isJust» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 1)).label ≠ 0 then
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Prover/ONFR.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
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
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
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
                     let _ : T := Const.child x1 (leaf 0); leaf 1
                   else
                     leaf 0);
    x1

def «Prover/ONFRList.fromMaybe» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x3
                   else
                     x0);
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
          let x4 : T := Const.child x3 (leaf 0); ((x2).1, (x4 :: (x2).2))
        else
          (leaf 0, (x2).2))
      (leaf 1, ([] : List T))
      x0;
    x1

def «Prover.nfrsOf» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
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
            x2);
    x1

def «Prover.bindNT» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prelude.none»);
    x2

def «Prover.bindNN» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prover/ONFR.nothing»);
    x2

def «Prover.mapNN» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); «Prover/ONFR.just» (x0 x3)
                   else
                     «Prover/ONFR.nothing»);
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
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prover/ONFR.nothing»);
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
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prover/ONFR.nothing»);
    x2

def «Prover.bindHT» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (let x2 : T := x0;
                   if (Const.eq (Const.label x2) (leaf 1)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); x1 x3
                   else
                     «Prelude.none»);
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
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Prover.termOf» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
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

def «Prover/NormEach.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.normStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : List T → List T → T → T) =>
    let x5 : List T →
      List T →
        T →
          T := (fun (x5 : List T) (x6 : List T) (x7 : T) =>
      «Prover.bindSN»
        («Derivation.childCtxs» x0 x2 x7 x5 x6)
        (fun (x8 : T) =>
          let x9 : List T := «Derivation.scopesOf» x8;
          «Prover.bindLN»
            («Prover.allSomeN»
              («Prover/NormEach.map»
                (fun (x10 : T) =>
                  let x11 : T := «Prover.scopeOf» x10;
                  x4
                    («Derivation.scopeCtx» x11)
                    («Derivation.scopeHyps» x11)
                    («Prover.termOf» x10))
                («Prover.zipTs» x9 («Language.mArgs» x7))))
            (fun (x10 : T) =>
              let x11 : List T := «Prover.nfrsOf» x10;
              let x12 : T := «Prover.rebuild» x7 x11;
              let x13 : T := (if («Prover.marked» x11).label ≠ 0 then
                «Prover.mark»
                  («Prover.dNode»
                    (leaf 2)
                    ([] : List T)
                    («Prover/NFRTerm.map»
                      (fun (x13 : T) => «Prover.mDeriv» («Prover.nfMarked» x13))
                      x11))
                  (leaf 1)
              else
                «Prover.dRefl»);
              let x14 : T := «Prover.rootRewrite» x0 x1 x2 x3 x5 x6 x12;
              if («Language/OTPair.isJust» x14).label ≠ 0 then
                let x15 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x14;
                «Prover.mapNN»
                  (fun (x16 : T) =>
                    «Prover.nfr»
                      («Prover.nfTerm» x16)
                      («Prover.dTrans»
                        x13
                        («Prover.dTrans»
                          («Prover.mark» («Language.p2» x15) (leaf 1))
                          («Prover.nfMarked» x16))))
                  (x4 x5 x6 («Language.p1» x15))
              else
                «Prover/ONFR.just» («Prover.nfr» x12 x13))));
    x5

def «Prover.normalize» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : List T →
      List T →
        T →
          T := Const.iter
      (α := List T → List T → T → T)
      («Prover.normStep» x0 x1 x2 x3)
      (fun (_ : List T) (_ : List T) (x7 : T) =>
        «Prover/ONFR.just» («Prover.nfr» x7 «Prover.dRefl»))
      x4;
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
    (x3 : List (T × (T → T → List T → T)))
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
    (x6 : List (T × (T → T → List T → T)))
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
    (x6 : List (T × (T → T → List T → T)))
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
  fun (x0 : List (T × (T → T → List T → T))) (x1 : T) =>
    let x2 : List
      (T ×
        (T →
          T →
            List T →
              T)) := Const.foldr
      (α := T × (T → T → List T → T))
      (β := List (T × (T → T → List T → T)))
      (fun (x2 : T × (T → T → List T → T))
         (x3 : List (T × (T → T → List T → T))) =>
        (x2 :: x3))
      ((«Prover.nrHyp» x1, «Prover.noMatch») ::
        ([] : List (T × (T → T → List T → T))))
      x0;
    x2

def «Prover.byNatIndHyp» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : T)
    (x5 : List (T × (T → T → List T → T)))
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
    (x5 : List (T × (T → T → List T → T)))
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

def «Prover.ufAt» :=
  fun (x0 : List (T → T)) (x1 : T) =>
    let x2 : T →
      T := Const.lcase
      (α := T → T)
      (β := T → T)
      (Const.iter (α := List (T → T)) «Prover/UFs.tail» x0 x1)
      (fun (_ : T) => leaf 0)
      (fun (x2 : T → T) (_ : List (T → T)) => x2);
    x2

def «Prover.ufSum» :=
  fun (x0 : List (T → T)) (x1 : T) =>
    let x2 : T := Const.foldr
      (α := T → T)
      (β := T)
      (fun (x2 : T → T) (x3 : T) => Const.add (x2 x1) x3)
      (leaf 0)
      («Prover/UFs.tail» x0);
    x2

def «Prover.usesStep» :=
  fun (x0 : T) (x1 : List (T → T)) =>
    let x2 : T →
      T := (fun (x2 : T) =>
      let x3 : T := Const.label x0;
      let x4 : T := «Prelude.length» («Language.mArgs» x0);
      if (Const.eq x3 (leaf 0)).label ≠ 0 then
        if (Const.eq («Language.mD» x0 (leaf 0)) x2).label ≠ 0 then
          leaf 1
        else
          leaf 0
      else
        if (Const.eq x3 (leaf 5)).label ≠ 0 then
          Const.mul (leaf 2) («Prover.ufSum» x1 (Const.add x2 (leaf 1)))
        else
          if («Prelude.and»
            («Prelude.or» (Const.eq x3 (leaf 8)) (Const.eq x3 (leaf 9)))
            (Const.eq x4 (leaf 3))).label ≠ 0 then
            Const.add
              (Const.add
                («Prover.ufAt» x1 (leaf 1) x2)
                (Const.mul
                  (leaf 2)
                  («Prover.ufAt»
                    x1
                    (leaf 2)
                    (Const.add
                      x2
                      (if (Const.eq x3 (leaf 8)).label ≠ 0 then leaf 1 else leaf 2)))))
              («Prover.ufAt» x1 (leaf 3) x2)
          else
            if («Prelude.and»
              (Const.eq x3 (leaf 10))
              (Const.eq x4 (leaf 2))).label ≠ 0 then
              Const.add
                (Const.mul
                  (leaf 2)
                  («Prover.ufAt» x1 (leaf 1) (Const.add x2 (leaf 1))))
                («Prover.ufAt» x1 (leaf 2) x2)
            else
              «Prover.ufSum» x1 x2);
    x2

def «Prover.uses» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.para (α := T → T) «Prover.usesStep» x0 x1; x2

def «Prover.atRoot» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «Prover.rootRewrite» x0 x1 x2 x3 x5 x6 x8;
                    if («Language/OTPair.isJust» x10).label ≠ 0 then
                      let x11 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x10;
                      «Prover.mapNN»
                        (fun (x12 : T) =>
                          «Prover.nfr»
                            («Prover.nfTerm» x12)
                            («Prover.dTrans»
                              x9
                              («Prover.dTrans»
                                («Prover.mark» («Language.p2» x11) (leaf 1))
                                («Prover.nfMarked» x12))))
                        (x4 x7 x5 x6 («Language.p1» x11))
                    else
                      «Prover/ONFR.just» («Prover.nfr» x8 x9));
    x10

def «Prover.headStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T)
    (x5 : List T)
    (x6 : List T)
    (x7 : T) =>
    let x8 : T := (if («Language.mIs» (leaf 6) (leaf 2) x7).label ≠ 0 then
      «Prover.bindNN»
        (x4 (leaf 0) x5 x6 («Language.mArg» x7 (leaf 0)))
        (fun (x8 : T) =>
          let x9 : T := «Prover.nfTerm» x8;
          let x10 : T := «Language.mArg» x7 (leaf 1);
          «Prover.bindNN»
            (if («Language.mIs» (leaf 5) (leaf 1) x9).label ≠ 0 then
              if (Const.lt
                («Prover.uses» («Language.mArg» x9 (leaf 0)) (leaf 0))
                (leaf 2)).label ≠ 0 then
                «Prover/ONFR.just» («Prover.nfr» x10 «Prover.dRefl»)
              else
                x4 (leaf 1) x5 x6 x10
            else
              x4 (leaf 0) x5 x6 x10)
            (fun (x11 : T) =>
              «Prover.atRoot»
                x0
                x1
                x2
                x3
                x4
                x5
                x6
                (leaf 0)
                («Language.app» x9 («Prover.nfTerm» x11))
                («Prover.dCong»
                  («Prover/MarkedF.l2»
                    («Prover.nfMarked» x8)
                    («Prover.nfMarked» x11)))))
    else
      let x8 : T := «Prover.rootRewrite» x0 x1 x2 x3 x5 x6 x7;
      if («Language/OTPair.isJust» x8).label ≠ 0 then
        let x9 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x8;
        «Prover.mapNN»
          (fun (x10 : T) =>
            «Prover.nfr»
              («Prover.nfTerm» x10)
              («Prover.dTrans»
                («Prover.mark» («Language.p2» x9) (leaf 1))
                («Prover.nfMarked» x10)))
          (x4 (leaf 0) x5 x6 («Language.p1» x9))
      else
        let x9 : T := «Prover.headChild» x7;
        if («Prelude.isSome» x9).label ≠ 0 then
          let x10 : T := «Prelude.get» x9;
          let x11 : List T := «Language.mArgs» x7;
          «Prover.bindTN»
            («Prelude.nth» x11 x10)
            (fun (x12 : T) =>
              «Prover.bindNN»
                (x4 (leaf 0) x5 x6 x12)
                (fun (x13 : T) =>
                  if («Prover.mFlag» («Prover.nfMarked» x13)).label ≠ 0 then
                    «Prover.atRoot»
                      x0
                      x1
                      x2
                      x3
                      x4
                      x5
                      x6
                      (leaf 0)
                      (Const.node
                        (Const.label x7)
                        ((Const.child x7 (leaf 0)) ::
                          («Prover.setAt» x11 x10 («Prover.nfTerm» x13))))
                      («Prover.dCong»
                        («Prover/MarkedAt.map»
                          (fun (x14 : T) =>
                            if (Const.eq x14 x10).label ≠ 0 then
                              «Prover.nfMarked» x13
                            else
                              «Prover.dRefl»)
                          («Base.range» («Prelude.length» x11))))
                  else
                    «Prover/ONFR.just» («Prover.nfr» x7 «Prover.dRefl»)))
        else
          «Prover/ONFR.just» («Prover.nfr» x7 «Prover.dRefl»));
    x8

def «Prover/NormAt.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Prover.deepStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T)
    (x5 : T)
    (x6 : List T)
    (x7 : List T)
    (x8 : T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := Const.label x8;
                    let x11 : List T := «Language.mArgs» x8;
                    if (Const.eq x5 (leaf 1)).label ≠ 0 then
                      «Prover.bindLN»
                        («Prover.allSomeN»
                          («Prover/NormAt.map»
                            (fun (x12 : T) =>
                              if («Prover.keepsWeak» x10 x12).label ≠ 0 then
                                «Prover/ONFR.just»
                                  («Prover.nfr» («Prelude.at» x11 x12) «Prover.dRefl»)
                              else
                                x4 (leaf 1) x6 x7 («Prelude.at» x11 x12))
                            («Base.range» («Prelude.length» x11))))
                        (fun (x12 : T) =>
                          let x13 : List T := «Prover.nfrsOf» x12;
                          let x14 : T := «Prover.rebuild» x8 x13;
                          let x15 : T := «Prover.dTrans»
                            x9
                            («Prover.dCong» («Prover/NFRMarked.map» «Prover.nfMarked» x13));
                          if («Prover.marked» x13).label ≠ 0 then
                            «Prover.atRoot» x0 x1 x2 x3 x4 x6 x7 (leaf 1) x14 x15
                          else
                            «Prover/ONFR.just» («Prover.nfr» x14 x15))
                    else
                      «Prover.bindSN»
                        («Derivation.childCtxs» x0 x2 x8 x6 x7)
                        (fun (x12 : T) =>
                          let x13 : List T := «Derivation.scopesOf» x12;
                          «Prover.bindLN»
                            (let x14 : List T := «Prover.zipTs» x13 x11;
                             «Prover.allSomeN»
                               («Prover/NormAt.map»
                                 (fun (x15 : T) =>
                                   let x16 : T := «Prover/ScopeTerms.atOr»
                                     («Prover.scopeTerm» «Derivation.scope0» (leaf 0))
                                     x14
                                     x15;
                                   let x17 : T := «Prover.scopeOf» x16;
                                   if («Prelude.and»
                                     (Const.eq x5 (leaf 2))
                                     («Prover.keepsFold» x10 x15)).label ≠ 0 then
                                     «Prover/ONFR.just»
                                       («Prover.nfr» («Prover.termOf» x16) «Prover.dRefl»)
                                   else
                                     x4
                                       x5
                                       («Derivation.scopeCtx» x17)
                                       («Derivation.scopeHyps» x17)
                                       («Prover.termOf» x16))
                                 («Base.range» («Prover/ScopeTerms.length» x14))))
                            (fun (x14 : T) =>
                              let x15 : List T := «Prover.nfrsOf» x14;
                              let x16 : T := «Prover.rebuild» x8 x15;
                              if (Const.eq x5 (leaf 2)).label ≠ 0 then
                                let x17 : T := «Prover.dTrans»
                                  x9
                                  («Prover.dCong» («Prover/NFRMarked.map» «Prover.nfMarked» x15));
                                if («Prover.marked» x15).label ≠ 0 then
                                  «Prover.atRoot» x0 x1 x2 x3 x4 x6 x7 (leaf 2) x16 x17
                                else
                                  «Prover/ONFR.just» («Prover.nfr» x16 x17)
                              else
                                let x17 : T := «Prover.dCong»
                                  («Prover/NFRMarked.map» «Prover.nfMarked» x15);
                                let x18 : T := «Prover.rootRewrite» x0 x1 x2 x3 x6 x7 x16;
                                if («Language/OTPair.isJust» x18).label ≠ 0 then
                                  let x19 : T := «Language/OTPair.fromMaybe» «Prover.pr0» x18;
                                  «Prover.mapNN»
                                    (fun (x20 : T) =>
                                      «Prover.nfr»
                                        («Prover.nfTerm» x20)
                                        («Prover.dTrans»
                                          x9
                                          («Prover.dTrans»
                                            x17
                                            («Prover.dTrans»
                                              («Prover.mark» («Language.p2» x19) (leaf 1))
                                              («Prover.nfMarked» x20)))))
                                    (x4 (leaf 3) x6 x7 («Language.p1» x19))
                                else
                                  «Prover/ONFR.just» («Prover.nfr» x16 («Prover.dTrans» x9 x17)))));
    x10

def «Prover.evalStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T → List T → List T → T → T) =>
    let x5 : T →
      List T →
        List T →
          T →
            T := (fun (x5 : T) (x6 : List T) (x7 : List T) (x8 : T) =>
      «Prover.bindNN»
        («Prover.headStep» x0 x1 x2 x3 x4 x6 x7 x8)
        (fun (x9 : T) =>
          if (Const.eq x5 (leaf 0)).label ≠ 0 then
            «Prover/ONFR.just» x9
          else
            «Prover.deepStep»
              x0
              x1
              x2
              x3
              x4
              x5
              x6
              x7
              («Prover.nfTerm» x9)
              («Prover.nfMarked» x9)));
    x5

def «Prover.eval» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : T →
      List T →
        List T →
          T →
            T := Const.iter
      (α := T → List T → List T → T → T)
      («Prover.evalStep» x0 x1 x2 x3)
      (fun (_ : T) (_ : List T) (_ : List T) (x8 : T) =>
        «Prover/ONFR.just» («Prover.nfr» x8 «Prover.dRefl»))
      x4;
    x5

def «Prover.whnf» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : List T →
      List T → T → T := «Prover.eval» x0 x1 x2 x3 x4 (leaf 0);
    x5

def «Prover.normalizeW» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
    (x4 : T) =>
    let x5 : List T →
      List T → T → T := «Prover.eval» x0 x1 x2 x3 x4 (leaf 3);
    x5

def «Prover.byNormW» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List (T × (T → T → List T → T)))
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
    (x7 : List (T × (T → T → List T → T)))
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
            T := (fun (x4 : List T) (_ : List T) (x6 : T) (x7 : T) =>
      if (Const.eq («Prelude.length» x4) (leaf 1)).label ≠ 0 then
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
                («Theory.l2» («Theory.list» x8) x9)
                («Prelude.single» («Derivation.roseHyp» x1 x2 («Language.mEq» x6 x7)))
                («Derivation.roseNodeAt» x0 x8 x9 x6)
                («Derivation.roseNodeAt» x0 x8 x9 x7)))
      else
        «Prelude.none»);
    x4

end GebMirror.Metalogic

end
