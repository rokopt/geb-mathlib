module

public import Geb.Prototypes.Kernel.Reader

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

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

def «Base.getD» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x0).label ≠ 0 then
      «Prelude.get» x0
    else
      x1);
    x2

def «Base.mapO» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if («Prelude.isSome» x1).label ≠ 0 then
      «Prelude.some» (x0 («Prelude.get» x1))
    else
      «Prelude.none»);
    x2

def «Base.bindO» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := (if («Prelude.isSome» x0).label ≠ 0 then
      x1 («Prelude.get» x0)
    else
      «Prelude.none»);
    x2

def «Base.not» :=
  fun (x0 : T) => if (x0).label ≠ 0 then leaf 0 else leaf 1

def «Base.isEmpty» :=
  fun (x0 : List T) => Const.eq («Prelude.length» x0) (leaf 0)

def «Base.equalTs» :=
  fun (x0 : List T) (x1 : List T) =>
    Const.equal (Const.node (leaf 0) x0) (Const.node (leaf 0) x1)

def «Base.take» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (let x2 : T := «Prelude.length» x1;
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

def «Base.range» :=
  fun (x0 : T) =>
    let x1 : List
      T := (Const.iter
      (α := T × List T)
      (fun (x1 : T × List T) =>
        (Const.add (x1).1 (leaf 1),
          «Prelude.append» (x1).2 («Prelude.single» (x1).1)))
      (leaf 0, ([] : List T))
      x0).2;
    x1

def «Base.mapT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Base.allT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.and» (x0 x2) x3)
      (leaf 1)
      x1;
    x2

def «Base.anyT» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «Prelude.or» (x0 x2) x3)
      (leaf 0)
      x1;
    x2

def «Base.allSomeT» :=
  fun (x0 : List T) =>
    let x1 : T := (if («Base.allT» «Prelude.isSome» x0).label ≠ 0 then
      «Prelude.some» (Const.node (leaf 0) («Base.mapT» «Prelude.get» x0))
    else
      «Prelude.none»);
    x1

def «PartialHorn.phVar» :=
  fun (x0 : T) =>
    let x1 : T := Const.node
      (leaf 0)
      («Prelude.single» (Const.node x0 ([] : List T)));
    x1

def «PartialHorn.phOp» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.node (Const.add x0 (leaf 1)) x1; x2

def «PartialHorn.ptTrees» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «PartialHorn.ptValues» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0;
    x1

def «PartialHorn.opSig» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «PartialHorn.opArgs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «PartialHorn.opSort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «PartialHorn.sortOf» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := (Const.fold
      (α := T × T)
      (fun (x3 : T) (x4 : List (T × T)) =>
        let x5 : List T := «PartialHorn.ptTrees» x4;
        (Const.node x3 x5,
          if (Const.eq x3 (leaf 0)).label ≠ 0 then
            if (Const.eq («Prelude.length» x5) (leaf 1)).label ≠ 0 then
              let x6 : T := «Prelude.at» x5 (leaf 0);
              if (Const.eq (Const.arity x6) (leaf 0)).label ≠ 0 then
                «Prelude.nth» x1 (Const.label x6)
              else
                «Prelude.none»
            else
              «Prelude.none»
          else
            «Base.bindO»
              («Prelude.nth» x0 (Const.sub x3 (leaf 1)))
              (fun (x6 : T) =>
                if («Base.equalTs»
                  («PartialHorn.ptValues» x4)
                  («Base.mapT» «Prelude.some» («PartialHorn.opArgs» x6))).label ≠ 0 then
                  «Prelude.some» («PartialHorn.opSort» x6)
                else
                  «Prelude.none»)))
      x2).2;
    x3

def «PartialHorn.scoped» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : List T := «PartialHorn.ptTrees» x3;
        (Const.node x2 x4,
          if (Const.eq x2 (leaf 0)).label ≠ 0 then
            if (Const.eq («Prelude.length» x4) (leaf 1)).label ≠ 0 then
              let x5 : T := «Prelude.at» x4 (leaf 0);
              «Prelude.and»
                (Const.eq (Const.arity x5) (leaf 0))
                (Const.lt (Const.label x5) x0)
            else
              leaf 0
          else
            «Base.allT» (fun (x5 : T) => x5) («PartialHorn.ptValues» x3)))
      x1).2;
    x2

def «PartialHorn.phSubst» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : List T := «PartialHorn.ptTrees» x3;
        (Const.node x2 x4,
          if («Prelude.and»
            (Const.eq x2 (leaf 0))
            (Const.eq («Prelude.length» x4) (leaf 1))).label ≠ 0 then
            let x5 : T := «Prelude.at» x4 (leaf 0);
            if (Const.eq (Const.arity x5) (leaf 0)).label ≠ 0 then
              «Base.getD»
                («Prelude.nth» x0 (Const.label x5))
                («PartialHorn.phVar» (Const.label x5))
            else
              Const.node (leaf 0) x4
          else
            Const.node x2 («PartialHorn.ptValues» x3)))
      x1).2;
    x2

def «PartialHorn.eqn» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «PartialHorn.eqLhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «PartialHorn.eqRhs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «PartialHorn.eqSubst» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «PartialHorn.eqn»
      («PartialHorn.phSubst» x0 («PartialHorn.eqLhs» x1))
      («PartialHorn.phSubst» x0 («PartialHorn.eqRhs» x1));
    x2

def «PartialHorn.eqScoped» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («PartialHorn.scoped» x0 («PartialHorn.eqLhs» x1))
      («PartialHorn.scoped» x0 («PartialHorn.eqRhs» x1));
    x2

def «PartialHorn.seq» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «PartialHorn.seqCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x2);
    x1

def «PartialHorn.seqHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x3);
    x1

def «PartialHorn.seqConcl» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «PartialHorn.mkSeq» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «PartialHorn.seq»
      (Const.node (leaf 0) x0)
      (Const.node (leaf 0) x1)
      x2;
    x3

def «PartialHorn.seqScoped» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Prelude.length» («PartialHorn.seqCtx» x0);
                   «Prelude.and»
                     («Base.allT» («PartialHorn.eqScoped» x1) («PartialHorn.seqHyps» x0))
                     («PartialHorn.eqScoped» x1 («PartialHorn.seqConcl» x0)));
    x1

def «PartialHorn.theory» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «PartialHorn.thySig» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1); Const.children x2);
    x1

def «PartialHorn.thyAxioms» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1); Const.children x3);
    x1

def «PartialHorn.pcTrees» :=
  fun (x0 : List (T × (List T → List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (List T → List T → T))
      (β := List T)
      (fun (x1 : T × (List T → List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «PartialHorn.pcResults» :=
  fun (x0 : List (T × (List T → List T → T)))
    (x1 : List T)
    (x2 : List T) =>
    let x3 : List
      T := Const.foldr
      (α := T × (List T → List T → T))
      (β := List T)
      (fun (x3 : T × (List T → List T → T)) (x4 : List T) =>
        (((x3).2 x1 x2) :: x4))
      ([] : List T)
      x0;
    x3

def «PartialHorn/PCs.tail» :=
  fun (x0 : List (T × (List T → List T → T))) =>
    Const.lcase
      (α := T × (List T → List T → T))
      (β := List (T × (List T → List T → T)))
      x0
      ([] : List (T × (List T → List T → T)))
      (fun (_ : T × (List T → List T → T))
         (x2 : List (T × (List T → List T → T))) =>
        x2)

def «PartialHorn.pcPrem» :=
  fun (x0 : List (T × (List T → List T → T))) (x1 : T) =>
    let x2 : List T →
      List T →
        T := Const.lcase
      (α := T × (List T → List T → T))
      (β := List T → List T → T)
      (Const.iter
        (α := List (T × (List T → List T → T)))
        «PartialHorn/PCs.tail»
        x0
        x1)
      (fun (_ : List T) (_ : List T) => «Prelude.none»)
      (fun (x2 : T × (List T → List T → T))
         (_ : List (T × (List T → List T → T))) =>
        (x2).2);
    x2

def «PartialHorn.leafIndex» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq (Const.arity x0) (leaf 0)).label ≠ 0 then
      «Prelude.some» (Const.label x0)
    else
      «Prelude.none»);
    x1

def «PartialHorn.inst» :=
  fun (x0 : List T)
    (x1 : T)
    (x2 : List (T × (List T → List T → T)))
    (x3 : List T)
    (x4 : List T) =>
    let x5 : T := (let x5 : T := «Prelude.length» («PartialHorn.seqCtx» x1);
                   let x6 : List T := «Base.take» x5 («PartialHorn.pcTrees» x2);
                   let x7 : List T := «PartialHorn.pcResults» x2 x3 x4;
                   if («Prelude.and»
                     («PartialHorn.seqScoped» x1)
                     («Prelude.and»
                       («Base.equalTs»
                         («Base.mapT» («PartialHorn.sortOf» x0 x3) x6)
                         («Base.mapT» «Prelude.some» («PartialHorn.seqCtx» x1)))
                       («Prelude.and»
                         («Base.equalTs»
                           («Base.mapT»
                             («Base.mapO» «PartialHorn.eqLhs»)
                             («Base.take» x5 («Prelude.drop» x5 x7)))
                           («Base.mapT» «Prelude.some» x6))
                         («Base.equalTs»
                           («Prelude.drop» (Const.add x5 x5) x7)
                           («Base.mapT»
                             (fun (x8 : T) => «Prelude.some» («PartialHorn.eqSubst» x6 x8))
                             («PartialHorn.seqHyps» x1)))))).label ≠ 0 then
                     «Prelude.some» («PartialHorn.eqSubst» x6 («PartialHorn.seqConcl» x1))
                   else
                     «Prelude.none»);
    x5

def «PartialHorn.pShape» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Prelude.and» (Const.eq x0 x2) (Const.eq x1 x3); x4

def «PartialHorn.pcheckStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List (T × (List T → List T → T)))
    (x5 : List T)
    (x6 : List T) =>
    let x7 : T := (let x7 : T := «Prelude.length» x3;
                   let x8 : T := «Prelude.at» x3 (leaf 0);
                   if («PartialHorn.pShape» x2 x7 (leaf 0) (leaf 1)).label ≠ 0 then
                     «Base.bindO»
                       («PartialHorn.leafIndex» x8)
                       (fun (x9 : T) => «Prelude.nth» x6 x9)
                   else
                     if («PartialHorn.pShape» x2 x7 (leaf 1) (leaf 1)).label ≠ 0 then
                       «Base.bindO»
                         («PartialHorn.leafIndex» x8)
                         (fun (x9 : T) =>
                           if (Const.lt x9 («Prelude.length» x5)).label ≠ 0 then
                             «Prelude.some»
                               («PartialHorn.eqn» («PartialHorn.phVar» x9) («PartialHorn.phVar» x9))
                           else
                             «Prelude.none»)
                     else
                       if («PartialHorn.pShape» x2 x7 (leaf 2) (leaf 1)).label ≠ 0 then
                         «Base.mapO»
                           (fun (x9 : T) =>
                             «PartialHorn.eqn» («PartialHorn.eqRhs» x9) («PartialHorn.eqLhs» x9))
                           («PartialHorn.pcPrem» x4 (leaf 0) x5 x6)
                       else
                         if («PartialHorn.pShape» x2 x7 (leaf 3) (leaf 2)).label ≠ 0 then
                           «Base.bindO»
                             («PartialHorn.pcPrem» x4 (leaf 0) x5 x6)
                             (fun (x9 : T) =>
                               «Base.bindO»
                                 («PartialHorn.pcPrem» x4 (leaf 1) x5 x6)
                                 (fun (x10 : T) =>
                                   if (Const.equal
                                     («PartialHorn.eqRhs» x9)
                                     («PartialHorn.eqLhs» x10)).label ≠ 0 then
                                     «Prelude.some»
                                       («PartialHorn.eqn»
                                         («PartialHorn.eqLhs» x9)
                                         («PartialHorn.eqRhs» x10))
                                   else
                                     «Prelude.none»))
                         else
                           if («Prelude.and»
                             (Const.eq x2 (leaf 4))
                             (Const.lt (leaf 0) x7)).label ≠ 0 then
                             «Base.bindO»
                               («PartialHorn.pcPrem» x4 (leaf 0) x5 x6)
                               (fun (x9 : T) =>
                                 let x10 : List
                                   T := «PartialHorn.pcResults» («PartialHorn/PCs.tail» x4) x5 x6;
                                 if («Prelude.and»
                                   («Base.not»
                                     (Const.eq (Const.label («PartialHorn.eqLhs» x9)) (leaf 0)))
                                   («Base.equalTs»
                                     («Base.mapT» («Base.mapO» «PartialHorn.eqLhs») x10)
                                     («Base.mapT»
                                       «Prelude.some»
                                       (Const.children («PartialHorn.eqLhs» x9))))).label ≠ 0 then
                                   «Base.mapO»
                                     (fun (x11 : T) =>
                                       «PartialHorn.eqn»
                                         («PartialHorn.eqLhs» x9)
                                         (Const.node
                                           (Const.label («PartialHorn.eqLhs» x9))
                                           (Const.children x11)))
                                     («Base.allSomeT»
                                       («Base.mapT» («Base.mapO» «PartialHorn.eqRhs») x10))
                                 else
                                   «Prelude.none»)
                           else
                             if («PartialHorn.pShape» x2 x7 (leaf 5) (leaf 2)).label ≠ 0 then
                               «Base.bindO»
                                 («PartialHorn.leafIndex» x8)
                                 (fun (x9 : T) =>
                                   «Base.bindO»
                                     («PartialHorn.pcPrem» x4 (leaf 1) x5 x6)
                                     (fun (x10 : T) =>
                                       if («Base.not»
                                         (Const.eq
                                           (Const.label («PartialHorn.eqLhs» x10))
                                           (leaf 0))).label ≠ 0 then
                                         «Base.mapO»
                                           (fun (x11 : T) => «PartialHorn.eqn» x11 x11)
                                           («Prelude.nth»
                                             (Const.children («PartialHorn.eqLhs» x10))
                                             x9)
                                       else
                                         «Prelude.none»))
                             else
                               if («Prelude.and»
                                 (Const.eq x2 (leaf 6))
                                 (Const.lt (leaf 0) x7)).label ≠ 0 then
                                 «Base.bindO»
                                   («PartialHorn.leafIndex» x8)
                                   (fun (x9 : T) =>
                                     «Base.bindO»
                                       («Prelude.nth» («PartialHorn.thyAxioms» x0) x9)
                                       (fun (x10 : T) =>
                                         «PartialHorn.inst»
                                           («PartialHorn.thySig» x0)
                                           x10
                                           («PartialHorn/PCs.tail» x4)
                                           x5
                                           x6))
                               else
                                 if («PartialHorn.pShape» x2 x7 (leaf 7) (leaf 2)).label ≠ 0 then
                                   «Base.bindO»
                                     («PartialHorn.pcPrem» x4 (leaf 0) x5 x6)
                                     (fun (x9 : T) =>
                                       «PartialHorn.pcPrem» x4 (leaf 1) x5 (x9 :: x6))
                                 else
                                   if («Prelude.and»
                                     (Const.eq x2 (leaf 8))
                                     (Const.lt (leaf 0) x7)).label ≠ 0 then
                                     «Base.bindO»
                                       («PartialHorn.leafIndex» x8)
                                       (fun (x9 : T) =>
                                         «Base.bindO»
                                           («Prelude.nth» x1 x9)
                                           (fun (x10 : T) =>
                                             «PartialHorn.inst»
                                               («PartialHorn.thySig» x0)
                                               x10
                                               («PartialHorn/PCs.tail» x4)
                                               x5
                                               x6))
                                   else
                                     «Prelude.none»);
    x7

def «PartialHorn.pcheck» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : List T →
      List T →
        T := (Const.fold
      (α := T × (List T → List T → T))
      (fun (x3 : T) (x4 : List (T × (List T → List T → T))) =>
        let x5 : List T := «PartialHorn.pcTrees» x4;
        (Const.node x3 x5,
          fun (x6 : List T) (x7 : List T) =>
            «PartialHorn.pcheckStep» x0 x1 x3 x5 x4 x6 x7))
      x2).2;
    x3

def «PartialHorn.pdefn» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «PartialHorn.pdCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x2);
    x1

def «PartialHorn.pdSort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «PartialHorn.pdBody» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «PartialHorn.opVars» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp»
      x0
      («Base.mapT» «PartialHorn.phVar» («Base.range» x1));
    x2

def «PartialHorn.pdAxioms» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : T := «PartialHorn.opVars»
              x0
              («Prelude.length» («PartialHorn.pdCtx» x1));
            let x3 : T := «PartialHorn.pdBody» x1;
            ((«PartialHorn.mkSeq»
              («PartialHorn.pdCtx» x1)
              («Prelude.single» («PartialHorn.eqn» x3 x3))
              («PartialHorn.eqn» x2 x3)) ::
              («Prelude.single»
                («PartialHorn.mkSeq»
                  («PartialHorn.pdCtx» x1)
                  («Prelude.single» («PartialHorn.eqn» x2 x2))
                  («PartialHorn.eqn» x3 x3)))));
    x2

def «PartialHorn.thyExtend» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «PartialHorn.thySig» x0;
                   «PartialHorn.theory»
                     (Const.node
                       (leaf 0)
                       («Prelude.append»
                         x2
                         («Prelude.single»
                           («PartialHorn.opSig»
                             (Const.node (leaf 0) («PartialHorn.pdCtx» x1))
                             («PartialHorn.pdSort» x1)))))
                     (Const.node
                       (leaf 0)
                       («Prelude.append»
                         («PartialHorn.thyAxioms» x0)
                         («PartialHorn.pdAxioms» («Prelude.length» x2) x1))));
    x2

def «PartialHorn.thyExtendAll» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) => «PartialHorn.thyExtend» x3 x2)
      x0
      («Prelude.reverse» x1);
    x2

def «Theory.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: («Prelude.single» x1)); x2

def «Theory.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Theory.l2» x1 x2)); x3

def «Theory.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Theory.l3» x1 x2 x3)); x4

def «Theory.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Theory.l4» x1 x2 x3 x4)); x5

def «Theory.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Theory.l5» x1 x2 x3 x4 x5)); x6

def «Theory.os» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «PartialHorn.opSig» (Const.node (leaf 0) x0) x1; x2

def «Theory.sig» :=
  «Prelude.append»
    («Theory.l4»
      («Theory.os» («Prelude.single» (leaf 1)) (leaf 0))
      («Theory.os» («Prelude.single» (leaf 1)) (leaf 0))
      («Theory.os» («Prelude.single» (leaf 0)) (leaf 1))
      («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 1)))
    («Prelude.append»
      («Theory.l2»
        («Theory.os» ([] : List T) (leaf 0))
        («Theory.os» («Prelude.single» (leaf 0)) (leaf 1)))
      («Prelude.append»
        («Theory.l4»
          («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 0))
          («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 1))
          («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 1))
          («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 1)))
        («Prelude.append»
          («Theory.l3»
            («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 0))
            («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 1))
            («Theory.os» («Theory.l3» (leaf 1) (leaf 1) (leaf 1)) (leaf 1)))
          («Prelude.append»
            («Theory.l2»
              («Theory.os» ([] : List T) (leaf 0))
              («Theory.os» («Prelude.single» (leaf 0)) (leaf 1)))
            («Prelude.append»
              («Theory.l4»
                («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 0))
                («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 1))
                («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 1))
                («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 1)))
              («Prelude.append»
                («Theory.l3»
                  («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 0))
                  («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 1))
                  («Theory.os» («Theory.l3» (leaf 1) (leaf 1) (leaf 1)) (leaf 1)))
                («Prelude.append»
                  («Theory.l3»
                    («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 0))
                    («Theory.os» («Theory.l2» (leaf 0) (leaf 0)) (leaf 1))
                    («Theory.os» («Theory.l3» (leaf 0) (leaf 0) (leaf 1)) (leaf 1)))
                  («Prelude.append»
                    («Theory.l4»
                      («Theory.os» ([] : List T) (leaf 0))
                      («Theory.os» ([] : List T) (leaf 1))
                      («Theory.os» («Prelude.single» (leaf 1)) (leaf 1))
                      («Theory.os» («Prelude.single» (leaf 1)) (leaf 1)))
                    («Prelude.append»
                      («Theory.l4»
                        («Theory.os» ([] : List T) (leaf 0))
                        («Theory.os» ([] : List T) (leaf 1))
                        («Theory.os» ([] : List T) (leaf 1))
                        («Theory.os» («Theory.l2» (leaf 1) (leaf 1)) (leaf 1)))
                      («Prelude.append»
                        («Theory.l4»
                          («Theory.os» («Prelude.single» (leaf 0)) (leaf 0))
                          («Theory.os» («Prelude.single» (leaf 0)) (leaf 1))
                          («Theory.os» («Prelude.single» (leaf 0)) (leaf 1))
                          («Theory.os» («Theory.l3» (leaf 0) (leaf 1) (leaf 1)) (leaf 1)))
                        («Prelude.append»
                          («Theory.l3»
                            («Theory.os» ([] : List T) (leaf 0))
                            («Theory.os» ([] : List T) (leaf 1))
                            («Theory.os» («Prelude.single» (leaf 1)) (leaf 1)))
                          («Theory.l3»
                            («Theory.os» («Prelude.single» (leaf 0)) (leaf 0))
                            («Theory.os» («Prelude.single» (leaf 0)) (leaf 1))
                            («Theory.os» («Theory.l2» (leaf 0) (leaf 1)) (leaf 1))))))))))))))

def «Theory.x» :=
  fun (x0 : T) => let x1 : T := «PartialHorn.phVar» x0; x1

def «Theory.dom» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 0) («Prelude.single» x0); x1

def «Theory.cod» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 1) («Prelude.single» x0); x1

def «Theory.idt» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 2) («Prelude.single» x0); x1

def «Theory.comp» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 3) («Theory.l2» x0 x1); x2

def «Theory.one» := «PartialHorn.phOp» (leaf 4) ([] : List T)

def «Theory.bang» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 5) («Prelude.single» x0); x1

def «Theory.prod» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 6) («Theory.l2» x0 x1); x2

def «Theory.cFst» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 7) («Theory.l2» x0 x1); x2

def «Theory.cSnd» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 8) («Theory.l2» x0 x1); x2

def «Theory.cPair» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 9) («Theory.l2» x0 x1); x2

def «Theory.eqz» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 10) («Theory.l2» x0 x1); x2

def «Theory.eqIncl» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 11) («Theory.l2» x0 x1); x2

def «Theory.eqLift» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «PartialHorn.phOp» (leaf 12) («Theory.l3» x0 x1 x2); x3

def «Theory.cZero» := «PartialHorn.phOp» (leaf 13) ([] : List T)

def «Theory.absurd» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 14) («Prelude.single» x0); x1

def «Theory.coprod» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 15) («Theory.l2» x0 x1); x2

def «Theory.inl» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 16) («Theory.l2» x0 x1); x2

def «Theory.inr» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 17) («Theory.l2» x0 x1); x2

def «Theory.copair» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 18) («Theory.l2» x0 x1); x2

def «Theory.coeqz» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 19) («Theory.l2» x0 x1); x2

def «Theory.coeqProj» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 20) («Theory.l2» x0 x1); x2

def «Theory.coeqDesc» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «PartialHorn.phOp» (leaf 21) («Theory.l3» x0 x1 x2); x3

def «Theory.exp» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 22) («Theory.l2» x0 x1); x2

def «Theory.ev» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 23) («Theory.l2» x0 x1); x2

def «Theory.curry» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «PartialHorn.phOp» (leaf 24) («Theory.l3» x0 x1 x2); x3

def «Theory.omega» := «PartialHorn.phOp» (leaf 25) ([] : List T)

def «Theory.tru» := «PartialHorn.phOp» (leaf 26) ([] : List T)

def «Theory.chi» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 27) («Prelude.single» x0); x1

def «Theory.chiInv» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 28) («Prelude.single» x0); x1

def «Theory.nat» := «PartialHorn.phOp» (leaf 29) ([] : List T)

def «Theory.zeroN» := «PartialHorn.phOp» (leaf 30) ([] : List T)

def «Theory.succ» := «PartialHorn.phOp» (leaf 31) ([] : List T)

def «Theory.natRec» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 32) («Theory.l2» x0 x1); x2

def «Theory.list» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 33) («Prelude.single» x0); x1

def «Theory.cNil» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 34) («Prelude.single» x0); x1

def «Theory.cCons» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 35) («Prelude.single» x0); x1

def «Theory.listRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «PartialHorn.phOp» (leaf 36) («Theory.l3» x0 x1 x2); x3

def «Theory.rose» := «PartialHorn.phOp» (leaf 37) ([] : List T)

def «Theory.cNode» := «PartialHorn.phOp» (leaf 38) ([] : List T)

def «Theory.roseRec» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 39) («Prelude.single» x0); x1

def «Theory.lrose» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 40) («Prelude.single» x0); x1

def «Theory.lnode» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.phOp» (leaf 41) («Prelude.single» x0); x1

def «Theory.lroseRec» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «PartialHorn.phOp» (leaf 42) («Theory.l2» x0 x1); x2

def «Theory.dfd» :=
  fun (x0 : T) => let x1 : T := «PartialHorn.eqn» x0 x0; x1

def «Theory.prodMapLeft» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Theory.cPair»
      («Theory.comp» x0 («Theory.cFst» («Theory.dom» x0) x1))
      («Theory.cSnd» («Theory.dom» x0) x1);
    x2

def «Theory.prodMapRight» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Theory.cPair»
      («Theory.cFst» x0 («Theory.dom» x1))
      («Theory.comp» x1 («Theory.cSnd» x0 («Theory.dom» x1)));
    x2

def «Theory.listMap» :=
  fun (x0 : T) =>
    let x1 : T := «Theory.listRec»
      («Theory.dom» x0)
      («Theory.cNil» («Theory.cod» x0))
      («Theory.comp»
        («Theory.cCons» («Theory.cod» x0))
        («Theory.prodMapLeft» x0 («Theory.list» («Theory.cod» x0))));
    x1

def «Theory.diag» :=
  fun (x0 : T) =>
    let x1 : T := «Theory.cPair» («Theory.idt» x0) («Theory.idt» x0); x1

def «Theory.monoCond» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Theory.dom» x0;
                   let x2 : T := «Theory.eqIncl»
                     («Theory.comp» x0 («Theory.cFst» x1 x1))
                     («Theory.comp» x0 («Theory.cSnd» x1 x1));
                   «PartialHorn.eqn»
                     («Theory.comp» («Theory.cFst» x1 x1) x2)
                     («Theory.comp» («Theory.cSnd» x1 x1) x2));
    x1

def «Theory.truthEq» :=
  fun (x0 : T) =>
    let x1 : T := «Theory.eqz»
      x0
      («Theory.comp» «Theory.tru» («Theory.bang» («Theory.dom» x0)));
    x1

def «Theory.truthIncl» :=
  fun (x0 : T) =>
    let x1 : T := «Theory.eqIncl»
      x0
      («Theory.comp» «Theory.tru» («Theory.bang» («Theory.dom» x0)));
    x1

def «Theory.truthLift» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Theory.eqLift»
      x0
      («Theory.comp» «Theory.tru» («Theory.bang» («Theory.dom» x0)))
      x1;
    x2

def «Theory.sq» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «PartialHorn.mkSeq» x0 x1 x2; x3

def «Theory.ctxOO» := «Theory.l2» (leaf 0) (leaf 0)

def «Theory.ctxAA» := «Theory.l2» (leaf 1) (leaf 1)

def «Theory.ctxAAA» := «Theory.l3» (leaf 1) (leaf 1) (leaf 1)

def «Theory.ctxA» := «Prelude.single» (leaf 1)

def «Theory.ctxO» := «Prelude.single» (leaf 0)

def «Theory.categoryAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxA»
        ([] : List T)
        («Theory.dfd» («Theory.dom» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxA»
        ([] : List T)
        («Theory.dfd» («Theory.cod» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («Theory.dfd» («Theory.idt» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod» («Theory.x» (leaf 1)))
          («Theory.dom» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 1)))
            («Theory.dom» («Theory.x» (leaf 0)))))
        («Theory.dfd»
          («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.dom» («Theory.x» (leaf 1))))))
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.cod» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxAAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.comp»
              («Theory.x» (leaf 0))
              («Theory.comp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2))))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.x» (leaf 0))
            («Theory.comp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2))))
          («Theory.comp»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
            («Theory.x» (leaf 2)))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom» («Theory.idt» («Theory.x» (leaf 0))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod» («Theory.idt» («Theory.x» (leaf 0))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxA»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.x» (leaf 0))
            («Theory.idt» («Theory.dom» («Theory.x» (leaf 0)))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxA»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.idt» («Theory.cod» («Theory.x» (leaf 0))))
            («Theory.x» (leaf 0)))
          («Theory.x» (leaf 0)))))

def «Theory.terminalAxioms» :=
  «Theory.l4»
    («Theory.sq» ([] : List T) ([] : List T) («Theory.dfd» «Theory.one»))
    («Theory.sq»
      «Theory.ctxO»
      ([] : List T)
      («PartialHorn.eqn»
        («Theory.dom» («Theory.bang» («Theory.x» (leaf 0))))
        («Theory.x» (leaf 0))))
    («Theory.sq»
      «Theory.ctxO»
      ([] : List T)
      («PartialHorn.eqn»
        («Theory.cod» («Theory.bang» («Theory.x» (leaf 0))))
        «Theory.one»))
    («Theory.sq»
      «Theory.ctxA»
      («Prelude.single»
        («PartialHorn.eqn» («Theory.cod» («Theory.x» (leaf 0))) «Theory.one»))
      («PartialHorn.eqn»
        («Theory.x» (leaf 0))
        («Theory.bang» («Theory.dom» («Theory.x» (leaf 0))))))

def «Theory.productAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («Theory.dfd»
          («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.cFst» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.cFst» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.cSnd» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.cSnd» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 1))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 0)))
          («Theory.dom» («Theory.x» (leaf 1))))))
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 0)))
            («Theory.dom» («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.dom» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.prod»
            («Theory.cod» («Theory.x» (leaf 0)))
            («Theory.cod» («Theory.x» (leaf 1))))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.cFst»
              («Theory.cod» («Theory.x» (leaf 0)))
              («Theory.cod» («Theory.x» (leaf 1))))
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.cSnd»
              («Theory.cod» («Theory.x» (leaf 0)))
              («Theory.cod» («Theory.x» (leaf 1))))
            («Theory.cPair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 1))))
      («Theory.sq»
        («Theory.l3» (leaf 1) (leaf 0) (leaf 0))
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 0)))
            («Theory.prod» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.cPair»
            («Theory.comp»
              («Theory.cFst» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))
              («Theory.x» (leaf 0)))
            («Theory.comp»
              («Theory.cSnd» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))
              («Theory.x» (leaf 0))))
          («Theory.x» (leaf 0)))))

def «Theory.equalizerAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 0)))
          («Theory.dom» («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod» («Theory.x» (leaf 0)))
          («Theory.cod» («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Theory.l2»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 0)))
            («Theory.dom» («Theory.x» (leaf 1))))
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 0)))
            («Theory.cod» («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))))
    («Prelude.append»
      («Theory.l6»
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.cod»
              («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («Theory.dom» («Theory.x» (leaf 0)))))
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.x» (leaf 0))
              («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («Theory.comp»
              («Theory.x» (leaf 1))
              («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («Theory.dfd»
            («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 2)))
            («Theory.comp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Theory.l2»
            («Theory.dfd»
              («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («PartialHorn.eqn»
              («Theory.comp» («Theory.x» (leaf 0)) («Theory.x» (leaf 2)))
              («Theory.comp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
          («Theory.dfd»
            («Theory.eqLift»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.dom»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.dom» («Theory.x» (leaf 2))))))
      («Theory.l3»
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.cod»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
              («Theory.eqLift»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.x» (leaf 2))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Theory.l2»
            («Theory.dfd»
              («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («PartialHorn.eqn»
              («Theory.cod» («Theory.x» (leaf 2)))
              («Theory.eqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.eqLift»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.comp»
                («Theory.eqIncl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
                («Theory.x» (leaf 2))))
            («Theory.x» (leaf 2))))))

def «Theory.initialAxioms» :=
  «Theory.l4»
    («Theory.sq»
      ([] : List T)
      ([] : List T)
      («Theory.dfd» «Theory.cZero»))
    («Theory.sq»
      «Theory.ctxO»
      ([] : List T)
      («PartialHorn.eqn»
        («Theory.dom» («Theory.absurd» («Theory.x» (leaf 0))))
        «Theory.cZero»))
    («Theory.sq»
      «Theory.ctxO»
      ([] : List T)
      («PartialHorn.eqn»
        («Theory.cod» («Theory.absurd» («Theory.x» (leaf 0))))
        («Theory.x» (leaf 0))))
    («Theory.sq»
      «Theory.ctxA»
      («Prelude.single»
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 0)))
          «Theory.cZero»))
      («PartialHorn.eqn»
        («Theory.x» (leaf 0))
        («Theory.absurd» («Theory.cod» («Theory.x» (leaf 0))))))

def «Theory.coproductAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («Theory.dfd»
          («Theory.coprod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.inl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.inl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.coprod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.inr» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 1))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.inr» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.coprod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod» («Theory.x» (leaf 0)))
          («Theory.cod» («Theory.x» (leaf 1))))))
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 0)))
            («Theory.cod» («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.coprod»
            («Theory.dom» («Theory.x» (leaf 0)))
            («Theory.dom» («Theory.x» (leaf 1))))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.cod» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
            («Theory.inl»
              («Theory.dom» («Theory.x» (leaf 0)))
              («Theory.dom» («Theory.x» (leaf 1)))))
          («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.copair» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
            («Theory.inr»
              («Theory.dom» («Theory.x» (leaf 0)))
              («Theory.dom» («Theory.x» (leaf 1)))))
          («Theory.x» (leaf 1))))
      («Theory.sq»
        («Theory.l3» (leaf 1) (leaf 0) (leaf 0))
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 0)))
            («Theory.coprod» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.copair»
            («Theory.comp»
              («Theory.x» (leaf 0))
              («Theory.inl» («Theory.x» (leaf 1)) («Theory.x» (leaf 2))))
            («Theory.comp»
              («Theory.x» (leaf 0))
              («Theory.inr» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
          («Theory.x» (leaf 0)))))

def «Theory.coequalizerAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 0)))
          («Theory.dom» («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod» («Theory.x» (leaf 0)))
          («Theory.cod» («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Theory.l2»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 0)))
            («Theory.dom» («Theory.x» (leaf 1))))
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 0)))
            («Theory.cod» («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.cod» («Theory.x» (leaf 0))))))
    («Prelude.append»
      («Theory.l6»
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.cod»
              («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
              («Theory.x» (leaf 0)))
            («Theory.comp»
              («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
              («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («Theory.dfd»
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.comp» («Theory.x» (leaf 2)) («Theory.x» (leaf 0)))
            («Theory.comp» («Theory.x» (leaf 2)) («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Theory.l2»
            («Theory.dfd»
              («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («PartialHorn.eqn»
              («Theory.comp» («Theory.x» (leaf 2)) («Theory.x» (leaf 0)))
              («Theory.comp» («Theory.x» (leaf 2)) («Theory.x» (leaf 1)))))
          («Theory.dfd»
            («Theory.coeqDesc»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.dom»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))))
      («Theory.l3»
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.cod»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.cod» («Theory.x» (leaf 2)))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.coeqDesc»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))
              («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («Theory.x» (leaf 2))))
        («Theory.sq»
          «Theory.ctxAAA»
          («Theory.l2»
            («Theory.dfd»
              («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («PartialHorn.eqn»
              («Theory.dom» («Theory.x» (leaf 2)))
              («Theory.coeqz» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.coeqDesc»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.comp»
                («Theory.x» (leaf 2))
                («Theory.coeqProj» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
            («Theory.x» (leaf 2))))))

def «Theory.ctxOOA» := «Theory.l3» (leaf 0) (leaf 0) (leaf 1)

def «Theory.exponentialAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («Theory.dfd»
          («Theory.exp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.ev» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.prod»
            («Theory.exp» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
            («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxOO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.ev» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.x» (leaf 1))))
      («Theory.sq»
        «Theory.ctxOOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 2)))
          («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOOA»
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 2)))
            («Theory.prod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.dfd»
          («Theory.curry»
            («Theory.x» (leaf 0))
            («Theory.x» (leaf 1))
            («Theory.x» (leaf 2)))))
      («Theory.sq»
        «Theory.ctxOOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2))))
          («Theory.x» (leaf 0)))))
    («Theory.l3»
      («Theory.sq»
        «Theory.ctxOOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2))))
          («Theory.exp»
            («Theory.x» (leaf 1))
            («Theory.cod» («Theory.x» (leaf 2))))))
      («Theory.sq»
        «Theory.ctxOOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.curry»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.ev»
              («Theory.x» (leaf 1))
              («Theory.cod» («Theory.x» (leaf 2))))
            («Theory.prodMapLeft»
              («Theory.curry»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))
              («Theory.x» (leaf 1))))
          («Theory.x» (leaf 2))))
      («Theory.sq»
        («Theory.l4» (leaf 0) (leaf 0) (leaf 0) (leaf 1))
        («Theory.l2»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 3)))
            («Theory.x» (leaf 0)))
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 3)))
            («Theory.exp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.curry»
            («Theory.x» (leaf 0))
            («Theory.x» (leaf 1))
            («Theory.comp»
              («Theory.ev» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))
              («Theory.prodMapLeft» («Theory.x» (leaf 3)) («Theory.x» (leaf 1)))))
          («Theory.x» (leaf 3)))))

def «Theory.classifierAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («Theory.dfd» «Theory.omega»))
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.dom» «Theory.tru») «Theory.one»))
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.cod» «Theory.tru») «Theory.omega»))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
        («Theory.monoCond» («Theory.x» (leaf 0))))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single» («Theory.monoCond» («Theory.x» (leaf 0))))
        («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.chi» («Theory.x» (leaf 0))))
          («Theory.cod» («Theory.x» (leaf 0))))))
    («Prelude.append»
      («Theory.l6»
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («PartialHorn.eqn»
            («Theory.cod» («Theory.chi» («Theory.x» (leaf 0))))
            «Theory.omega»))
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.chi» («Theory.x» (leaf 0)))
              («Theory.x» (leaf 0)))
            («Theory.comp»
              «Theory.tru»
              («Theory.bang» («Theory.dom» («Theory.x» (leaf 0)))))))
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single»
            («Theory.dfd» («Theory.chiInv» («Theory.x» (leaf 0)))))
          («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («Theory.dfd» («Theory.chiInv» («Theory.x» (leaf 0)))))
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («PartialHorn.eqn»
            («Theory.dom» («Theory.chiInv» («Theory.x» (leaf 0))))
            («Theory.truthEq» («Theory.chi» («Theory.x» (leaf 0))))))
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («PartialHorn.eqn»
            («Theory.cod» («Theory.chiInv» («Theory.x» (leaf 0))))
            («Theory.dom» («Theory.x» (leaf 0))))))
      («Theory.l3»
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.truthLift»
                («Theory.chi» («Theory.x» (leaf 0)))
                («Theory.x» (leaf 0)))
              («Theory.chiInv» («Theory.x» (leaf 0))))
            («Theory.idt»
              («Theory.truthEq» («Theory.chi» («Theory.x» (leaf 0)))))))
        («Theory.sq»
          «Theory.ctxA»
          («Prelude.single» («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.chiInv» («Theory.x» (leaf 0)))
              («Theory.truthLift»
                («Theory.chi» («Theory.x» (leaf 0)))
                («Theory.x» (leaf 0))))
            («Theory.idt» («Theory.dom» («Theory.x» (leaf 0))))))
        («Theory.sq»
          («Theory.l4» (leaf 1) (leaf 1) (leaf 1) (leaf 1))
          («Theory.l6»
            («Theory.dfd» («Theory.chi» («Theory.x» (leaf 0))))
            («PartialHorn.eqn»
              («Theory.dom» («Theory.x» (leaf 1)))
              («Theory.cod» («Theory.x» (leaf 0))))
            («PartialHorn.eqn»
              («Theory.cod» («Theory.x» (leaf 1)))
              «Theory.omega»)
            («PartialHorn.eqn»
              («Theory.comp»
                («Theory.truthIncl» («Theory.x» (leaf 1)))
                («Theory.x» (leaf 2)))
              («Theory.x» (leaf 0)))
            («PartialHorn.eqn»
              («Theory.comp» («Theory.x» (leaf 2)) («Theory.x» (leaf 3)))
              («Theory.idt» («Theory.truthEq» («Theory.x» (leaf 1)))))
            («PartialHorn.eqn»
              («Theory.comp» («Theory.x» (leaf 3)) («Theory.x» (leaf 2)))
              («Theory.idt» («Theory.dom» («Theory.x» (leaf 0))))))
          («PartialHorn.eqn»
            («Theory.x» (leaf 1))
            («Theory.chi» («Theory.x» (leaf 0)))))))

def «Theory.natAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.dom» «Theory.zeroN») «Theory.one»))
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.cod» «Theory.zeroN») «Theory.nat»))
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.dom» «Theory.succ») «Theory.nat»))
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.cod» «Theory.succ») «Theory.nat»))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn» («Theory.dom» («Theory.x» (leaf 0))) «Theory.one»))
      («Theory.sq»
        «Theory.ctxAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod» («Theory.x» (leaf 0)))
          («Theory.dom» («Theory.x» (leaf 1))))))
    («Prelude.append»
      («Theory.l6»
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 1)))
            («Theory.cod» («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAA»
          («Theory.l3»
            («PartialHorn.eqn» («Theory.dom» («Theory.x» (leaf 0))) «Theory.one»)
            («PartialHorn.eqn»
              («Theory.cod» («Theory.x» (leaf 0)))
              («Theory.dom» («Theory.x» (leaf 1))))
            («PartialHorn.eqn»
              («Theory.dom» («Theory.x» (leaf 1)))
              («Theory.cod» («Theory.x» (leaf 1)))))
          («Theory.dfd»
            («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.dom»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            «Theory.nat»))
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.cod»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («Theory.cod» («Theory.x» (leaf 0)))))
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
              «Theory.zeroN»)
            («Theory.x» (leaf 0))))
        («Theory.sq»
          «Theory.ctxAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
              «Theory.succ»)
            («Theory.comp»
              («Theory.x» (leaf 1))
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))))
      («Prelude.single»
        («Theory.sq»
          «Theory.ctxAAA»
          («Theory.l4»
            («Theory.dfd»
              («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
            («PartialHorn.eqn» («Theory.dom» («Theory.x» (leaf 2))) «Theory.nat»)
            («PartialHorn.eqn»
              («Theory.comp» («Theory.x» (leaf 2)) «Theory.zeroN»)
              («Theory.x» (leaf 0)))
            («PartialHorn.eqn»
              («Theory.comp» («Theory.x» (leaf 2)) «Theory.succ»)
              («Theory.comp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.x» (leaf 2))
            («Theory.natRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))))

def «Theory.ctxOAA» := «Theory.l3» (leaf 0) (leaf 1) (leaf 1)

def «Theory.listAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («Theory.dfd» («Theory.list» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom» («Theory.cNil» («Theory.x» (leaf 0))))
          «Theory.one»))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod» («Theory.cNil» («Theory.x» (leaf 0))))
          («Theory.list» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom» («Theory.cCons» («Theory.x» (leaf 0))))
          («Theory.prod»
            («Theory.x» (leaf 0))
            («Theory.list» («Theory.x» (leaf 0))))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod» («Theory.cCons» («Theory.x» (leaf 0))))
          («Theory.list» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxOAA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.listRec»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 1)))
          «Theory.one»)))
    («Prelude.append»
      («Theory.l6»
        («Theory.sq»
          «Theory.ctxOAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.cod» («Theory.x» (leaf 1)))
            («Theory.cod» («Theory.x» (leaf 2)))))
        («Theory.sq»
          «Theory.ctxOAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 2)))
            («Theory.prod»
              («Theory.x» (leaf 0))
              («Theory.cod» («Theory.x» (leaf 2))))))
        («Theory.sq»
          «Theory.ctxOAA»
          («Theory.l3»
            («PartialHorn.eqn» («Theory.dom» («Theory.x» (leaf 1))) «Theory.one»)
            («PartialHorn.eqn»
              («Theory.cod» («Theory.x» (leaf 1)))
              («Theory.cod» («Theory.x» (leaf 2))))
            («PartialHorn.eqn»
              («Theory.dom» («Theory.x» (leaf 2)))
              («Theory.prod»
                («Theory.x» (leaf 0))
                («Theory.cod» («Theory.x» (leaf 2))))))
          («Theory.dfd»
            («Theory.listRec»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))
        («Theory.sq»
          «Theory.ctxOAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.dom»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.list» («Theory.x» (leaf 0)))))
        («Theory.sq»
          «Theory.ctxOAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.cod»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («Theory.cod» («Theory.x» (leaf 1)))))
        («Theory.sq»
          «Theory.ctxOAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))
              («Theory.cNil» («Theory.x» (leaf 0))))
            («Theory.x» (leaf 1)))))
      («Theory.l2»
        («Theory.sq»
          «Theory.ctxOAA»
          («Prelude.single»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2)))
              («Theory.cCons» («Theory.x» (leaf 0))))
            («Theory.comp»
              («Theory.x» (leaf 2))
              («Theory.prodMapRight»
                («Theory.x» (leaf 0))
                («Theory.listRec»
                  («Theory.x» (leaf 0))
                  («Theory.x» (leaf 1))
                  («Theory.x» (leaf 2)))))))
        («Theory.sq»
          («Theory.l4» (leaf 0) (leaf 1) (leaf 1) (leaf 1))
          («Theory.l4»
            («Theory.dfd»
              («Theory.listRec»
                («Theory.x» (leaf 0))
                («Theory.x» (leaf 1))
                («Theory.x» (leaf 2))))
            («PartialHorn.eqn»
              («Theory.dom» («Theory.x» (leaf 3)))
              («Theory.list» («Theory.x» (leaf 0))))
            («PartialHorn.eqn»
              («Theory.comp»
                («Theory.x» (leaf 3))
                («Theory.cNil» («Theory.x» (leaf 0))))
              («Theory.x» (leaf 1)))
            («PartialHorn.eqn»
              («Theory.comp»
                («Theory.x» (leaf 3))
                («Theory.cCons» («Theory.x» (leaf 0))))
              («Theory.comp»
                («Theory.x» (leaf 2))
                («Theory.prodMapRight» («Theory.x» (leaf 0)) («Theory.x» (leaf 3))))))
          («PartialHorn.eqn»
            («Theory.x» (leaf 3))
            («Theory.listRec»
              («Theory.x» (leaf 0))
              («Theory.x» (leaf 1))
              («Theory.x» (leaf 2)))))))

def «Theory.roseAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom» «Theory.cNode»)
          («Theory.prod» «Theory.nat» («Theory.list» «Theory.rose»))))
      («Theory.sq»
        ([] : List T)
        ([] : List T)
        («PartialHorn.eqn» («Theory.cod» «Theory.cNode») «Theory.rose»))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single»
          («Theory.dfd» («Theory.roseRec» («Theory.x» (leaf 0)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 0)))
          («Theory.prod»
            «Theory.nat»
            («Theory.list» («Theory.cod» («Theory.x» (leaf 0)))))))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 0)))
            («Theory.prod»
              «Theory.nat»
              («Theory.list» («Theory.cod» («Theory.x» (leaf 0)))))))
        («Theory.dfd» («Theory.roseRec» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single»
          («Theory.dfd» («Theory.roseRec» («Theory.x» (leaf 0)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.roseRec» («Theory.x» (leaf 0))))
          «Theory.rose»))
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single»
          («Theory.dfd» («Theory.roseRec» («Theory.x» (leaf 0)))))
        («PartialHorn.eqn»
          («Theory.cod» («Theory.roseRec» («Theory.x» (leaf 0))))
          («Theory.cod» («Theory.x» (leaf 0))))))
    («Theory.l2»
      («Theory.sq»
        «Theory.ctxA»
        («Prelude.single»
          («Theory.dfd» («Theory.roseRec» («Theory.x» (leaf 0)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.roseRec» («Theory.x» (leaf 0)))
            «Theory.cNode»)
          («Theory.comp»
            («Theory.x» (leaf 0))
            («Theory.prodMapRight»
              «Theory.nat»
              («Theory.listMap» («Theory.roseRec» («Theory.x» (leaf 0))))))))
      («Theory.sq»
        «Theory.ctxAA»
        («Theory.l3»
          («Theory.dfd» («Theory.roseRec» («Theory.x» (leaf 0))))
          («PartialHorn.eqn» («Theory.dom» («Theory.x» (leaf 1))) «Theory.rose»)
          («PartialHorn.eqn»
            («Theory.comp» («Theory.x» (leaf 1)) «Theory.cNode»)
            («Theory.comp»
              («Theory.x» (leaf 0))
              («Theory.prodMapRight»
                «Theory.nat»
                («Theory.listMap» («Theory.x» (leaf 1)))))))
        («PartialHorn.eqn»
          («Theory.x» (leaf 1))
          («Theory.roseRec» («Theory.x» (leaf 0))))))

def «Theory.ctxOA» := «Theory.l2» (leaf 0) (leaf 1)

def «Theory.lroseAxioms» :=
  «Prelude.append»
    («Theory.l6»
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («Theory.dfd» («Theory.lrose» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.dom» («Theory.lnode» («Theory.x» (leaf 0))))
          («Theory.prod»
            («Theory.x» (leaf 0))
            («Theory.list» («Theory.lrose» («Theory.x» (leaf 0)))))))
      («Theory.sq»
        «Theory.ctxO»
        ([] : List T)
        («PartialHorn.eqn»
          («Theory.cod» («Theory.lnode» («Theory.x» (leaf 0))))
          («Theory.lrose» («Theory.x» (leaf 0)))))
      («Theory.sq»
        «Theory.ctxOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom» («Theory.x» (leaf 1)))
          («Theory.prod»
            («Theory.x» (leaf 0))
            («Theory.list» («Theory.cod» («Theory.x» (leaf 1)))))))
      («Theory.sq»
        «Theory.ctxOA»
        («Prelude.single»
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 1)))
            («Theory.prod»
              («Theory.x» (leaf 0))
              («Theory.list» («Theory.cod» («Theory.x» (leaf 1)))))))
        («Theory.dfd»
          («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.dom»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.lrose» («Theory.x» (leaf 0))))))
    («Theory.l3»
      («Theory.sq»
        «Theory.ctxOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.cod»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («Theory.cod» («Theory.x» (leaf 1)))))
      («Theory.sq»
        «Theory.ctxOA»
        («Prelude.single»
          («Theory.dfd»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))))
        («PartialHorn.eqn»
          («Theory.comp»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
            («Theory.lnode» («Theory.x» (leaf 0))))
          («Theory.comp»
            («Theory.x» (leaf 1))
            («Theory.prodMapRight»
              («Theory.x» (leaf 0))
              («Theory.listMap»
                («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))))))
      («Theory.sq»
        «Theory.ctxOAA»
        («Theory.l3»
          («Theory.dfd»
            («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))
          («PartialHorn.eqn»
            («Theory.dom» («Theory.x» (leaf 2)))
            («Theory.lrose» («Theory.x» (leaf 0))))
          («PartialHorn.eqn»
            («Theory.comp»
              («Theory.x» (leaf 2))
              («Theory.lnode» («Theory.x» (leaf 0))))
            («Theory.comp»
              («Theory.x» (leaf 1))
              («Theory.prodMapRight»
                («Theory.x» (leaf 0))
                («Theory.listMap» («Theory.x» (leaf 2)))))))
        («PartialHorn.eqn»
          («Theory.x» (leaf 2))
          («Theory.lroseRec» («Theory.x» (leaf 0)) («Theory.x» (leaf 1))))))

def «Theory.axioms» :=
  «Prelude.append»
    «Theory.categoryAxioms»
    («Prelude.append»
      «Theory.terminalAxioms»
      («Prelude.append»
        «Theory.productAxioms»
        («Prelude.append»
          «Theory.equalizerAxioms»
          («Prelude.append»
            «Theory.initialAxioms»
            («Prelude.append»
              «Theory.coproductAxioms»
              («Prelude.append»
                «Theory.coequalizerAxioms»
                («Prelude.append»
                  «Theory.exponentialAxioms»
                  («Prelude.append»
                    «Theory.classifierAxioms»
                    («Prelude.append»
                      «Theory.natAxioms»
                      («Prelude.append»
                        «Theory.listAxioms»
                        («Prelude.append» «Theory.roseAxioms» «Theory.lroseAxioms»)))))))))))

def «Theory.toposTheory» :=
  «PartialHorn.theory»
    (Const.node (leaf 0) «Theory.sig»)
    (Const.node (leaf 0) «Theory.axioms»)

def «Infer.direct» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Infer.strict» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Infer.rhsRule» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «Infer.argSorts» :=
  fun (x0 : T) =>
    let x1 : List
      T := Const.children
      («Base.getD»
        («Base.mapO»
          (fun (x1 : T) => Const.node (leaf 0) («PartialHorn.opArgs» x1))
          («Prelude.nth» «Theory.sig» x0))
        (Const.node (leaf 0) ([] : List T)));
    x1

def «Infer.findAxiom» :=
  fun (x0 : T → T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x1 : T) (x2 : T × T) =>
        (Const.sub (x2).1 (leaf 1),
          if (x0 x1).label ≠ 0 then
            «Prelude.some» (Const.sub (x2).1 (leaf 1))
          else
            (x2).2))
      («Prelude.length» «Theory.axioms», «Prelude.none»)
      «Theory.axioms»).2;
    x1

def «Infer.dfdRule» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : List T := «Infer.argSorts» x0;
                   let x2 : T := «PartialHorn.opVars» x0 («Prelude.length» x1);
                   let x3 : T := «Infer.findAxiom»
                     (fun (x3 : T) =>
                       «Prelude.and»
                         («Base.equalTs» («PartialHorn.seqCtx» x3) x1)
                         («Prelude.and»
                           (Const.equal («PartialHorn.eqLhs» («PartialHorn.seqConcl» x3)) x2)
                           (Const.equal («PartialHorn.eqRhs» («PartialHorn.seqConcl» x3)) x2)));
                   if («Prelude.isSome» x3).label ≠ 0 then
                     «Prelude.some» («Infer.direct» («Prelude.get» x3))
                   else
                     let x4 : T := «Infer.findAxiom»
                       (fun (x4 : T) =>
                         «Prelude.and»
                           («Base.equalTs» («PartialHorn.seqCtx» x4) x1)
                           («Prelude.and»
                             («Base.isEmpty» («PartialHorn.seqHyps» x4))
                             («Prelude.and»
                               («Base.not»
                                 (Const.eq
                                   (Const.label («PartialHorn.eqLhs» («PartialHorn.seqConcl» x4)))
                                   (leaf 0)))
                               («Base.equalTs»
                                 (Const.children («PartialHorn.eqLhs» («PartialHorn.seqConcl» x4)))
                                 («Prelude.single» x2)))));
                     if («Prelude.isSome» x4).label ≠ 0 then
                       «Prelude.some» («Infer.strict» («Prelude.get» x4))
                     else
                       «Base.mapO»
                         «Infer.rhsRule»
                         («Infer.findAxiom»
                           (fun (x5 : T) =>
                             «Prelude.and»
                               («Base.isEmpty» («PartialHorn.seqCtx» x5))
                               («Prelude.and»
                                 («Base.isEmpty» («PartialHorn.seqHyps» x5))
                                 (Const.equal
                                   («PartialHorn.eqRhs» («PartialHorn.seqConcl» x5))
                                   x2)))));
    x1

def «Infer.boundRule» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : List T := «Infer.argSorts» x1;
                   let x3 : T := «PartialHorn.opVars» x1 («Prelude.length» x2);
                   «Infer.findAxiom»
                     (fun (x4 : T) =>
                       «Prelude.and»
                         («Base.equalTs» («PartialHorn.seqCtx» x4) x2)
                         («Prelude.and»
                           (Const.equal
                             («PartialHorn.eqLhs» («PartialHorn.seqConcl» x4))
                             («PartialHorn.phOp» x0 («Prelude.single» x3)))
                           («Base.allT»
                             (fun (x5 : T) =>
                               Const.equal («PartialHorn.eqLhs» x5) («PartialHorn.eqRhs» x5))
                             («PartialHorn.seqHyps» x4)))));
    x2

def «Infer.dfdRules» :=
  «Base.mapT»
    «Infer.dfdRule»
    («Base.range» («Prelude.length» «Theory.sig»))

def «Infer.domRules» :=
  «Base.mapT»
    («Infer.boundRule» (leaf 0))
    («Base.range» («Prelude.length» «Theory.sig»))

def «Infer.codRules» :=
  «Base.mapT»
    («Infer.boundRule» (leaf 1))
    («Base.range» («Prelude.length» «Theory.sig»))

def «Infer.defAxIdx» :=
  fun (x0 : T) =>
    let x1 : T := Const.add
      («Prelude.length» «Theory.axioms»)
      (Const.mul (leaf 2) x0);
    x1

def «Infer.ann» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Infer.annSort» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x2);
    x1

def «Infer.annLo» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2); x3);
    x1

def «Infer.annHi» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «Infer.typed» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Infer.tyTerm» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1); x2);
    x1

def «Infer.tyAnn» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1); x3);
    x1

def «Infer.ext» :=
  fun (x0 : List T) =>
    let x1 : T := «PartialHorn.thyExtendAll» «Theory.toposTheory» x0; x1

def «Infer.extEnv» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: (x5 :: ([] : List T)))))))

def «Infer.envDefs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x2);
    x1

def «Infer.envAxs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x3);
    x1

def «Infer.envSg» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x4);
    x1

def «Infer.envDfds» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let x5 : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x5);
    x1

def «Infer.envDoms» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let x6 : T := Const.child x1 (leaf 4);
            let _ : T := Const.child x1 (leaf 5); Const.children x6);
    x1

def «Infer.envCods» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3);
            let _ : T := Const.child x1 (leaf 4);
            let x7 : T := Const.child x1 (leaf 5); Const.children x7);
    x1

def «Infer.envOfDefs» :=
  fun (x0 : List T) =>
    let x1 : T := (let x1 : T := «Infer.ext» x0;
                   «Infer.extEnv»
                     (Const.node (leaf 0) x0)
                     (Const.node (leaf 0) («PartialHorn.thyAxioms» x1))
                     (Const.node (leaf 0) («PartialHorn.thySig» x1))
                     (Const.node (leaf 0) «Infer.dfdRules»)
                     (Const.node (leaf 0) «Infer.domRules»)
                     (Const.node (leaf 0) «Infer.codRules»));
    x1

def «Infer.argSortsOf» :=
  fun (x0 : List T) =>
    let x1 : List
      T := «Base.mapT»
      (fun (x1 : T) => «Infer.annSort» («Infer.tyAnn» x1))
      x0;
    x1

def «Infer.hypOk» :=
  fun (x0 : List T → T → T) (x1 : List T) (x2 : T) =>
    let x3 : T := (if (Const.equal
      («PartialHorn.eqLhs» x2)
      («PartialHorn.eqRhs» x2)).label ≠ 0 then
      «Prelude.isSome» (x0 x1 («PartialHorn.eqLhs» x2))
    else
      let x3 : T := x0 x1 («PartialHorn.eqLhs» x2);
      let x4 : T := x0 x1 («PartialHorn.eqRhs» x2);
      if («Prelude.and»
        («Prelude.isSome» x3)
        («Prelude.isSome» x4)).label ≠ 0 then
        let x5 : T := «Infer.tyAnn» («Prelude.get» x3);
        let x6 : T := «Infer.tyAnn» («Prelude.get» x4);
        «Prelude.and»
          (Const.eq («Infer.annSort» x5) (leaf 0))
          («Prelude.and»
            (Const.eq («Infer.annSort» x6) (leaf 0))
            (Const.equal («Infer.annLo» x5) («Infer.annLo» x6)))
      else
        leaf 0);
    x3

def «Infer.bound» :=
  fun (x0 : T)
    (x1 : List T → T → T)
    (x2 : List T)
    (x3 : T)
    (x4 : T)
    (x5 : T) =>
    let x6 : T := «Base.bindO»
      («Prelude.nth» («Infer.envAxs» x0) x5)
      (fun (x6 : T) =>
        let x7 : T := «PartialHorn.opVars» x4 («Prelude.length» x2);
        if («Prelude.and»
          («PartialHorn.seqScoped» x6)
          («Prelude.and»
            («Base.equalTs» («PartialHorn.seqCtx» x6) («Infer.argSortsOf» x2))
            («Prelude.and»
              (Const.equal
                («PartialHorn.eqLhs» («PartialHorn.seqConcl» x6))
                («PartialHorn.phOp» x3 («Prelude.single» x7)))
              («Base.allT»
                (fun (x8 : T) =>
                  «Prelude.and»
                    (Const.equal («PartialHorn.eqLhs» x8) («PartialHorn.eqRhs» x8))
                    («Prelude.or»
                      (Const.equal («PartialHorn.eqLhs» x8) x7)
                      («Prelude.isSome» (x1 x2 («PartialHorn.eqLhs» x8)))))
                («PartialHorn.seqHyps» x6))))).label ≠ 0 then
          «Base.bindO»
            (x1 x2 («PartialHorn.eqRhs» («PartialHorn.seqConcl» x6)))
            (fun (x8 : T) =>
              if (Const.eq
                («Infer.annSort» («Infer.tyAnn» x8))
                (leaf 0)).label ≠ 0 then
                «Prelude.some» («Infer.annLo» («Infer.tyAnn» x8))
              else
                «Prelude.none»)
        else
          «Prelude.none»);
    x6

def «Infer.dfdOk» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : List T := «Infer.argSortsOf» x2;
                   let x5 : T := «PartialHorn.opVars» x3 («Prelude.length» x2);
                   let x6 : T := «Prelude.nth» («Infer.envDfds» x0) x3;
                   if («Prelude.and»
                     («Prelude.isSome» x6)
                     («Prelude.isSome» («Prelude.get» x6))).label ≠ 0 then
                     let x7 : T := «Prelude.get» («Prelude.get» x6);
                     let x8 : T := x7;
                     if (Const.eq (Const.label x8) (leaf 0)).label ≠ 0 then
                       let x9 : T := Const.child x8 (leaf 0);
                       let x10 : T := «Prelude.nth» («Infer.envAxs» x0) x9;
                       if («Prelude.isSome» x10).label ≠ 0 then
                         let x11 : T := «Prelude.get» x10;
                         «Prelude.and»
                           («PartialHorn.seqScoped» x11)
                           («Prelude.and»
                             («Base.equalTs» («PartialHorn.seqCtx» x11) x4)
                             («Prelude.and»
                               (Const.equal («PartialHorn.eqLhs» («PartialHorn.seqConcl» x11)) x5)
                               («Prelude.and»
                                 (Const.equal («PartialHorn.eqRhs» («PartialHorn.seqConcl» x11)) x5)
                                 («Base.allT» («Infer.hypOk» x1 x2) («PartialHorn.seqHyps» x11)))))
                       else
                         leaf 0
                     else
                       if (Const.eq (Const.label x8) (leaf 1)).label ≠ 0 then
                         let x9 : T := Const.child x8 (leaf 0);
                         let x10 : T := «Prelude.nth» («Infer.envAxs» x0) x9;
                         if («Prelude.isSome» x10).label ≠ 0 then
                           let x11 : T := «Prelude.get» x10;
                           «Prelude.and»
                             («Base.equalTs» («PartialHorn.seqCtx» x11) x4)
                             («Prelude.and»
                               («Base.isEmpty» («PartialHorn.seqHyps» x11))
                               («Prelude.and»
                                 («Base.not»
                                   (Const.eq
                                     (Const.label
                                       («PartialHorn.eqLhs» («PartialHorn.seqConcl» x11)))
                                     (leaf 0)))
                                 («Base.equalTs»
                                   (Const.children
                                     («PartialHorn.eqLhs» («PartialHorn.seqConcl» x11)))
                                   («Prelude.single» x5))))
                         else
                           leaf 0
                       else
                         let x9 : T := Const.child x8 (leaf 0);
                         let x10 : T := «Prelude.nth» («Infer.envAxs» x0) x9;
                         if («Prelude.isSome» x10).label ≠ 0 then
                           let x11 : T := «Prelude.get» x10;
                           «Prelude.and»
                             («Base.isEmpty» («PartialHorn.seqCtx» x11))
                             («Prelude.and»
                               («Base.isEmpty» («PartialHorn.seqHyps» x11))
                               («Prelude.and»
                                 («Base.isEmpty» x2)
                                 (Const.equal
                                   («PartialHorn.eqRhs» («PartialHorn.seqConcl» x11))
                                   x5)))
                         else
                           leaf 0
                   else
                     leaf 0);
    x4

def «Infer.inferObj» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (let x2 : T := «Infer.tyAnn» («Prelude.at» x1 (leaf 0));
                   if («Prelude.and»
                     (Const.eq x0 (leaf 0))
                     (Const.eq («Prelude.length» x1) (leaf 1))).label ≠ 0 then
                     if (Const.eq («Infer.annSort» x2) (leaf 1)).label ≠ 0 then
                       «Prelude.some»
                         («Infer.ann» (leaf 0) («Infer.annLo» x2) («Infer.annLo» x2))
                     else
                       «Prelude.none»
                   else
                     if («Prelude.and»
                       (Const.eq x0 (leaf 1))
                       (Const.eq («Prelude.length» x1) (leaf 1))).label ≠ 0 then
                       if (Const.eq («Infer.annSort» x2) (leaf 1)).label ≠ 0 then
                         «Prelude.some»
                           («Infer.ann» (leaf 0) («Infer.annHi» x2) («Infer.annHi» x2))
                       else
                         «Prelude.none»
                     else
                       let x3 : T := «PartialHorn.phOp»
                         x0
                         («Base.mapT»
                           (fun (x3 : T) =>
                             if (Const.eq
                               («Infer.annSort» («Infer.tyAnn» x3))
                               (leaf 0)).label ≠ 0 then
                               «Infer.annLo» («Infer.tyAnn» x3)
                             else
                               «Infer.tyTerm» x3)
                           x1);
                       «Prelude.some» («Infer.ann» (leaf 0) x3 x3));
    x2

def «Infer.inferArr» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : T) (x3 : List T) =>
    let x4 : T := (let x4 : T := «Base.bindO»
                     («Base.bindO»
                       («Prelude.nth» («Infer.envDoms» x0) x2)
                       (fun (x4 : T) => x4))
                     («Infer.bound» x0 x1 x3 (leaf 0) x2);
                   let x5 : T := «Base.bindO»
                     («Base.bindO»
                       («Prelude.nth» («Infer.envCods» x0) x2)
                       (fun (x5 : T) => x5))
                     («Infer.bound» x0 x1 x3 (leaf 1) x2);
                   if («Prelude.and»
                     («Prelude.isSome» x4)
                     («Prelude.isSome» x5)).label ≠ 0 then
                     «Prelude.some»
                       («Infer.ann» (leaf 1) («Prelude.get» x4) («Prelude.get» x5))
                   else
                     «Prelude.none»);
    x4

def «Infer.inferDef» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : T) (x3 : List T) =>
    let x4 : T := (let x4 : T := Const.sub x2 («Prelude.length» «Theory.sig»);
                   let x5 : T := «Prelude.nth» («Infer.envDefs» x0) x4;
                   let x6 : T := «Prelude.nth» («Infer.envAxs» x0) («Infer.defAxIdx» x4);
                   if («Prelude.and»
                     («Prelude.isSome» x5)
                     («Prelude.isSome» x6)).label ≠ 0 then
                     let x7 : T := «PartialHorn.pdBody» («Prelude.get» x5);
                     let x8 : T := «Prelude.get» x6;
                     if («Prelude.and»
                       («PartialHorn.seqScoped» x8)
                       («Prelude.and»
                         («Base.equalTs» («PartialHorn.seqCtx» x8) («Infer.argSortsOf» x3))
                         («Prelude.and»
                           («Base.equalTs»
                             («PartialHorn.seqHyps» x8)
                             («Prelude.single» («PartialHorn.eqn» x7 x7)))
                           (Const.equal
                             («PartialHorn.seqConcl» x8)
                             («PartialHorn.eqn»
                               («PartialHorn.opVars» x2 («Prelude.length» x3))
                               x7))))).label ≠ 0 then
                       «Base.mapO» «Infer.tyAnn» (x1 x3 x7)
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x4

def «Infer.inferOp» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : T) (x3 : List T) =>
    let x4 : T := «Base.bindO»
      («Prelude.nth» («Infer.envSg» x0) x2)
      (fun (x4 : T) =>
        if («Base.equalTs»
          («Infer.argSortsOf» x3)
          («PartialHorn.opArgs» x4)).label ≠ 0 then
          if (Const.lt x2 («Prelude.length» «Theory.sig»)).label ≠ 0 then
            if («Infer.dfdOk» x0 x1 x3 x2).label ≠ 0 then
              if (Const.eq («PartialHorn.opSort» x4) (leaf 0)).label ≠ 0 then
                «Infer.inferObj» x2 x3
              else
                if (Const.eq («PartialHorn.opSort» x4) (leaf 1)).label ≠ 0 then
                  «Infer.inferArr» x0 x1 x2 x3
                else
                  «Prelude.none»
            else
              «Prelude.none»
          else
            «Infer.inferDef» x0 x1 x2 x3
        else
          «Prelude.none»);
    x4

def «Infer.inferSide» :=
  fun (x0 : T) (x1 : List T) (x2 : T → T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := «Base.bindO»
                     («Prelude.nth» («Infer.envAxs» x0) x4)
                     (fun (x5 : T) =>
                       «Prelude.some»
                         («Prelude.and»
                           («Base.equalTs» («PartialHorn.seqCtx» x5) («Prelude.single» (leaf 1)))
                           («Prelude.and»
                             («Base.isEmpty» («PartialHorn.seqHyps» x5))
                             (Const.equal
                               («PartialHorn.seqConcl» x5)
                               («Theory.dfd»
                                 («PartialHorn.phOp»
                                   x4
                                   («Prelude.single» («Theory.x» (leaf 0)))))))));
                   if («Prelude.and»
                     («Prelude.isSome» x5)
                     («Prelude.get» x5)).label ≠ 0 then
                     let x6 : T := Const.foldr
                       (α := T)
                       (β := T)
                       (fun (x6 : T) (x7 : T) =>
                         if (Const.equal
                           («PartialHorn.eqLhs» x6)
                           («PartialHorn.phOp»
                             x4
                             («Prelude.single» («PartialHorn.phVar» x3)))).label ≠ 0 then
                           «Prelude.some» x6
                         else
                           x7)
                       «Prelude.none»
                       x1;
                     if («Prelude.isSome» x6).label ≠ 0 then
                       «Base.bindO»
                         (x2 («PartialHorn.eqRhs» («Prelude.get» x6)))
                         (fun (x7 : T) =>
                           if (Const.eq («Infer.annSort» x7) (leaf 0)).label ≠ 0 then
                             «Prelude.some» («Infer.annLo» x7)
                           else
                             «Prelude.none»)
                     else
                       «Prelude.some»
                         («PartialHorn.phOp» x4 («Prelude.single» («PartialHorn.phVar» x3)))
                   else
                     «Prelude.none»);
    x5

def «Infer.inferVar» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T → T) (x4 : T) =>
    let x5 : T := «Base.bindO»
      («Prelude.nth» x1 x4)
      (fun (x5 : T) =>
        if (Const.eq x5 (leaf 0)).label ≠ 0 then
          «Prelude.some»
            («Infer.ann»
              (leaf 0)
              («PartialHorn.phVar» x4)
              («PartialHorn.phVar» x4))
        else
          if (Const.eq x5 (leaf 1)).label ≠ 0 then
            «Base.bindO»
              («Infer.inferSide» x0 x2 x3 x4 (leaf 0))
              (fun (x6 : T) =>
                «Base.mapO»
                  (fun (x7 : T) => «Infer.ann» (leaf 1) x6 x7)
                  («Infer.inferSide» x0 x2 x3 x4 (leaf 1)))
          else
            «Prelude.none»);
    x5

def «Infer.poTrees» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Infer.poValues» :=
  fun (x0 : List (T × T)) =>
    let x1 : List
      T := Const.foldr
      (α := T × T)
      (β := List T)
      (fun (x1 : T × T) (x2 : List T) => ((x1).2 :: x2))
      ([] : List T)
      x0;
    x1

def «Infer.patInfer» :=
  fun (x0 : T) (x1 : List T → T → T) (x2 : List T) (x3 : T) =>
    let x4 : T := (Const.fold
      (α := T × T)
      (fun (x4 : T) (x5 : List (T × T)) =>
        let x6 : List T := «Infer.poTrees» x5;
        (Const.node x4 x6,
          if (Const.eq x4 (leaf 0)).label ≠ 0 then
            if (Const.eq («Prelude.length» x6) (leaf 1)).label ≠ 0 then
              let x7 : T := «Prelude.at» x6 (leaf 0);
              if (Const.eq (Const.arity x7) (leaf 0)).label ≠ 0 then
                «Prelude.nth» x2 (Const.label x7)
              else
                «Prelude.none»
            else
              «Prelude.none»
          else
            «Base.bindO»
              («Base.allSomeT» («Infer.poValues» x5))
              (fun (x7 : T) =>
                let x8 : List T := Const.children x7;
                «Base.mapO»
                  (fun (x9 : T) =>
                    «Infer.typed»
                      («PartialHorn.phOp»
                        (Const.sub x4 (leaf 1))
                        («Base.mapT» «Infer.tyTerm» x8))
                      x9)
                  («Infer.inferOp» x0 x1 (Const.sub x4 (leaf 1)) x8))))
      x3).2;
    x4

def «Infer.treeInfer» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T → T → T)
    (x4 : T → T)
    (x5 : T) =>
    let x6 : T := (Const.fold
      (α := T × T)
      (fun (x6 : T) (x7 : List (T × T)) =>
        let x8 : List T := «Infer.poTrees» x7;
        (Const.node x6 x8,
          if (Const.eq x6 (leaf 0)).label ≠ 0 then
            if (Const.eq («Prelude.length» x8) (leaf 1)).label ≠ 0 then
              let x9 : T := «Prelude.at» x8 (leaf 0);
              if (Const.eq (Const.arity x9) (leaf 0)).label ≠ 0 then
                «Infer.inferVar» x0 x1 x2 x4 (Const.label x9)
              else
                «Prelude.none»
            else
              «Prelude.none»
          else
            «Base.bindO»
              («Base.allSomeT» («Infer.poValues» x7))
              (fun (x9 : T) =>
                «Infer.inferOp»
                  x0
                  x3
                  (Const.sub x6 (leaf 1))
                  (Const.foldr
                    (α := T)
                    (β := List T × List T)
                    (fun (x10 : T) (x11 : List T × List T) =>
                      («Prelude.tail» (x11).1,
                        ((«Infer.typed» x10 («Prelude.at» (x11).1 (leaf 0))) :: (x11).2)))
                    («Prelude.reverse» (Const.children x9), ([] : List T))
                    x8).2)))
      x5).2;
    x6

def «Infer.infers» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : (List T → T → T) ×
      (T →
        T) := Const.iter
      (α := (List T → T → T) × (T → T))
      (fun (x4 : (List T → T → T) × (T → T)) =>
        (fun (x5 : List T) (x6 : T) => «Infer.patInfer» x0 (x4).1 x5 x6,
          fun (x5 : T) => «Infer.treeInfer» x0 x1 x2 (x4).1 (x4).2 x5))
      (fun (_ : List T) (_ : T) => «Prelude.none»,
        fun (_ : T) => «Prelude.none»)
      x3;
    x4

def «Infer.inferFuel» := leaf 8

def «Language.pr» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 0) («Theory.l2» x0 x1); x2

def «Language.p1» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 0); x1

def «Language.p2» :=
  fun (x0 : T) => let x1 : T := Const.child x0 (leaf 1); x1

def «Language.mNode» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := Const.node x0 ((Const.node (leaf 0) x1) :: x2); x3

def «Language.var» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mNode»
      (leaf 0)
      («Prelude.single» x0)
      ([] : List T);
    x1

def «Language.mStar» :=
  «Language.mNode» (leaf 1) ([] : List T) ([] : List T)

def «Language.mPair» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mNode»
      (leaf 2)
      ([] : List T)
      («Theory.l2» x0 x1);
    x2

def «Language.mFst» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mNode»
      (leaf 3)
      ([] : List T)
      («Prelude.single» x0);
    x1

def «Language.mSnd» :=
  fun (x0 : T) =>
    let x1 : T := «Language.mNode»
      (leaf 4)
      ([] : List T)
      («Prelude.single» x0);
    x1

def «Language.mLam» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mNode»
      (leaf 5)
      («Prelude.single» x0)
      («Prelude.single» x1);
    x2

def «Language.app» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mNode»
      (leaf 6)
      ([] : List T)
      («Theory.l2» x0 x1);
    x2

def «Language.mArr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Language.mNode»
      (leaf 7)
      («Theory.l2» x0 (Const.node (leaf 0) x1))
      («Prelude.single» x2);
    x3

def «Language.mNatRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mNode»
      (leaf 8)
      ([] : List T)
      («Theory.l3» x0 x1 x2);
    x3

def «Language.mListRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mNode»
      (leaf 9)
      ([] : List T)
      («Theory.l3» x0 x1 x2);
    x3

def «Language.mRoseRec» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mNode»
      (leaf 10)
      («Prelude.single» x0)
      («Theory.l2» x1 x2);
    x3

def «Language.mDefn» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := «Language.mNode»
      (leaf 11)
      («Theory.l2» x0 (Const.node (leaf 0) x1))
      x2;
    x3

def «Language.mEq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.mNode»
      (leaf 12)
      ([] : List T)
      («Theory.l2» x0 x1);
    x2

def «Language.mData» :=
  fun (x0 : T) =>
    let x1 : List T := Const.children (Const.child x0 (leaf 0)); x1

def «Language.mArgs» :=
  fun (x0 : T) =>
    let x1 : List T := «Prelude.tail» (Const.children x0); x1

def «Language.mIs» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      (Const.eq (Const.label x2) x0)
      (Const.eq («Prelude.length» («Language.mArgs» x2)) x1);
    x3

def «Language.mArg» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.at» («Language.mArgs» x0) x1; x2

def «Language.mD» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.at» («Language.mData» x0) x1; x2

def «Language.rpTrees» :=
  fun (x0 : List (T × ((T → T) → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × ((T → T) → T))
      (β := List T)
      (fun (x1 : T × ((T → T) → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Language/RPs.tail» :=
  fun (x0 : List (T × ((T → T) → T))) =>
    Const.lcase
      (α := T × ((T → T) → T))
      (β := List (T × ((T → T) → T)))
      x0
      ([] : List (T × ((T → T) → T)))
      (fun (_ : T × ((T → T) → T)) (x2 : List (T × ((T → T) → T))) => x2)

def «Language.rpAll» :=
  fun (x0 : List (T × ((T → T) → T))) (x1 : T → T) =>
    let x2 : List
      T := Const.foldr
      (α := T × ((T → T) → T))
      (β := List T)
      (fun (x2 : T × ((T → T) → T)) (x3 : List T) => (((x2).2 x1) :: x3))
      ([] : List T)
      x0;
    x2

def «Language.rpAt» :=
  fun (x0 : List (T × ((T → T) → T))) (x1 : T) (x2 : T → T) =>
    let x3 : T := Const.lcase
      (α := T × ((T → T) → T))
      (β := T)
      (Const.iter (α := List (T × ((T → T) → T))) «Language/RPs.tail» x0 x1)
      (leaf 0)
      (fun (x3 : T × ((T → T) → T)) (_ : List (T × ((T → T) → T))) =>
        (x3).2 x2);
    x3

def «Language.travStep» :=
  fun (x0 : (T → T) → T → T)
    (x1 : T → T)
    (x2 : T)
    (x3 : List (T × ((T → T) → T)))
    (x4 : T → T) =>
    let x5 : T := (let x5 : T := «Prelude.at» («Language.rpTrees» x3) (leaf 0);
                   let x6 : List (T × ((T → T) → T)) := «Language/RPs.tail» x3;
                   let x7 : List T := «Language.rpTrees» x6;
                   let x8 : T := «Prelude.length» x7;
                   if (Const.eq x2 (leaf 0)).label ≠ 0 then
                     x1 (x4 («Prelude.at» (Const.children x5) (leaf 0)))
                   else
                     if («Prelude.and»
                       (Const.eq x2 (leaf 5))
                       (Const.eq x8 (leaf 1))).label ≠ 0 then
                       Const.node
                         x2
                         (x5 :: («Prelude.single» («Language.rpAt» x6 (leaf 0) (x0 x4))))
                     else
                       if («Prelude.and»
                         («Prelude.or» (Const.eq x2 (leaf 8)) (Const.eq x2 (leaf 9)))
                         (Const.eq x8 (leaf 3))).label ≠ 0 then
                         Const.node
                           x2
                           (x5 ::
                             («Theory.l3»
                               («Prelude.at» x7 (leaf 0))
                               («Prelude.at» x7 (leaf 1))
                               («Language.rpAt» x6 (leaf 2) x4)))
                       else
                         if («Prelude.and»
                           (Const.eq x2 (leaf 10))
                           (Const.eq x8 (leaf 2))).label ≠ 0 then
                           Const.node
                             x2
                             (x5 ::
                               («Theory.l2»
                                 («Prelude.at» x7 (leaf 0))
                                 («Language.rpAt» x6 (leaf 1) x4)))
                         else
                           Const.node x2 (x5 :: («Language.rpAll» x6 x4)));
    x5

def «Language.trav» :=
  fun (x0 : (T → T) → T → T) (x1 : T → T) (x2 : T) =>
    let x3 : (T → T) →
      T := (Const.fold
      (α := T × ((T → T) → T))
      (fun (x3 : T) (x4 : List (T × ((T → T) → T))) =>
        (Const.node x3 («Language.rpTrees» x4),
          fun (x5 : T → T) => «Language.travStep» x0 x1 x3 x4 x5))
      x2).2;
    x3

def «Language.liftR» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      leaf 0
    else
      Const.add (x0 (Const.sub x1 (leaf 1))) (leaf 1));
    x2

def «Language.rename» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := «Language.trav» «Language.liftR» «Language.var» x0 x1;
    x2

def «Language.liftS» :=
  fun (x0 : T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      «Language.var» (leaf 0)
    else
      «Language.rename»
        (x0 (Const.sub x1 (leaf 1)))
        (fun (x2 : T) => Const.add x2 (leaf 1)));
    x2

def «Language.subst» :=
  fun (x0 : T) (x1 : T → T) =>
    let x2 : T := «Language.trav»
      «Language.liftS»
      (fun (x2 : T) => x2)
      x0
      x1;
    x2

def «Language.substList» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «Base.getD» («Prelude.nth» x0 x1) («Language.var» x1);
    x2

def «Language.dataOsubst» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := (if («Prelude.or»
      (Const.eq x1 (leaf 5))
      (Const.eq x1 (leaf 10))).label ≠ 0 then
      «Base.mapT» («PartialHorn.phSubst» x0) x2
    else
      if («Prelude.or»
        (Const.eq x1 (leaf 7))
        (Const.eq x1 (leaf 11))).label ≠ 0 then
        «Theory.l2»
          («Prelude.at» x2 (leaf 0))
          (Const.node
            (leaf 0)
            («Base.mapT»
              («PartialHorn.phSubst» x0)
              (Const.children («Prelude.at» x2 (leaf 1)))))
      else
        x2);
    x3

def «Language.osubst» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (Const.fold
      (α := T × T)
      (fun (x2 : T) (x3 : List (T × T)) =>
        let x4 : List T := «PartialHorn.ptTrees» x3;
        (Const.node x2 x4,
          Const.node
            x2
            ((Const.node
              (leaf 0)
              («Language.dataOsubst»
                x0
                x2
                (Const.children («Prelude.at» x4 (leaf 0))))) ::
              («Prelude.tail» («PartialHorn.ptValues» x3)))))
      x1).2;
    x2

def «Language.tyOps» :=
  ((«Language.pr» (leaf 4) (leaf 0)) ::
    ((«Language.pr» (leaf 6) (leaf 2)) ::
      ((«Language.pr» (leaf 13) (leaf 0)) ::
        ((«Language.pr» (leaf 15) (leaf 2)) ::
          ((«Language.pr» (leaf 22) (leaf 2)) ::
            ((«Language.pr» (leaf 25) (leaf 0)) ::
              ((«Language.pr» (leaf 29) (leaf 0)) ::
                ((«Language.pr» (leaf 33) (leaf 1)) ::
                  ((«Language.pr» (leaf 37) (leaf 0)) ::
                    («Prelude.single» («Language.pr» (leaf 40) (leaf 1))))))))))))

def «Language.binParts» :=
  fun (x0 : T → T → T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.arity x1) (leaf 2)).label ≠ 0 then
      let x2 : T := Const.child x1 (leaf 0);
      let x3 : T := Const.child x1 (leaf 1);
      if (Const.equal x1 (x0 x2 x3)).label ≠ 0 then
        «Prelude.some» («Language.pr» x2 x3)
      else
        «Prelude.none»
    else
      «Prelude.none»);
    x2

def «Language.prodParts» :=
  fun (x0 : T) => let x1 : T := «Language.binParts» «Theory.prod» x0; x1

def «Language.coprodParts» :=
  fun (x0 : T) =>
    let x1 : T := «Language.binParts» «Theory.coprod» x0; x1

def «Language.expParts» :=
  fun (x0 : T) => let x1 : T := «Language.binParts» «Theory.exp» x0; x1

def «Language.listPart» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.eq (Const.arity x0) (leaf 1)).label ≠ 0 then
      let x1 : T := Const.child x0 (leaf 0);
      if (Const.equal x0 («Theory.list» x1)).label ≠ 0 then
        «Prelude.some» x1
      else
        «Prelude.none»
    else
      «Prelude.none»);
    x1

def «Language.roseLabel» :=
  fun (x0 : T) =>
    let x1 : T := (if (Const.equal x0 «Theory.rose»).label ≠ 0 then
      «Prelude.some» «Theory.nat»
    else
      if (Const.eq (Const.arity x0) (leaf 1)).label ≠ 0 then
        let x1 : T := Const.child x0 (leaf 0);
        if (Const.equal x0 («Theory.lrose» x1)).label ≠ 0 then
          «Prelude.some» x1
        else
          «Prelude.none»
      else
        «Prelude.none»);
    x1

def «Language.roseFold» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.equal x0 «Theory.rose»).label ≠ 0 then
      «Theory.roseRec» x1
    else
      «Theory.lroseRec» (Const.child x0 (leaf 0)) x1);
    x2

def «Language.ctxObj» :=
  fun (x0 : List T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x1 : T) (x2 : T × T) =>
        (if ((x2).2).label ≠ 0 then «Theory.prod» (x2).1 x1 else x1, leaf 1))
      («Theory.one», leaf 0)
      x0).1;
    x1

def «Language.extendEnv» :=
  fun (x0 : T) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := ((«Language.pr» («Theory.cSnd» x0 x1) x1) ::
      («Base.mapT»
        (fun (x3 : T) =>
          «Language.pr»
            («Theory.comp» («Language.p1» x3) («Theory.cFst» x0 x1))
            («Language.p2» x3))
        x2));
    x3

def «Language.stdEnv» :=
  fun (x0 : List T) =>
    let x1 : List
      T := (Const.foldr
      (α := T)
      (β := List T × List T)
      (fun (x1 : T) (x2 : List T × List T) =>
        (if («Base.isEmpty» (x2).2).label ≠ 0 then
          «Prelude.single» («Language.pr» («Theory.idt» x1) x1)
        else
          «Language.extendEnv» («Language.ctxObj» (x2).2) x1 (x2).1,
          (x1 :: (x2).2)))
      (([] : List T), ([] : List T))
      x0).1;
    x1

def «Language.tuple» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := (Const.foldr
      (α := T)
      (β := T × T)
      (fun (x2 : T) (x3 : T × T) =>
        (if ((x3).2).label ≠ 0 then «Theory.cPair» (x3).1 x2 else x2, leaf 1))
      («Theory.bang» x0, leaf 0)
      x1).1;
    x2

def «Language.ldefn» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Language.ldArity» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x2);
    x1

def «Language.ldParams» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3); Const.children x3);
    x1

def «Language.ldType» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x4);
    x1

def «Language.ldBody» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3); x5);
    x1

def «Language.primitive» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Language.prArity» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x2);
    x1

def «Language.prArrow» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let x3 : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x3);
    x1

def «Language.prDom» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x4);
    x1

def «Language.prCod» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3); x5);
    x1

def «Language.defLang» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Language.defObj» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «Language.defLanguage» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); «Prelude.some» x2
                   else
                     let _ : T := Const.child x1 (leaf 0);
                     let _ : T := Const.child x1 (leaf 1); «Prelude.none»);
    x1

def «Language.globals» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Language.gPrims» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let x2 : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x2);
    x1

def «Language.gDefs» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2); Const.children x3);
    x1

def «Language.gBase» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let x4 : T := Const.child x1 (leaf 2); x4);
    x1

def «Language.isTyOp» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.or»
      («Base.anyT»
        (fun (x3 : T) => Const.equal x3 («Language.pr» x1 x2))
        «Language.tyOps»)
      («Prelude.and»
        («Base.not» (Const.lt x1 («Language.gBase» x0)))
        (let x3 : T := «Prelude.nth»
           («Language.gDefs» x0)
           (Const.sub x1 («Language.gBase» x0));
         if («Prelude.isSome» x3).label ≠ 0 then
           let x4 : T := «Prelude.get» x3;
           if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
             let _ : T := Const.child x4 (leaf 0); leaf 0
           else
             let x5 : T := Const.child x4 (leaf 0);
             let _ : T := Const.child x4 (leaf 1); Const.eq x5 x2
         else
           leaf 0));
    x3

def «Language.isTy» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (Const.fold
      (α := T × T)
      (fun (x3 : T) (x4 : List (T × T)) =>
        let x5 : List T := «PartialHorn.ptTrees» x4;
        (Const.node x3 x5,
          if (Const.eq x3 (leaf 0)).label ≠ 0 then
            if (Const.eq («Prelude.length» x5) (leaf 1)).label ≠ 0 then
              let x6 : T := «Prelude.at» x5 (leaf 0);
              «Prelude.and»
                (Const.eq (Const.arity x6) (leaf 0))
                (Const.lt (Const.label x6) x1)
            else
              leaf 0
          else
            «Prelude.and»
              («Language.isTyOp» x0 (Const.sub x3 (leaf 1)) («Prelude.length» x5))
              («Base.allT» (fun (x6 : T) => x6) («PartialHorn.ptValues» x4))))
      x2).2;
    x3

def «Language.cpTrees» :=
  fun (x0 : List (T × (T → List T → T))) =>
    let x1 : List
      T := Const.foldr
      (α := T × (T → List T → T))
      (β := List T)
      (fun (x1 : T × (T → List T → T)) (x2 : List T) => ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Language/CPs.tail» :=
  fun (x0 : List (T × (T → List T → T))) =>
    Const.lcase
      (α := T × (T → List T → T))
      (β := List (T × (T → List T → T)))
      x0
      ([] : List (T × (T → List T → T)))
      (fun (_ : T × (T → List T → T)) (x2 : List (T × (T → List T → T))) =>
        x2)

def «Language.cpAt» :=
  fun (x0 : List (T × (T → List T → T))) (x1 : T) =>
    let x2 : T →
      List T →
        T := Const.lcase
      (α := T × (T → List T → T))
      (β := T → List T → T)
      (Const.iter
        (α := List (T × (T → List T → T)))
        «Language/CPs.tail»
        x0
        x1)
      (fun (_ : T) (_ : List T) => «Prelude.none»)
      (fun (x2 : T × (T → List T → T)) (_ : List (T × (T → List T → T))) =>
        (x2).2);
    x2

def «Language.cpAll» :=
  fun (x0 : List (T × (T → List T → T))) (x1 : T) (x2 : List T) =>
    let x3 : List
      T := Const.foldr
      (α := T × (T → List T → T))
      (β := List T)
      (fun (x3 : T × (T → List T → T)) (x4 : List T) =>
        (((x3).2 x1 x2) :: x4))
      ([] : List T)
      x0;
    x3

def «Language.compileStep» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List (T × (T → List T → T)))
    (x4 : T)
    (x5 : List T) =>
    let x6 : T := (let x6 : List
                     T := Const.children («Prelude.at» («Language.cpTrees» x3) (leaf 0));
                   let x7 : List (T × (T → List T → T)) := «Language/CPs.tail» x3;
                   let x8 : T := «Prelude.length» («Language.cpTrees» x7);
                   let x9 : T → List T → T := «Language.cpAt» x7 (leaf 0);
                   let x10 : T → List T → T := «Language.cpAt» x7 (leaf 1);
                   let x11 : T → List T → T := «Language.cpAt» x7 (leaf 2);
                   if («Prelude.and»
                     (Const.eq x2 (leaf 0))
                     (Const.eq x8 (leaf 0))).label ≠ 0 then
                     «Prelude.nth» x5 («Prelude.at» x6 (leaf 0))
                   else
                     if («Prelude.and»
                       (Const.eq x2 (leaf 1))
                       (Const.eq x8 (leaf 0))).label ≠ 0 then
                       «Prelude.some» («Language.pr» («Theory.bang» x4) «Theory.one»)
                     else
                       if («Prelude.and»
                         (Const.eq x2 (leaf 2))
                         (Const.eq x8 (leaf 2))).label ≠ 0 then
                         «Base.bindO»
                           (x9 x4 x5)
                           (fun (x12 : T) =>
                             «Base.bindO»
                               (x10 x4 x5)
                               (fun (x13 : T) =>
                                 «Prelude.some»
                                   («Language.pr»
                                     («Theory.cPair» («Language.p1» x12) («Language.p1» x13))
                                     («Theory.prod» («Language.p2» x12) («Language.p2» x13)))))
                       else
                         if («Prelude.and»
                           («Prelude.or» (Const.eq x2 (leaf 3)) (Const.eq x2 (leaf 4)))
                           (Const.eq x8 (leaf 1))).label ≠ 0 then
                           «Base.bindO»
                             (x9 x4 x5)
                             (fun (x12 : T) =>
                               «Base.bindO»
                                 («Language.prodParts» («Language.p2» x12))
                                 (fun (x13 : T) =>
                                   if (Const.eq x2 (leaf 3)).label ≠ 0 then
                                     «Prelude.some»
                                       («Language.pr»
                                         («Theory.comp»
                                           («Theory.cFst» («Language.p1» x13) («Language.p2» x13))
                                           («Language.p1» x12))
                                         («Language.p1» x13))
                                   else
                                     «Prelude.some»
                                       («Language.pr»
                                         («Theory.comp»
                                           («Theory.cSnd» («Language.p1» x13) («Language.p2» x13))
                                           («Language.p1» x12))
                                         («Language.p2» x13))))
                         else
                           if («Prelude.and»
                             (Const.eq x2 (leaf 5))
                             (Const.eq x8 (leaf 1))).label ≠ 0 then
                             let x12 : T := «Prelude.at» x6 (leaf 0);
                             if («Language.isTy» x0 x1 x12).label ≠ 0 then
                               «Base.bindO»
                                 (x9 («Theory.prod» x4 x12) («Language.extendEnv» x4 x12 x5))
                                 (fun (x13 : T) =>
                                   «Prelude.some»
                                     («Language.pr»
                                       («Theory.curry» x4 x12 («Language.p1» x13))
                                       («Theory.exp» x12 («Language.p2» x13))))
                             else
                               «Prelude.none»
                           else
                             if («Prelude.and»
                               (Const.eq x2 (leaf 6))
                               (Const.eq x8 (leaf 2))).label ≠ 0 then
                               «Base.bindO»
                                 (x9 x4 x5)
                                 (fun (x12 : T) =>
                                   «Base.bindO»
                                     («Language.expParts» («Language.p2» x12))
                                     (fun (x13 : T) =>
                                       «Base.bindO»
                                         (x10 x4 x5)
                                         (fun (x14 : T) =>
                                           if (Const.equal
                                             («Language.p2» x14)
                                             («Language.p1» x13)).label ≠ 0 then
                                             «Prelude.some»
                                               («Language.pr»
                                                 («Theory.comp»
                                                   («Theory.ev»
                                                     («Language.p1» x13)
                                                     («Language.p2» x13))
                                                   («Theory.cPair»
                                                     («Language.p1» x12)
                                                     («Language.p1» x14)))
                                                 («Language.p2» x13))
                                           else
                                             «Prelude.none»)))
                             else
                               if («Prelude.and»
                                 (Const.eq x2 (leaf 7))
                                 (Const.eq x8 (leaf 1))).label ≠ 0 then
                                 let x12 : List T := Const.children («Prelude.at» x6 (leaf 1));
                                 «Base.bindO»
                                   («Prelude.nth» («Language.gPrims» x0) («Prelude.at» x6 (leaf 0)))
                                   (fun (x13 : T) =>
                                     «Base.bindO»
                                       (x9 x4 x5)
                                       (fun (x14 : T) =>
                                         if («Prelude.and»
                                           (Const.eq
                                             («Prelude.length» x12)
                                             («Language.prArity» x13))
                                           («Prelude.and»
                                             («Base.allT» («Language.isTy» x0 x1) x12)
                                             (Const.equal
                                               («Language.p2» x14)
                                               («PartialHorn.phSubst»
                                                 x12
                                                 («Language.prDom» x13))))).label ≠ 0 then
                                           «Prelude.some»
                                             («Language.pr»
                                               («Theory.comp»
                                                 («PartialHorn.phSubst»
                                                   x12
                                                   («Language.prArrow» x13))
                                                 («Language.p1» x14))
                                               («PartialHorn.phSubst» x12 («Language.prCod» x13)))
                                         else
                                           «Prelude.none»))
                               else
                                 if («Prelude.and»
                                   (Const.eq x2 (leaf 8))
                                   (Const.eq x8 (leaf 3))).label ≠ 0 then
                                   «Base.bindO»
                                     (x9 «Theory.one» ([] : List T))
                                     (fun (x12 : T) =>
                                       let x13 : T := «Language.p2» x12;
                                       «Base.bindO»
                                         (x10
                                           x13
                                           («Prelude.single»
                                             («Language.pr» («Theory.idt» x13) x13)))
                                         (fun (x14 : T) =>
                                           «Base.bindO»
                                             (x11 x4 x5)
                                             (fun (x15 : T) =>
                                               if («Prelude.and»
                                                 (Const.equal («Language.p2» x14) x13)
                                                 (Const.equal
                                                   («Language.p2» x15)
                                                   «Theory.nat»)).label ≠ 0 then
                                                 «Prelude.some»
                                                   («Language.pr»
                                                     («Theory.comp»
                                                       («Theory.natRec»
                                                         («Language.p1» x12)
                                                         («Language.p1» x14))
                                                       («Language.p1» x15))
                                                     x13)
                                               else
                                                 «Prelude.none»)))
                                 else
                                   if («Prelude.and»
                                     (Const.eq x2 (leaf 9))
                                     (Const.eq x8 (leaf 3))).label ≠ 0 then
                                     «Base.bindO»
                                       (x11 x4 x5)
                                       (fun (x12 : T) =>
                                         «Base.bindO»
                                           («Language.listPart» («Language.p2» x12))
                                           (fun (x13 : T) =>
                                             «Base.bindO»
                                               (x9 «Theory.one» ([] : List T))
                                               (fun (x14 : T) =>
                                                 let x15 : T := «Language.p2» x14;
                                                 «Base.bindO»
                                                   (x10
                                                     («Theory.prod» x13 x15)
                                                     («Theory.l2»
                                                       («Language.pr» («Theory.cSnd» x13 x15) x15)
                                                       («Language.pr» («Theory.cFst» x13 x15) x13)))
                                                   (fun (x16 : T) =>
                                                     if (Const.equal
                                                       («Language.p2» x16)
                                                       x15).label ≠ 0 then
                                                       «Prelude.some»
                                                         («Language.pr»
                                                           («Theory.comp»
                                                             («Theory.listRec»
                                                               x13
                                                               («Language.p1» x14)
                                                               («Language.p1» x16))
                                                             («Language.p1» x12))
                                                           x15)
                                                     else
                                                       «Prelude.none»))))
                                   else
                                     if («Prelude.and»
                                       (Const.eq x2 (leaf 10))
                                       (Const.eq x8 (leaf 2))).label ≠ 0 then
                                       let x12 : T := «Prelude.at» x6 (leaf 0);
                                       if («Language.isTy» x0 x1 x12).label ≠ 0 then
                                         «Base.bindO»
                                           (x10 x4 x5)
                                           (fun (x13 : T) =>
                                             «Base.bindO»
                                               («Language.roseLabel» («Language.p2» x13))
                                               (fun (x14 : T) =>
                                                 let x15 : T := «Theory.prod»
                                                   x14
                                                   («Theory.list» x12);
                                                 «Base.bindO»
                                                   (x9
                                                     x15
                                                     («Prelude.single»
                                                       («Language.pr» («Theory.idt» x15) x15)))
                                                   (fun (x16 : T) =>
                                                     if (Const.equal
                                                       («Language.p2» x16)
                                                       x12).label ≠ 0 then
                                                       «Prelude.some»
                                                         («Language.pr»
                                                           («Theory.comp»
                                                             («Language.roseFold»
                                                               («Language.p2» x13)
                                                               («Language.p1» x16))
                                                             («Language.p1» x13))
                                                           x12)
                                                     else
                                                       «Prelude.none»)))
                                       else
                                         «Prelude.none»
                                     else
                                       if («Prelude.and»
                                         (Const.eq x2 (leaf 12))
                                         (Const.eq x8 (leaf 2))).label ≠ 0 then
                                         «Base.bindO»
                                           (x9 x4 x5)
                                           (fun (x12 : T) =>
                                             «Base.bindO»
                                               (x10 x4 x5)
                                               (fun (x13 : T) =>
                                                 if (Const.equal
                                                   («Language.p2» x12)
                                                   («Language.p2» x13)).label ≠ 0 then
                                                   «Prelude.some»
                                                     («Language.pr»
                                                       («Theory.comp»
                                                         («Theory.chi»
                                                           («Theory.diag» («Language.p2» x12)))
                                                         («Theory.cPair»
                                                           («Language.p1» x12)
                                                           («Language.p1» x13)))
                                                       «Theory.omega»)
                                                 else
                                                   «Prelude.none»))
                                       else
                                         if (Const.eq x2 (leaf 11)).label ≠ 0 then
                                           let x12 : List
                                             T := Const.children («Prelude.at» x6 (leaf 1));
                                           «Base.bindO»
                                             («Base.bindO»
                                               («Prelude.nth»
                                                 («Language.gDefs» x0)
                                                 («Prelude.at» x6 (leaf 0)))
                                               «Language.defLanguage»)
                                             (fun (x13 : T) =>
                                               «Base.bindO»
                                                 («Base.allSomeT» («Language.cpAll» x7 x4 x5))
                                                 (fun (x14 : T) =>
                                                   let x15 : List T := Const.children x14;
                                                   if («Prelude.and»
                                                     (Const.eq
                                                       («Prelude.length» x12)
                                                       («Language.ldArity» x13))
                                                     («Prelude.and»
                                                       («Base.allT» («Language.isTy» x0 x1) x12)
                                                       («Base.equalTs»
                                                         («Base.mapT» «Language.p2» x15)
                                                         («Base.mapT»
                                                           («PartialHorn.phSubst» x12)
                                                           («Language.ldParams»
                                                             x13))))).label ≠ 0 then
                                                     «Prelude.some»
                                                       («Language.pr»
                                                         («Theory.comp»
                                                           («PartialHorn.phOp»
                                                             (Const.add
                                                               («Language.gBase» x0)
                                                               («Prelude.at» x6 (leaf 0)))
                                                             x12)
                                                           («Language.tuple»
                                                             x4
                                                             («Base.mapT» «Language.p1» x15)))
                                                         («PartialHorn.phSubst»
                                                           x12
                                                           («Language.ldType» x13)))
                                                   else
                                                     «Prelude.none»))
                                         else
                                           «Prelude.none»);
    x6

def «Language.compile» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T →
      List T →
        T := (Const.fold
      (α := T × (T → List T → T))
      (fun (x3 : T) (x4 : List (T × (T → List T → T))) =>
        (Const.node x3 («Language.cpTrees» x4),
          fun (x5 : T) (x6 : List T) =>
            «Language.compileStep» x0 x1 x3 x4 x5 x6))
      x2).2;
    x3

def «Language.ldCompile» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Base.bindO»
      («Language.compile»
        x0
        («Language.ldArity» x1)
        («Language.ldBody» x1)
        («Language.ctxObj» («Language.ldParams» x1))
        («Language.stdEnv» («Language.ldParams» x1)))
      (fun (x2 : T) =>
        if («Prelude.and»
          («Base.allT»
            («Language.isTy» x0 («Language.ldArity» x1))
            («Language.ldParams» x1))
          (Const.equal
            («Language.p2» x2)
            («Language.ldType» x1))).label ≠ 0 then
          «Prelude.some»
            («PartialHorn.pdefn»
              (Const.node
                (leaf 0)
                («Prelude.replicate» («Language.ldArity» x1) (leaf 0)))
              (leaf 1)
              («Language.p1» x2))
        else
          «Prelude.none»);
    x2

def «Language.defCompile» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); «Language.ldCompile» x0 x3
                   else
                     let x3 : T := Const.child x2 (leaf 0);
                     let x4 : T := Const.child x2 (leaf 1);
                     «Prelude.some»
                       («PartialHorn.pdefn»
                         (Const.node (leaf 0) («Prelude.replicate» x3 (leaf 0)))
                         (leaf 0)
                         x4));
    x2

def «Language.compileDefs» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : List T := «Language.gDefs» x0;
                   «Base.allSomeT»
                     («Base.mapT»
                       (fun (x2 : T) =>
                         «Language.defCompile»
                           («Language.globals»
                             (Const.node (leaf 0) («Language.gPrims» x0))
                             (Const.node (leaf 0) («Base.take» x2 x1))
                             («Language.gBase» x0))
                           («Prelude.at» x1 x2))
                       («Base.range» («Prelude.length» x1))));
    x1

def «Language.compileEq» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := «Base.bindO»
      («Language.compile»
        x0
        x1
        x3
        («Language.ctxObj» x2)
        («Language.stdEnv» x2))
      (fun (x5 : T) =>
        «Base.bindO»
          («Language.compile»
            x0
            x1
            x4
            («Language.ctxObj» x2)
            («Language.stdEnv» x2))
          (fun (x6 : T) =>
            if («Prelude.and»
              («Base.allT» («Language.isTy» x0 x1) x2)
              (Const.equal («Language.p2» x5) («Language.p2» x6))).label ≠ 0 then
              «Prelude.some»
                («PartialHorn.mkSeq»
                  («Prelude.replicate» x1 (leaf 0))
                  ([] : List T)
                  («PartialHorn.eqn» («Language.p1» x5) («Language.p1» x6)))
            else
              «Prelude.none»));
    x5

def «Language.primWf» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Language.prArity» x2;
                   «Prelude.and»
                     («PartialHorn.scoped» x3 («Language.prArrow» x2))
                     («Prelude.and»
                       («Language.isTy» x0 x3 («Language.prDom» x2))
                       («Prelude.and»
                         («Language.isTy» x0 x3 («Language.prCod» x2))
                         (Const.equal
                           («PartialHorn.sortOf»
                             x1
                             («Prelude.replicate» x3 (leaf 0))
                             («Language.prArrow» x2))
                           («Prelude.some» (leaf 1))))));
    x3

def «Language.primOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Language.primWf» x0 («Infer.envSg» x1) x2)
      (let x3 : T →
         T := («Infer.infers»
         x1
         («Prelude.replicate» («Language.prArity» x2) (leaf 0))
         ([] : List T)
         «Infer.inferFuel»).2;
       let x4 : T := x3 («Language.prArrow» x2);
       let x5 : T := x3 («Language.prDom» x2);
       let x6 : T := x3 («Language.prCod» x2);
       if («Prelude.and»
         («Prelude.isSome» x4)
         («Prelude.and»
           («Prelude.isSome» x5)
           («Prelude.isSome» x6))).label ≠ 0 then
         let x7 : T := «Prelude.get» x4;
         let x8 : T := «Prelude.get» x5;
         let x9 : T := «Prelude.get» x6;
         «Prelude.and»
           (Const.eq («Infer.annSort» x7) (leaf 1))
           («Prelude.and»
             (Const.eq («Infer.annSort» x8) (leaf 0))
             («Prelude.and»
               (Const.eq («Infer.annSort» x9) (leaf 0))
               («Prelude.and»
                 (Const.equal («Infer.annLo» x7) («Infer.annLo» x8))
                 (Const.equal («Infer.annHi» x7) («Infer.annLo» x9)))))
       else
         leaf 0);
    x3

def «Language.objOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      (Const.equal
        («PartialHorn.sortOf»
          («Infer.envSg» x0)
          («Prelude.replicate» x1 (leaf 0))
          x2)
        («Prelude.some» (leaf 0)))
      («Prelude.isSome»
        ((«Infer.infers»
          x0
          («Prelude.replicate» x1 (leaf 0))
          ([] : List T)
          «Infer.inferFuel»).2
          x2));
    x3

def «Derivation.copairIn» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «Theory.comp»
      («Theory.ev» x0 x3)
      («Theory.cPair»
        («Theory.comp»
          («Theory.copair»
            («Theory.curry»
              x1
              x0
              («Theory.comp»
                x4
                («Theory.cPair» («Theory.cSnd» x1 x0) («Theory.cFst» x1 x0))))
            («Theory.curry»
              x2
              x0
              («Theory.comp»
                x5
                («Theory.cPair» («Theory.cSnd» x2 x0) («Theory.cFst» x2 x0)))))
          («Theory.cSnd» x0 («Theory.coprod» x1 x2)))
        («Theory.cFst» x0 («Theory.coprod» x1 x2)));
    x6

def «Derivation.caseArr» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Theory.prod» («Theory.exp» x0 x2) («Theory.exp» x1 x2);
                   «Theory.curry»
                     x3
                     («Theory.coprod» x0 x1)
                     («Derivation.copairIn»
                       x3
                       x0
                       x1
                       x2
                       («Theory.comp»
                         («Theory.ev» x0 x2)
                         («Theory.cPair»
                           («Theory.comp»
                             («Theory.cFst» («Theory.exp» x0 x2) («Theory.exp» x1 x2))
                             («Theory.cFst» x3 x0))
                           («Theory.cSnd» x3 x0)))
                       («Theory.comp»
                         («Theory.ev» x1 x2)
                         («Theory.cPair»
                           («Theory.comp»
                             («Theory.cSnd» («Theory.exp» x0 x2) («Theory.exp» x1 x2))
                             («Theory.cFst» x3 x1))
                           («Theory.cSnd» x3 x1)))));
    x3

def «Derivation.zeroPrim» :=
  «Language.primitive» (leaf 0) «Theory.zeroN» «Theory.one» «Theory.nat»

def «Derivation.succPrim» :=
  «Language.primitive» (leaf 0) «Theory.succ» «Theory.nat» «Theory.nat»

def «Derivation.nilPrim» :=
  «Language.primitive»
    (leaf 1)
    («Theory.cNil» («Theory.x» (leaf 0)))
    «Theory.one»
    («Theory.list» («Theory.x» (leaf 0)))

def «Derivation.consPrim» :=
  «Language.primitive»
    (leaf 1)
    («Theory.cCons» («Theory.x» (leaf 0)))
    («Theory.prod»
      («Theory.x» (leaf 0))
      («Theory.list» («Theory.x» (leaf 0))))
    («Theory.list» («Theory.x» (leaf 0)))

def «Derivation.nodePrim» :=
  «Language.primitive»
    (leaf 0)
    «Theory.cNode»
    («Theory.prod» «Theory.nat» («Theory.list» «Theory.rose»))
    «Theory.rose»

def «Derivation.lnodePrim» :=
  «Language.primitive»
    (leaf 1)
    («Theory.lnode» («Theory.x» (leaf 0)))
    («Theory.prod»
      («Theory.x» (leaf 0))
      («Theory.list» («Theory.lrose» («Theory.x» (leaf 0)))))
    («Theory.lrose» («Theory.x» (leaf 0)))

def «Derivation.inlPrim» :=
  «Language.primitive»
    (leaf 2)
    («Theory.inl» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
    («Theory.x» (leaf 0))
    («Theory.coprod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))

def «Derivation.inrPrim» :=
  «Language.primitive»
    (leaf 2)
    («Theory.inr» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
    («Theory.x» (leaf 1))
    («Theory.coprod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))

def «Derivation.casePrim» :=
  «Language.primitive»
    (leaf 3)
    («Derivation.caseArr»
      («Theory.x» (leaf 0))
      («Theory.x» (leaf 1))
      («Theory.x» (leaf 2)))
    («Theory.prod»
      («Theory.exp» («Theory.x» (leaf 0)) («Theory.x» (leaf 2)))
      («Theory.exp» («Theory.x» (leaf 1)) («Theory.x» (leaf 2))))
    («Theory.exp»
      («Theory.coprod» («Theory.x» (leaf 0)) («Theory.x» (leaf 1)))
      («Theory.x» (leaf 2)))

def «Derivation.primIs» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := Const.equal
      («Prelude.nth» («Language.gPrims» x0) x1)
      («Prelude.some» x2);
    x3

def «Derivation.objVars» :=
  fun (x0 : T) =>
    let x1 : List T := «Base.mapT» «Theory.x» («Base.range» x0); x1

def «Derivation.isCoeqProj» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Language.prArrow» x0;
                   if (Const.eq (Const.arity x1) (leaf 2)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     let x3 : T := Const.child x1 (leaf 1);
                     if («Prelude.and»
                       (Const.eq (Const.arity x2) (leaf 2))
                       (Const.eq (Const.arity x3) (leaf 2))).label ≠ 0 then
                       «Prelude.and»
                         (Const.equal x1 («Theory.coeqProj» x2 x3))
                         («Prelude.and»
                           (Const.equal
                             x2
                             («Theory.comp» (Const.child x2 (leaf 0)) (Const.child x2 (leaf 1))))
                           (Const.equal
                             x3
                             («Theory.comp» (Const.child x3 (leaf 0)) (Const.child x3 (leaf 1)))))
                     else
                       leaf 0
                   else
                     leaf 0);
    x1

def «Derivation.relL» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Theory.comp»
      («Theory.cFst» x0 x0)
      («Theory.truthIncl» x1);
    x2

def «Derivation.relR» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Theory.comp»
      («Theory.cSnd» x0 x0)
      («Theory.truthIncl» x1);
    x2

def «Derivation.primRel» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Language.prArrow» x0;
                   if (Const.eq (Const.arity x1) (leaf 2)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0);
                     if (Const.eq (Const.arity x2) (leaf 2)).label ≠ 0 then
                       let x3 : T := Const.child x2 (leaf 1);
                       if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                         let x4 : T := Const.child x3 (leaf 0);
                         if (Const.equal
                           x1
                           («Theory.coeqProj»
                             («Derivation.relL» («Language.prDom» x0) x4)
                             («Derivation.relR» («Language.prDom» x0) x4))).label ≠ 0 then
                           «Prelude.some» x4
                         else
                           «Prelude.none»
                       else
                         «Prelude.none»
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x1

def «Derivation.instVar» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      x0
    else
      «Language.var» (Const.sub x1 (leaf 1)));
    x2

def «Derivation.atVar0» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x1 (leaf 0)).label ≠ 0 then
      x0
    else
      «Language.var» x1);
    x2

def «Derivation.natSuccAt» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Language.subst»
      x1
      («Derivation.atVar0»
        («Language.mArr» x0 ([] : List T) («Language.var» (leaf 0))));
    x2

def «Derivation.listConsAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.subst»
      x2
      (fun (x3 : T) =>
        if (Const.eq x3 (leaf 0)).label ≠ 0 then
          «Language.mArr»
            x0
            («Prelude.single» x1)
            («Language.mPair» («Language.var» (leaf 1)) («Language.var» (leaf 0)))
        else
          «Language.var» (Const.add x3 (leaf 1)));
    x3

def «Derivation.roseNodeAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Language.subst»
      x3
      («Derivation.instVar»
        («Language.mArr»
          x0
          (if (Const.equal x1 «Theory.rose»).label ≠ 0 then
            ([] : List T)
          else
            «Prelude.single» x2)
          («Language.mPair»
            («Language.var» (leaf 1))
            («Language.var» (leaf 0)))));
    x4

def «Derivation.weakenElem» :=
  fun (x0 : T) =>
    let x1 : T := «Language.rename»
      x0
      (fun (x1 : T) =>
        if (Const.eq x1 (leaf 0)).label ≠ 0 then
          leaf 0
        else
          Const.add x1 (leaf 1));
    x1

def «Derivation.weaken1» :=
  fun (x0 : T) =>
    let x1 : T := «Language.rename»
      x0
      (fun (x1 : T) => Const.add x1 (leaf 1));
    x1

def «Derivation.weaken2» :=
  fun (x0 : T) =>
    let x1 : T := «Language.rename»
      x0
      (fun (x1 : T) => Const.add x1 (leaf 2));
    x1

def «Derivation.lower1» :=
  fun (x0 : T) =>
    let x1 : T := «Language.rename»
      x0
      (fun (x1 : T) => Const.sub x1 (leaf 1));
    x1

def «Derivation.roseMapAt» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : T := «Language.mListRec»
      («Language.mArr» x0 («Prelude.single» x2) «Language.mStar»)
      («Language.mArr»
        x1
        («Prelude.single» x2)
        («Language.mPair»
          («Derivation.weaken1» x3)
          («Language.var» (leaf 0))))
      («Language.var» (leaf 0));
    x4

def «Derivation.roseHyp» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Language.mEq»
      («Derivation.roseMapAt» x0 x1 «Theory.omega» x2)
      («Derivation.roseMapAt»
        x0
        x1
        «Theory.omega»
        («Language.mEq» «Language.mStar» «Language.mStar»));
    x3

def «Derivation.eqParts» :=
  fun (x0 : T) =>
    let x1 : T := (if («Language.mIs»
      (leaf 12)
      (leaf 2)
      x0).label ≠ 0 then
      «Prelude.some»
        («Language.pr»
          («Language.mArg» x0 (leaf 0))
          («Language.mArg» x0 (leaf 1)))
    else
      «Prelude.none»);
    x1

def «Derivation.instTerm» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := «Language.subst»
      («Language.osubst» x0 x2)
      («Language.substList» x1);
    x3

def «Derivation.typeIn» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := «Base.mapO»
      «Language.p2»
      («Language.compile»
        x0
        x1
        x3
        («Language.ctxObj» x2)
        («Language.stdEnv» x2));
    x4

def «Derivation.isFormula» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := Const.equal
      («Derivation.typeIn» x0 x1 x2 x3)
      («Prelude.some» «Theory.omega»);
    x4

def «Derivation.lowerHyps» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Base.allSomeT»
      («Base.mapT»
        (fun (x4 : T) =>
          let x5 : T := «Derivation.lower1» x4;
          if («Prelude.and»
            (Const.equal («Derivation.weaken1» x5) x4)
            («Derivation.isFormula» x0 x1 x2 x5)).label ≠ 0 then
            «Prelude.some» x5
          else
            «Prelude.none»)
        x3);
    x4

def «Derivation.mkThm» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Derivation.thArity» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let x2 : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let _ : T := Const.child x1 (leaf 3); x2);
    x1

def «Derivation.thCtx» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let x3 : T := Const.child x1 (leaf 1);
            let _ : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3); Const.children x3);
    x1

def «Derivation.thHyps» :=
  fun (x0 : T) =>
    let x1 : List
      T := (let x1 : T := x0;
            let _ : T := Const.child x1 (leaf 0);
            let _ : T := Const.child x1 (leaf 1);
            let x4 : T := Const.child x1 (leaf 2);
            let _ : T := Const.child x1 (leaf 3); Const.children x4);
    x1

def «Derivation.thConcl» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   let _ : T := Const.child x1 (leaf 0);
                   let _ : T := Const.child x1 (leaf 1);
                   let _ : T := Const.child x1 (leaf 2);
                   let x5 : T := Const.child x1 (leaf 3); x5);
    x1

def «Derivation.instOk» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := «Prelude.and»
      (Const.eq («Prelude.length» x4) («Derivation.thArity» x3))
      («Prelude.and»
        («Base.allT» («Language.isTy» x0 x1) x4)
        («Prelude.and»
          (Const.eq
            («Prelude.length» x5)
            («Prelude.length» («Derivation.thCtx» x3)))
          («Base.allT»
            (fun (x6 : T) =>
              Const.equal
                («Derivation.typeIn» x0 x1 x2 («Prelude.at» x5 x6))
                («Prelude.some»
                  («PartialHorn.phSubst» x4 («Prelude.at» («Derivation.thCtx» x3) x6))))
            («Base.range» («Prelude.length» x5)))));
    x6

def «Derivation.truthSub» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x2 : T) (x3 : T) =>
        let x4 : T := «Theory.comp» x2 («Language.p2» x3);
        «Language.pr»
          («Theory.truthEq» x4)
          («Theory.comp» («Language.p2» x3) («Theory.truthIncl» x4)))
      («Language.pr» x0 («Theory.idt» x0))
      («Prelude.reverse» x1);
    x2

def «Derivation.thmArrow» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Base.getD»
      («Base.mapO»
        «Language.p1»
        («Language.compile»
          x0
          («Derivation.thArity» x1)
          x2
          («Language.ctxObj» («Derivation.thCtx» x1))
          («Language.stdEnv» («Derivation.thCtx» x1))))
      («Theory.idt» («Language.ctxObj» («Derivation.thCtx» x1)));
    x3

def «Derivation.thmSide» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (if («Base.isEmpty»
      («Derivation.thHyps» x1)).label ≠ 0 then
      x2
    else
      «Theory.comp»
        x2
        («Language.p2»
          («Derivation.truthSub»
            («Language.ctxObj» («Derivation.thCtx» x1))
            («Base.mapT»
              («Derivation.thmArrow» x0 x1)
              («Derivation.thHyps» x1)))));
    x3

def «Derivation.thmSeq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Derivation.eqParts» («Derivation.thConcl» x1);
                   «PartialHorn.mkSeq»
                     («Prelude.replicate» («Derivation.thArity» x1) (leaf 0))
                     ([] : List T)
                     (if («Prelude.isSome» x2).label ≠ 0 then
                       «PartialHorn.eqn»
                         («Derivation.thmSide»
                           x0
                           x1
                           («Derivation.thmArrow» x0 x1 («Language.p1» («Prelude.get» x2))))
                         («Derivation.thmSide»
                           x0
                           x1
                           («Derivation.thmArrow» x0 x1 («Language.p2» («Prelude.get» x2))))
                     else
                       «PartialHorn.eqn»
                         («Derivation.thmSide»
                           x0
                           x1
                           («Derivation.thmArrow» x0 x1 («Derivation.thConcl» x1)))
                         («Derivation.thmSide»
                           x0
                           x1
                           («Theory.comp»
                             «Theory.tru»
                             («Theory.bang» («Language.ctxObj» («Derivation.thCtx» x1)))))));
    x2

def «Derivation.entLang» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Derivation.entComb» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Derivation.entryLanguage» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := x0;
                   if (Const.eq (Const.label x1) (leaf 0)).label ≠ 0 then
                     let x2 : T := Const.child x1 (leaf 0); «Prelude.some» x2
                   else
                     let _ : T := Const.child x1 (leaf 0); «Prelude.none»);
    x1

def «Derivation.entrySeq» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := x1;
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let x3 : T := Const.child x2 (leaf 0); «Derivation.thmSeq» x0 x3
                   else
                     let x3 : T := Const.child x2 (leaf 0); x3);
    x2

def «Derivation.anyDefs» :=
  fun (x0 : T) (x1 : List T → T) =>
    let x2 : T := (let x2 : T := «Language.compileDefs» x0;
                   if («Prelude.isSome» x2).label ≠ 0 then
                     x1 (Const.children («Prelude.get» x2))
                   else
                     leaf 0);
    x2

def «Derivation.certifies» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := «Derivation.anyDefs»
      x0
      (fun (x4 : List T) =>
        if (Const.eq
          («Language.gBase» x0)
          («Prelude.length» «Theory.sig»)).label ≠ 0 then
          Const.equal
            («PartialHorn.pcheck»
              («Infer.ext» x4)
              («Base.mapT» («Derivation.entrySeq» x0) x1)
              x2
              («PartialHorn.seqCtx» x3)
              («PartialHorn.seqHyps» x3))
            («Prelude.some» («PartialHorn.seqConcl» x3))
        else
          leaf 0);
    x4

def «Derivation.ctxPair» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := «Language.pr»
      (Const.node (leaf 0) x0)
      (Const.node (leaf 0) x1);
    x2

def «Derivation.childCtxs» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) (x4 : List T) =>
    let x5 : T := (let x5 : T := Const.label x2;
                   let x6 : List T := «Language.mArgs» x2;
                   let x7 : T := «Prelude.length» x6;
                   if («Prelude.and»
                     (Const.eq x5 (leaf 5))
                     (Const.eq x7 (leaf 1))).label ≠ 0 then
                     «Prelude.some»
                       (Const.node
                         (leaf 0)
                         («Prelude.single»
                           («Derivation.ctxPair»
                             ((«Language.mD» x2 (leaf 0)) :: x3)
                             («Base.mapT» «Derivation.weaken1» x4))))
                   else
                     if («Prelude.and»
                       (Const.eq x5 (leaf 8))
                       (Const.eq x7 (leaf 3))).label ≠ 0 then
                       «Base.bindO»
                         («Derivation.typeIn» x0 x1 ([] : List T) («Prelude.at» x6 (leaf 0)))
                         (fun (x8 : T) =>
                           «Prelude.some»
                             (Const.node
                               (leaf 0)
                               («Theory.l3»
                                 («Derivation.ctxPair» ([] : List T) ([] : List T))
                                 («Derivation.ctxPair» («Prelude.single» x8) ([] : List T))
                                 («Derivation.ctxPair» x3 x4))))
                     else
                       if («Prelude.and»
                         (Const.eq x5 (leaf 9))
                         (Const.eq x7 (leaf 3))).label ≠ 0 then
                         «Base.bindO»
                           («Derivation.typeIn» x0 x1 ([] : List T) («Prelude.at» x6 (leaf 0)))
                           (fun (x8 : T) =>
                             «Base.bindO»
                               («Base.bindO»
                                 («Derivation.typeIn» x0 x1 x3 («Prelude.at» x6 (leaf 2)))
                                 «Language.listPart»)
                               (fun (x9 : T) =>
                                 «Prelude.some»
                                   (Const.node
                                     (leaf 0)
                                     («Theory.l3»
                                       («Derivation.ctxPair» ([] : List T) ([] : List T))
                                       («Derivation.ctxPair» («Theory.l2» x8 x9) ([] : List T))
                                       («Derivation.ctxPair» x3 x4)))))
                       else
                         if («Prelude.and»
                           (Const.eq x5 (leaf 10))
                           (Const.eq x7 (leaf 2))).label ≠ 0 then
                           «Base.bindO»
                             («Base.bindO»
                               («Derivation.typeIn» x0 x1 x3 («Prelude.at» x6 (leaf 1)))
                               «Language.roseLabel»)
                             (fun (x8 : T) =>
                               «Prelude.some»
                                 (Const.node
                                   (leaf 0)
                                   («Theory.l2»
                                     («Derivation.ctxPair»
                                       («Prelude.single»
                                         («Theory.prod»
                                           x8
                                           («Theory.list» («Language.mD» x2 (leaf 0)))))
                                       ([] : List T))
                                     («Derivation.ctxPair» x3 x4))))
                         else
                           «Prelude.some»
                             (Const.node
                               (leaf 0)
                               («Base.mapT» (fun (_ : T) => «Derivation.ctxPair» x3 x4) x6)));
    x5

def «Derivation.sameCtx» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq x0 (leaf 5)).label ≠ 0 then
      leaf 0
    else
      if («Prelude.or»
        (Const.eq x0 (leaf 8))
        (Const.eq x0 (leaf 9))).label ≠ 0 then
        Const.eq x1 (leaf 2)
      else
        if (Const.eq x0 (leaf 10)).label ≠ 0 then
          Const.eq x1 (leaf 1)
        else
          leaf 1);
    x2

def «Derivation.congCtxs» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := (if («Base.allT»
      (fun (x6 : T) =>
        «Prelude.or»
          («Derivation.sameCtx» (Const.label x2) x6)
          (Const.eq (Const.label («Prelude.at» x5 x6)) (leaf 0)))
      («Base.range» («Prelude.length» x5))).label ≠ 0 then
      «Prelude.some»
        (Const.node
          (leaf 0)
          («Base.mapT»
            (fun (_ : T) => «Derivation.ctxPair» x3 x4)
            («Language.mArgs» x2)))
    else
      «Derivation.childCtxs» x0 x1 x2 x3 x4);
    x6

def «Derivation.rootBeta» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Language.mArg» x0 (leaf 0);
                   if («Prelude.and»
                     («Language.mIs» (leaf 6) (leaf 2) x0)
                     («Language.mIs» (leaf 5) (leaf 1) x1)).label ≠ 0 then
                     «Prelude.some»
                       («Language.subst»
                         («Language.mArg» x1 (leaf 0))
                         («Derivation.instVar» («Language.mArg» x0 (leaf 1))))
                   else
                     «Prelude.none»);
    x1

def «Derivation.rootFst» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Language.mArg» x0 (leaf 0);
                   if («Prelude.and»
                     («Language.mIs» (leaf 3) (leaf 1) x0)
                     («Language.mIs» (leaf 2) (leaf 2) x1)).label ≠ 0 then
                     «Prelude.some» («Language.mArg» x1 (leaf 0))
                   else
                     «Prelude.none»);
    x1

def «Derivation.rootSnd» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Language.mArg» x0 (leaf 0);
                   if («Prelude.and»
                     («Language.mIs» (leaf 4) (leaf 1) x0)
                     («Language.mIs» (leaf 2) (leaf 2) x1)).label ≠ 0 then
                     «Prelude.some» («Language.mArg» x1 (leaf 1))
                   else
                     «Prelude.none»);
    x1

def «Derivation.rootPairEta» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Language.mArg» x0 (leaf 0);
                   let x2 : T := «Language.mArg» x0 (leaf 1);
                   if («Prelude.and»
                     («Language.mIs» (leaf 2) (leaf 2) x0)
                     («Prelude.and»
                       («Language.mIs» (leaf 3) (leaf 1) x1)
                       («Language.mIs» (leaf 4) (leaf 1) x2))).label ≠ 0 then
                     if (Const.equal
                       («Language.mArg» x1 (leaf 0))
                       («Language.mArg» x2 (leaf 0))).label ≠ 0 then
                       «Prelude.some» («Language.mArg» x1 (leaf 0))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x1

def «Derivation.rootUnitEta» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := (if (Const.equal
      («Derivation.typeIn» x0 x1 x2 x3)
      («Prelude.some» «Theory.one»)).label ≠ 0 then
      «Prelude.some» «Language.mStar»
    else
      «Prelude.none»);
    x4

def «Derivation.rootDelta» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (if (Const.eq (Const.label x1) (leaf 11)).label ≠ 0 then
      «Base.mapO»
        (fun (x2 : T) =>
          «Language.subst»
            («Language.osubst»
              (Const.children («Language.mD» x1 (leaf 1)))
              («Language.ldBody» x2))
            («Language.substList» («Language.mArgs» x1)))
        («Base.bindO»
          («Prelude.nth» («Language.gDefs» x0) («Language.mD» x1 (leaf 0)))
          «Language.defLanguage»)
    else
      «Prelude.none»);
    x2

def «Derivation.rootNat» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Language.mArg» x3 (leaf 0);
                   let x5 : T := «Language.mArg» x3 (leaf 1);
                   let x6 : T := «Language.mArg» x3 (leaf 2);
                   if («Prelude.and»
                     («Language.mIs» (leaf 8) (leaf 3) x3)
                     («Prelude.and»
                       («Language.mIs» (leaf 7) (leaf 1) x6)
                       (Const.eq
                         (Const.arity («Language.mD» x6 (leaf 1)))
                         (leaf 0)))).label ≠ 0 then
                     let x7 : T := «Prelude.at» x2 (leaf 0);
                     if (Const.eq x1 (leaf 9)).label ≠ 0 then
                       if («Prelude.and»
                         (Const.eq («Language.mD» x6 (leaf 0)) x7)
                         («Prelude.and»
                           («Derivation.primIs» x0 x7 «Derivation.zeroPrim»)
                           (Const.equal
                             («Language.mArg» x6 (leaf 0))
                             «Language.mStar»))).label ≠ 0 then
                         «Prelude.some» x4
                       else
                         «Prelude.none»
                     else
                       if («Prelude.and»
                         (Const.eq («Language.mD» x6 (leaf 0)) x7)
                         («Derivation.primIs» x0 x7 «Derivation.succPrim»)).label ≠ 0 then
                         «Prelude.some»
                           («Language.subst»
                             x5
                             («Derivation.instVar»
                               («Language.mNatRec» x4 x5 («Language.mArg» x6 (leaf 0)))))
                       else
                         «Prelude.none»
                   else
                     «Prelude.none»);
    x4

def «Derivation.rootListNil» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Language.mArg» x2 (leaf 2);
                   if («Prelude.and»
                     («Language.mIs» (leaf 9) (leaf 3) x2)
                     («Prelude.and»
                       («Language.mIs» (leaf 7) (leaf 1) x3)
                       (Const.eq
                         (Const.arity («Language.mD» x3 (leaf 1)))
                         (leaf 1)))).label ≠ 0 then
                     let x4 : T := «Prelude.at» x1 (leaf 0);
                     if («Prelude.and»
                       (Const.eq («Language.mD» x3 (leaf 0)) x4)
                       («Prelude.and»
                         («Derivation.primIs» x0 x4 «Derivation.nilPrim»)
                         (Const.equal
                           («Language.mArg» x3 (leaf 0))
                           «Language.mStar»))).label ≠ 0 then
                       «Prelude.some» («Language.mArg» x2 (leaf 0))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x3

def «Derivation.rootListCons» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Language.mArg» x2 (leaf 2);
                   if («Prelude.and»
                     («Language.mIs» (leaf 9) (leaf 3) x2)
                     («Prelude.and»
                       («Language.mIs» (leaf 7) (leaf 1) x3)
                       (Const.eq
                         (Const.arity («Language.mD» x3 (leaf 1)))
                         (leaf 1)))).label ≠ 0 then
                     let x4 : T := «Language.mArg» x3 (leaf 0);
                     let x5 : T := «Prelude.at» x1 (leaf 0);
                     if («Prelude.and»
                       («Language.mIs» (leaf 2) (leaf 2) x4)
                       («Prelude.and»
                         (Const.eq («Language.mD» x3 (leaf 0)) x5)
                         («Derivation.primIs» x0 x5 «Derivation.consPrim»))).label ≠ 0 then
                       «Prelude.some»
                         («Language.subst»
                           («Language.mArg» x2 (leaf 1))
                           («Language.substList»
                             («Theory.l2»
                               («Language.mListRec»
                                 («Language.mArg» x2 (leaf 0))
                                 («Language.mArg» x2 (leaf 1))
                                 («Language.mArg» x4 (leaf 1)))
                               («Language.mArg» x4 (leaf 0)))))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x3

def «Derivation.rootRoseNode» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Language.mArg» x2 (leaf 0);
                   let x4 : T := «Language.mArg» x2 (leaf 1);
                   if («Prelude.and»
                     («Language.mIs» (leaf 10) (leaf 2) x2)
                     («Language.mIs» (leaf 7) (leaf 1) x4)).label ≠ 0 then
                     let x5 : T := «Language.mArg» x4 (leaf 0);
                     let x6 : T := «Prelude.at» x1 (leaf 0);
                     let x7 : T := «Prelude.at» x1 (leaf 1);
                     let x8 : T := «Prelude.at» x1 (leaf 2);
                     let x9 : T := «Language.mD» x2 (leaf 0);
                     if («Prelude.and»
                       («Language.mIs» (leaf 2) (leaf 2) x5)
                       («Prelude.and»
                         (Const.eq («Language.mD» x4 (leaf 0)) x6)
                         («Prelude.and»
                           («Prelude.or»
                             («Derivation.primIs» x0 x6 «Derivation.nodePrim»)
                             («Derivation.primIs» x0 x6 «Derivation.lnodePrim»))
                           («Prelude.and»
                             («Derivation.primIs» x0 x7 «Derivation.nilPrim»)
                             («Derivation.primIs» x0 x8 «Derivation.consPrim»))))).label ≠ 0 then
                       «Prelude.some»
                         («Language.subst»
                           x3
                           («Derivation.instVar»
                             («Language.mPair»
                               («Language.mArg» x5 (leaf 0))
                               («Language.mListRec»
                                 («Language.mArr» x7 («Prelude.single» x9) «Language.mStar»)
                                 («Language.mArr»
                                   x8
                                   («Prelude.single» x9)
                                   («Language.mPair»
                                     («Language.mRoseRec» x9 x3 («Language.var» (leaf 1)))
                                     («Language.var» (leaf 0))))
                                 («Language.mArg» x5 (leaf 1))))))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x3

def «Derivation.rootCase» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : List T) (x4 : T) =>
    let x5 : T := (let x5 : T := «Language.mArg» x4 (leaf 0);
                   let x6 : T := «Language.mArg» x4 (leaf 1);
                   if («Prelude.and»
                     («Language.mIs» (leaf 6) (leaf 2) x4)
                     («Prelude.and»
                       («Language.mIs» (leaf 7) (leaf 1) x5)
                       («Language.mIs» (leaf 7) (leaf 1) x6))).label ≠ 0 then
                     let x7 : T := «Language.mArg» x5 (leaf 0);
                     let x8 : T := «Prelude.at» x3 (leaf 0);
                     let x9 : T := «Prelude.at» x3 (leaf 1);
                     if («Prelude.and»
                       («Language.mIs» (leaf 2) (leaf 2) x7)
                       («Prelude.and»
                         (Const.eq («Language.mD» x5 (leaf 0)) x8)
                         («Prelude.and»
                           (Const.eq («Language.mD» x6 (leaf 0)) x9)
                           («Prelude.and»
                             («Derivation.primIs» x0 x8 «Derivation.casePrim»)
                             («Derivation.primIs» x0 x9 x1))))).label ≠ 0 then
                       «Prelude.some»
                         («Language.app» («Language.mArg» x7 x2) («Language.mArg» x6 (leaf 0)))
                     else
                       «Prelude.none»
                   else
                     «Prelude.none»);
    x5

def «Derivation.rootThm» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (let x6 : List T := Const.children («Prelude.at» x4 (leaf 1));
                   let x7 : List T := Const.children («Prelude.at» x4 (leaf 2));
                   let x8 : T := «Prelude.at» x4 (leaf 3);
                   «Base.bindO»
                     («Base.bindO»
                       («Prelude.nth» x1 («Prelude.at» x4 (leaf 0)))
                       «Derivation.entryLanguage»)
                     (fun (x9 : T) =>
                       «Base.bindO»
                         (if («Base.isEmpty» («Derivation.thHyps» x9)).label ≠ 0 then
                           «Derivation.eqParts» («Derivation.thConcl» x9)
                         else
                           «Prelude.none»)
                         (fun (x10 : T) =>
                           if («Prelude.and»
                             («Derivation.instOk» x0 x2 x3 x9 x6 x7)
                             (Const.equal
                               x5
                               («Derivation.instTerm»
                                 x6
                                 x7
                                 (if (x8).label ≠ 0 then
                                   «Language.p2» x10
                                 else
                                   «Language.p1» x10)))).label ≠ 0 then
                             «Prelude.some»
                               («Derivation.instTerm»
                                 x6
                                 x7
                                 (if (x8).label ≠ 0 then «Language.p1» x10 else «Language.p2» x10))
                           else
                             «Prelude.none»)));
    x6

def «Derivation.rootHyp» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Prelude.at» x1 (leaf 1);
                   «Base.bindO»
                     («Base.bindO»
                       («Prelude.nth» x0 («Prelude.at» x1 (leaf 0)))
                       «Derivation.eqParts»)
                     (fun (x4 : T) =>
                       if (Const.equal
                         x2
                         (if (x3).label ≠ 0 then
                           «Language.p2» x4
                         else
                           «Language.p1» x4)).label ≠ 0 then
                         «Prelude.some»
                           (if (x3).label ≠ 0 then «Language.p1» x4 else «Language.p2» x4)
                       else
                         «Prelude.none»));
    x3

def «Derivation.rootStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List T)
    (x7 : T) =>
    let x8 : T := (if (Const.eq x5 (leaf 3)).label ≠ 0 then
      «Derivation.rootBeta» x7
    else
      if (Const.eq x5 (leaf 4)).label ≠ 0 then
        «Derivation.rootFst» x7
      else
        if (Const.eq x5 (leaf 5)).label ≠ 0 then
          «Derivation.rootSnd» x7
        else
          if (Const.eq x5 (leaf 6)).label ≠ 0 then
            «Derivation.rootPairEta» x7
          else
            if (Const.eq x5 (leaf 7)).label ≠ 0 then
              «Derivation.rootUnitEta» x0 x2 x3 x7
            else
              if (Const.eq x5 (leaf 8)).label ≠ 0 then
                «Derivation.rootDelta» x0 x7
              else
                if («Prelude.or»
                  (Const.eq x5 (leaf 9))
                  (Const.eq x5 (leaf 10))).label ≠ 0 then
                  «Derivation.rootNat» x0 x5 x6 x7
                else
                  if (Const.eq x5 (leaf 11)).label ≠ 0 then
                    «Derivation.rootListNil» x0 x6 x7
                  else
                    if (Const.eq x5 (leaf 12)).label ≠ 0 then
                      «Derivation.rootListCons» x0 x6 x7
                    else
                      if (Const.eq x5 (leaf 13)).label ≠ 0 then
                        «Derivation.rootRoseNode» x0 x6 x7
                      else
                        if (Const.eq x5 (leaf 14)).label ≠ 0 then
                          «Derivation.rootCase» x0 «Derivation.inlPrim» (leaf 0) x6 x7
                        else
                          if (Const.eq x5 (leaf 15)).label ≠ 0 then
                            «Derivation.rootCase» x0 «Derivation.inrPrim» (leaf 1) x6 x7
                          else
                            if (Const.eq x5 (leaf 16)).label ≠ 0 then
                              «Derivation.rootThm» x0 x1 x2 x3 x6 x7
                            else
                              if (Const.eq x5 (leaf 17)).label ≠ 0 then
                                «Derivation.rootHyp» x4 x6 x7
                              else
                                «Prelude.none»);
    x8

def «Derivation.dpTrees» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
    let x1 : List
      T := Const.foldr
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (β := List T)
      (fun (x1 : T × ((List T → List T → T → T) × (List T → List T → T → T)))
         (x2 : List T) =>
        ((x1).1 :: x2))
      ([] : List T)
      x0;
    x1

def «Derivation/DPs.tail» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
    Const.lcase
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (β := List
        (T × ((List T → List T → T → T) × (List T → List T → T → T))))
      x0
      ([] : List (T ×
        ((List T → List T → T → T) × (List T → List T → T → T))))
      (fun (_ : T × ((List T → List T → T → T) × (List T → List T → T → T)))
         (x2 : List
           (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
        x2)

def «Derivation.dpAt» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x1 : T) =>
    let x2 : (List T → List T → T → T) ×
      (List T →
        List T →
          T →
            T) := Const.lcase
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (β := (List T → List T → T → T) × (List T → List T → T → T))
      (Const.iter
        (α := List
          (T × ((List T → List T → T → T) × (List T → List T → T → T))))
        «Derivation/DPs.tail»
        x0
        x1)
      (fun (_ : List T) (_ : List T) (_ : T) => «Prelude.none»,
        fun (_ : List T) (_ : List T) (_ : T) => leaf 0)
      (fun (x2 : T × ((List T → List T → T → T) × (List T → List T → T → T)))
         (_ : List
           (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
        (x2).2);
    x2

def «Derivation.rw» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x1 : T) =>
    let x2 : List T → List T → T → T := («Derivation.dpAt» x0 x1).1; x2

def «Derivation.pf» :=
  fun (x0 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x1 : T) =>
    let x2 : List T → List T → T → T := («Derivation.dpAt» x0 x1).2; x2

def «Derivation.rewriteStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T)
    (x6 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x7 : List T)
    (x8 : List T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «Prelude.length» x5;
                    if («Prelude.and»
                      (Const.eq x3 (leaf 0))
                      (Const.eq x10 (leaf 0))).label ≠ 0 then
                      «Prelude.some» x9
                    else
                      if («Prelude.and»
                        (Const.eq x3 (leaf 1))
                        (Const.eq x10 (leaf 2))).label ≠ 0 then
                        «Base.bindO»
                          («Derivation.rw» x6 (leaf 0) x7 x8 x9)
                          («Derivation.rw» x6 (leaf 1) x7 x8)
                      else
                        if (Const.eq x3 (leaf 2)).label ≠ 0 then
                          «Base.bindO»
                            («Derivation.congCtxs» x0 x2 x9 x7 x8 x5)
                            (fun (x11 : T) =>
                              let x12 : List T := Const.children x11;
                              let x13 : List T := «Language.mArgs» x9;
                              if («Prelude.and»
                                (Const.eq x10 («Prelude.length» x13))
                                (Const.eq
                                  («Prelude.length» x12)
                                  («Prelude.length» x13))).label ≠ 0 then
                                «Base.mapO»
                                  (fun (x14 : T) =>
                                    Const.node
                                      (Const.label x9)
                                      ((Const.child x9 (leaf 0)) :: (Const.children x14)))
                                  («Base.allSomeT»
                                    («Base.mapT»
                                      (fun (x14 : T) =>
                                        let x15 : T := «Prelude.at» x12 x14;
                                        «Derivation.rw»
                                          x6
                                          x14
                                          (Const.children («Language.p1» x15))
                                          (Const.children («Language.p2» x15))
                                          («Prelude.at» x13 x14))
                                      («Base.range» x10)))
                              else
                                «Prelude.none»)
                        else
                          if (Const.eq x10 (leaf 0)).label ≠ 0 then
                            «Derivation.rootStep» x0 x1 x2 x7 x8 x3 x4 x9
                          else
                            «Prelude.none»);
    x10

def «Derivation.rosePrimsOk» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «Prelude.and»
      («Prelude.or»
        («Prelude.and»
          («Derivation.primIs» x0 x1 «Derivation.nodePrim»)
          (Const.equal x4 «Theory.rose»))
        («Prelude.and»
          («Derivation.primIs» x0 x1 «Derivation.lnodePrim»)
          (Const.equal x4 («Theory.lrose» x5))))
      («Prelude.and»
        («Derivation.primIs» x0 x2 «Derivation.nilPrim»)
        («Derivation.primIs» x0 x3 «Derivation.consPrim»));
    x6

def «Derivation.proveStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : T)
    (x3 : T)
    (x4 : List T)
    (x5 : List T)
    (x6 : List
      (T × ((List T → List T → T → T) × (List T → List T → T → T))))
    (x7 : List T)
    (x8 : List T)
    (x9 : T) =>
    let x10 : T := (let x10 : T := «Prelude.length» x5;
                    let x11 : T := «Derivation.eqParts» x9;
                    let x12 : T := «Language.p1» («Prelude.get» x11);
                    let x13 : T := «Language.p2» («Prelude.get» x11);
                    let x14 : T := «Prelude.at» x4 (leaf 0);
                    let x15 : T := «Prelude.at» x4 (leaf 1);
                    if («Prelude.and»
                      (Const.eq x3 (leaf 18))
                      (Const.eq x10 (leaf 2))).label ≠ 0 then
                      if («Prelude.isSome» x11).label ≠ 0 then
                        let x16 : T := «Derivation.rw» x6 (leaf 0) x7 x8 x12;
                        let x17 : T := «Derivation.rw» x6 (leaf 1) x7 x8 x13;
                        «Prelude.and»
                          («Prelude.isSome» x16)
                          («Prelude.and»
                            («Prelude.isSome» x17)
                            (Const.equal («Prelude.get» x16) («Prelude.get» x17)))
                      else
                        leaf 0
                    else
                      if («Prelude.and»
                        (Const.eq x3 (leaf 19))
                        (Const.eq x10 (leaf 3))).label ≠ 0 then
                        if («Prelude.and»
                          («Prelude.isSome» x11)
                          («Base.not» («Base.isEmpty» x7))).label ≠ 0 then
                          let x16 : T := «Prelude.at» x7 (leaf 0);
                          let x17 : List T := «Prelude.tail» x7;
                          let x18 : T := «Prelude.at» x4 (leaf 2);
                          let x19 : T := «Derivation.typeIn» x0 x2 x7 x12;
                          let x20 : T := «Derivation.lowerHyps» x0 x2 x17 x8;
                          if («Prelude.and»
                            («Prelude.isSome» x19)
                            («Prelude.isSome» x20)).label ≠ 0 then
                            let x21 : T := «Prelude.get» x19;
                            let x22 : T := «Language.mArr» x14 ([] : List T) «Language.mStar»;
                            if («Prelude.and»
                              (Const.equal x16 «Theory.nat»)
                              («Prelude.and»
                                («Derivation.primIs» x0 x14 «Derivation.zeroPrim»)
                                («Prelude.and»
                                  («Derivation.primIs» x0 x15 «Derivation.succPrim»)
                                  («Prelude.and»
                                    (Const.equal
                                      («Derivation.typeIn» x0 x2 x7 x13)
                                      («Prelude.some» x21))
                                    (Const.equal
                                      («Derivation.typeIn» x0 x2 (x21 :: x17) x18)
                                      («Prelude.some» x21)))))).label ≠ 0 then
                              if («Derivation.pf»
                                x6
                                (leaf 0)
                                x17
                                (Const.children («Prelude.get» x20))
                                («Language.mEq»
                                  («Language.subst» x12 («Derivation.instVar» x22))
                                  («Language.subst» x13 («Derivation.instVar» x22)))).label ≠ 0 then
                                if («Derivation.pf»
                                  x6
                                  (leaf 1)
                                  x7
                                  x8
                                  («Language.mEq»
                                    («Derivation.natSuccAt» x15 x12)
                                    («Language.subst»
                                      x18
                                      («Derivation.atVar0» x12)))).label ≠ 0 then
                                  «Derivation.pf»
                                    x6
                                    (leaf 2)
                                    x7
                                    x8
                                    («Language.mEq»
                                      («Derivation.natSuccAt» x15 x13)
                                      («Language.subst» x18 («Derivation.atVar0» x13)))
                                else
                                  leaf 0
                              else
                                leaf 0
                            else
                              leaf 0
                          else
                            leaf 0
                        else
                          leaf 0
                      else
                        if («Prelude.and»
                          (Const.eq x3 (leaf 20))
                          (Const.eq x10 (leaf 3))).label ≠ 0 then
                          if («Prelude.and»
                            («Prelude.isSome» x11)
                            («Base.not» («Base.isEmpty» x7))).label ≠ 0 then
                            let x16 : T := «Prelude.at» x7 (leaf 0);
                            let x17 : List T := «Prelude.tail» x7;
                            let x18 : T := «Prelude.at» x4 (leaf 2);
                            let x19 : T := «Derivation.typeIn» x0 x2 x7 x12;
                            let x20 : T := «Language.listPart» x16;
                            let x21 : T := «Derivation.lowerHyps» x0 x2 x17 x8;
                            if («Prelude.and»
                              («Prelude.isSome» x19)
                              («Prelude.and»
                                («Prelude.isSome» x20)
                                («Prelude.isSome» x21))).label ≠ 0 then
                              let x22 : T := «Prelude.get» x19;
                              let x23 : T := «Prelude.get» x20;
                              let x24 : List T := (x16 :: (x23 :: x17));
                              let x25 : List
                                T := «Base.mapT»
                                «Derivation.weaken2»
                                (Const.children («Prelude.get» x21));
                              let x26 : T := «Language.mArr»
                                x14
                                («Prelude.single» x23)
                                «Language.mStar»;
                              if («Prelude.and»
                                («Derivation.primIs» x0 x14 «Derivation.nilPrim»)
                                («Prelude.and»
                                  («Derivation.primIs» x0 x15 «Derivation.consPrim»)
                                  («Prelude.and»
                                    (Const.equal
                                      («Derivation.typeIn» x0 x2 x7 x13)
                                      («Prelude.some» x22))
                                    (Const.equal
                                      («Derivation.typeIn» x0 x2 (x22 :: (x23 :: x17)) x18)
                                      («Prelude.some» x22))))).label ≠ 0 then
                                if («Derivation.pf»
                                  x6
                                  (leaf 0)
                                  x17
                                  (Const.children («Prelude.get» x21))
                                  («Language.mEq»
                                    («Language.subst» x12 («Derivation.instVar» x26))
                                    («Language.subst»
                                      x13
                                      («Derivation.instVar» x26)))).label ≠ 0 then
                                  if («Derivation.pf»
                                    x6
                                    (leaf 1)
                                    x24
                                    x25
                                    («Language.mEq»
                                      («Derivation.listConsAt» x15 x23 x12)
                                      («Language.subst»
                                        x18
                                        («Derivation.atVar0»
                                          («Derivation.weakenElem» x12))))).label ≠ 0 then
                                    «Derivation.pf»
                                      x6
                                      (leaf 2)
                                      x24
                                      x25
                                      («Language.mEq»
                                        («Derivation.listConsAt» x15 x23 x13)
                                        («Language.subst»
                                          x18
                                          («Derivation.atVar0» («Derivation.weakenElem» x13))))
                                  else
                                    leaf 0
                                else
                                  leaf 0
                              else
                                leaf 0
                            else
                              leaf 0
                          else
                            leaf 0
                        else
                          if («Prelude.and»
                            (Const.eq x3 (leaf 21))
                            (Const.eq x10 (leaf 0))).label ≠ 0 then
                            Const.equal («Prelude.nth» x8 x14) («Prelude.some» x9)
                          else
                            if («Prelude.and»
                              (Const.eq x3 (leaf 22))
                              (Const.eq x10 (leaf 2))).label ≠ 0 then
                              if («Derivation.isFormula» x0 x2 x7 x14).label ≠ 0 then
                                if («Derivation.pf» x6 (leaf 0) x7 x8 x14).label ≠ 0 then
                                  «Derivation.pf»
                                    x6
                                    (leaf 1)
                                    x7
                                    («Prelude.append» x8 («Prelude.single» x14))
                                    x9
                                else
                                  leaf 0
                              else
                                leaf 0
                            else
                              if («Prelude.and»
                                (Const.eq x3 (leaf 23))
                                (Const.eq x10 (leaf 2))).label ≠ 0 then
                                let x16 : T := «Derivation.rw» x6 (leaf 0) x7 x8 x9;
                                if («Prelude.isSome» x16).label ≠ 0 then
                                  «Derivation.pf» x6 (leaf 1) x7 x8 («Prelude.get» x16)
                                else
                                  leaf 0
                              else
                                if («Prelude.and»
                                  (Const.eq x3 (leaf 24))
                                  (Const.eq x10 (leaf 2))).label ≠ 0 then
                                  if («Prelude.and»
                                    («Derivation.isFormula» x0 x2 x7 x14)
                                    (Const.equal
                                      («Derivation.rw» x6 (leaf 0) x7 x8 x14)
                                      («Prelude.some» x9))).label ≠ 0 then
                                    «Derivation.pf» x6 (leaf 1) x7 x8 x14
                                  else
                                    leaf 0
                                else
                                  if («Prelude.and»
                                    (Const.eq x3 (leaf 25))
                                    (Const.eq x10 (leaf 2))).label ≠ 0 then
                                    if («Prelude.isSome» x11).label ≠ 0 then
                                      if («Prelude.and»
                                        («Derivation.isFormula» x0 x2 x7 x12)
                                        («Derivation.isFormula» x0 x2 x7 x13)).label ≠ 0 then
                                        if («Derivation.pf»
                                          x6
                                          (leaf 0)
                                          x7
                                          («Prelude.append» x8 («Prelude.single» x12))
                                          x13).label ≠ 0 then
                                          «Derivation.pf»
                                            x6
                                            (leaf 1)
                                            x7
                                            («Prelude.append» x8 («Prelude.single» x13))
                                            x12
                                        else
                                          leaf 0
                                      else
                                        leaf 0
                                    else
                                      leaf 0
                                  else
                                    if («Prelude.and»
                                      (Const.eq x3 (leaf 26))
                                      (Const.eq x10 (leaf 1))).label ≠ 0 then
                                      if («Prelude.isSome» x11).label ≠ 0 then
                                        let x16 : T := «Base.bindO»
                                          («Derivation.typeIn» x0 x2 x7 x12)
                                          «Language.expParts»;
                                        if («Prelude.isSome» x16).label ≠ 0 then
                                          «Derivation.pf»
                                            x6
                                            (leaf 0)
                                            ((«Language.p1» («Prelude.get» x16)) :: x7)
                                            («Base.mapT» «Derivation.weaken1» x8)
                                            («Language.mEq»
                                              («Language.app»
                                                («Derivation.weaken1» x12)
                                                («Language.var» (leaf 0)))
                                              («Language.app»
                                                («Derivation.weaken1» x13)
                                                («Language.var» (leaf 0))))
                                        else
                                          leaf 0
                                      else
                                        leaf 0
                                    else
                                      if (Const.eq x3 (leaf 27)).label ≠ 0 then
                                        let x16 : List T := Const.children x15;
                                        let x17 : List
                                          T := Const.children («Prelude.at» x4 (leaf 2));
                                        let x18 : T := «Base.bindO»
                                          («Prelude.nth» x1 x14)
                                          «Derivation.entryLanguage»;
                                        if («Prelude.isSome» x18).label ≠ 0 then
                                          let x19 : T := «Prelude.get» x18;
                                          if («Prelude.and»
                                            («Derivation.instOk» x0 x2 x7 x19 x16 x17)
                                            («Prelude.and»
                                              (Const.equal
                                                x9
                                                («Derivation.instTerm»
                                                  x16
                                                  x17
                                                  («Derivation.thConcl» x19)))
                                              (Const.eq
                                                x10
                                                («Prelude.length»
                                                  («Derivation.thHyps» x19))))).label ≠ 0 then
                                            «Base.allT»
                                              (fun (x20 : T) =>
                                                «Derivation.pf»
                                                  x6
                                                  x20
                                                  x7
                                                  x8
                                                  («Derivation.instTerm»
                                                    x16
                                                    x17
                                                    («Prelude.at» («Derivation.thHyps» x19) x20)))
                                              («Base.range» x10)
                                          else
                                            leaf 0
                                        else
                                          leaf 0
                                      else
                                        if («Prelude.and»
                                          (Const.eq x3 (leaf 28))
                                          (Const.eq x10 (leaf 2))).label ≠ 0 then
                                          if («Base.not» («Base.isEmpty» x7)).label ≠ 0 then
                                            let x16 : T := «Prelude.at» x7 (leaf 0);
                                            let x17 : List T := «Prelude.tail» x7;
                                            let x18 : T := «Derivation.lowerHyps» x0 x2 x17 x8;
                                            if («Prelude.isSome» x18).label ≠ 0 then
                                              if («Prelude.and»
                                                (Const.equal x16 «Theory.nat»)
                                                («Prelude.and»
                                                  («Derivation.primIs» x0 x14 «Derivation.zeroPrim»)
                                                  («Prelude.and»
                                                    («Derivation.primIs»
                                                      x0
                                                      x15
                                                      «Derivation.succPrim»)
                                                    («Derivation.isFormula»
                                                      x0
                                                      x2
                                                      x7
                                                      x9)))).label ≠ 0 then
                                                if («Derivation.pf»
                                                  x6
                                                  (leaf 0)
                                                  x17
                                                  (Const.children («Prelude.get» x18))
                                                  («Language.subst»
                                                    x9
                                                    («Derivation.instVar»
                                                      («Language.mArr»
                                                        x14
                                                        ([] : List T)
                                                        «Language.mStar»)))).label ≠ 0 then
                                                  «Derivation.pf»
                                                    x6
                                                    (leaf 1)
                                                    x7
                                                    («Prelude.append» x8 («Prelude.single» x9))
                                                    («Derivation.natSuccAt» x15 x9)
                                                else
                                                  leaf 0
                                              else
                                                leaf 0
                                            else
                                              leaf 0
                                          else
                                            leaf 0
                                        else
                                          if («Prelude.and»
                                            (Const.eq x3 (leaf 29))
                                            (Const.eq x10 (leaf 2))).label ≠ 0 then
                                            if («Base.not» («Base.isEmpty» x7)).label ≠ 0 then
                                              let x16 : T := «Prelude.at» x7 (leaf 0);
                                              let x17 : List T := «Prelude.tail» x7;
                                              let x18 : T := «Language.listPart» x16;
                                              let x19 : T := «Derivation.lowerHyps» x0 x2 x17 x8;
                                              if («Prelude.and»
                                                («Prelude.isSome» x18)
                                                («Prelude.isSome» x19)).label ≠ 0 then
                                                let x20 : T := «Prelude.get» x18;
                                                if («Prelude.and»
                                                  («Derivation.primIs» x0 x14 «Derivation.nilPrim»)
                                                  («Prelude.and»
                                                    («Derivation.primIs»
                                                      x0
                                                      x15
                                                      «Derivation.consPrim»)
                                                    («Derivation.isFormula»
                                                      x0
                                                      x2
                                                      x7
                                                      x9))).label ≠ 0 then
                                                  if («Derivation.pf»
                                                    x6
                                                    (leaf 0)
                                                    x17
                                                    (Const.children («Prelude.get» x19))
                                                    («Language.subst»
                                                      x9
                                                      («Derivation.instVar»
                                                        («Language.mArr»
                                                          x14
                                                          («Prelude.single» x20)
                                                          «Language.mStar»)))).label ≠ 0 then
                                                    «Derivation.pf»
                                                      x6
                                                      (leaf 1)
                                                      (x16 :: (x20 :: x17))
                                                      («Prelude.append»
                                                        («Base.mapT»
                                                          «Derivation.weaken2»
                                                          (Const.children («Prelude.get» x19)))
                                                        («Prelude.single»
                                                          («Derivation.weakenElem» x9)))
                                                      («Derivation.listConsAt» x15 x20 x9)
                                                  else
                                                    leaf 0
                                                else
                                                  leaf 0
                                              else
                                                leaf 0
                                            else
                                              leaf 0
                                          else
                                            if («Prelude.and»
                                              (Const.eq x3 (leaf 34))
                                              (Const.eq x10 (leaf 2))).label ≠ 0 then
                                              if («Base.not» («Base.isEmpty» x7)).label ≠ 0 then
                                                let x16 : T := «Prelude.at» x7 (leaf 0);
                                                let x17 : List T := «Prelude.tail» x7;
                                                let x18 : T := «Language.coprodParts» x16;
                                                let x19 : T := «Derivation.lowerHyps» x0 x2 x17 x8;
                                                if («Prelude.and»
                                                  («Prelude.isSome» x18)
                                                  («Prelude.isSome» x19)).label ≠ 0 then
                                                  let x20 : T := «Language.p1» («Prelude.get» x18);
                                                  let x21 : T := «Language.p2» («Prelude.get» x18);
                                                  if («Prelude.and»
                                                    («Derivation.primIs»
                                                      x0
                                                      x14
                                                      «Derivation.inlPrim»)
                                                    («Prelude.and»
                                                      («Derivation.primIs»
                                                        x0
                                                        x15
                                                        «Derivation.inrPrim»)
                                                      («Derivation.isFormula»
                                                        x0
                                                        x2
                                                        x7
                                                        x9))).label ≠ 0 then
                                                    if («Derivation.pf»
                                                      x6
                                                      (leaf 0)
                                                      (x20 :: x17)
                                                      x8
                                                      («Language.subst»
                                                        x9
                                                        («Derivation.atVar0»
                                                          («Language.mArr»
                                                            x14
                                                            («Theory.l2» x20 x21)
                                                            («Language.var»
                                                              (leaf 0)))))).label ≠ 0 then
                                                      «Derivation.pf»
                                                        x6
                                                        (leaf 1)
                                                        (x21 :: x17)
                                                        x8
                                                        («Language.subst»
                                                          x9
                                                          («Derivation.atVar0»
                                                            («Language.mArr»
                                                              x15
                                                              («Theory.l2» x20 x21)
                                                              («Language.var» (leaf 0)))))
                                                    else
                                                      leaf 0
                                                  else
                                                    leaf 0
                                                else
                                                  leaf 0
                                              else
                                                leaf 0
                                            else
                                              if («Prelude.and»
                                                (Const.eq x3 (leaf 35))
                                                (Const.eq x10 (leaf 0))).label ≠ 0 then
                                                «Prelude.and»
                                                  (Const.equal
                                                    («Prelude.nth» x7 x14)
                                                    («Prelude.some» «Theory.cZero»))
                                                  («Derivation.isFormula» x0 x2 x7 x9)
                                              else
                                                if («Prelude.and»
                                                  (Const.eq x3 (leaf 36))
                                                  (Const.eq x10 (leaf 1))).label ≠ 0 then
                                                  let x16 : List T := Const.children x15;
                                                  let x17 : T := «Prelude.nth»
                                                    («Language.gPrims» x0)
                                                    x14;
                                                  if («Prelude.and»
                                                    («Base.not» («Base.isEmpty» x7))
                                                    («Prelude.isSome» x17)).label ≠ 0 then
                                                    let x18 : T := «Prelude.at» x7 (leaf 0);
                                                    let x19 : List T := «Prelude.tail» x7;
                                                    let x20 : T := «Prelude.get» x17;
                                                    if («Prelude.and»
                                                      («Derivation.isCoeqProj» x20)
                                                      («Prelude.isSome»
                                                        («Derivation.lowerHyps»
                                                          x0
                                                          x2
                                                          x19
                                                          x8))).label ≠ 0 then
                                                      if («Prelude.and»
                                                        (Const.eq
                                                          («Prelude.length» x16)
                                                          («Language.prArity» x20))
                                                        («Prelude.and»
                                                          («Base.allT» («Language.isTy» x0 x2) x16)
                                                          («Prelude.and»
                                                            (Const.equal
                                                              x18
                                                              («PartialHorn.phSubst»
                                                                x16
                                                                («Language.prCod» x20)))
                                                            («Derivation.isFormula»
                                                              x0
                                                              x2
                                                              x7
                                                              x9)))).label ≠ 0 then
                                                        «Derivation.pf»
                                                          x6
                                                          (leaf 0)
                                                          ((«PartialHorn.phSubst»
                                                            x16
                                                            («Language.prDom» x20)) ::
                                                            x19)
                                                          x8
                                                          («Language.subst»
                                                            x9
                                                            («Derivation.atVar0»
                                                              («Language.mArr»
                                                                x14
                                                                x16
                                                                («Language.var» (leaf 0)))))
                                                      else
                                                        leaf 0
                                                    else
                                                      leaf 0
                                                  else
                                                    leaf 0
                                                else
                                                  if («Prelude.and»
                                                    (Const.eq x3 (leaf 30))
                                                    (Const.eq x10 (leaf 0))).label ≠ 0 then
                                                    if («Prelude.isSome» x11).label ≠ 0 then
                                                      let x16 : T := «Language.compileEq»
                                                        x0
                                                        x2
                                                        x7
                                                        x12
                                                        x13;
                                                      if («Prelude.isSome» x16).label ≠ 0 then
                                                        «Derivation.certifies»
                                                          x0
                                                          x1
                                                          x14
                                                          («Prelude.get» x16)
                                                      else
                                                        leaf 0
                                                    else
                                                      leaf 0
                                                  else
                                                    if («Prelude.and»
                                                      (Const.eq x3 (leaf 31))
                                                      (Const.eq x10 (leaf 0))).label ≠ 0 then
                                                      if («Prelude.and»
                                                        («Base.allT»
                                                          («Derivation.isFormula» x0 x2 x7)
                                                          x8)
                                                        («Derivation.isFormula»
                                                          x0
                                                          x2
                                                          x7
                                                          x9)).label ≠ 0 then
                                                        «Derivation.certifies»
                                                          x0
                                                          x1
                                                          x14
                                                          («Derivation.thmSeq»
                                                            x0
                                                            («Derivation.mkThm»
                                                              x2
                                                              (Const.node (leaf 0) x7)
                                                              (Const.node (leaf 0) x8)
                                                              x9))
                                                      else
                                                        leaf 0
                                                    else
                                                      if («Prelude.and»
                                                        (Const.eq x3 (leaf 32))
                                                        (Const.eq x10 (leaf 2))).label ≠ 0 then
                                                        if («Prelude.and»
                                                          («Prelude.isSome» x11)
                                                          (Const.eq
                                                            («Prelude.length» x7)
                                                            (leaf 1))).label ≠ 0 then
                                                          let x16 : T := «Prelude.at» x7 (leaf 0);
                                                          let x17 : T := «Derivation.typeIn»
                                                            x0
                                                            x2
                                                            x7
                                                            x12;
                                                          let x18 : T := «Language.roseLabel» x16;
                                                          if («Prelude.and»
                                                            («Prelude.isSome» x17)
                                                            («Prelude.isSome» x18)).label ≠ 0 then
                                                            let x19 : T := «Prelude.get» x17;
                                                            let x20 : T := «Prelude.get» x18;
                                                            let x21 : T := «Prelude.at» x4 (leaf 3);
                                                            let x22 : T := x15;
                                                            let x23 : T := «Prelude.at» x4 (leaf 2);
                                                            let x24 : List
                                                              T := «Theory.l2»
                                                              («Theory.list» x16)
                                                              x20;
                                                            if («Prelude.and»
                                                              («Derivation.rosePrimsOk»
                                                                x0
                                                                x14
                                                                x22
                                                                x23
                                                                x16
                                                                x20)
                                                              («Prelude.and»
                                                                (Const.equal
                                                                  («Derivation.typeIn» x0 x2 x7 x13)
                                                                  («Prelude.some» x19))
                                                                (Const.equal
                                                                  («Derivation.typeIn»
                                                                    x0
                                                                    x2
                                                                    («Theory.l2»
                                                                      («Theory.list» x19)
                                                                      x20)
                                                                    x21)
                                                                  («Prelude.some»
                                                                    x19)))).label ≠ 0 then
                                                              if («Derivation.pf»
                                                                x6
                                                                (leaf 0)
                                                                x24
                                                                ([] : List T)
                                                                («Language.mEq»
                                                                  («Derivation.roseNodeAt»
                                                                    x14
                                                                    x16
                                                                    x20
                                                                    x12)
                                                                  («Language.subst»
                                                                    x21
                                                                    («Derivation.atVar0»
                                                                      («Derivation.roseMapAt»
                                                                        x22
                                                                        x23
                                                                        x19
                                                                        x12))))).label ≠ 0 then
                                                                «Derivation.pf»
                                                                  x6
                                                                  (leaf 1)
                                                                  x24
                                                                  ([] : List T)
                                                                  («Language.mEq»
                                                                    («Derivation.roseNodeAt»
                                                                      x14
                                                                      x16
                                                                      x20
                                                                      x13)
                                                                    («Language.subst»
                                                                      x21
                                                                      («Derivation.atVar0»
                                                                        («Derivation.roseMapAt»
                                                                          x22
                                                                          x23
                                                                          x19
                                                                          x13))))
                                                              else
                                                                leaf 0
                                                            else
                                                              leaf 0
                                                          else
                                                            leaf 0
                                                        else
                                                          leaf 0
                                                      else
                                                        if («Prelude.and»
                                                          (Const.eq x3 (leaf 33))
                                                          (Const.eq x10 (leaf 1))).label ≠ 0 then
                                                          if (Const.eq
                                                            («Prelude.length» x7)
                                                            (leaf 1)).label ≠ 0 then
                                                            let x16 : T := «Prelude.at» x7 (leaf 0);
                                                            let x17 : T := «Language.roseLabel» x16;
                                                            if («Prelude.isSome» x17).label ≠ 0 then
                                                              let x18 : T := «Prelude.get» x17;
                                                              let x19 : T := «Prelude.at»
                                                                x4
                                                                (leaf 2);
                                                              if («Prelude.and»
                                                                («Derivation.rosePrimsOk»
                                                                  x0
                                                                  x14
                                                                  x15
                                                                  x19
                                                                  x16
                                                                  x18)
                                                                («Derivation.isFormula»
                                                                  x0
                                                                  x2
                                                                  x7
                                                                  x9)).label ≠ 0 then
                                                                «Derivation.pf»
                                                                  x6
                                                                  (leaf 0)
                                                                  («Theory.l2»
                                                                    («Theory.list» x16)
                                                                    x18)
                                                                  («Prelude.single»
                                                                    («Derivation.roseHyp»
                                                                      x15
                                                                      x19
                                                                      x9))
                                                                  («Derivation.roseNodeAt»
                                                                    x14
                                                                    x16
                                                                    x18
                                                                    x9)
                                                              else
                                                                leaf 0
                                                            else
                                                              leaf 0
                                                          else
                                                            leaf 0
                                                        else
                                                          leaf 0);
    x10

def «Derivation.check» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : (List T → List T → T → T) ×
      (List T →
        List T →
          T →
            T) := (Const.fold
      (α := T × ((List T → List T → T → T) × (List T → List T → T → T)))
      (fun (x4 : T)
         (x5 : List
           (T × ((List T → List T → T → T) × (List T → List T → T → T)))) =>
        let x6 : List T := «Derivation.dpTrees» x5;
        let x7 : List T := Const.children («Prelude.at» x6 (leaf 0));
        let x8 : List
          (T ×
            ((List T → List T → T → T) ×
              (List T → List T → T → T))) := «Derivation/DPs.tail» x5;
        let x9 : List T := «Prelude.tail» x6;
        (Const.node x4 x6,
          (fun (x10 : List T) (x11 : List T) (x12 : T) =>
            «Derivation.rewriteStep» x0 x1 x2 x4 x7 x9 x8 x10 x11 x12,
            fun (x10 : List T) (x11 : List T) (x12 : T) =>
              «Derivation.proveStep» x0 x1 x2 x4 x7 x9 x8 x10 x11 x12)))
      x3).2;
    x4

def «Derivation.thmChecks» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (let x4 : T := «Derivation.thArity» x2;
                   let x5 : List T := «Derivation.thCtx» x2;
                   if («Prelude.and»
                     («Base.allT» («Language.isTy» x0 x4) x5)
                     («Prelude.and»
                       («Base.allT»
                         («Derivation.isFormula» x0 x4 x5)
                         («Derivation.thHyps» x2))
                       («Derivation.isFormula»
                         x0
                         x4
                         x5
                         («Derivation.thConcl» x2)))).label ≠ 0 then
                     («Derivation.check» x0 x1 x4 x3).2
                       x5
                       («Derivation.thHyps» x2)
                       («Derivation.thConcl» x2)
                   else
                     leaf 0);
    x4

def «Derivation.primSeq» :=
  fun (x0 : T) =>
    let x1 : T := «PartialHorn.mkSeq»
      («Prelude.replicate» («Language.prArity» x0) (leaf 0))
      ([] : List T)
      («PartialHorn.eqn»
        («Theory.comp»
          («Theory.idt» («Language.prCod» x0))
          («Theory.comp»
            («Language.prArrow» x0)
            («Theory.idt» («Language.prDom» x0))))
        («Language.prArrow» x0));
    x1

def «Derivation.primConfirms» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := (if («Prelude.isSome» x3).label ≠ 0 then
      if («Derivation.anyDefs»
        x0
        (fun (x4 : List T) =>
          «Language.primWf»
            x0
            («PartialHorn.thySig» («Infer.ext» x4))
            x2)).label ≠ 0 then
        «Derivation.certifies»
          x0
          x1
          («Prelude.get» x3)
          («Derivation.primSeq» x2)
      else
        leaf 0
    else
      «Derivation.anyDefs»
        x0
        (fun (x4 : List T) =>
          if (Const.eq
            («Language.gBase» x0)
            («Prelude.length» «Theory.sig»)).label ≠ 0 then
            «Language.primOk» x0 («Infer.envOfDefs» x4) x2
          else
            leaf 0));
    x4

def «Derivation.objConfirms» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (if («Prelude.isSome» x4).label ≠ 0 then
      if («Derivation.anyDefs»
        x0
        (fun (x5 : List T) =>
          Const.equal
            («PartialHorn.sortOf»
              («PartialHorn.thySig» («Infer.ext» x5))
              («Prelude.replicate» x2 (leaf 0))
              x3)
            («Prelude.some» (leaf 0)))).label ≠ 0 then
        «Derivation.certifies»
          x0
          x1
          («Prelude.get» x4)
          («PartialHorn.mkSeq»
            («Prelude.replicate» x2 (leaf 0))
            ([] : List T)
            («Theory.dfd» x3))
      else
        leaf 0
    else
      «Derivation.anyDefs»
        x0
        (fun (x5 : List T) =>
          if (Const.eq
            («Language.gBase» x0)
            («Prelude.length» «Theory.sig»)).label ≠ 0 then
            «Language.objOk» («Infer.envOfDefs» x5) x2 x3
          else
            leaf 0));
    x5

def «Derivation.ldChecks» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Prelude.isSome» («Language.ldCompile» x0 x1))
      («Language.isTy» x0 («Language.ldArity» x1) («Language.ldType» x1));
    x2

def «Derivation.declLang» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Derivation.declComb» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «Derivation.declDef» :=
  fun (x0 : T) => Const.node (leaf 2) (x0 :: ([] : List T))

def «Derivation.declConst» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 3) (x0 :: (x1 :: ([] : List T)))

def «Derivation.declObj» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 4) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Derivation.declQuot» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    Const.node (leaf 5) (x0 :: (x1 :: (x2 :: ([] : List T))))

def «Derivation.declDesc» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 6) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Derivation.devState» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Language.pr» x0 (Const.node (leaf 0) x1); x2

def «Derivation.withPrims» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Language.globals»
      (Const.node (leaf 0) x1)
      (Const.node (leaf 0) («Language.gDefs» x0))
      («Language.gBase» x0);
    x2

def «Derivation.withDefs» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Language.globals»
      (Const.node (leaf 0) («Language.gPrims» x0))
      (Const.node (leaf 0) x1)
      («Language.gBase» x0);
    x2

def «Derivation.push» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : List T := «Prelude.append» x0 («Prelude.single» x1); x2

def «Derivation.sortsArr» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Derivation.anyDefs»
      x0
      (fun (x3 : List T) =>
        Const.equal
          («PartialHorn.sortOf»
            («PartialHorn.thySig» («Infer.ext» x3))
            («Prelude.replicate» x1 (leaf 0))
            x2)
          («Prelude.some» (leaf 1)));
    x3

def «Derivation.quotStep» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : List T := «Theory.l2» x3 x3;
                   «Base.bindO»
                     («Language.compile»
                       x0
                       x2
                       x4
                       («Language.ctxObj» x5)
                       («Language.stdEnv» x5))
                     (fun (x6 : T) =>
                       let x7 : T := «Derivation.relL» x3 («Language.p1» x6);
                       let x8 : T := «Derivation.relR» x3 («Language.p1» x6);
                       let x9 : T := «Language.primitive»
                         x2
                         («Theory.coeqProj» x7 x8)
                         x3
                         («PartialHorn.phOp»
                           (Const.add
                             («Language.gBase» x0)
                             («Prelude.length» («Language.gDefs» x0)))
                           («Derivation.objVars» x2));
                       let x10 : T := «Language.globals»
                         (Const.node (leaf 0) («Derivation.push» («Language.gPrims» x0) x9))
                         (Const.node
                           (leaf 0)
                           («Derivation.push»
                             («Language.gDefs» x0)
                             («Language.defObj» x2 («Theory.coeqz» x7 x8))))
                         («Language.gBase» x0);
                       let x11 : T := «Prelude.length» («Language.gPrims» x0);
                       let x12 : T := «Derivation.mkThm»
                         x2
                         (Const.node (leaf 0) x5)
                         (Const.node (leaf 0) («Prelude.single» x4))
                         («Language.mEq»
                           («Language.mArr»
                             x11
                             («Derivation.objVars» x2)
                             («Language.var» (leaf 1)))
                           («Language.mArr»
                             x11
                             («Derivation.objVars» x2)
                             («Language.var» (leaf 0))));
                       if («Prelude.and»
                         (Const.eq («Language.gBase» x0) («Prelude.length» «Theory.sig»))
                         («Prelude.and»
                           («Language.isTy» x0 x2 x3)
                           («Prelude.and»
                             (Const.equal («Language.p2» x6) «Theory.omega»)
                             («Prelude.and»
                               («PartialHorn.scoped» x2 («Language.prArrow» x9))
                               («Prelude.and»
                                 («Language.isTy» x10 x2 («Language.prCod» x9))
                                 («Prelude.and»
                                   («Derivation.sortsArr» x0 x2 («Language.prArrow» x9))
                                   («Derivation.isFormula»
                                     x10
                                     x2
                                     x5
                                     («Derivation.thConcl» x12)))))))).label ≠ 0 then
                         «Prelude.some»
                           («Derivation.devState»
                             x10
                             («Derivation.push» x1 («Derivation.entLang» x12)))
                       else
                         «Prelude.none»));
    x5

def «Derivation.descStep» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : T := «Base.bindO»
      («Prelude.nth» («Language.gPrims» x0) x2)
      (fun (x6 : T) =>
        «Base.bindO»
          («Base.bindO» («Prelude.nth» x1 x5) «Derivation.entryLanguage»)
          (fun (x7 : T) =>
            «Base.bindO»
              («Derivation.primRel» x6)
              (fun (x8 : T) =>
                let x9 : T := «Language.prArity» x6;
                let x10 : List T := «Prelude.single» («Language.prDom» x6);
                «Base.bindO»
                  («Language.compile»
                    x0
                    x9
                    x4
                    («Language.ctxObj» x10)
                    («Language.stdEnv» x10))
                  (fun (x11 : T) =>
                    if (Const.eq
                      («Prelude.length» («Derivation.thHyps» x7))
                      (leaf 1)).label ≠ 0 then
                      let x12 : T := «Prelude.at» («Derivation.thHyps» x7) (leaf 0);
                      let x13 : List
                        T := «Theory.l2» («Language.prDom» x6) («Language.prDom» x6);
                      let x14 : T := «Language.primitive»
                        x9
                        («Theory.coeqDesc»
                          («Derivation.relL» («Language.prDom» x6) x8)
                          («Derivation.relR» («Language.prDom» x6) x8)
                          («Language.p1» x11))
                        («Language.prCod» x6)
                        x3;
                      let x15 : T := «Derivation.withPrims»
                        x0
                        («Derivation.push» («Language.gPrims» x0) x14);
                      let x16 : T := «Language.mArr»
                        («Prelude.length» («Language.gPrims» x0))
                        («Derivation.objVars» x9)
                        («Language.mArr»
                          x2
                          («Derivation.objVars» x9)
                          («Language.var» (leaf 0)));
                      let x17 : T := «Derivation.mkThm»
                        x9
                        (Const.node (leaf 0) x10)
                        (Const.node (leaf 0) ([] : List T))
                        («Language.mEq» x16 x4);
                      if («Prelude.and»
                        (Const.eq («Language.gBase» x0) («Prelude.length» «Theory.sig»))
                        («Prelude.and»
                          (Const.equal («Language.p2» x11) x3)
                          («Prelude.and»
                            («Language.isTy» x0 x9 x3)
                            («Prelude.and»
                              (Const.eq («Derivation.thArity» x7) x9)
                              («Prelude.and»
                                («Base.equalTs» («Derivation.thCtx» x7) x13)
                                («Prelude.and»
                                  (Const.equal
                                    («Derivation.thConcl» x7)
                                    («Language.mEq» («Derivation.weaken1» x4) x4))
                                  («Prelude.and»
                                    (Const.equal
                                      («Language.compile»
                                        x0
                                        x9
                                        x12
                                        («Language.ctxObj» x13)
                                        («Language.stdEnv» x13))
                                      («Prelude.some» («Language.pr» x8 «Theory.omega»)))
                                    («Prelude.and»
                                      («PartialHorn.scoped» x9 («Language.prArrow» x14))
                                      («Prelude.and»
                                        («Derivation.sortsArr» x0 x9 («Language.prArrow» x14))
                                        («Derivation.isFormula»
                                          x15
                                          x9
                                          x10
                                          («Derivation.thConcl» x17))))))))))).label ≠ 0 then
                        «Prelude.some»
                          («Derivation.devState»
                            x15
                            («Derivation.push» x1 («Derivation.entLang» x17)))
                      else
                        «Prelude.none»
                    else
                      «Prelude.none»))));
    x6

def «Derivation.declStep» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := x2;
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let x4 : T := Const.child x3 (leaf 0);
                     let x5 : T := Const.child x3 (leaf 1);
                     if («Derivation.thmChecks» x0 x1 x4 x5).label ≠ 0 then
                       «Prelude.some»
                         («Derivation.devState»
                           x0
                           («Derivation.push» x1 («Derivation.entLang» x4)))
                     else
                       «Prelude.none»
                   else
                     if (Const.eq (Const.label x3) (leaf 1)).label ≠ 0 then
                       let x4 : T := Const.child x3 (leaf 0);
                       let x5 : T := Const.child x3 (leaf 1);
                       if («Derivation.certifies» x0 x1 x5 x4).label ≠ 0 then
                         «Prelude.some»
                           («Derivation.devState»
                             x0
                             («Derivation.push» x1 («Derivation.entComb» x4)))
                       else
                         «Prelude.none»
                     else
                       if (Const.eq (Const.label x3) (leaf 2)).label ≠ 0 then
                         let x4 : T := Const.child x3 (leaf 0);
                         if («Derivation.ldChecks» x0 x4).label ≠ 0 then
                           «Prelude.some»
                             («Derivation.devState»
                               («Derivation.withDefs»
                                 x0
                                 («Derivation.push» («Language.gDefs» x0) («Language.defLang» x4)))
                               x1)
                         else
                           «Prelude.none»
                       else
                         if (Const.eq (Const.label x3) (leaf 3)).label ≠ 0 then
                           let x4 : T := Const.child x3 (leaf 0);
                           let x5 : T := Const.child x3 (leaf 1);
                           if («Derivation.primConfirms» x0 x1 x4 x5).label ≠ 0 then
                             «Prelude.some»
                               («Derivation.devState»
                                 («Derivation.withPrims»
                                   x0
                                   («Derivation.push» («Language.gPrims» x0) x4))
                                 x1)
                           else
                             «Prelude.none»
                         else
                           if (Const.eq (Const.label x3) (leaf 4)).label ≠ 0 then
                             let x4 : T := Const.child x3 (leaf 0);
                             let x5 : T := Const.child x3 (leaf 1);
                             let x6 : T := Const.child x3 (leaf 2);
                             if («Derivation.objConfirms» x0 x1 x4 x5 x6).label ≠ 0 then
                               «Prelude.some»
                                 («Derivation.devState»
                                   («Derivation.withDefs»
                                     x0
                                     («Derivation.push»
                                       («Language.gDefs» x0)
                                       («Language.defObj» x4 x5)))
                                   x1)
                             else
                               «Prelude.none»
                           else
                             if (Const.eq (Const.label x3) (leaf 5)).label ≠ 0 then
                               let x4 : T := Const.child x3 (leaf 0);
                               let x5 : T := Const.child x3 (leaf 1);
                               let x6 : T := Const.child x3 (leaf 2);
                               «Derivation.quotStep» x0 x1 x4 x5 x6
                             else
                               let x4 : T := Const.child x3 (leaf 0);
                               let x5 : T := Const.child x3 (leaf 1);
                               let x6 : T := Const.child x3 (leaf 2);
                               let x7 : T := Const.child x3 (leaf 3);
                               «Derivation.descStep» x0 x1 x4 x5 x6 x7);
    x3

def «Derivation.checkDev» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) =>
    let x3 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x3 : T) (x4 : T) =>
        «Base.bindO»
          x4
          (fun (x5 : T) =>
            «Derivation.declStep»
              («Language.p1» x5)
              (Const.children («Language.p2» x5))
              x3))
      («Prelude.some» («Derivation.devState» x0 x1))
      («Prelude.reverse» x2);
    x3

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

end GebMirror.Metalogic

end
