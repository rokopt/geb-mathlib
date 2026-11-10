module

public import GebMirror.Metalogic.Tactics

/-! Generated from a Geb program by `bootstrap/stage1/lean.geb`. -/

@[expose] public section

open Geb.Kernel
open Geb.Kernel renaming Tree → T

namespace GebMirror.Metalogic

def «Authoring/LD.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/LD.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/LD.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/LD.reverse» :=
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

def «Authoring/LD.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/LD.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Authoring/LD.tail» x1 x0;
    x2

def «Authoring/LD.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/LD.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/OS.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/OS.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/OS.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/OS.reverse» :=
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

def «Authoring/OS.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/OS.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List T := Const.iter (α := List T) «Authoring/OS.tail» x1 x0;
    x2

def «Authoring/OS.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/OS.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/PF.l2» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List T := (x0 :: (x1 :: ([] : List T))); x2

def «Authoring/PF.l3» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : List T := (x0 :: («Authoring/PF.l2» x1 x2)); x3

def «Authoring/PF.l4» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    let x4 : List T := (x0 :: («Authoring/PF.l3» x1 x2 x3)); x4

def «Authoring/PF.l5» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    let x5 : List T := (x0 :: («Authoring/PF.l4» x1 x2 x3 x4)); x5

def «Authoring/PF.l6» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) (x5 : T) =>
    let x6 : List T := (x0 :: («Authoring/PF.l5» x1 x2 x3 x4 x5)); x6

def «Authoring/DL.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring/Decls.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Decls.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Decls.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Decls.reverse» :=
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

def «Authoring/Decls.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Decls.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Decls.tail» x1 x0;
    x2

def «Authoring/Decls.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Decls.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/Rules.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Rules.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Rules.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Rules.reverse» :=
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

def «Authoring/Rules.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Rules.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Rules.tail» x1 x0;
    x2

def «Authoring/Rules.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Rules.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring.word» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isAtom» x0)
      (Const.equal («Reader.nameOf» x0) x1);
    x2

def «Authoring.form» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := «Prelude.and»
      («Reader.isList» x0)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x0)) x2)
        («Authoring.word» (Const.child x0 (leaf 0)) x1));
    x3

def «Authoring.headed» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x0)
      («Prelude.and»
        (Const.lt (leaf 0) («Prelude.length» (Const.children x0)))
        («Authoring.word» (Const.child x0 (leaf 0)) x1));
    x2

def «Authoring.number» :=
  fun (x0 : T) =>
    let x1 : T := (if («Reader.isAtom» x0).label ≠ 0 then
      «Reader.numeral» (Const.children x0)
    else
      «Prelude.none»);
    x1

def «Authoring.has» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : T := «Prelude.isSome» («Reader.indexOf» x0 x1); x2

def «Authoring.declared» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      («Reader.isAtom» x0)
      («Prelude.and»
        («Base.not» («Base.isEmpty» (Const.children x0)))
        («Prelude.and»
          («Base.not» («Prelude.isSome» («Authoring.number» x0)))
          («Base.not»
            («Authoring.has» («Reader.nameOf» x0) «Reader.reservedNames»))));
    x1

def «Authoring.internalNames» :=
  Const.children
    (mk 0 [mk 0 [leaf 105, leaf 110, leaf 108],
      mk 0 [leaf 105, leaf 110, leaf 114],
      mk 0 [leaf 99, leaf 97, leaf 115, leaf 101],
      mk 0 [leaf 108,
        leaf 105,
        leaf 115,
        leaf 116,
        leaf 45,
        leaf 114,
        leaf 101,
        leaf 99],
      mk 0 [leaf 114,
        leaf 111,
        leaf 115,
        leaf 101,
        leaf 45,
        leaf 114,
        leaf 101,
        leaf 99],
      mk 0 [leaf 108, leaf 105, leaf 98],
      mk 0 [leaf 107, leaf 101, leaf 114, leaf 110, leaf 101, leaf 108]])

def «Authoring.bindable» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.and»
      («Authoring.declared» x0)
      («Base.not»
        («Authoring.has» («Reader.nameOf» x0) «Authoring.internalNames»));
    x1

def «Authoring.distinctFrom» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : T := Const.foldr
      (α := T)
      (β := List T → T)
      (fun (x2 : T) (x3 : List T → T) (x4 : List T) =>
        «Prelude.and» («Base.not» («Authoring.has» x2 x4)) (x3 (x2 :: x4)))
      (fun (_ : List T) => leaf 1)
      x1
      x0;
    x2

def «Authoring.namesOk» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x1)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x1)) x0)
        («Base.allT» «Authoring.bindable» (Const.children x1)));
    x2

def «Authoring.globalsOf» :=
  fun (x0 : List T) =>
    let x1 : T := «Language.globals»
      («Language.prims»
        («Authoring/PF.l6»
          «Derivation.nilPrim»
          «Derivation.consPrim»
          «Derivation.lnodePrim»
          «Derivation.inlPrim»
          «Derivation.inrPrim»
          «Derivation.casePrim»))
      («Language.defs»
        («Authoring/DL.map»
          «Language.defLang»
          («Authoring/LD.append» «Translation.lib» x0)))
      («Authoring/OS.length» «Theory.sig»);
    x1

def «Authoring.rulesOf» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : List
      T := (let x2 : List
              T := «Authoring/Rules.single»
              («Prover.nrBelow» x1 («Derivation.terms» ([] : List T)));
            ((«Prover.nrRule» (leaf 3) («Derivation.terms» ([] : List T))) ::
              ((«Prover.nrRule» (leaf 4) («Derivation.terms» ([] : List T))) ::
                ((«Prover.nrRule» (leaf 5) («Derivation.terms» ([] : List T))) ::
                  (if (Const.eq x0 (leaf 0)).label ≠ 0 then
                    x2
                  else
                    ((«Prover.nrRule»
                      (leaf 11)
                      («Derivation.terms» («Prelude.single» (leaf 0)))) ::
                      ((«Prover.nrRule»
                        (leaf 12)
                        («Derivation.terms» («Prelude.single» (leaf 1)))) ::
                        ((«Prover.nrRule»
                          (leaf 13)
                          («Derivation.terms» («Theory.l3» (leaf 2) (leaf 0) (leaf 1)))) ::
                          ((«Prover.nrRule»
                            (leaf 14)
                            («Derivation.terms» («Theory.l2» (leaf 5) (leaf 3)))) ::
                            ((«Prover.nrRule»
                              (leaf 15)
                              («Derivation.terms» («Theory.l2» (leaf 5) (leaf 4)))) ::
                              («Prover.nrUnit» :: x2)))))))))));
    x2

def «Authoring.kernelType» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Reader.resolve»
                     ([] : List T)
                     x0
                     (Const.node
                       (leaf 2)
                       («Theory.l2»
                         (Const.node (leaf 1) (Const.children «Reader.kwNil»))
                         x1))
                     ([] : List T);
                   if («Prelude.isSome» x2).label ≠ 0 then
                     «Prelude.some» (Const.child («Prelude.get» x2) (leaf 0))
                   else
                     «Prelude.none»);
    x2

def «Authoring.itype» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := Const.para
      (α := T)
      (fun (x2 : T) (x3 : List T) =>
        let x4 : T := «Prelude.length» x3;
        let x5 : T := Const.child x2 (leaf 0);
        let x6 : (T → T → T) →
          T := (fun (x6 : T → T → T) =>
          if (Const.eq x4 (leaf 3)).label ≠ 0 then
            «Base.bindO»
              («Prelude.at» x3 (leaf 1))
              (fun (x7 : T) => «Base.mapO» (x6 x7) («Prelude.at» x3 (leaf 2)))
          else
            «Prelude.none»);
        let x7 : (T → T) →
          T := (fun (x7 : T → T) =>
          if (Const.eq x4 (leaf 2)).label ≠ 0 then
            «Base.mapO» x7 («Prelude.at» x3 (leaf 1))
          else
            «Prelude.none»);
        if («Reader.isAtom» x2).label ≠ 0 then
          let x8 : T := «Reader.nameOf» x2;
          if (Const.equal x8 «Reader.kwT»).label ≠ 0 then
            «Prelude.some» «Translation.treeTy»
          else
            if (Const.equal x8 «Reader.kwUnit»).label ≠ 0 then
              «Prelude.some» «Theory.one»
            else
              if (Const.equal
                x8
                (mk 0 [leaf 66, leaf 105, leaf 116])).label ≠ 0 then
                «Prelude.some» («Theory.coprod» «Theory.one» «Theory.one»)
              else
                if (Const.equal
                  x8
                  (mk 0 [leaf 66, leaf 105, leaf 116, leaf 115])).label ≠ 0 then
                  «Prelude.some» «Translation.bitsTy»
                else
                  if (Const.equal
                    x8
                    (mk 0 [leaf 79,
                      leaf 109,
                      leaf 101,
                      leaf 103,
                      leaf 97])).label ≠ 0 then
                    «Prelude.some» «Theory.omega»
                  else
                    «Base.mapO» «Theory.x» («Reader.indexOf» x8 x0)
        else
          if («Base.not» («Reader.isList» x2)).label ≠ 0 then
            «Prelude.none»
          else
            if («Authoring.word» x5 «Reader.kwProd»).label ≠ 0 then
              x6 «Theory.prod»
            else
              if («Authoring.word»
                x5
                (mk 0 [leaf 83, leaf 117, leaf 109])).label ≠ 0 then
                x6 «Theory.coprod»
              else
                if («Authoring.word» x5 «Reader.kwArrow»).label ≠ 0 then
                  x6 «Theory.exp»
                else
                  if («Authoring.word» x5 «Reader.kwList»).label ≠ 0 then
                    x7 «Theory.list»
                  else
                    if («Authoring.word»
                      x5
                      (mk 0 [leaf 82, leaf 111, leaf 115, leaf 101])).label ≠ 0 then
                      x7 «Theory.lrose»
                    else
                      «Prelude.none»)
      x1;
    x2

def «Authoring.listElem» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.isSome» x0).label ≠ 0 then
      if («Prelude.and»
        (Const.eq (Const.label («Prelude.get» x0)) (leaf 4))
        (Const.eq (Const.arity («Prelude.get» x0)) (leaf 1))).label ≠ 0 then
        «Prelude.some» (Const.child («Prelude.get» x0) (leaf 0))
      else
        «Prelude.none»
    else
      «Prelude.none»);
    x1

def «Authoring.ikernel» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : T)
    (x3 : List T)
    (x4 : List T) =>
    let x5 : T := (let x5 : List
                     T := Const.foldr
                     (α := T)
                     (β := List T)
                     (fun (x5 : T) (x6 : List T) =>
                       if («Prelude.isSome» («Prelude.at» x4 x5)).label ≠ 0 then
                         (x5 :: x6)
                       else
                         x6)
                     ([] : List T)
                     («Base.range» («Prelude.length» x3));
                   «Base.bindO»
                     («Reader.resolve»
                       ([] : List T)
                       x1
                       x2
                       («Base.mapT» («Prelude.at» x3) x5))
                     (fun (x6 : T) =>
                       let x7 : T := «Translation.term»
                         x0
                         («Base.mapT» (fun (x7 : T) => «Prelude.get» («Prelude.at» x4 x7)) x5)
                         x6;
                       if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
                         let _ : List T := Const.children x7; «Prelude.none»
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
                         «Prelude.some»
                           (if (Const.eq
                             («Prelude.length» x5)
                             («Prelude.length» x3)).label ≠ 0 then
                             «Language.p2» x9
                           else
                             «Language.rename»
                               («Language.p2» x9)
                               (fun (x11 : T) => «Prelude.at» x5 x11))));
    x5

def «Authoring.libEntry» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 0) («Theory.l2» x0 x1); x2

def «Authoring.libTable» :=
  «Prelude.append»
    («Theory.l6»
      («Authoring.libEntry»
        (mk 0 [leaf 98, leaf 110, leaf 105, leaf 108])
        (leaf 0))
      («Authoring.libEntry» (mk 0 [leaf 98, leaf 48]) (leaf 1))
      («Authoring.libEntry» (mk 0 [leaf 98, leaf 49]) (leaf 2))
      («Authoring.libEntry» (mk 0 [leaf 108, leaf 97, leaf 98]) (leaf 3))
      («Authoring.libEntry»
        (mk 0 [leaf 117, leaf 110, leaf 110, leaf 111, leaf 100, leaf 101])
        (leaf 4))
      («Authoring.libEntry»
        (mk 0 [leaf 99,
          leaf 104,
          leaf 105,
          leaf 108,
          leaf 100,
          leaf 114,
          leaf 101,
          leaf 110])
        (leaf 5)))
    («Prelude.append»
      («Theory.l6»
        («Authoring.libEntry»
          (mk 0 [leaf 99, leaf 111, leaf 110, leaf 100])
          (leaf 6))
        («Authoring.libEntry»
          (mk 0 [leaf 116, leaf 97, leaf 105, leaf 108])
          (leaf 7))
        («Authoring.libEntry»
          (mk 0 [leaf 104, leaf 101, leaf 97, leaf 100, leaf 68])
          (leaf 8))
        («Authoring.libEntry»
          (mk 0 [leaf 108, leaf 99, leaf 97, leaf 115, leaf 101])
          (leaf 9))
        («Authoring.libEntry»
          (mk 0 [leaf 105, leaf 115, leaf 78, leaf 105, leaf 108])
          (leaf 10))
        («Authoring.libEntry»
          (mk 0 [leaf 115, leaf 117, leaf 99, leaf 99])
          (leaf 11)))
      («Prelude.append»
        («Theory.l6»
          («Authoring.libEntry»
            (mk 0 [leaf 108, leaf 101, leaf 110, leaf 103, leaf 116, leaf 104])
            (leaf 12))
          («Authoring.libEntry»
            (mk 0 [leaf 112, leaf 114, leaf 101, leaf 100])
            (leaf 13))
          («Authoring.libEntry» (mk 0 [leaf 100, leaf 98, leaf 108]) (leaf 14))
          («Authoring.libEntry» (mk 0 [leaf 97, leaf 100, leaf 100]) (leaf 15))
          («Authoring.libEntry» (mk 0 [leaf 99, leaf 109, leaf 112]) (leaf 16))
          («Authoring.libEntry» (mk 0 [leaf 108, leaf 116, leaf 66]) (leaf 17)))
        («Prelude.append»
          («Theory.l6»
            («Authoring.libEntry» (mk 0 [leaf 101, leaf 113, leaf 66]) (leaf 18))
            («Authoring.libEntry»
              (mk 0 [leaf 115, leaf 117, leaf 98, leaf 69])
              (leaf 19))
            («Authoring.libEntry» (mk 0 [leaf 115, leaf 117, leaf 98]) (leaf 20))
            («Authoring.libEntry» (mk 0 [leaf 109, leaf 117, leaf 108]) (leaf 21))
            («Authoring.libEntry»
              (mk 0 [leaf 100, leaf 105, leaf 118, leaf 77, leaf 111, leaf 100])
              (leaf 22))
            («Authoring.libEntry»
              (mk 0 [leaf 108, leaf 111, leaf 103, leaf 50])
              (leaf 23)))
          («Theory.l5»
            («Authoring.libEntry»
              (mk 0 [leaf 105, leaf 116, leaf 101, leaf 114])
              (leaf 24))
            («Authoring.libEntry»
              (mk 0 [leaf 109, leaf 97, leaf 112, leaf 65, leaf 112, leaf 112])
              (leaf 25))
            («Authoring.libEntry» (mk 0 [leaf 97, leaf 110, leaf 100]) (leaf 26))
            («Authoring.libEntry»
              (mk 0 [leaf 97, leaf 108, leaf 108, leaf 90, leaf 105, leaf 112])
              (leaf 27))
            («Authoring.libEntry»
              (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
              (leaf 28))))))

def «Authoring.ilib» :=
  fun (x0 : List T) (x1 : List T) (x2 : T → T) =>
    let x3 : T := «Base.bindO»
      (if («Reader.isAtom» («Prelude.at» x1 (leaf 1))).label ≠ 0 then
        «Reader.lookupAbbrev»
          («Reader.nameOf» («Prelude.at» x1 (leaf 1)))
          «Authoring.libTable»
      else
        «Prelude.none»)
      (fun (x3 : T) =>
        let x4 : T := «Language/OLDefn.nthOf» «Translation.lib» x3;
        if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
          let _ : List T := Const.children x4; «Prelude.none»
        else
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
          let x8 : T := x6;
          let x9 : List T := Const.children x8;
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
          let x12 : T := Const.lcase
            (α := T)
            (β := T)
            x11
            (leaf 0)
            (fun (x12 : T) (_ : List T) => x12);
          let x13 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x11
            ([] : List T)
            (fun (_ : T) (x14 : List T) => x14);
          let _ : T := Const.lcase
            (α := T)
            (β := T)
            x13
            (leaf 0)
            (fun (x14 : T) (_ : List T) => x14);
          let x15 : List
            T := Const.lcase
            (α := T)
            (β := List T)
            x13
            ([] : List T)
            (fun (_ : T) (x16 : List T) => x16);
          let _ : T := Const.lcase
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
          let x18 : T := x12;
          let x19 : List T := Const.children x18;
          let x20 : List T := x19;
          if (Const.eq
            («Prelude.length» x1)
            (Const.add
              (leaf 2)
              (Const.add x10 («Prelude.length» x20)))).label ≠ 0 then
            «Base.bindO»
              («Base.allSomeT»
                («Base.mapT»
                  (fun (x21 : T) =>
                    «Authoring.itype» x0 («Prelude.at» x1 (Const.add (leaf 2) x21)))
                  («Base.range» x10)))
              (fun (x21 : T) =>
                «Base.mapO»
                  (fun (x22 : T) =>
                    «Translation.call» x3 (Const.children x21) (Const.children x22))
                  («Base.allSomeT»
                    («Base.mapT»
                      (fun (x22 : T) => x2 (Const.add (Const.add (leaf 2) x10) x22))
                      («Base.range» («Prelude.length» x20)))))
          else
            «Prelude.none»);
    x3

def «Authoring/IRs.single» :=
  fun (x0 : List T → List T → T) =>
    let x1 : List
      (List T → List T → T) := (x0 :: ([] : List (List T → List T → T)));
    x1

def «Authoring/IRs.length» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : T := Const.foldr
      (α := List T → List T → T)
      (β := T)
      (fun (_ : List T → List T → T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/IRs.append» :=
  fun (x0 : List (List T → List T → T))
    (x1 : List (List T → List T → T)) =>
    let x2 : List
      (List T →
        List T →
          T) := Const.foldr
      (α := List T → List T → T)
      (β := List (List T → List T → T))
      (fun (x2 : List T → List T → T) (x3 : List (List T → List T → T)) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/IRs.reverse» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : List
      (List T →
        List T →
          T) := Const.foldr
      (α := List T → List T → T)
      (β := List (List T → List T → T) → List (List T → List T → T))
      (fun (x1 : List T → List T → T)
         (x2 : List (List T → List T → T) → List (List T → List T → T))
         (x3 : List (List T → List T → T)) =>
        x2 (x1 :: x3))
      (fun (x1 : List (List T → List T → T)) => x1)
      x0
      ([] : List (List T → List T → T));
    x1

def «Authoring/IRs.tail» :=
  fun (x0 : List (List T → List T → T)) =>
    let x1 : List
      (List T →
        List T →
          T) := Const.lcase
      (α := List T → List T → T)
      (β := List (List T → List T → T))
      x0
      ([] : List (List T → List T → T))
      (fun (_ : List T → List T → T) (x2 : List (List T → List T → T)) =>
        x2);
    x1

def «Authoring/IRs.drop» :=
  fun (x0 : T) (x1 : List (List T → List T → T)) =>
    let x2 : List
      (List T →
        List T →
          T) := Const.iter
      (α := List (List T → List T → T))
      «Authoring/IRs.tail»
      x1
      x0;
    x2

def «Authoring/IRs.atOr» :=
  fun (x0 : List T → List T → T)
    (x1 : List (List T → List T → T))
    (x2 : T) =>
    let x3 : List T →
      List T →
        T := Const.lcase
      (α := List T → List T → T)
      (β := List T → List T → T)
      («Authoring/IRs.drop» x2 x1)
      x0
      (fun (x3 : List T → List T → T) (_ : List (List T → List T → T)) =>
        x3);
    x3

def «Authoring.failIR» :=
  fun (_ : List T) (_ : List T) => «Prelude.none»

def «Authoring.map2» :=
  fun (x0 : T → T → T) (x1 : T) (x2 : T) =>
    let x3 : T := «Base.bindO»
      x1
      (fun (x3 : T) => «Base.mapO» (x0 x3) x2);
    x3

def «Authoring.binderName» :=
  fun (x0 : T) =>
    let x1 : T := «Reader.nameOf» (Const.child x0 (leaf 0)); x1

def «Authoring.ibinder» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x1)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x1)) (leaf 2))
        («Prelude.and»
          («Authoring.bindable» (Const.child x1 (leaf 0)))
          («Prelude.isSome» («Authoring.itype» x0 (Const.child x1 (leaf 1))))));
    x2

def «Authoring.ilam» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T → List T → T)
    (x4 : List T)
    (x5 : List T) =>
    let x6 : T := (if («Prelude.and»
      («Base.not» («Base.isEmpty» x2))
      («Base.allT» («Authoring.ibinder» x1) x2)).label ≠ 0 then
      «Base.mapO»
        (fun (x6 : T) =>
          Const.foldr
            (α := T)
            (β := T)
            (fun (x7 : T) (x8 : T) =>
              «Language.mLam»
                («Base.getD»
                  («Authoring.itype» x1 (Const.child x7 (leaf 1)))
                  «Theory.one»)
                x8)
            x6
            x2)
        (x3
          («Prelude.append»
            («Prelude.reverse» («Base.mapT» «Authoring.binderName» x2))
            x4)
          («Prelude.append»
            («Prelude.reverse»
              («Base.mapT»
                (fun (x6 : T) => «Authoring.kernelType» x0 (Const.child x6 (leaf 1)))
                x2))
            x5))
    else
      «Prelude.none»);
    x6

def «Authoring.iatom» :=
  fun (x0 : List T) (x1 : T) (x2 : List T) =>
    let x3 : T := (let x3 : T := «Reader.indexOf» x1 x2;
                   if («Prelude.isSome» x3).label ≠ 0 then
                     «Prelude.some» («Language.var» («Prelude.get» x3))
                   else
                     if (Const.equal x1 «Reader.kwUnitValue»).label ≠ 0 then
                       «Prelude.some» «Language.mStar»
                     else
                       «Base.mapO»
                         (fun (x4 : T) =>
                           «Translation.call»
                             (Const.add («Authoring/LD.length» «Translation.lib») x4)
                             ([] : List T)
                             ([] : List T))
                         («Reader.indexOf» x1 x0));
    x3

def «Authoring.iprim» :=
  fun (x0 : List T) (x1 : List T) (x2 : T → T) =>
    let x3 : T := (let x3 : T := «Prelude.length» x1;
                   let x4 : T := «Prelude.at» x1 (leaf 0);
                   let x5 : T →
                     T := (fun (x5 : T) => «Authoring.itype» x0 («Prelude.at» x1 x5));
                   if («Authoring.word» x4 «Reader.kwNil»).label ≠ 0 then
                     if (Const.eq x3 (leaf 2)).label ≠ 0 then
                       «Base.mapO»
                         (fun (x6 : T) =>
                           «Language.mArr» (leaf 0) («Prelude.single» x6) «Language.mStar»)
                         (x5 (leaf 1))
                     else
                       «Prelude.none»
                   else
                     if («Authoring.word» x4 «Reader.kwCons»).label ≠ 0 then
                       if (Const.eq x3 (leaf 4)).label ≠ 0 then
                         «Base.bindO»
                           (x5 (leaf 1))
                           (fun (x6 : T) =>
                             «Authoring.map2»
                               (fun (x7 : T) (x8 : T) =>
                                 «Language.mArr»
                                   (leaf 1)
                                   («Prelude.single» x6)
                                   («Language.mPair» x7 x8))
                               (x2 (leaf 2))
                               (x2 (leaf 3)))
                       else
                         «Prelude.none»
                     else
                       if («Authoring.word»
                         x4
                         (mk 0 [leaf 110, leaf 111, leaf 100, leaf 101])).label ≠ 0 then
                         if (Const.eq x3 (leaf 3)).label ≠ 0 then
                           «Authoring.map2»
                             (fun (x6 : T) (x7 : T) =>
                               «Language.mArr» (leaf 2) («Prelude.single» x6) x7)
                             (x5 (leaf 1))
                             (x2 (leaf 2))
                         else
                           «Prelude.none»
                       else
                         if («Prelude.or»
                           («Authoring.word» x4 (mk 0 [leaf 105, leaf 110, leaf 108]))
                           («Authoring.word»
                             x4
                             (mk 0 [leaf 105, leaf 110, leaf 114]))).label ≠ 0 then
                           if (Const.eq x3 (leaf 4)).label ≠ 0 then
                             «Base.bindO»
                               (x5 (leaf 1))
                               (fun (x6 : T) =>
                                 «Authoring.map2»
                                   (fun (x7 : T) (x8 : T) =>
                                     «Language.mArr»
                                       (if («Authoring.word»
                                         x4
                                         (mk 0 [leaf 105, leaf 110, leaf 108])).label ≠ 0 then
                                         leaf 3
                                       else
                                         leaf 4)
                                       («Theory.l2» x6 x7)
                                       x8)
                                   (x5 (leaf 2))
                                   (x2 (leaf 3)))
                           else
                             «Prelude.none»
                         else
                           if (Const.eq x3 (leaf 5)).label ≠ 0 then
                             «Base.bindO»
                               (x5 (leaf 1))
                               (fun (x6 : T) =>
                                 «Base.bindO»
                                   (x5 (leaf 2))
                                   (fun (x7 : T) =>
                                     «Authoring.map2»
                                       (fun (x8 : T) (x9 : T) =>
                                         «Language.mArr» (leaf 5) («Theory.l3» x6 x7 x8) x9)
                                       (x5 (leaf 3))
                                       (x2 (leaf 4))))
                           else
                             «Prelude.none»);
    x3

def «Authoring.primHead» :=
  fun (x0 : T) =>
    let x1 : T := «Prelude.or»
      («Authoring.word» x0 «Reader.kwNil»)
      («Prelude.or»
        («Authoring.word» x0 «Reader.kwCons»)
        («Prelude.or»
          («Authoring.word» x0 (mk 0 [leaf 110, leaf 111, leaf 100, leaf 101]))
          («Prelude.or»
            («Authoring.word» x0 (mk 0 [leaf 105, leaf 110, leaf 108]))
            («Prelude.or»
              («Authoring.word» x0 (mk 0 [leaf 105, leaf 110, leaf 114]))
              («Authoring.word»
                x0
                (mk 0 [leaf 99, leaf 97, leaf 115, leaf 101]))))));
    x1

def «Authoring.itermStep» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : T)
    (x4 : List (List T → List T → T)) =>
    let x5 : List T →
      List T →
        T := (let x5 : List T := Const.children x3;
              let x6 : T := «Prelude.length» x5;
              let x7 : T := «Prelude.at» x5 (leaf 0);
              fun (x8 : List T) (x9 : List T) =>
                let x10 : T →
                  List T →
                    List T →
                      T := (fun (x10 : T) =>
                  «Authoring/IRs.atOr» «Authoring.failIR» x4 x10);
                let x11 : T → T := (fun (x11 : T) => x10 x11 x8 x9);
                let x12 : List
                  T := «Base.mapT»
                  «Reader.nameOf»
                  (Const.children («Prelude.at» x5 (leaf 2)));
                if («Reader.isAtom» x3).label ≠ 0 then
                  «Authoring.iatom» x1 («Reader.nameOf» x3) x8
                else
                  if («Base.not» («Reader.isList» x3)).label ≠ 0 then
                    «Prelude.none»
                  else
                    if («Authoring.word» x7 «Reader.kwPair»).label ≠ 0 then
                      if (Const.eq x6 (leaf 3)).label ≠ 0 then
                        «Authoring.map2» «Language.mPair» (x11 (leaf 1)) (x11 (leaf 2))
                      else
                        «Prelude.none»
                    else
                      if («Authoring.word» x7 «Reader.kwFst»).label ≠ 0 then
                        if (Const.eq x6 (leaf 2)).label ≠ 0 then
                          «Base.mapO» «Language.mFst» (x11 (leaf 1))
                        else
                          «Prelude.none»
                      else
                        if («Authoring.word» x7 «Reader.kwSnd»).label ≠ 0 then
                          if (Const.eq x6 (leaf 2)).label ≠ 0 then
                            «Base.mapO» «Language.mSnd» (x11 (leaf 1))
                          else
                            «Prelude.none»
                        else
                          if («Authoring.word»
                            x7
                            (mk 0 [leaf 101,
                              leaf 113,
                              leaf 117,
                              leaf 97,
                              leaf 108])).label ≠ 0 then
                            if (Const.eq x6 (leaf 3)).label ≠ 0 then
                              «Authoring.map2» «Language.mEq» (x11 (leaf 1)) (x11 (leaf 2))
                            else
                              «Prelude.none»
                          else
                            if («Authoring.word» x7 «Reader.kwLam»).label ≠ 0 then
                              if («Prelude.and»
                                (Const.eq x6 (leaf 3))
                                («Reader.isList» («Prelude.at» x5 (leaf 1)))).label ≠ 0 then
                                «Authoring.ilam»
                                  x1
                                  x2
                                  (Const.children («Prelude.at» x5 (leaf 1)))
                                  (x10 (leaf 2))
                                  x8
                                  x9
                              else
                                «Prelude.none»
                            else
                              if («Authoring.primHead» x7).label ≠ 0 then
                                «Authoring.iprim» x2 x5 x11
                              else
                                if («Authoring.word»
                                  x7
                                  (mk 0 [leaf 108,
                                    leaf 105,
                                    leaf 115,
                                    leaf 116,
                                    leaf 45,
                                    leaf 114,
                                    leaf 101,
                                    leaf 99])).label ≠ 0 then
                                  if («Prelude.and»
                                    (Const.eq x6 (leaf 5))
                                    («Authoring.namesOk»
                                      (leaf 2)
                                      («Prelude.at» x5 (leaf 2)))).label ≠ 0 then
                                    «Base.bindO»
                                      (x11 (leaf 1))
                                      (fun (x13 : T) =>
                                        «Base.bindO»
                                          (x10
                                            (leaf 3)
                                            ((«Prelude.at» x12 (leaf 1)) ::
                                              ((«Prelude.at» x12 (leaf 0)) :: x8))
                                            («Prelude.none» :: («Prelude.none» :: x9)))
                                          (fun (x14 : T) =>
                                            «Base.mapO»
                                              («Language.mListRec» x13 x14)
                                              (x11 (leaf 4))))
                                  else
                                    «Prelude.none»
                                else
                                  if («Authoring.word»
                                    x7
                                    (mk 0 [leaf 114,
                                      leaf 111,
                                      leaf 115,
                                      leaf 101,
                                      leaf 45,
                                      leaf 114,
                                      leaf 101,
                                      leaf 99])).label ≠ 0 then
                                    if («Prelude.and»
                                      (Const.eq x6 (leaf 5))
                                      («Authoring.namesOk»
                                        (leaf 1)
                                        («Prelude.at» x5 (leaf 2)))).label ≠ 0 then
                                      «Base.bindO»
                                        («Authoring.itype» x2 («Prelude.at» x5 (leaf 1)))
                                        (fun (x13 : T) =>
                                          «Base.bindO»
                                            (x10
                                              (leaf 3)
                                              ((«Prelude.at» x12 (leaf 0)) :: x8)
                                              («Prelude.none» :: x9))
                                            (fun (x14 : T) =>
                                              «Base.mapO»
                                                («Language.mRoseRec» x13 x14)
                                                (x11 (leaf 4))))
                                    else
                                      «Prelude.none»
                                  else
                                    if («Authoring.word»
                                      x7
                                      (mk 0 [leaf 108, leaf 105, leaf 98])).label ≠ 0 then
                                      «Authoring.ilib» x2 x5 x11
                                    else
                                      if («Authoring.word»
                                        x7
                                        (mk 0 [leaf 107,
                                          leaf 101,
                                          leaf 114,
                                          leaf 110,
                                          leaf 101,
                                          leaf 108])).label ≠ 0 then
                                        if (Const.eq x6 (leaf 2)).label ≠ 0 then
                                          «Authoring.ikernel» x0 x1 («Prelude.at» x5 (leaf 1)) x8 x9
                                        else
                                          «Prelude.none»
                                      else
                                        if (Const.lt (leaf 1) x6).label ≠ 0 then
                                          «Base.bindO»
                                            (x11 (leaf 0))
                                            (fun (x13 : T) =>
                                              «Base.mapO»
                                                (fun (x14 : T) =>
                                                  «Tactics.apps» x13 (Const.children x14))
                                                («Base.allSomeT»
                                                  («Base.mapT»
                                                    x11
                                                    («Prelude.drop» (leaf 1) («Base.range» x6)))))
                                        else
                                          «Prelude.none»);
    x5

def «Authoring.iterm» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : List T →
      List T →
        T := Const.para
      (α := List T → List T → T)
      («Authoring.itermStep» x0 x1 x2)
      x3;
    x4

def «Authoring.readEqn» :=
  fun (x0 : T) (x1 : T) (x2 : List T) (x3 : T → T) (x4 : T) =>
    let x5 : T := (if («Authoring.form»
      x4
      (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
      (leaf 3)).label ≠ 0 then
      «Base.bindO»
        (x3 (Const.child x4 (leaf 1)))
        (fun (x5 : T) =>
          «Base.bindO»
            (x3 (Const.child x4 (leaf 2)))
            (fun (x6 : T) =>
              let x7 : T := «Derivation.typeIn» x0 x1 x2 x5;
              if («Prelude.and»
                («Prelude.isSome» x7)
                (Const.equal x7 («Derivation.typeIn» x0 x1 x2 x6))).label ≠ 0 then
                «Prelude.some» («Language.mEq» x5 x6)
              else
                «Prelude.none»))
    else
      «Prelude.none»);
    x5

def «Authoring.statement» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) (x4 : T) =>
    Const.node
      (leaf 0)
      (x0 :: (x1 :: (x2 :: (x3 :: (x4 :: ([] : List T))))))

def «Authoring/OSt.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OSt.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OSt.isJust» :=
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

def «Authoring/OSt.fromMaybe» :=
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

def «Authoring/OSt.nthOf» :=
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
      «Authoring/OSt.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OSt.just» x2);
    x2

def «Authoring/OSt.allJust» :=
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

def «Authoring.binderOk» :=
  fun (x0 : List T) (x1 : List T) (x2 : T) (x3 : T) =>
    let x4 : T := «Prelude.and»
      («Reader.isList» x3)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x3)) (leaf 2))
        (if (x2).label ≠ 0 then
          «Prelude.and»
            («Authoring.bindable» (Const.child x3 (leaf 0)))
            («Prelude.isSome» («Authoring.itype» x1 (Const.child x3 (leaf 1))))
        else
          «Prelude.and»
            («Authoring.declared» (Const.child x3 (leaf 0)))
            («Prelude.isSome»
              («Authoring.kernelType» x0 (Const.child x3 (leaf 1))))));
    x4

def «Authoring.hypOk» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := «Prelude.and»
      («Reader.isList» x1)
      («Prelude.and»
        (Const.eq («Prelude.length» (Const.children x1)) (leaf 2))
        (if (x0).label ≠ 0 then
          «Authoring.bindable» (Const.child x1 (leaf 0))
        else
          «Authoring.declared» (Const.child x1 (leaf 0))));
    x2

def «Authoring.readQuantified» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := «Authoring.form»
                     x6
                     (mk 0 [leaf 102, leaf 111, leaf 114, leaf 97, leaf 108, leaf 108])
                     (leaf 3);
                   let x8 : List
                     T := (if (x7).label ≠ 0 then
                     Const.children (Const.child x6 (leaf 1))
                   else
                     ([] : List T));
                   let x9 : T := (if (x7).label ≠ 0 then
                     Const.child x6 (leaf 2)
                   else
                     x6);
                   let x10 : T := «Prelude.length» (Const.children x9);
                   let x11 : T := «Prelude.and»
                     («Authoring.headed»
                       x9
                       (mk 0 [leaf 105,
                         leaf 109,
                         leaf 112,
                         leaf 108,
                         leaf 105,
                         leaf 101,
                         leaf 115]))
                     (Const.lt (leaf 2) x10);
                   let x12 : List
                     T := (if (x11).label ≠ 0 then
                     «Base.take»
                       (Const.sub x10 (leaf 2))
                       («Prelude.drop» (leaf 1) (Const.children x9))
                   else
                     ([] : List T));
                   let x13 : T := (if (x11).label ≠ 0 then
                     «Prelude.at» (Const.children x9) (Const.sub x10 (leaf 1))
                   else
                     x9);
                   let x14 : List
                     T := «Prelude.reverse» («Base.mapT» «Authoring.binderName» x8);
                   let x15 : List T := «Base.mapT» «Authoring.binderName» x12;
                   let x16 : T := «Prelude.length» x4;
                   if («Prelude.and»
                     («Prelude.or»
                       («Base.not» x7)
                       («Prelude.and»
                         («Reader.isList» (Const.child x6 (leaf 1)))
                         («Base.not» («Base.isEmpty» x8))))
                     («Prelude.and»
                       («Base.allT» («Authoring.binderOk» x2 x4 x5) x8)
                       («Prelude.and»
                         («Base.allT» («Authoring.hypOk» x5) x12)
                         («Authoring.distinctFrom»
                           x3
                           («Prelude.append» x14 x15))))).label ≠ 0 then
                     let x17 : List
                       T := «Prelude.reverse»
                       («Base.mapT»
                         (fun (x17 : T) =>
                           «Base.getD»
                             («Authoring.itype» x4 (Const.child x17 (leaf 1)))
                             «Theory.one»)
                         x8);
                     let x18 : List
                       T := «Prelude.reverse»
                       («Base.mapT»
                         (fun (x18 : T) =>
                           «Authoring.kernelType» x2 (Const.child x18 (leaf 1)))
                         x8);
                     let x19 : T →
                       T := (fun (x19 : T) =>
                       if (x5).label ≠ 0 then
                         «Authoring.iterm» x1 x2 x4 x19 x14 x18
                       else
                         «Authoring.ikernel» x1 x2 x19 x14 x18);
                     let x20 : T := «Base.allSomeT»
                       («Base.mapT»
                         (fun (x20 : T) =>
                           «Authoring.readEqn» x0 x16 x17 x19 (Const.child x20 (leaf 1)))
                         x12);
                     let x21 : T := «Authoring.readEqn» x0 x16 x17 x19 x13;
                     if («Prelude.and»
                       («Prelude.isSome» x20)
                       («Prelude.isSome» x21)).label ≠ 0 then
                       «Authoring/OSt.just»
                         («Authoring.statement»
                           (Const.node (leaf 0) x4)
                           (Const.node (leaf 0) x14)
                           (Const.node (leaf 0) x18)
                           (Const.node (leaf 0) x15)
                           («Derivation.mkThm»
                             x16
                             («Language.objs» x17)
                             («Derivation.terms» (Const.children («Prelude.get» x20)))
                             («Prelude.get» x21)))
                     else
                       «Authoring/OSt.nothing»
                   else
                     «Authoring/OSt.nothing»);
    x7

def «Authoring.readStatement» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : T := (if («Prelude.and»
      (Const.lt (leaf 1) x0)
      («Authoring.form»
        x5
        (mk 0 [leaf 105,
          leaf 110,
          leaf 116,
          leaf 101,
          leaf 114,
          leaf 110,
          leaf 97,
          leaf 108])
        (leaf 3))).label ≠ 0 then
      let x6 : List
        T := «Base.mapT»
        «Reader.nameOf»
        (Const.children (Const.child x5 (leaf 1)));
      if («Prelude.and»
        («Reader.isList» (Const.child x5 (leaf 1)))
        («Prelude.and»
          («Base.allT»
            «Authoring.bindable»
            (Const.children (Const.child x5 (leaf 1))))
          («Authoring.distinctFrom» x4 x6))).label ≠ 0 then
        «Authoring.readQuantified»
          x1
          x2
          x3
          («Prelude.append» x4 x6)
          x6
          (leaf 1)
          (Const.child x5 (leaf 2))
      else
        «Authoring/OSt.nothing»
    else
      «Authoring.readQuantified» x1 x2 x3 x4 ([] : List T) (leaf 0) x5);
    x6

def «Authoring/SRs.single» :=
  fun (x0 : List T →
      List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T)) =>
    let x1 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := (x0 ::
      ([] : List (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))));
    x1

def «Authoring/SRs.length» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : T := Const.foldr
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := T)
      (fun (_ : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : T) =>
        Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/SRs.append» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x1 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x2 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.foldr
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (x2 : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x3 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/SRs.reverse» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.foldr
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)) →
        List
          (List T →
            List T →
              List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (x1 : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T)) →
           List
             (List T →
               List T →
                 List T → T × (T → List T → List T → List T → List T → T → T → T)))
         (x3 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x2 (x1 :: x3))
      (fun (x1 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x1)
      x0
      ([] : List (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)));
    x1

def «Authoring/SRs.tail» :=
  fun (x0 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x1 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.lcase
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      x0
      ([] : List (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
      (fun (_ : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (x2 : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x2);
    x1

def «Authoring/SRs.drop» :=
  fun (x0 : T)
    (x1 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x2 : List
      (List T →
        List T →
          List T →
            T ×
              (T →
                List T →
                  List T →
                    List T →
                      List T →
                        T →
                          T →
                            T)) := Const.iter
      (α := List
        (List T →
          List T →
            List T → T × (T → List T → List T → List T → List T → T → T → T)))
      «Authoring/SRs.tail»
      x1
      x0;
    x2

def «Authoring/SRs.atOr» :=
  fun (x0 : List T →
      List T →
        List T → T × (T → List T → List T → List T → List T → T → T → T))
    (x1 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x2 : T) =>
    let x3 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := Const.lcase
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      (β := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      («Authoring/SRs.drop» x2 x1)
      x0
      (fun (x3 : List T →
           List T →
             List T → T × (T → List T → List T → List T → List T → T → T → T))
         (_ : List
           (List T →
             List T →
               List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
        x3);
    x3

def «Authoring.failTac» :=
  fun (_ : T)
    (_ : List T)
    (_ : List T)
    (_ : List T)
    (_ : List T)
    (_ : T)
    (_ : T) =>
    «Prelude.none»

def «Authoring.failSR» :=
  fun (_ : List T) (_ : List T) (_ : List T) =>
    (leaf 0, «Authoring.failTac»)

def «Authoring.ruleOk» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) (x4 : T) =>
    let x5 : T := (if («Reader.isAtom» x4).label ≠ 0 then
      «Prelude.or»
        («Authoring.has» («Reader.nameOf» x4) x2)
        («Authoring.has» («Reader.nameOf» x4) x3)
    else
      «Prelude.and»
        (Const.lt (leaf 1) x0)
        («Prelude.and»
          («Reader.isList» x4)
          («Prelude.and»
            («Reader.isAtom» (Const.child x4 (leaf 0)))
            («Prelude.and»
              («Authoring.has» («Reader.nameOf» (Const.child x4 (leaf 0))) x3)
              («Base.allT»
                (fun (x5 : T) => «Prelude.isSome» («Authoring.itype» x1 x5))
                («Prelude.drop» (leaf 1) (Const.children x4)))))));
    x5

def «Authoring.ruleOf» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : T) =>
    let x4 : T := (let x4 : T := (if («Reader.isAtom» x3).label ≠ 0 then
                     «Reader.indexOf» («Reader.nameOf» x3) x1
                   else
                     «Prelude.none»);
                   if («Prelude.isSome» x4).label ≠ 0 then
                     «Prover.nrHyp» («Prelude.get» x4)
                   else
                     «Prover.nrThm»
                       (Const.add
                         (Const.mul
                           (leaf 2)
                           («Base.getD»
                             («Reader.indexOf»
                               («Reader.nameOf»
                                 (if («Reader.isAtom» x3).label ≠ 0 then
                                   x3
                                 else
                                   Const.child x3 (leaf 0)))
                               x2)
                             (leaf 0)))
                         (leaf 1))
                       («Language.objs»
                         (if («Reader.isAtom» x3).label ≠ 0 then
                           ([] : List T)
                         else
                           «Base.mapT»
                             (fun (x5 : T) => «Base.getD» («Authoring.itype» x0 x5) «Theory.one»)
                             («Prelude.drop» (leaf 1) (Const.children x3)))));
    x4

def «Authoring.rulesFrom» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x4 : T) (x5 : List T) =>
        ((«Authoring.ruleOf» x0 x1 x2 x4) :: x5))
      ([] : List T)
      x3;
    x4

def «Authoring.depthOf» :=
  fun (x0 : T) =>
    let x1 : T := (if («Authoring.word»
      x0
      (mk 0 [leaf 104, leaf 101, leaf 97, leaf 100])).label ≠ 0 then
      «Prelude.some» (leaf 0)
    else
      if («Authoring.word»
        x0
        (mk 0 [leaf 119, leaf 101, leaf 97, leaf 107])).label ≠ 0 then
        «Prelude.some» (leaf 1)
      else
        if («Authoring.word»
          x0
          (mk 0 [leaf 111, leaf 112, leaf 101, leaf 110])).label ≠ 0 then
          «Prelude.some» (leaf 2)
        else
          if («Authoring.word»
            x0
            (mk 0 [leaf 102, leaf 117, leaf 108, leaf 108])).label ≠ 0 then
            «Prelude.some» (leaf 3)
          else
            «Prelude.none»);
    x1

def «Authoring.lemmaOf» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (if («Reader.isAtom» x1).label ≠ 0 then
      «Base.mapO»
        (fun (x2 : T) => Const.mul (leaf 2) x2)
        («Reader.indexOf» («Reader.nameOf» x1) x0)
    else
      «Prelude.none»);
    x2

def «Authoring.byPointwise» :=
  fun (x0 : T) (x1 : List T) (x2 : T) (x3 : T) (x4 : List T) (x5 : T) =>
    let x6 : List T →
      List T →
        T →
          T →
            T := (fun (x6 : List T) (x7 : List T) (x8 : T) (x9 : T) =>
      let x10 : T := «Derivation.thmAt» x1 x3;
      if (Const.eq (Const.label x10) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x10; «Prelude.none»
      else
        let x11 : List T := Const.children x10;
        let x12 : T := Const.lcase
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
        «Derivation.bindPT»
          («Derivation.eqParts» («Derivation.thConcl» x12))
          (fun (x14 : T) =>
            let x15 : T := «Language.app»
              («Derivation.weaken1» («Language.p1» x14))
              («Language.var» (leaf 0));
            let x16 : T := «Language.app»
              («Derivation.weaken1» («Language.p2» x14))
              («Language.var» (leaf 0));
            «Prover.bindNT»
              («Prover.eval» x0 x1 x2 x4 (leaf 4096) x5 x6 x7 x15)
              (fun (x17 : T) =>
                «Prover.bindNT»
                  («Prover.eval» x0 x1 x2 x4 (leaf 4096) x5 x6 x7 x16)
                  (fun (x18 : T) =>
                    «Prover.bindNT»
                      («Prover.eval» x0 x1 x2 x4 (leaf 4096) x5 x6 x7 x8)
                      (fun (x19 : T) =>
                        «Prover.bindNT»
                          («Prover.eval» x0 x1 x2 x4 (leaf 4096) x5 x6 x7 x9)
                          (fun (x20 : T) =>
                            if («Prelude.and»
                              (Const.equal («Prover.nfTerm» x19) («Prover.nfTerm» x17))
                              (Const.equal
                                («Prover.nfTerm» x20)
                                («Prover.nfTerm» x18))).label ≠ 0 then
                              «Prelude.some»
                                («Prover.dNode»
                                  (leaf 23)
                                  ([] : List T)
                                  («Theory.l2»
                                    («Prover.dNode»
                                      (leaf 2)
                                      ([] : List T)
                                      («Theory.l2»
                                        («Prover.mDeriv» («Prover.nfMarked» x19))
                                        («Prover.mDeriv» («Prover.nfMarked» x20))))
                                    («Prover.dNode»
                                      (leaf 24)
                                      («Prelude.single» («Language.mEq» x15 x16))
                                      («Theory.l2»
                                        («Prover.dNode»
                                          (leaf 2)
                                          ([] : List T)
                                          («Theory.l2»
                                            («Prover.mDeriv» («Prover.nfMarked» x17))
                                            («Prover.mDeriv» («Prover.nfMarked» x18))))
                                        («Prover.dNode»
                                          (leaf 18)
                                          ([] : List T)
                                          («Theory.l2»
                                            («Prover.dNode»
                                              (leaf 2)
                                              ([] : List T)
                                              («Theory.l2»
                                                («Prover.dNode»
                                                  (leaf 16)
                                                  («Theory.l4»
                                                    x3
                                                    (Const.node
                                                      (leaf 0)
                                                      («Base.mapT» «Theory.x» («Base.range» x2)))
                                                    (Const.node
                                                      (leaf 0)
                                                      («Base.mapT»
                                                        (fun (x21 : T) =>
                                                          «Language.var» (Const.add x21 (leaf 1)))
                                                        («Base.range»
                                                          («Prelude.length»
                                                            («Derivation.thCtx» x12)))))
                                                    (leaf 0))
                                                  ([] : List T))
                                                («Prover.dNode»
                                                  (leaf 0)
                                                  ([] : List T)
                                                  ([] : List T))))
                                            («Prover.dNode»
                                              (leaf 0)
                                              ([] : List T)
                                              ([] : List T))))))))
                            else
                              «Prelude.none»))))));
    x6

def «Authoring.script3» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List T)
    (x6 : List T)
    (x7 : List T) =>
    let x8 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x8 : List T := Const.children x4;
                           let x9 : T := «Prelude.length» x8;
                           let x10 : T := «Prelude.length» x2;
                           let x11 : T := «Prelude.at» x8 (leaf 1);
                           let x12 : T →
                             T := (fun (x12 : T) => «Authoring.iterm» x0 x1 x2 x12 x5 x6);
                           if («Authoring.headed»
                             x4
                             (mk 0 [leaf 112,
                               leaf 111,
                               leaf 105,
                               leaf 110,
                               leaf 116,
                               leaf 119,
                               leaf 105,
                               leaf 115,
                               leaf 101])).label ≠ 0 then
                             let x13 : T := «Authoring.lemmaOf» x3 x11;
                             («Prelude.and»
                               (Const.lt (leaf 2) x9)
                               («Prelude.and»
                                 («Prelude.isSome» x13)
                                 («Prelude.and»
                                   («Prelude.isSome»
                                     («Authoring.depthOf» («Prelude.at» x8 (leaf 2))))
                                   («Base.allT»
                                     («Authoring.ruleOk» (leaf 2) x2 x7 x3)
                                     («Prelude.drop» (leaf 3) x8)))),
                               fun (x14 : T) (x15 : List T) (x16 : List T) =>
                                 «Authoring.byPointwise»
                                   x14
                                   x15
                                   x10
                                   («Base.getD» x13 (leaf 0))
                                   («Authoring/Rules.append»
                                     («Authoring.rulesFrom» x2 x7 x3 («Prelude.drop» (leaf 3) x8))
                                     x16)
                                   («Base.getD»
                                     («Authoring.depthOf» («Prelude.at» x8 (leaf 2)))
                                     (leaf 0)))
                           else
                             if («Authoring.form»
                               x4
                               (mk 0 [leaf 109,
                                 leaf 97,
                                 leaf 115,
                                 leaf 107,
                                 leaf 45,
                                 leaf 114,
                                 leaf 101,
                                 leaf 119,
                                 leaf 114,
                                 leaf 105,
                                 leaf 116,
                                 leaf 101])
                               (leaf 12)).label ≠ 0 then
                               let x13 : T := «Authoring.itype» x2 x11;
                               let x14 : T := «Authoring.itype» x2 («Prelude.at» x8 (leaf 2));
                               let x15 : T := «Authoring.lemmaOf» x3 («Prelude.at» x8 (leaf 3));
                               let x16 : T := «Prelude.at» x8 (leaf 4);
                               let x17 : T := «Authoring.lemmaOf»
                                 x3
                                 (if («Reader.isAtom» x16).label ≠ 0 then
                                   x16
                                 else
                                   Const.child x16 (leaf 0));
                               let x18 : T := «Base.allSomeT»
                                 («Base.mapT»
                                   («Authoring.itype» x2)
                                   (if («Reader.isAtom» x16).label ≠ 0 then
                                     ([] : List T)
                                   else
                                     «Prelude.drop» (leaf 1) (Const.children x16)));
                               let x19 : T := «Base.allSomeT»
                                 («Base.mapT» x12 (Const.children («Prelude.at» x8 (leaf 5))));
                               let x20 : T := «Base.allSomeT»
                                 («Base.mapT» x12 («Prelude.drop» (leaf 6) x8));
                               («Prelude.and»
                                 («Prelude.isSome» x13)
                                 («Prelude.and»
                                   («Prelude.isSome» x14)
                                   («Prelude.and»
                                     («Prelude.isSome» x15)
                                     («Prelude.and»
                                       («Prelude.isSome» x17)
                                       («Prelude.and»
                                         («Prelude.isSome» x18)
                                         («Prelude.and»
                                           («Reader.isList» («Prelude.at» x8 (leaf 5)))
                                           («Prelude.and»
                                             («Prelude.isSome» x19)
                                             («Prelude.isSome» x20))))))),
                                 fun (_ : T)
                                   (_ : List T)
                                   (_ : List T)
                                   (_ : List T)
                                   (_ : List T)
                                   (_ : T)
                                   (_ : T) =>
                                   let x28 : List
                                     T := Const.children
                                     («Base.getD» x20 (Const.node (leaf 0) ([] : List T)));
                                   «Prelude.some»
                                     («Tactics.maskRw»
                                       («Base.getD» x13 «Theory.one»)
                                       («Base.getD» x14 «Theory.one»)
                                       («Base.getD» x15 (leaf 0))
                                       («Base.getD» x17 (leaf 0))
                                       (Const.children
                                         («Base.getD» x18 (Const.node (leaf 0) ([] : List T))))
                                       (Const.children
                                         («Base.getD» x19 (Const.node (leaf 0) ([] : List T))))
                                       («Prelude.at» x28 (leaf 0))
                                       («Prelude.at» x28 (leaf 1))
                                       («Prelude.at» x28 (leaf 2))
                                       («Prelude.at» x28 (leaf 3))
                                       («Prelude.at» x28 (leaf 4))
                                       («Prelude.at» x28 (leaf 5))))
                             else
                               (leaf 0, «Authoring.failTac»));
    x8

def «Authoring.script2» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T)))
    (x6 : List T)
    (x7 : List T)
    (x8 : List T) =>
    let x9 : T ×
      (T →
        List T →
          List T →
            List T →
              List T →
                T →
                  T →
                    T) := (let x9 : List T := Const.children x4;
                           let x10 : T := «Prelude.length» x9;
                           let x11 : T := «Prelude.length» x2;
                           let x12 : T := «Prelude.at» x9 (leaf 1);
                           let x13 : List
                             T := «Base.mapT»
                             «Reader.nameOf»
                             (Const.children («Prelude.at» x9 (leaf 2)));
                           let x14 : T →
                             List T →
                               List T →
                                 List T →
                                   T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := (fun (x14 : T) =>
                             «Authoring/SRs.atOr» «Authoring.failSR» x5 x14);
                           let x15 : T →
                             List
                               T := (fun (x15 : T) =>
                             «Authoring.rulesFrom» x2 x8 x3 («Prelude.drop» x15 x9));
                           let x16 : T →
                             T := (fun (x16 : T) =>
                             «Base.allT»
                               («Authoring.ruleOk» (leaf 2) x2 x8 x3)
                               («Prelude.drop» x16 x9));
                           let x17 : List T →
                             List T →
                               T := (fun (x17 : List T) (x18 : List T) =>
                             «Authoring.distinctFrom»
                               («Prelude.append» x17 («Prelude.append» x8 x3))
                               x18);
                           let x18 : T := «Reader.indexOf» («Reader.nameOf» x12) x6;
                           let x19 : T := «Authoring.number» («Prelude.at» x9 (leaf 4));
                           if («Authoring.headed»
                             x4
                             (mk 0 [leaf 102,
                               leaf 111,
                               leaf 108,
                               leaf 100,
                               leaf 45,
                               leaf 105,
                               leaf 110,
                               leaf 100,
                               leaf 117,
                               leaf 99,
                               leaf 116,
                               leaf 105,
                               leaf 111,
                               leaf 110])).label ≠ 0 then
                             let x20 : List T := «Prelude.drop» (leaf 1) x6;
                             let x21 : T := «Authoring.iterm»
                               x0
                               x1
                               x2
                               («Prelude.at» x9 (leaf 3))
                               ((«Prelude.at» x13 (leaf 1)) :: ((«Prelude.at» x13 (leaf 0)) :: x20))
                               («Prelude.none» :: («Prelude.none» :: («Prelude.drop» (leaf 1) x7)));
                             («Prelude.and»
                               (Const.lt (leaf 4) x10)
                               («Prelude.and»
                                 («Prelude.and»
                                   («Base.not» («Base.isEmpty» x6))
                                   («Authoring.word» x12 («Prelude.at» x6 (leaf 0))))
                                 («Prelude.and»
                                   («Authoring.namesOk» (leaf 2) («Prelude.at» x9 (leaf 2)))
                                   («Prelude.and»
                                     (x17 x20 x13)
                                     («Prelude.and»
                                       («Prelude.isSome» x21)
                                       («Prelude.and» («Prelude.isSome» x19) (x16 (leaf 5))))))),
                               fun (x22 : T) (x23 : List T) (x24 : List T) =>
                                 «Prover.byListInd»
                                   x22
                                   x23
                                   x11
                                   (leaf 0)
                                   (leaf 1)
                                   («Base.getD» x21 «Language.mStar»)
                                   («Authoring/Rules.append» (x15 (leaf 5)) x24)
                                   («Base.getD» x19 (leaf 0)))
                           else
                             if («Authoring.headed»
                               x4
                               (mk 0 [leaf 116,
                                 leaf 114,
                                 leaf 101,
                                 leaf 101,
                                 leaf 45,
                                 leaf 102,
                                 leaf 111,
                                 leaf 108,
                                 leaf 100,
                                 leaf 45,
                                 leaf 105,
                                 leaf 110,
                                 leaf 100,
                                 leaf 117,
                                 leaf 99,
                                 leaf 116,
                                 leaf 105,
                                 leaf 111,
                                 leaf 110])).label ≠ 0 then
                               let x20 : T := «Authoring.iterm»
                                 x0
                                 x1
                                 x2
                                 («Prelude.at» x9 (leaf 3))
                                 ((«Prelude.at» x13 (leaf 1)) ::
                                   ((«Prelude.at» x13 (leaf 0)) :: ([] : List T)))
                                 («Prelude.none» :: («Prelude.none» :: ([] : List T)));
                               («Prelude.and»
                                 (Const.lt (leaf 4) x10)
                                 («Prelude.and»
                                   («Prelude.and»
                                     (Const.eq («Prelude.length» x6) (leaf 1))
                                     («Authoring.word» x12 («Prelude.at» x6 (leaf 0))))
                                   («Prelude.and»
                                     («Base.isEmpty» x8)
                                     («Prelude.and»
                                       («Authoring.namesOk» (leaf 2) («Prelude.at» x9 (leaf 2)))
                                       («Prelude.and»
                                         (x17 ([] : List T) x13)
                                         («Prelude.and»
                                           («Prelude.isSome» x20)
                                           («Prelude.and»
                                             («Prelude.isSome» x19)
                                             (x16 (leaf 5)))))))),
                                 fun (x21 : T)
                                   (x22 : List T)
                                   (x23 : List T)
                                   (x24 : List T)
                                   (_ : List T)
                                   (x26 : T)
                                   (x27 : T) =>
                                   «Prover.byRoseInd»
                                     x21
                                     x22
                                     x11
                                     (leaf 2)
                                     (leaf 0)
                                     (leaf 1)
                                     («Base.getD» x20 «Language.mStar»)
                                     («Authoring/Rules.append» (x15 (leaf 5)) x23)
                                     («Base.getD» x19 (leaf 0))
                                     x24
                                     x26
                                     x27)
                             else
                               if («Authoring.form»
                                 x4
                                 (mk 0 [leaf 115,
                                   leaf 117,
                                   leaf 109,
                                   leaf 45,
                                   leaf 99,
                                   leaf 97,
                                   leaf 115,
                                   leaf 101,
                                   leaf 115])
                                 (leaf 5)).label ≠ 0 then
                                 let x20 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T →
                                           List T →
                                             T →
                                               T →
                                                 T) := x14
                                   (leaf 3)
                                   ((«Prelude.at» x13 (leaf 0)) :: x6)
                                   («Prelude.none» :: x7)
                                   x8;
                                 let x21 : T ×
                                   (T →
                                     List T →
                                       List T →
                                         List T →
                                           List T →
                                             T →
                                               T →
                                                 T) := x14
                                   (leaf 4)
                                   ((«Prelude.at» x13 (leaf 0)) :: x6)
                                   («Prelude.none» :: x7)
                                   x8;
                                 («Prelude.and»
                                   («Prelude.isSome» x18)
                                   («Prelude.and»
                                     («Authoring.namesOk» (leaf 1) («Prelude.at» x9 (leaf 2)))
                                     («Prelude.and» (x17 x6 x13) («Prelude.and» (x20).1 (x21).1))),
                                   fun (x22 : T) (x23 : List T) (x24 : List T) =>
                                     «Tactics.bySplit2»
                                       (leaf 3)
                                       (leaf 4)
                                       («Base.getD» x18 (leaf 0))
                                       ((x20).2 x22 x23 x24)
                                       ((x21).2 x22 x23 x24))
                               else
                                 if («Authoring.form»
                                   x4
                                   (mk 0 [leaf 116,
                                     leaf 114,
                                     leaf 101,
                                     leaf 101,
                                     leaf 45,
                                     leaf 99,
                                     leaf 97,
                                     leaf 115,
                                     leaf 101,
                                     leaf 115])
                                   (leaf 5)).label ≠ 0 then
                                   let x20 : T ×
                                     (T →
                                       List T →
                                         List T →
                                           List T →
                                             List T →
                                               T →
                                                 T →
                                                   T) := x14
                                     (leaf 4)
                                     ((«Prelude.at» x13 (leaf 1)) ::
                                       ((«Prelude.at» x13 (leaf 0)) :: x6))
                                     («Prelude.none» :: («Prelude.none» :: x7))
                                     x8;
                                   let x21 : T := «Authoring.lemmaOf» x3 («Prelude.at» x9 (leaf 3));
                                   («Prelude.and»
                                     («Prelude.isSome» x18)
                                     («Prelude.and»
                                       («Authoring.namesOk» (leaf 2) («Prelude.at» x9 (leaf 2)))
                                       («Prelude.and»
                                         (x17 x6 x13)
                                         («Prelude.and» («Prelude.isSome» x21) (x20).1))),
                                     fun (x22 : T) (x23 : List T) (x24 : List T) =>
                                       «Tactics.byTreeSplit»
                                         («Base.getD» x21 (leaf 0))
                                         («Base.getD» x18 (leaf 0))
                                         ((x20).2 x22 x23 x24))
                                 else
                                   if («Authoring.headed»
                                     x4
                                     (mk 0 [leaf 97,
                                       leaf 117,
                                       leaf 116,
                                       leaf 111,
                                       leaf 45,
                                       leaf 116,
                                       leaf 114,
                                       leaf 101,
                                       leaf 101,
                                       leaf 115])).label ≠ 0 then
                                     let x20 : T := «Authoring.lemmaOf»
                                       x3
                                       («Prelude.at» x9 (leaf 3));
                                     («Prelude.and»
                                       (Const.lt (leaf 3) x10)
                                       («Prelude.and»
                                         («Prelude.isSome» («Authoring.depthOf» x12))
                                         («Prelude.and»
                                           («Prelude.isSome»
                                             («Authoring.number» («Prelude.at» x9 (leaf 2))))
                                           («Prelude.and» («Prelude.isSome» x20) (x16 (leaf 4))))),
                                       fun (x21 : T) (x22 : List T) (x23 : List T) =>
                                         «Tactics.byAutoT»
                                           x21
                                           x22
                                           x11
                                           («Base.getD» x20 (leaf 0))
                                           («Authoring/Rules.append» (x15 (leaf 4)) x23)
                                           («Base.getD»
                                             («Authoring.number» («Prelude.at» x9 (leaf 2)))
                                             (leaf 0))
                                           («Base.getD» («Authoring.depthOf» x12) (leaf 0)))
                                   else
                                     if («Authoring.form»
                                       x4
                                       (mk 0 [leaf 103,
                                         leaf 101,
                                         leaf 110,
                                         leaf 101,
                                         leaf 114,
                                         leaf 97,
                                         leaf 108,
                                         leaf 105,
                                         leaf 122,
                                         leaf 101])
                                       (leaf 4)).label ≠ 0 then
                                       let x20 : T := «Authoring.itype»
                                         x2
                                         (Const.child x12 (leaf 1));
                                       let x21 : T := «Authoring.iterm»
                                         x0
                                         x1
                                         x2
                                         («Prelude.at» x9 (leaf 2))
                                         x6
                                         x7;
                                       let x22 : T := «Reader.nameOf» (Const.child x12 (leaf 0));
                                       let x23 : T ×
                                         (T →
                                           List T →
                                             List T →
                                               List T →
                                                 List T →
                                                   T →
                                                     T →
                                                       T) := x14
                                         (leaf 3)
                                         (x22 :: x6)
                                         ((«Authoring.kernelType» x1 (Const.child x12 (leaf 1))) ::
                                           x7)
                                         x8;
                                       («Prelude.and»
                                         («Authoring.ibinder» x2 x12)
                                         («Prelude.and»
                                           (x17 x6 («Prelude.single» x22))
                                           («Prelude.and» («Prelude.isSome» x21) (x23).1)),
                                         fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                           «Tactics.byGeneralize»
                                             («Base.getD» x20 «Theory.one»)
                                             («Base.getD» x21 «Language.mStar»)
                                             ((x23).2 x24 x25 x26))
                                     else
                                       «Authoring.script3» x0 x1 x2 x3 x4 x6 x7 x8);
    x9

def «Authoring.scriptStep» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T)
    (x6 : List
      (List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))) =>
    let x7 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := (let x7 : List T := Const.children x5;
                                 let x8 : T := «Prelude.length» x7;
                                 let x9 : T := «Prelude.length» x3;
                                 let x10 : T := «Prelude.at» x7 (leaf 1);
                                 let x11 : T →
                                   List T →
                                     List T →
                                       List T →
                                         T ×
                                           (T →
                                             List T →
                                               List T →
                                                 List T →
                                                   List T →
                                                     T →
                                                       T →
                                                         T) := (fun (x11 : T) =>
                                   «Authoring/SRs.atOr» «Authoring.failSR» x6 x11);
                                 fun (x12 : List T) (x13 : List T) (x14 : List T) =>
                                   let x15 : T →
                                     List
                                       T := (fun (x15 : T) =>
                                     «Authoring.rulesFrom» x3 x14 x4 («Prelude.drop» x15 x7));
                                   let x16 : T →
                                     T := (fun (x16 : T) =>
                                     «Base.allT»
                                       («Authoring.ruleOk» x0 x3 x14 x4)
                                       («Prelude.drop» x16 x7));
                                   let x17 : List T →
                                     List T →
                                       T := (fun (x17 : List T) (x18 : List T) =>
                                     «Prelude.and»
                                       («Base.allT»
                                         (fun (x19 : T) =>
                                           if (Const.lt (leaf 1) x0).label ≠ 0 then
                                             «Authoring.bindable» x19
                                           else
                                             «Authoring.declared» x19)
                                         x18)
                                       («Authoring.distinctFrom»
                                         («Prelude.append» x17 («Prelude.append» x14 x4))
                                         («Base.mapT» «Reader.nameOf» x18)));
                                   if («Base.not» («Reader.isList» x5)).label ≠ 0 then
                                     (leaf 0, «Authoring.failTac»)
                                   else
                                     if («Authoring.headed»
                                       x5
                                       (mk 0 [leaf 110,
                                         leaf 111,
                                         leaf 114,
                                         leaf 109,
                                         leaf 97,
                                         leaf 108,
                                         leaf 105,
                                         leaf 122,
                                         leaf 101])).label ≠ 0 then
                                       («Prelude.and»
                                         (Const.lt (leaf 1) x8)
                                         («Prelude.and»
                                           («Prelude.isSome» («Authoring.number» x10))
                                           (x16 (leaf 2))),
                                         fun (x18 : T)
                                           (x19 : List T)
                                           (x20 : List T)
                                           (x21 : List T)
                                           (x22 : List T)
                                           (x23 : T)
                                           (x24 : T) =>
                                           «Prover.byNormW»
                                             x18
                                             x19
                                             x9
                                             («Authoring/Rules.append» (x15 (leaf 2)) x20)
                                             («Base.getD» («Authoring.number» x10) (leaf 0))
                                             x21
                                             x22
                                             x23
                                             x24)
                                     else
                                       if («Authoring.headed»
                                         x5
                                         (mk 0 [leaf 114,
                                           leaf 101,
                                           leaf 100,
                                           leaf 117,
                                           leaf 99,
                                           leaf 101])).label ≠ 0 then
                                         («Prelude.and»
                                           (Const.lt (leaf 1) x8)
                                           («Prelude.and»
                                             («Prelude.isSome» («Authoring.depthOf» x10))
                                             (x16 (leaf 2))),
                                           fun (x18 : T) (x19 : List T) (x20 : List T) =>
                                             «Tactics.byMode»
                                               («Base.getD» («Authoring.depthOf» x10) (leaf 0))
                                               x18
                                               x19
                                               x9
                                               («Authoring/Rules.append» (x15 (leaf 2)) x20))
                                       else
                                         if («Authoring.headed»
                                           x5
                                           (mk 0 [leaf 97,
                                             leaf 117,
                                             leaf 116,
                                             leaf 111])).label ≠ 0 then
                                           («Prelude.and»
                                             (Const.lt (leaf 2) x8)
                                             («Prelude.and»
                                               («Prelude.isSome» («Authoring.depthOf» x10))
                                               («Prelude.and»
                                                 («Prelude.isSome»
                                                   («Authoring.number» («Prelude.at» x7 (leaf 2))))
                                                 (x16 (leaf 3)))),
                                             fun (x18 : T) (x19 : List T) (x20 : List T) =>
                                               «Tactics.byAuto»
                                                 x18
                                                 x19
                                                 x9
                                                 («Authoring/Rules.append» (x15 (leaf 3)) x20)
                                                 («Base.getD»
                                                   («Authoring.number» («Prelude.at» x7 (leaf 2)))
                                                   (leaf 0))
                                                 («Base.getD» («Authoring.depthOf» x10) (leaf 0)))
                                         else
                                           if («Authoring.form»
                                             x5
                                             (mk 0 [leaf 101,
                                               leaf 120,
                                               leaf 116,
                                               leaf 101,
                                               leaf 110,
                                               leaf 115,
                                               leaf 105,
                                               leaf 111,
                                               leaf 110,
                                               leaf 97,
                                               leaf 108,
                                               leaf 105,
                                               leaf 116,
                                               leaf 121])
                                             (leaf 3)).label ≠ 0 then
                                             let x18 : T ×
                                               (T →
                                                 List T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         T →
                                                           T →
                                                             T) := x11
                                               (leaf 2)
                                               ((«Reader.nameOf» x10) :: x12)
                                               («Prelude.none» :: x13)
                                               x14;
                                             («Prelude.and»
                                               (x17 x12 («Prelude.single» x10))
                                               (x18).1,
                                               fun (x19 : T) (x20 : List T) (x21 : List T) =>
                                                 «Prover.byFunExt» x19 x9 ((x18).2 x19 x20 x21))
                                           else
                                             let x18 : List
                                               T := Const.children («Prelude.at» x7 (leaf 2));
                                             let x19 : T := «Reader.nameOf»
                                               («Prelude.at» x18 (leaf 0));
                                             let x20 : T := «Reader.nameOf»
                                               («Prelude.at» x18 (leaf 1));
                                             if («Authoring.form»
                                               x5
                                               (mk 0 [leaf 105,
                                                 leaf 110,
                                                 leaf 100,
                                                 leaf 117,
                                                 leaf 99,
                                                 leaf 116,
                                                 leaf 105,
                                                 leaf 111,
                                                 leaf 110])
                                               (leaf 5)).label ≠ 0 then
                                               let x21 : List T := «Prelude.drop» (leaf 1) x12;
                                               let x22 : T ×
                                                 (T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           T →
                                                             T →
                                                               T) := x11
                                                 (leaf 3)
                                                 x21
                                                 («Prelude.drop» (leaf 1) x13)
                                                 x14;
                                               let x23 : T ×
                                                 (T →
                                                   List T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           T →
                                                             T →
                                                               T) := x11
                                                 (leaf 4)
                                                 (x20 :: (x19 :: x21))
                                                 ((«Prelude.at» x13 (leaf 0)) ::
                                                   ((«Authoring.listElem»
                                                     («Prelude.at» x13 (leaf 0))) ::
                                                     («Prelude.drop» (leaf 1) x13)))
                                                 («Prelude.append»
                                                   x14
                                                   («Prelude.single»
                                                     («Reader.nameOf»
                                                       («Prelude.at» x18 (leaf 2)))));
                                               («Prelude.and»
                                                 («Prelude.and»
                                                   («Base.not» («Base.isEmpty» x12))
                                                   («Authoring.word»
                                                     x10
                                                     («Prelude.at» x12 (leaf 0))))
                                                 («Prelude.and»
                                                   («Reader.isList» («Prelude.at» x7 (leaf 2)))
                                                   («Prelude.and»
                                                     (Const.eq («Prelude.length» x18) (leaf 3))
                                                     («Prelude.and»
                                                       (x17 x21 x18)
                                                       («Prelude.and» (x22).1 (x23).1)))),
                                                 fun (x24 : T) (x25 : List T) (x26 : List T) =>
                                                   «Prover.byListIndWith»
                                                     x24
                                                     x9
                                                     (leaf 0)
                                                     (leaf 1)
                                                     ((x22).2 x24 x25 x26)
                                                     ((x23).2 x24 x25 x26))
                                             else
                                               if («Authoring.form»
                                                 x5
                                                 (mk 0 [leaf 99,
                                                   leaf 97,
                                                   leaf 115,
                                                   leaf 101,
                                                   leaf 115])
                                                 (leaf 5)).label ≠ 0 then
                                                 let x21 : T := «Reader.indexOf»
                                                   («Reader.nameOf» x10)
                                                   x12;
                                                 let x22 : T := «Prelude.at»
                                                   x13
                                                   («Base.getD» x21 (leaf 0));
                                                 let x23 : T ×
                                                   (T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             T → T → T) := x11 (leaf 3) x12 x13 x14;
                                                 let x24 : T ×
                                                   (T →
                                                     List T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             T →
                                                               T →
                                                                 T) := x11
                                                   (leaf 4)
                                                   (x20 :: (x19 :: x12))
                                                   (x22 :: ((«Authoring.listElem» x22) :: x13))
                                                   («Prelude.append»
                                                     x14
                                                     («Prelude.single»
                                                       (Const.node (leaf 0) ([] : List T))));
                                                 («Prelude.and»
                                                   («Reader.isAtom» x10)
                                                   («Prelude.and»
                                                     («Prelude.isSome» x21)
                                                     («Prelude.and»
                                                       («Reader.isList» («Prelude.at» x7 (leaf 2)))
                                                       («Prelude.and»
                                                         (Const.eq («Prelude.length» x18) (leaf 2))
                                                         («Prelude.and»
                                                           (x17 x12 x18)
                                                           («Prelude.and» (x23).1 (x24).1))))),
                                                   fun (x25 : T) (x26 : List T) (x27 : List T) =>
                                                     «Tactics.byListSplit»
                                                       x25
                                                       x9
                                                       («Base.getD» x21 (leaf 0))
                                                       ((x23).2 x25 x26 x27)
                                                       ((x24).2 x25 x26 x27))
                                               else
                                                 if («Authoring.form»
                                                   x5
                                                   (mk 0 [leaf 114,
                                                     leaf 101,
                                                     leaf 100,
                                                     leaf 117,
                                                     leaf 99,
                                                     leaf 101,
                                                     leaf 45,
                                                     leaf 104,
                                                     leaf 121,
                                                     leaf 112,
                                                     leaf 111,
                                                     leaf 116,
                                                     leaf 104,
                                                     leaf 101,
                                                     leaf 115,
                                                     leaf 101,
                                                     leaf 115])
                                                   (leaf 4)).label ≠ 0 then
                                                   let x21 : List
                                                     T := «Base.mapT»
                                                     «Reader.nameOf»
                                                     (Const.children («Prelude.at» x7 (leaf 2)));
                                                   let x22 : T ×
                                                     (T →
                                                       List T →
                                                         List T →
                                                           List T →
                                                             List T →
                                                               T →
                                                                 T →
                                                                   T) := x11
                                                     (leaf 3)
                                                     x12
                                                     x13
                                                     («Prelude.append»
                                                       («Base.mapT»
                                                         (fun (x22 : T) =>
                                                           if («Authoring.has»
                                                             x22
                                                             x21).label ≠ 0 then
                                                             Const.node (leaf 0) ([] : List T)
                                                           else
                                                             x22)
                                                         x14)
                                                       x21);
                                                   («Prelude.and»
                                                     («Prelude.isSome» («Authoring.depthOf» x10))
                                                     («Prelude.and»
                                                       («Reader.isList» («Prelude.at» x7 (leaf 2)))
                                                       («Prelude.and»
                                                         («Base.not» («Base.isEmpty» x21))
                                                         («Prelude.and»
                                                           («Base.allT»
                                                             (fun (x23 : T) =>
                                                               «Prelude.and»
                                                                 («Reader.isAtom» x23)
                                                                 («Authoring.has»
                                                                   («Reader.nameOf» x23)
                                                                   x14))
                                                             (Const.children
                                                               («Prelude.at» x7 (leaf 2))))
                                                           («Prelude.and»
                                                             («Authoring.distinctFrom»
                                                               ([] : List T)
                                                               x21)
                                                             (x22).1)))),
                                                     fun (x23 : T) (x24 : List T) (x25 : List T) =>
                                                       «Tactics.withWeakHyps»
                                                         x23
                                                         x24
                                                         x9
                                                         x25
                                                         («Base.mapT»
                                                           (fun (x26 : T) =>
                                                             «Base.getD»
                                                               («Reader.indexOf» x26 x14)
                                                               (leaf 0))
                                                           x21)
                                                         (fun (_ : List T) => (x22).2 x23 x24 x25)
                                                         («Base.getD»
                                                           («Authoring.depthOf» x10)
                                                           (leaf 0)))
                                                 else
                                                   if (Const.lt (leaf 1) x0).label ≠ 0 then
                                                     «Authoring.script2»
                                                       x1
                                                       x2
                                                       x3
                                                       x4
                                                       x5
                                                       x6
                                                       x12
                                                       x13
                                                       x14
                                                   else
                                                     (leaf 0, «Authoring.failTac»));
    x7

def «Authoring.readScript» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : T) =>
    let x6 : List T →
      List T →
        List T →
          T ×
            (T →
              List T →
                List T →
                  List T →
                    List T →
                      T →
                        T →
                          T) := Const.para
      (α := List T →
        List T →
          List T → T × (T → List T → List T → List T → List T → T → T → T))
      («Authoring.scriptStep» x0 x1 x2 x3 x4)
      x5;
    x6

def «Authoring.request» :=
  fun (x0 : T) (x1 : T) (x2 : T) (x3 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: (x2 :: (x3 :: ([] : List T)))))

def «Authoring.requestName» :=
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
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   x3);
    x1

def «Authoring.requestThm» :=
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
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x8
                     ([] : List T)
                     (fun (_ : T) (x11 : List T) => x11);
                   let x11 : T := x5;
                   let x12 : List T := Const.children x11;
                   let _ : T := Const.lcase
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
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x14
                     (leaf 0)
                     (fun (x15 : T) (_ : List T) => x15);
                   let x16 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x14
                     ([] : List T)
                     (fun (_ : T) (x17 : List T) => x17);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x16
                     (leaf 0)
                     (fun (x17 : T) (_ : List T) => x17);
                   let x18 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x16
                     ([] : List T)
                     (fun (_ : T) (x19 : List T) => x19);
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x18
                     (leaf 0)
                     (fun (x19 : T) (_ : List T) => x19);
                   let x20 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x18
                     ([] : List T)
                     (fun (_ : T) (x21 : List T) => x21);
                   let x21 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x20
                     (leaf 0)
                     (fun (x21 : T) (_ : List T) => x21);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x20
                     ([] : List T)
                     (fun (_ : T) (x23 : List T) => x23);
                   x21);
    x1

def «Authoring.failure» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := Const.node (leaf 2) («Theory.l2» x0 x1); x2

def «Authoring.requestOk» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Authoring.requestBad» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring.version0» :=
  fun (x0 : List T) (x1 : T) =>
    let x2 : T := (let x2 : T := Const.child x1 (leaf 2);
                   let x3 : T := Const.child x1 (leaf 3);
                   «Prelude.and»
                     («Authoring.form»
                       x2
                       (mk 0 [leaf 101, leaf 113, leaf 117, leaf 97, leaf 108])
                       (leaf 3))
                     («Prelude.and»
                       («Prelude.and»
                         («Reader.isAtom» (Const.child x2 (leaf 1)))
                         («Authoring.has» («Reader.nameOf» (Const.child x2 (leaf 1))) x0))
                       («Prelude.and»
                         («Prelude.and»
                           («Reader.isAtom» (Const.child x2 (leaf 2)))
                           («Authoring.has» («Reader.nameOf» (Const.child x2 (leaf 2))) x0))
                         («Prelude.and»
                           («Authoring.form» x3 (mk 0 [leaf 98, leaf 121]) (leaf 2))
                           («Authoring.form»
                             (Const.child x3 (leaf 1))
                             (mk 0 [leaf 110,
                               leaf 111,
                               leaf 114,
                               leaf 109,
                               leaf 97,
                               leaf 108,
                               leaf 105,
                               leaf 122,
                               leaf 101])
                             (leaf 2))))));
    x2

def «Authoring.theoremName» :=
  fun (x0 : T) =>
    let x1 : T := (if («Prelude.and»
      («Reader.isList» x0)
      (Const.lt
        (leaf 1)
        («Prelude.length» (Const.children x0)))).label ≠ 0 then
      «Reader.nameOf» (Const.child x0 (leaf 1))
    else
      Const.node (leaf 0) ([] : List T));
    x1

def «Authoring.readRequest» :=
  fun (x0 : T)
    (x1 : T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := (if («Prelude.and»
      («Authoring.form»
        x6
        (mk 0 [leaf 116,
          leaf 104,
          leaf 101,
          leaf 111,
          leaf 114,
          leaf 101,
          leaf 109])
        (leaf 4))
      («Prelude.and»
        («Reader.isAtom» (Const.child x6 (leaf 1)))
        («Prelude.and»
          («Base.not»
            («Base.isEmpty» (Const.children (Const.child x6 (leaf 1)))))
          («Prelude.and»
            («Authoring.form»
              (Const.child x6 (leaf 3))
              (mk 0 [leaf 98, leaf 121])
              (leaf 2))
            («Prelude.or»
              (Const.lt (leaf 0) x0)
              («Authoring.version0» x3 x6)))))).label ≠ 0 then
      let x7 : T := «Authoring.readStatement»
        x0
        x1
        x2
        x3
        («Prelude.append» x3 x4)
        (Const.child x6 (leaf 2));
      if (Const.eq (Const.label x7) (leaf 0)).label ≠ 0 then
        let _ : List T := Const.children x7; «Authoring.requestBad» (leaf 2)
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
        let x11 : T := x9;
        let x12 : List T := Const.children x11;
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
        let x16 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x14
          ([] : List T)
          (fun (_ : T) (x17 : List T) => x17);
        let x17 : T := Const.lcase
          (α := T)
          (β := T)
          x16
          (leaf 0)
          (fun (x17 : T) (_ : List T) => x17);
        let x18 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x16
          ([] : List T)
          (fun (_ : T) (x19 : List T) => x19);
        let x19 : T := Const.lcase
          (α := T)
          (β := T)
          x18
          (leaf 0)
          (fun (x19 : T) (_ : List T) => x19);
        let x20 : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x18
          ([] : List T)
          (fun (_ : T) (x21 : List T) => x21);
        let _ : T := Const.lcase
          (α := T)
          (β := T)
          x20
          (leaf 0)
          (fun (x21 : T) (_ : List T) => x21);
        let _ : List
          T := Const.lcase
          (α := T)
          (β := List T)
          x20
          ([] : List T)
          (fun (_ : T) (x23 : List T) => x23);
        let x23 : T := Const.child (Const.child x6 (leaf 3)) (leaf 1);
        if ((«Authoring.readScript»
          x0
          x2
          x3
          (Const.children x13)
          x5
          x23
          (Const.children x15)
          (Const.children x17)
          (Const.children x19)).1).label ≠ 0 then
          «Authoring.requestOk»
            («Authoring.request»
              («Reader.nameOf» (Const.child x6 (leaf 1)))
              x9
              x23
              x0)
        else
          «Authoring.requestBad» (leaf 3)
    else
      «Authoring.requestBad» (leaf 2));
    x7

def «Authoring.document» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring/ODoc.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/ODoc.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/ODoc.isJust» :=
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

def «Authoring/ODoc.fromMaybe» :=
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

def «Authoring/ODoc.nthOf» :=
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
      «Authoring/ODoc.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/ODoc.just» x2);
    x2

def «Authoring/ODoc.allJust» :=
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

def «Authoring.readDocument» :=
  fun (x0 : T) =>
    let x1 : T := (let x1 : T := «Reader.readSExps» (Const.children x0);
                   let x2 : T := Const.child («Prelude.get» x1) (leaf 0);
                   let x3 : T := «Authoring.number» (Const.child x2 (leaf 1));
                   if («Prelude.and»
                     («Prelude.isSome» x1)
                     («Prelude.and»
                       (Const.eq
                         («Prelude.length» (Const.children («Prelude.get» x1)))
                         (leaf 1))
                       («Prelude.and»
                         («Reader.isList» x2)
                         («Prelude.and»
                           («Authoring.word»
                             (Const.child x2 (leaf 0))
                             (mk 0 [leaf 112, leaf 114, leaf 111, leaf 111, leaf 102, leaf 115]))
                           («Prelude.and»
                             («Prelude.isSome» x3)
                             (Const.lt («Prelude.get» x3) (leaf 3))))))).label ≠ 0 then
                     let x4 : List
                       T := Const.foldr
                       (α := T)
                       (β := List T)
                       (fun (x4 : T) (x5 : List T) =>
                         if («Prelude.and»
                           (Const.eq («Prelude.get» x3) (leaf 2))
                           («Authoring.form»
                             x4
                             (mk 0 [leaf 105, leaf 109, leaf 112, leaf 111, leaf 114, leaf 116])
                             (leaf 2))).label ≠ 0 then
                           x5
                         else
                           (x4 :: x5))
                       ([] : List T)
                       («Prelude.drop» (leaf 2) (Const.children x2));
                     if («Base.isEmpty» x4).label ≠ 0 then
                       «Authoring/ODoc.nothing»
                     else
                       «Authoring/ODoc.just» («Authoring.document» («Prelude.get» x3) x4)
                   else
                     «Authoring/ODoc.nothing»);
    x1

def «Authoring.formList» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring/OForms.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OForms.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OForms.isJust» :=
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

def «Authoring/OForms.fromMaybe» :=
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

def «Authoring/OForms.nthOf» :=
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
      «Authoring/OForms.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OForms.just» x2);
    x2

def «Authoring/OForms.allJust» :=
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

def «Authoring/Items.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Items.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Items.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Items.reverse» :=
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

def «Authoring/Items.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Items.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Items.tail» x1 x0;
    x2

def «Authoring/Items.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Items.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring/ItemsOf.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring/ItemOut.map» :=
  fun (x0 : T → T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => ((x0 x2) :: x3))
      ([] : List T)
      x1;
    x2

def «Authoring.readDocuments» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (x1 : T) (x2 : T) =>
        let x3 : T := x2;
        if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
          let _ : List T := Const.children x3; «Authoring/OForms.nothing»
        else
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
          let x7 : T := x5;
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
          let x11 : List T := x10;
          let x12 : T := «Authoring.readDocument» x1;
          if (Const.eq (Const.label x12) (leaf 0)).label ≠ 0 then
            let _ : List T := Const.children x12; «Authoring/OForms.nothing»
          else
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
            let x16 : T := x14;
            let x17 : List T := Const.children x16;
            let x18 : T := Const.lcase
              (α := T)
              (β := T)
              x17
              (leaf 0)
              (fun (x18 : T) (_ : List T) => x18);
            let x19 : List
              T := Const.lcase
              (α := T)
              (β := List T)
              x17
              ([] : List T)
              (fun (_ : T) (x20 : List T) => x20);
            let x20 : List T := x19;
            if («Prelude.and»
              (Const.eq x18 (leaf 0))
              (Const.lt (leaf 1) («Prelude.length» x0))).label ≠ 0 then
              «Authoring/OForms.nothing»
            else
              «Authoring/OForms.just»
                («Authoring.formList»
                  (if (Const.eq («Authoring/Items.length» x11) (leaf 0)).label ≠ 0 then
                    x18
                  else
                    x9)
                  («Authoring/Items.append»
                    («Authoring/ItemsOf.map» (fun (x21 : T) => «Language.pr» x18 x21) x20)
                    x11)))
      (if («Base.isEmpty» x0).label ≠ 0 then
        «Authoring/OForms.nothing»
      else
        «Authoring/OForms.just» («Authoring.formList» (leaf 0) ([] : List T)))
      x0;
    x1

def «Authoring/Requests.single» :=
  fun (x0 : T) => let x1 : List T := (x0 :: ([] : List T)); x1

def «Authoring/Requests.length» :=
  fun (x0 : List T) =>
    let x1 : T := Const.foldr
      (α := T)
      (β := T)
      (fun (_ : T) (x2 : T) => Const.add x2 (leaf 1))
      (leaf 0)
      x0;
    x1

def «Authoring/Requests.append» :=
  fun (x0 : List T) (x1 : List T) =>
    let x2 : List
      T := Const.foldr
      (α := T)
      (β := List T)
      (fun (x2 : T) (x3 : List T) => (x2 :: x3))
      x1
      x0;
    x2

def «Authoring/Requests.reverse» :=
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

def «Authoring/Requests.tail» :=
  fun (x0 : List T) =>
    let x1 : List
      T := Const.lcase
      (α := T)
      (β := List T)
      x0
      ([] : List T)
      (fun (_ : T) (x2 : List T) => x2);
    x1

def «Authoring/Requests.drop» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := Const.iter (α := List T) «Authoring/Requests.tail» x1 x0;
    x2

def «Authoring/Requests.atOr» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := Const.lcase
      (α := T)
      (β := T)
      («Authoring/Requests.drop» x2 x1)
      x0
      (fun (x3 : T) (_ : List T) => x3);
    x3

def «Authoring.requests» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring.readOk» :=
  fun (x0 : T) => Const.node (leaf 0) (x0 :: ([] : List T))

def «Authoring.readBad» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «Authoring.firstRepeated» :=
  fun (x0 : List T) =>
    let x1 : T := (Const.foldr
      (α := T)
      (β := List T × T)
      (fun (x1 : T) (x2 : List T × T) =>
        ((x1 :: (x2).1),
          if («Authoring.has» x1 (x2).1).label ≠ 0 then
            «Prelude.some» x1
          else
            (x2).2))
      (([] : List T), «Prelude.none»)
      («Prelude.reverse» x0)).2;
    x1

def «Authoring.readSources» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (let x4 : T := «Authoring.readDocuments» x3;
                   if (Const.eq (Const.label x4) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x4;
                     «Authoring.readBad» (leaf 0) (Const.node (leaf 0) ([] : List T))
                   else
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
                     let x8 : T := x6;
                     let x9 : List T := Const.children x8;
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
                     let x12 : List T := x11;
                     let x13 : List
                       T := «Authoring/ItemOut.map»
                       (fun (x13 : T) => «Authoring.theoremName» («Language.p2» x13))
                       x12;
                     let x14 : T := «Authoring.firstRepeated» x13;
                     if («Prelude.isSome» x14).label ≠ 0 then
                       «Authoring.readBad» (leaf 1) («Prelude.get» x14)
                     else
                       Const.foldr
                         (α := T)
                         (β := T)
                         (fun (x15 : T) (x16 : T) =>
                           let x17 : T := «Authoring/Items.atOr»
                             («Language.pr» (leaf 0) (leaf 0))
                             x12
                             x15;
                           let x18 : T := «Authoring.readRequest»
                             («Language.p1» x17)
                             x0
                             x1
                             x2
                             x13
                             («Base.take» x15 x13)
                             («Language.p2» x17);
                           if (Const.eq (Const.label x18) (leaf 1)).label ≠ 0 then
                             let x19 : List T := Const.children x18;
                             let x20 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x19
                               (leaf 0)
                               (fun (x20 : T) (_ : List T) => x20);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x19
                               ([] : List T)
                               (fun (_ : T) (x22 : List T) => x22);
                             «Authoring.readBad» x20 («Prelude.at» x13 x15)
                           else
                             let x19 : List T := Const.children x18;
                             let x20 : T := Const.lcase
                               (α := T)
                               (β := T)
                               x19
                               (leaf 0)
                               (fun (x20 : T) (_ : List T) => x20);
                             let _ : List
                               T := Const.lcase
                               (α := T)
                               (β := List T)
                               x19
                               ([] : List T)
                               (fun (_ : T) (x22 : List T) => x22);
                             let x22 : T := x16;
                             if (Const.eq (Const.label x22) (leaf 1)).label ≠ 0 then
                               let x23 : List T := Const.children x22;
                               let _ : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x23
                                 (leaf 0)
                                 (fun (x24 : T) (_ : List T) => x24);
                               let x25 : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x23
                                 ([] : List T)
                                 (fun (_ : T) (x26 : List T) => x26);
                               let _ : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x25
                                 (leaf 0)
                                 (fun (x26 : T) (_ : List T) => x26);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x25
                                 ([] : List T)
                                 (fun (_ : T) (x28 : List T) => x28);
                               x16
                             else
                               let x23 : List T := Const.children x22;
                               let x24 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x23
                                 (leaf 0)
                                 (fun (x24 : T) (_ : List T) => x24);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x23
                                 ([] : List T)
                                 (fun (_ : T) (x26 : List T) => x26);
                               let x26 : T := x24;
                               let x27 : List T := Const.children x26;
                               let x28 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x27
                                 (leaf 0)
                                 (fun (x28 : T) (_ : List T) => x28);
                               let x29 : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x27
                                 ([] : List T)
                                 (fun (_ : T) (x30 : List T) => x30);
                               let x30 : List T := x29;
                               «Authoring.readOk» («Authoring.requests» x28 (x20 :: x30)))
                         («Authoring.readOk» («Authoring.requests» x10 ([] : List T)))
                         («Base.range» («Prelude.length» x13)));
    x4

def «Authoring.results» :=
  fun (x0 : T) (x1 : List T) => Const.node (leaf 0) (x0 :: x1)

def «Authoring.Results.member» :=
  fun (x0 : T) =>
    Const.child
      (Const.fold
        (α := T)
        (fun (x1 : T) (x2 : List T) =>
          let x3 : T := Const.node (leaf 0) x2;
          Const.node
            (leaf 0)
            ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
              if (Const.lt
                (leaf 1)
                (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                Const.foldr
                  (α := T)
                  (β := T)
                  (fun (x4 : T) (x5 : T) =>
                    if (Const.child x4 (leaf 1)).label ≠ 0 then x5 else leaf 0)
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
                    (leaf 1))
              else
                leaf 0
            else
              leaf 0).label ≠ 0 then
              leaf 1
            else
              leaf 0) ::
              ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                  Const.child (Const.child x3 (leaf 0)) (leaf 2)
                else
                  leaf 0
              else
                if (Const.eq x1 (leaf 1)).label ≠ 0 then
                  if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                    Const.child (Const.child x3 (leaf 0)) (leaf 3)
                  else
                    leaf 0
                else
                  if (Const.eq x1 (leaf 2)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 1)).label ≠ 0 then
                      Const.child (Const.child x3 (leaf 0)) (leaf 4)
                    else
                      leaf 0
                  else
                    if (Const.eq x1 (leaf 3)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 2)).label ≠ 0 then
                        Const.child (Const.child x3 (leaf 0)) (leaf 5)
                      else
                        leaf 0
                    else
                      if (Const.eq x1 (leaf 4)).label ≠ 0 then
                        Const.eq (Const.arity x3) (leaf 3)
                      else
                        if (Const.eq x1 (leaf 5)).label ≠ 0 then
                          Const.eq (Const.arity x3) (leaf 3)
                        else
                          if (Const.eq x1 (leaf 6)).label ≠ 0 then
                            Const.eq (Const.arity x3) (leaf 4)
                          else
                            leaf 0).label ≠ 0 then
                leaf 1
              else
                leaf 0) ::
                ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                  if (Const.eq (Const.arity x3) (leaf 4)).label ≠ 0 then
                    if (Const.child (Const.child x3 (leaf 1)) (leaf 6)).label ≠ 0 then
                      Const.child (Const.child x3 (leaf 2)) (leaf 10)
                    else
                      leaf 0
                  else
                    leaf 0
                else
                  leaf 0).label ≠ 0 then
                  leaf 1
                else
                  leaf 0) ::
                  ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                    if (Const.eq (Const.arity x3) (leaf 3)).label ≠ 0 then
                      if (Const.child (Const.child x3 (leaf 0)) (leaf 7)).label ≠ 0 then
                        if (Const.child (Const.child x3 (leaf 1)) (leaf 8)).label ≠ 0 then
                          Const.child (Const.child x3 (leaf 2)) (leaf 9)
                        else
                          leaf 0
                      else
                        leaf 0
                    else
                      leaf 0
                  else
                    leaf 0).label ≠ 0 then
                    leaf 1
                  else
                    leaf 0) ::
                    ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                      if (Const.eq (Const.arity x3) (leaf 4)).label ≠ 0 then
                        Const.child (Const.child x3 (leaf 1)) (leaf 6)
                      else
                        leaf 0
                    else
                      leaf 0).label ≠ 0 then
                      leaf 1
                    else
                      leaf 0) ::
                      ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                        Const.eq (Const.arity x3) (leaf 4)
                      else
                        leaf 0).label ≠ 0 then
                        leaf 1
                      else
                        leaf 0) ::
                        ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                          Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                        else
                          leaf 0).label ≠ 0 then
                          leaf 1
                        else
                          leaf 0) ::
                          ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                            Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                          else
                            leaf 0).label ≠ 0 then
                            leaf 1
                          else
                            leaf 0) ::
                            ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                              if (Const.lt
                                (leaf 0)
                                (Const.add (Const.arity x3) (leaf 1))).label ≠ 0 then
                                Const.foldr
                                  (α := T)
                                  (β := T)
                                  (fun (x4 : T) (x5 : T) =>
                                    if (Const.child x4 (leaf 9)).label ≠ 0 then x5 else leaf 0)
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
                              leaf 0) ::
                              ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                Const.eq (Const.arity x3) (leaf 2)
                              else
                                leaf 0).label ≠ 0 then
                                leaf 1
                              else
                                leaf 0) ::
                                ((if (if (Const.eq x1 (leaf 0)).label ≠ 0 then
                                  Const.lt (leaf 0) (Const.add (Const.arity x3) (leaf 1))
                                else
                                  leaf 0).label ≠ 0 then
                                  leaf 1
                                else
                                  leaf 0) ::
                                  ([] : List T)))))))))))))
        x0)
      (leaf 0)

def «Authoring.proving» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 0) (x0 :: (x1 :: ([] : List T)))

def «Authoring.stuck» :=
  fun (x0 : T) (x1 : T) =>
    Const.node (leaf 1) (x0 :: (x1 :: ([] : List T)))

def «Authoring/OEntries.nothing» := Const.node (leaf 0) ([] : List T)

def «Authoring/OEntries.just» :=
  fun (x0 : T) => Const.node (leaf 1) (x0 :: ([] : List T))

def «Authoring/OEntries.isJust» :=
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

def «Authoring/OEntries.fromMaybe» :=
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

def «Authoring/OEntries.nthOf» :=
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
      «Authoring/OEntries.nothing»
      (fun (x2 : T) (_ : List T) => «Authoring/OEntries.just» x2);
    x2

def «Authoring/OEntries.allJust» :=
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

def «Authoring.admit» :=
  fun (x0 : T) (x1 : List T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Derivation.declStep» x0 x1 x2;
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x3; «Authoring/OEntries.nothing»
                   else
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
                     let x7 : T := x5;
                     let x8 : List T := Const.children x7;
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
                     «Authoring/OEntries.just» x11);
    x3

def «Authoring.derive» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : List T)
    (x5 : List T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := x6;
                   let x8 : List T := Const.children x7;
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
                   let x17 : T := x11;
                   let x18 : List T := Const.children x17;
                   let x19 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x18
                     (leaf 0)
                     (fun (x19 : T) (_ : List T) => x19);
                   let x20 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x18
                     ([] : List T)
                     (fun (_ : T) (x21 : List T) => x21);
                   let x21 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x20
                     (leaf 0)
                     (fun (x21 : T) (_ : List T) => x21);
                   let x22 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x20
                     ([] : List T)
                     (fun (_ : T) (x23 : List T) => x23);
                   let x23 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x22
                     (leaf 0)
                     (fun (x23 : T) (_ : List T) => x23);
                   let x24 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x22
                     ([] : List T)
                     (fun (_ : T) (x25 : List T) => x25);
                   let x25 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x24
                     (leaf 0)
                     (fun (x25 : T) (_ : List T) => x25);
                   let x26 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x24
                     ([] : List T)
                     (fun (_ : T) (x27 : List T) => x27);
                   let x27 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x26
                     (leaf 0)
                     (fun (x27 : T) (_ : List T) => x27);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x26
                     ([] : List T)
                     (fun (_ : T) (x29 : List T) => x29);
                   let x29 : T := x27;
                   let x30 : List T := Const.children x29;
                   let _ : T := Const.lcase
                     (α := T)
                     (β := T)
                     x30
                     (leaf 0)
                     (fun (x31 : T) (_ : List T) => x31);
                   let x32 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x30
                     ([] : List T)
                     (fun (_ : T) (x33 : List T) => x33);
                   let x33 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x32
                     (leaf 0)
                     (fun (x33 : T) (_ : List T) => x33);
                   let x34 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x32
                     ([] : List T)
                     (fun (_ : T) (x35 : List T) => x35);
                   let x35 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x34
                     (leaf 0)
                     (fun (x35 : T) (_ : List T) => x35);
                   let x36 : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x34
                     ([] : List T)
                     (fun (_ : T) (x37 : List T) => x37);
                   let x37 : T := Const.lcase
                     (α := T)
                     (β := T)
                     x36
                     (leaf 0)
                     (fun (x37 : T) (_ : List T) => x37);
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x36
                     ([] : List T)
                     (fun (_ : T) (x39 : List T) => x39);
                   let x39 : T := x33;
                   let x40 : List T := Const.children x39;
                   let x41 : List T := x40;
                   let x42 : T := x35;
                   let x43 : List T := Const.children x42;
                   let x44 : List T := x43;
                   let x45 : T := «Derivation.eqParts» x37;
                   if (Const.eq (Const.label x45) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x45; «Prelude.none»
                   else
                     let x46 : List T := Const.children x45;
                     let x47 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x46
                       (leaf 0)
                       (fun (x47 : T) (_ : List T) => x47);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x46
                       ([] : List T)
                       (fun (_ : T) (x49 : List T) => x49);
                     («Authoring.readScript»
                       x15
                       x3
                       x4
                       (Const.children x19)
                       x5
                       x13
                       (Const.children x21)
                       (Const.children x23)
                       (Const.children x25)).2
                       x0
                       x1
                       x2
                       x41
                       x44
                       («Language.p1» x47)
                       («Language.p2» x47));
    x7

def «Authoring.companion» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : T) (x4 : T) =>
    let x5 : T := (let x5 : T := x4;
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
                   let _ : List
                     T := Const.lcase
                     (α := T)
                     (β := List T)
                     x12
                     ([] : List T)
                     (fun (_ : T) (x15 : List T) => x15);
                   let x15 : T := x9;
                   let x16 : List T := Const.children x15;
                   let x17 : List T := x16;
                   let x18 : T := x11;
                   let x19 : List T := Const.children x18;
                   let x20 : List T := x19;
                   let x21 : T := «Derivation.eqParts» x13;
                   if (Const.eq (Const.label x21) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x21; «Prelude.none»
                   else
                     let x22 : List T := Const.children x21;
                     let x23 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x22
                       (leaf 0)
                       (fun (x23 : T) (_ : List T) => x23);
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x22
                       ([] : List T)
                       (fun (_ : T) (x25 : List T) => x25);
                     «Prover.bindNT»
                       («Prover.eval»
                         x0
                         x1
                         x7
                         x2
                         (leaf 4096)
                         (leaf 1)
                         x17
                         x20
                         («Language.p1» x23))
                       (fun (x25 : T) =>
                         «Prover.bindNT»
                           («Prover.eval»
                             x0
                             x1
                             x7
                             x2
                             (leaf 4096)
                             (leaf 1)
                             x17
                             x20
                             («Language.p2» x23))
                           (fun (x26 : T) =>
                             «Prelude.some»
                               (Const.node
                                 (leaf 0)
                                 («Theory.l3»
                                   («Prover.nfTerm» x25)
                                   («Prover.nfTerm» x26)
                                   («Prover.dNode»
                                     (leaf 24)
                                     («Prelude.single» x13)
                                     («Theory.l2»
                                       («Prover.dNode»
                                         (leaf 2)
                                         ([] : List T)
                                         («Theory.l2»
                                           («Prover.mDeriv» («Prover.nfMarked» x25))
                                           («Prover.mDeriv» («Prover.nfMarked» x26))))
                                       («Prover.dNode»
                                         (leaf 27)
                                         («Theory.l3»
                                           x3
                                           (Const.node
                                             (leaf 0)
                                             («Base.mapT» «Theory.x» («Base.range» x7)))
                                           (Const.node
                                             (leaf 0)
                                             («Base.mapT»
                                               «Language.var»
                                               («Base.range» («Prelude.length» x17)))))
                                         («Base.mapT»
                                           (fun (x27 : T) =>
                                             «Prover.dNode»
                                               (leaf 21)
                                               («Prelude.single» x27)
                                               ([] : List T))
                                           («Base.range» («Prelude.length» x20)))))))))));
    x5

def «Authoring.withSides» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := x0;
                   let x4 : List T := Const.children x3;
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
                   «Derivation.mkThm» x5 x7 x9 («Language.mEq» x1 x2));
    x3

def «Authoring.sourceNames» :=
  fun (x0 : T) (x1 : List T) =>
    let x2 : List
      T := (if (Const.eq x0 (leaf 0)).label ≠ 0 then
      x1
    else
      «Base.mapT»
        (fun (x2 : T) => «Prelude.at» x1 (Const.mul (leaf 2) x2))
        («Base.range» (Const.div («Prelude.length» x1) (leaf 2))));
    x2

def «Authoring.advance» :=
  fun (x0 : T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T)
    (x5 : T)
    (x6 : T) =>
    let x7 : T := (let x7 : T := x6;
                   if (Const.eq (Const.label x7) (leaf 1)).label ≠ 0 then
                     let x8 : List T := Const.children x7;
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
                     x6
                   else
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
                     let x13 : T := x9;
                     let x14 : List T := Const.children x13;
                     let x15 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x14
                       (leaf 0)
                       (fun (x15 : T) (_ : List T) => x15);
                     let x16 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x14
                       ([] : List T)
                       (fun (_ : T) (x17 : List T) => x17);
                     let x17 : List T := x16;
                     let x18 : T := x11;
                     let x19 : List T := Const.children x18;
                     let x20 : List T := x19;
                     let x21 : T := «Authoring.derive»
                       x0
                       x20
                       x1
                       x2
                       x3
                       («Authoring.sourceNames» x4 (Const.children x15))
                       x5;
                     if («Prelude.isSome» x21).label ≠ 0 then
                       let x22 : T := «Derivation.declLang»
                         («Authoring.requestThm» x5)
                         («Prelude.get» x21);
                       let x23 : T := «Authoring.admit» x0 x20 x22;
                       if (Const.eq (Const.label x23) (leaf 0)).label ≠ 0 then
                         let _ : List T := Const.children x23;
                         «Authoring.stuck» (leaf 6) («Authoring.requestName» x5)
                       else
                         let x24 : List T := Const.children x23;
                         let x25 : T := Const.lcase
                           (α := T)
                           (β := T)
                           x24
                           (leaf 0)
                           (fun (x25 : T) (_ : List T) => x25);
                         let _ : List
                           T := Const.lcase
                           (α := T)
                           (β := List T)
                           x24
                           ([] : List T)
                           (fun (_ : T) (x27 : List T) => x27);
                         let x27 : T := x25;
                         let x28 : List T := Const.children x27;
                         let x29 : List T := x28;
                         let x30 : List
                           T := «Authoring/Decls.append» x17 («Authoring/Decls.single» x22);
                         if (Const.eq x4 (leaf 0)).label ≠ 0 then
                           «Authoring.proving»
                             («Authoring.results»
                               (Const.node
                                 (leaf 0)
                                 («Prelude.append»
                                   (Const.children x15)
                                   («Prelude.single» («Authoring.requestName» x5))))
                               x30)
                             x25
                         else
                           let x31 : T := «Authoring.companion»
                             x0
                             x29
                             x1
                             («Authoring/Decls.length» x17)
                             («Authoring.requestThm» x5);
                           if («Prelude.isSome» x31).label ≠ 0 then
                             let x32 : List T := Const.children («Prelude.get» x31);
                             let x33 : T := «Derivation.declLang»
                               («Authoring.withSides»
                                 («Authoring.requestThm» x5)
                                 («Prelude.at» x32 (leaf 0))
                                 («Prelude.at» x32 (leaf 1)))
                               («Prelude.at» x32 (leaf 2));
                             let x34 : T := «Authoring.admit» x0 x29 x33;
                             if (Const.eq (Const.label x34) (leaf 0)).label ≠ 0 then
                               let _ : List T := Const.children x34;
                               «Authoring.stuck» (leaf 6) («Authoring.requestName» x5)
                             else
                               let x35 : List T := Const.children x34;
                               let x36 : T := Const.lcase
                                 (α := T)
                                 (β := T)
                                 x35
                                 (leaf 0)
                                 (fun (x36 : T) (_ : List T) => x36);
                               let _ : List
                                 T := Const.lcase
                                 (α := T)
                                 (β := List T)
                                 x35
                                 ([] : List T)
                                 (fun (_ : T) (x38 : List T) => x38);
                               «Authoring.proving»
                                 («Authoring.results»
                                   (Const.node
                                     (leaf 0)
                                     («Prelude.append»
                                       (Const.children x15)
                                       («Theory.l2»
                                         («Authoring.requestName» x5)
                                         («Authoring.requestName» x5))))
                                   («Authoring/Decls.append» x30 («Authoring/Decls.single» x33)))
                                 x36
                           else
                             «Authoring.stuck» (leaf 5) («Authoring.requestName» x5)
                     else
                       «Authoring.stuck» (leaf 4) («Authoring.requestName» x5));
    x7

def «Authoring.proveWith» :=
  fun (x0 : List T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := (let x4 : T := «Authoring.globalsOf» x2;
                   let x5 : T := «Authoring.readSources» x4 x0 x1 x3;
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
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x8
                       ([] : List T)
                       (fun (_ : T) (x11 : List T) => x11);
                     «Authoring.failure» x7 x9
                   else
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
                     let x9 : T := x7;
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
                     let x13 : List T := x12;
                     let x14 : List
                       T := «Authoring.rulesOf»
                       x11
                       (Const.add
                         («Authoring/LD.length» «Translation.lib»)
                         («Authoring/LD.length» x2));
                     let x15 : T := Const.foldr
                       (α := T)
                       (β := T → T)
                       (fun (x15 : T) (x16 : T → T) (x17 : T) =>
                         x16 («Authoring.advance» x4 x14 x0 x1 x11 x15 x17))
                       (fun (x15 : T) => x15)
                       x13
                       («Authoring.proving»
                         («Authoring.results»
                           (Const.node (leaf 0) ([] : List T))
                           ([] : List T))
                         («Derivation.entries» ([] : List T)));
                     if (Const.eq (Const.label x15) (leaf 1)).label ≠ 0 then
                       let x16 : List T := Const.children x15;
                       let x17 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x16
                         (leaf 0)
                         (fun (x17 : T) (_ : List T) => x17);
                       let x18 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x16
                         ([] : List T)
                         (fun (_ : T) (x19 : List T) => x19);
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
                       «Authoring.failure» x17 x19
                     else
                       let x16 : List T := Const.children x15;
                       let x17 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x16
                         (leaf 0)
                         (fun (x17 : T) (_ : List T) => x17);
                       let x18 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x16
                         ([] : List T)
                         (fun (_ : T) (x19 : List T) => x19);
                       let _ : T := Const.lcase
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
                       «Prelude.some» x17);
    x4

def «Authoring.prove» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x2; «Prelude.none»
                   else
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
                     let x6 : T := x4;
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
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : T := x8;
                     let x13 : List T := Const.children x12;
                     let x14 : List T := x13;
                     let x15 : T := x10;
                     let x16 : List T := Const.children x15;
                     let x17 : List T := x16;
                     «Authoring.proveWith»
                       x14
                       (Const.children (Const.child x0 (leaf 1)))
                       x17
                       (Const.children x1));
    x2

def «Authoring.stated» :=
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
                     «Prelude.some» x3
                   else
                     «Prelude.none»);
    x1

def «Authoring.matches» :=
  fun (x0 : T) (x1 : List T) (x2 : List T) (x3 : List T) =>
    let x4 : T := «Prelude.and»
      (Const.eq
        (Const.mul
          (if (Const.eq x0 (leaf 0)).label ≠ 0 then leaf 1 else leaf 2)
          («Authoring/Requests.length» x1))
        («Authoring/Decls.length» x2))
      («Prelude.and»
        (Const.eq («Authoring/Decls.length» x2) («Prelude.length» x3))
        (Const.foldr
          (α := T)
          (β := List T → List T → T)
          (fun (x4 : T) (x5 : List T → List T → T) (x6 : List T) (x7 : List T) =>
            Const.lcase
              (α := T)
              (β := T)
              x6
              (leaf 0)
              (fun (x8 : T) (x9 : List T) =>
                «Prelude.and»
                  (Const.equal
                    («Authoring.stated» x8)
                    («Prelude.some» («Authoring.requestThm» x4)))
                  («Prelude.and»
                    (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 0)))
                    (if (Const.eq x0 (leaf 0)).label ≠ 0 then
                      x5 x9 («Prelude.drop» (leaf 1) x7)
                    else
                      Const.lcase
                        (α := T)
                        (β := T)
                        x9
                        (leaf 0)
                        (fun (x10 : T) (x11 : List T) =>
                          «Prelude.and»
                            («Prelude.isSome» («Authoring.stated» x10))
                            («Prelude.and»
                              (Const.equal («Authoring.requestName» x4) («Prelude.at» x7 (leaf 1)))
                              (x5 x11 («Prelude.drop» (leaf 2) x7))))))))
          (fun (_ : List T) (_ : List T) => leaf 1)
          x1
          x2
          x3));
    x4

def «Authoring.replayWith» :=
  fun (x0 : List T)
    (x1 : List T)
    (x2 : List T)
    (x3 : List T)
    (x4 : T) =>
    let x5 : T := (let x5 : T := «Authoring.globalsOf» x2;
                   let x6 : T := «Authoring.readSources» x5 x0 x1 x3;
                   if (Const.eq (Const.label x6) (leaf 1)).label ≠ 0 then
                     let x7 : List T := Const.children x6;
                     let _ : T := Const.lcase
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
                     leaf 0
                   else
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
                     let x10 : T := x8;
                     let x11 : List T := Const.children x10;
                     let x12 : T := Const.lcase
                       (α := T)
                       (β := T)
                       x11
                       (leaf 0)
                       (fun (x12 : T) (_ : List T) => x12);
                     let x13 : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x11
                       ([] : List T)
                       (fun (_ : T) (x14 : List T) => x14);
                     let x14 : List T := x13;
                     let x15 : T := x4;
                     if («Authoring.Results.member» x15).label ≠ 0 then
                       let x16 : T := x15;
                       let x17 : T := x16;
                       let x18 : List T := Const.children x17;
                       let x19 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x18
                         (leaf 0)
                         (fun (x19 : T) (_ : List T) => x19);
                       let x20 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x18
                         ([] : List T)
                         (fun (_ : T) (x21 : List T) => x21);
                       let x21 : List T := x20;
                       if («Authoring.matches»
                         x12
                         x14
                         x21
                         (Const.children x19)).label ≠ 0 then
                         let x22 : T := «Derivation.checkDev» x5 ([] : List T) x21;
                         if (Const.eq (Const.label x22) (leaf 0)).label ≠ 0 then
                           let _ : List T := Const.children x22; leaf 0
                         else
                           let x23 : List T := Const.children x22;
                           let _ : T := Const.lcase
                             (α := T)
                             (β := T)
                             x23
                             (leaf 0)
                             (fun (x24 : T) (_ : List T) => x24);
                           let _ : List
                             T := Const.lcase
                             (α := T)
                             (β := List T)
                             x23
                             ([] : List T)
                             (fun (_ : T) (x26 : List T) => x26);
                           leaf 1
                       else
                         leaf 0
                     else
                       leaf 0);
    x5

def «Authoring.replay» :=
  fun (x0 : T) (x1 : T) (x2 : T) =>
    let x3 : T := (let x3 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x3) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x3; leaf 0
                   else
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
                     let x7 : T := x5;
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
                     let x13 : T := x9;
                     let x14 : List T := Const.children x13;
                     let x15 : List T := x14;
                     let x16 : T := x11;
                     let x17 : List T := Const.children x16;
                     let x18 : List T := x17;
                     «Authoring.replayWith»
                       x15
                       (Const.children (Const.child x0 (leaf 1)))
                       x18
                       (Const.children x1)
                       x2);
    x3

def «Authoring.version» :=
  fun (x0 : T) (x1 : T) =>
    let x2 : T := (let x2 : T := «Translation.program»
                     (Const.children (Const.child x0 (leaf 0)));
                   if (Const.eq (Const.label x2) (leaf 0)).label ≠ 0 then
                     let _ : List T := Const.children x2; «Prelude.none»
                   else
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
                     let x6 : T := x4;
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
                     let _ : List
                       T := Const.lcase
                       (α := T)
                       (β := List T)
                       x9
                       ([] : List T)
                       (fun (_ : T) (x12 : List T) => x12);
                     let x12 : T := x8;
                     let x13 : List T := Const.children x12;
                     let x14 : List T := x13;
                     let x15 : T := x10;
                     let x16 : List T := Const.children x15;
                     let x17 : List T := x16;
                     let x18 : T := «Authoring.readSources»
                       («Authoring.globalsOf» x17)
                       x14
                       (Const.children (Const.child x0 (leaf 1)))
                       (Const.children x1);
                     if (Const.eq (Const.label x18) (leaf 1)).label ≠ 0 then
                       let x19 : List T := Const.children x18;
                       let x20 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x19
                         (leaf 0)
                         (fun (x20 : T) (_ : List T) => x20);
                       let x21 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x19
                         ([] : List T)
                         (fun (_ : T) (x22 : List T) => x22);
                       let x22 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x21
                         (leaf 0)
                         (fun (x22 : T) (_ : List T) => x22);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x21
                         ([] : List T)
                         (fun (_ : T) (x24 : List T) => x24);
                       «Authoring.failure» x20 x22
                     else
                       let x19 : List T := Const.children x18;
                       let x20 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x19
                         (leaf 0)
                         (fun (x20 : T) (_ : List T) => x20);
                       let _ : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x19
                         ([] : List T)
                         (fun (_ : T) (x22 : List T) => x22);
                       let x22 : T := x20;
                       let x23 : List T := Const.children x22;
                       let x24 : T := Const.lcase
                         (α := T)
                         (β := T)
                         x23
                         (leaf 0)
                         (fun (x24 : T) (_ : List T) => x24);
                       let x25 : List
                         T := Const.lcase
                         (α := T)
                         (β := List T)
                         x23
                         ([] : List T)
                         (fun (_ : T) (x26 : List T) => x26);
                       let _ : List T := x25; «Prelude.some» x24);
    x2

end GebMirror.Metalogic

end
