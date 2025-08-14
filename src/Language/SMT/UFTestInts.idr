module Language.SMT.UFTestInts

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Arity
import Language.SMT.Core
import Language.SMT.Serialise
import Language.SMT.Functions
import Language.SMT.TestInts

import Data.List.Quantifiers

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Modality
import MAST.Combinator.List
import MAST.Combinator.Restrict
import MAST.Combinator.Extend
import MAST.Combinator.List.Quantifiers
import MAST.Combinator.CoProd
import MAST.Combinator.Prod
import MAST.Combinator.Const
import MAST.Combinator.Compose
import MAST.Simple.Core

data UFTestIntsOps = Fun | Ints

data GroundSort : Type where
  IntS, BoolS : GroundSort

0
FunSortsSig : SimpleSig
FunSortsSig x = (x, List x)

0
FunSort : Type
FunSort = FunSortsSig GroundSort

0
OurSort : Type
OurSort = Either GroundSort FunSort

FunFulfillment : List GroundSort -> GroundSort -> FunReq OurSort
FunFulfillment a b = (FunFulfill
             { arg = map Left a
             , ret = Left b
             , fun = Right (b, a)
             })

IntsFulfillment : IntsReq OurSort
IntsFulfillment = IntsFulfill
  { int = Left IntS
  , bool = Left BoolS
  }

0
UFTestInts : (HomSorting {a = OurSort}).RSortedFamilyFun
UFTestInts = CoProd (\case
  Fun => CoProd (\a : List GroundSort =>
         CoProd (\b : GroundSort =>
         FunSig (HomSorting {a = OurSort}) (FunFulfillment a b)))
  Ints => TestIntsSig (HomSorting {a = OurSort}) IntsFulfillment)

UFTestIntsMap : UFTestInts .RSortedFamilyFunctor
UFTestIntsMap = CoProdMap (\case
  Fun => CoProdMap (\a =>
         CoProdMap (\b =>
         FunSigMap (FunFulfillment a b)))
  Ints => TestIntsSigMap (IntsFulfillment))

UFTestIntsStrength : UFTestInts .PointedClosedStrength
UFTestIntsStrength = CoProdPointedClosedStrength (\case
  Fun => CoProdPointedClosedStrength (\a =>
         CoProdPointedClosedStrength (\b =>
         FunSigStrength (FunFulfillment a b)))
  Ints => TestIntsPointedClosedStrength (IntsFulfillment))

UFTestIntsTerm : Term (HomSorting {a = OurSort}) UFTestInts MVar (Left IntS)
  [<("f" :- Right (IntS, [IntS])), ("y" :- Left IntS)]
UFTestIntsTerm = Op (Fun ** ([IntS] ** (IntS ** (App **
  Pack {ty' = ()} [Var (%% "f"), Var (%% "y")]))))
