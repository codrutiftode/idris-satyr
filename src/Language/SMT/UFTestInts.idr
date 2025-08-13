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
  IntS : GroundSort

0
FunSortsSig : SimpleSig
FunSortsSig x = (x, List x)

0
FunSort : Type
FunSort = FunSortsSig GroundSort

0
OurSort : Type
OurSort = Either GroundSort FunSort

Fulfillment : List GroundSort -> GroundSort -> OurSort .Requirement
Fulfillment a b = (MkRequirement
             { arg = map Left a
             , ret = Left b
             , fun = Right (b, a)
             })

0
UFTestInts : (HomSorting {a = OurSort}).RSortedFamilyFun
UFTestInts = CoProd (\case
  Fun => CoProd (\a : List GroundSort =>
         CoProd (\b : GroundSort =>
         FunSig (HomSorting {a = OurSort}) (Fulfillment a b)))
  Ints => TestIntsSig (HomSorting {a = OurSort}) (Left IntS))

UFTestIntsMap : UFTestInts .RSortedFamilyFunctor
UFTestIntsMap = CoProdMap (\case
  Fun => CoProdMap (\a =>
         CoProdMap (\b =>
         FunSigMap (Fulfillment a b)))
  Ints => TestIntsSigMap (Left IntS))

UFTestIntsStrength : UFTestInts .PointedClosedStrength
UFTestIntsStrength = CoProdPointedClosedStrength (\case
  Fun => CoProdPointedClosedStrength (\a =>
         CoProdPointedClosedStrength (\b =>
         FunSigStrength (Fulfillment a b)))
  Ints => TestIntsPointedClosedStrength (Left IntS))

UFTestIntsTerm : Term (HomSorting {a = OurSort}) UFTestInts MVar (Left IntS)
  [<("f" :- Right (IntS, [IntS])), ("y" :- Left IntS)]
UFTestIntsTerm = Op (Fun ** ([IntS] ** (IntS ** (App **
  Pack {ty' = ()} [Var (%% "f"), Var (%% "y")]))))
