module Language.SMT.TestInts

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Arity
import Language.SMT.Core
import Language.SMT.Serialise

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

public export
data TestIntsOps = AInt | Add

public export
record IntsReq (sort : Type) where
  constructor IntsFulfill
  bool, int : sort

public export
labelToArity : {0 sys : SortingSystemOver b s sort} ->
  (r : IntsReq sort) -> TestIntsOps -> Arity b sort
labelToArity r AInt = Const r.int Int
labelToArity r Add  = [r.int, r.int] :=> r.int

public export
0
TestIntsSig : IntsReq .Signature
TestIntsSig sys r = CoProd (arity . labelToArity {sys} r)

public export
TestIntsSigMap : {sys : SortingSystemOver b s sort} ->
  (r : IntsReq sort) ->
  (TestIntsSig sys r).RSortedFamilyFunctor
TestIntsSigMap r = CoProdMap (\x => ArityMap (labelToArity {sys} r x))

public export
TestIntsPointedClosedStrength : {sys : SortingSystemOver b s sort} ->
  (r : IntsReq sort) ->
  (TestIntsSig sys r).PointedClosedStrength
TestIntsPointedClosedStrength r = CoProdPointedClosedStrength
  (\x => ArityStrength (labelToArity {sys} r x))
