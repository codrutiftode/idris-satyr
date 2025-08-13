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
labelToArity : {0 sys : SortingSystemOver b s sort} ->
  (a : sort) -> TestIntsOps -> Arity b sort
labelToArity a AInt = Const a Int
labelToArity a Add  = [a, a] :=> a

public export
0
TestIntsSig : (sys : SortingSystemOver fstSort sndSort sort) ->
  (a : sort) -> sys.RSortedFamilyFun
TestIntsSig sys a = CoProd (arity . labelToArity {sys} a)

public export
TestIntsSigMap : {sys : SortingSystemOver b s sort} ->
  (a : sort) ->
  (TestIntsSig sys a).RSortedFamilyFunctor
TestIntsSigMap a = CoProdMap (\x => ArityMap (labelToArity {sys} a x))

public export
TestIntsPointedClosedStrength : {sys : SortingSystemOver b s sort} ->
  (a : sort) ->
  (TestIntsSig sys a).PointedClosedStrength
TestIntsPointedClosedStrength a = CoProdPointedClosedStrength
  (\x => ArityStrength (labelToArity {sys} a x))
