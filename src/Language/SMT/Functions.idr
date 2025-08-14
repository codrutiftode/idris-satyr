module Language.SMT.Functions

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Arity
import Language.SMT.Core

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
import MAST.Combinator.Shift
import MAST.Sorted.Core

import Data.List.Quantifiers
import Data.Singleton

public export
data FunOps = App

public export
record FunReq (sort : Type) where
  constructor FunFulfill
  arg : List sort
  fun, ret : sort

public export
labelToArity : {sys : SortingSystemOver fstSort sndSort sort} ->
  FunReq sort -> FunOps -> Arity fstSort sort
labelToArity r App = r.fun :: r.arg :=> r.ret

public export
0
FunSig : (sys : SortingSystemOver fstSort sndSort sort) ->
  FunReq sort -> sys.RSortedFamilyFun
FunSig sys r = CoProd (arity . labelToArity {sys} r)

public export
FunSigMap : {sys : SortingSystemOver b s sort} ->
  (r : FunReq sort) ->
  (FunSig sys r).RSortedFamilyFunctor
FunSigMap r = CoProdMap (\x => ArityMap (labelToArity {sys} r x))

public export
FunSigStrength : {sys : SortingSystemOver b s sort} ->
  (r : FunReq sort) ->
  (FunSig sys r).PointedClosedStrength
FunSigStrength r =
  CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} r x))

{-
term0 : HomTerm KCollate NoSortVar FunSig (KGround ** Op ())
  [<("f" :- (KFun ** Op (Op (), [Op ()]))), ("x" :- (KGround ** Op ()))]
term0 = Op (App ** ([Op ()] ** (_ **
        Pack {ty' = ()} [Var (%% "f"), Var (%% "x")]
        )))
