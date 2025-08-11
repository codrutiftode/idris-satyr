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

data Kind = KGround | KFun

KCollate : Collate Kind
KCollate fam = (i : Kind ** fam i)

TypesSig : Kind .SortedSig
TypesSig x KGround = ()
TypesSig x KFun = (x KGround, List (x KGround))

MapTypesSig : Map TypesSig
MapTypesSig {s = KGround} _ = id
MapTypesSig {s = KFun}    f = bimap f (map f)

public export
FunNeed : Signature Kind
FunNeed = MkSignature
  { ops = TypesSig
  , map = MapTypesSig
  }

public export
data FunOps = App

public export
labelToArity : {sys : SortingSystemOver fstSort sndSort (KCollate (l.Types vars))} ->
  (f : l |= FunNeed .ops) -> FunOps -> Arity fstSort (KCollate (l.Types vars))
labelToArity f App = CoProd (\s1 : List (l .term vars KGround) =>
                     CoProd (\s2 : _ =>
                     (KFun ** (f.op (s2, s1))) :: (map (\x => (KGround ** x)) s1) :=>
                     (KGround ** s2)))

public export
0
FunSig : (FunNeed .ops) .Signature KCollate vars
FunSig f sys = CoProd (arity . labelToArity {sys} f)

public export
FunSigMap : {sys : SortingSystemOver b s (KCollate (l.Types vars))} ->
  {f : l |= FunNeed .ops} -> (FunSig f sys).RSortedFamilyFunctor
FunSigMap = CoProdMap (\x => ArityMap (labelToArity {sys} f x))

public export
FunSigStrength : {sys : SortingSystemOver b s (KCollate (l.Types vars))} ->
  {f : l |= FunNeed .ops} -> (FunSig f sys).PointedClosedStrength
FunSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm KCollate NoSortVar FunSig (KGround ** Op ())
  [<("f" :- (KFun ** Op (Op (), [Op ()]))), ("x" :- (KGround ** Op ()))]
term0 = Op (App ** ([Op ()] ** (_ **
        Pack {ty' = ()} [Var (%% "f"), Var (%% "x")]
        )))
