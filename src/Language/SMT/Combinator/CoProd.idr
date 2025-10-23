module Language.SMT.Combinator.CoProd

import Language.SMT.Serialise
import Language.SMT.Names

import MAST.Core
import MAST.Signature
import MAST.Tensor

import public MAST.Combinator.CoProd

public export
CoProdSerialise : {0 func : a -> (sort, b) ====> (sort', b')} ->
  ((i : a) -> (func i).SerialiseAlgebra) ->
  (CoProd func).SerialiseAlgebra
CoProdSerialise f = MkSerialiseAlgebra (\(i ** fi) => (f i).alg fi)

public export
CoProdCombineSerialisers : {0 sys : SortingSystemOver b s sort} ->
  {0 func : a -> sys.RSortedFamilyFun} ->
  sys.MetaSerialise mvar ->
  ((i : a) -> sys.SerialiseWithAction (func i) mvar) ->
  sys.SerialiseWithAction (CoProd func) mvar
CoProdCombineSerialisers meta f = MkSerialiseWithAction
  { alg = CoProdSerialise (\i => (f i).alg)
  , meta = meta
  , oMap = CoProdMap (\i => (f i).oMap)
  , oStrength = CoProdPointedClosedStrength (\i => (f i).oStrength)
  }
