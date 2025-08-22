module Language.SMT.Combinator.CoProd

import Language.SMT.Serialise

import MAST.Core
import MAST.Signature

import public MAST.Combinator.CoProd

public export
CoProdSerialise : {0 func : a -> (sort, b) ====> (sort', b')} ->
  ((i : a) -> (func i).SerialiseAlgebra) ->
  (CoProd func).SerialiseAlgebra
CoProdSerialise f = MkSerialiseAlgebra (\(i ** fi) => (f i).alg fi)
