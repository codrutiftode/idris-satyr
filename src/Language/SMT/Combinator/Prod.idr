module Language.SMT.Combinator.Prod

import Language.SMT.Serialise

import MAST.Core
import MAST.Signature

import public MAST.Combinator.Prod

public export
ProdSerialise : {0 func : a -> (sort, b) ====> (sort', b')} ->
  ((i : a) -> (func i).SerialiseAlgebra) ->
  (Prod func).SerialiseAlgebra
ProdSerialise f = MkSerialiseAlgebra (\x => ?sth)
