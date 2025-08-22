module Language.SMT.Combinator.Const

import Language.SMT.Serialise
import Language.SMT.Names

import MAST.Core
import MAST.Substitution
import MAST.Signature

import public MAST.Combinator.Const

public export
ConstSerialise : (f : sort.SortedFamilyOver b) ->
  (metadata : {s : sort} -> {0 ctx : b.Ctx} -> f s ctx -> String) ->
  (Const f).SerialiseAlgebra
ConstSerialise f m = MkSerialiseAlgebra (\t => ([<] ** (Z, const (m t), LinTerminal)))
