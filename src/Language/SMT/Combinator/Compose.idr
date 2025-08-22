module Language.SMT.Combinator.Compose

import Language.SMT.Serialise

import MAST.Core
import MAST.Substitution
import MAST.Signature

import public MAST.Combinator.Compose

public export
ComposeSerialise : g.SerialiseAlgebra ->
  f.SerialiseAlgebra ->
  g.RSortedFamilyFunctor ->
  (g . f).SerialiseAlgebra
ComposeSerialise ga fa gmap = MkSerialiseAlgebra (ga.alg . gmap.map fa.alg)
