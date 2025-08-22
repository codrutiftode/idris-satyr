module Language.SMT.Combinator.Extend

import Language.SMT.Serialise

import MAST.Core
import MAST.Signature

import public MAST.Combinator.Extend

public export
ExtendSerialise : (phi : sort' -> sort) -> (Extend phi).SerialiseAlgebra
ExtendSerialise phi = MkSerialiseAlgebra (\(Pack x) => x)
