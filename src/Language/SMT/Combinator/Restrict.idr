module Language.SMT.Combinator.Restrict

import Language.SMT.Serialise

import MAST.Core
import MAST.Signature

import public MAST.Combinator.Restrict

public export
RestrictSerialise : (phi : sort' -> sort) -> (phi %|).SerialiseAlgebra
RestrictSerialise phi = MkSerialiseAlgebra id
