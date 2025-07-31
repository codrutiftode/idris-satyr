module Language.SMT.Ints

import Data.List.Quantifiers

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Arity
import Language.SMT.Core

import MAST.Core
import MAST.Signature
import MAST.Initiality
import MAST.Tensor

import MAST.Simple.Core

%hide Builtin.DPair.DPair.(.fst)
%hide Builtin.DPair.DPair.(.snd)

data TyInts : Type where
  TyInt : TyInts

IntNeed : Signature
IntNeed = MkSignature
  { ops = \x => Any id [TyInts, TyCore]
  , map = \_ => id
  }

data IntOps = AInt | Neg | Sub | Add | Mul | Div | Mod | Abs | Leq | Geq | Lt | Gt

labelToArity : (f : l |= IntNeed .ops) -> IntOps -> Arity (l.Types)
labelToArity f AInt = (Const (f.get (Here TyInt)) Int)
labelToArity f Neg  = [f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Sub  = [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Add  = [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Mul  = [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Div  = [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Mod  = [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Abs  = [f.get (Here TyInt)] :=> (f.get (Here TyInt))
labelToArity f Leq  =
  [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (There (Here TyBool)))
labelToArity f Geq  =
  [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (There (Here TyBool)))
labelToArity f Lt   =
  [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (There (Here TyBool)))
labelToArity f Gt   =
  [f.get (Here TyInt), f.get (Here TyInt)] :=> (f.get (There (Here TyBool)))

0
IntSig : (IntNeed .ops) .Signature
IntSig f sys = CoProd (arity . labelToArity {f})

IntSigMap : {f : l |= IntNeed .ops} -> (IntSig f sys).RSortedFamilyFunctor
IntSigMap = CoProdMap (\x => ArityMap (labelToArity f x))

IntSigStrength : {f : l |= IntNeed .ops} -> (IntSig f sys).ClosedStrength
IntSigStrength = CoProdClosedStrength (\x => ArityStrength (labelToArity f x))

term0 : HomTerm IntSig (HomFullfill .get (There (Here TyBool)))
  [<("x" :- Op (Here TyInt))]
term0 = Op (Leq ** Pack {ty' = ()} [Var (%% "x"), Op (AInt ** Pack {ty' = ()} 3)])
