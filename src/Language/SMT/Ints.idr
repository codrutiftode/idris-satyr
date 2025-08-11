module Language.SMT.Ints

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Arity
import Language.SMT.Core
import Language.SMT.Serialise

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

import MAST.Sorted.Core
import Data.List.Quantifiers

data TyInts : Type where
  TyInt : TyInts

IntNeed : Signature ()
IntNeed = MkSignature
  { ops = \x => const (Any id [TyInts, TyCore])
  , map = \_ => id
  }

data IntOps = AInt | Neg | Sub | Add | Mul | Div | Mod | Abs | Leq | Geq | Lt | Gt

labelToArity : {0 sys : SortingSystemOver b s (SingleKind $ l.Types vars)} ->
  (f : l |= IntNeed .ops) -> IntOps -> Arity b (SingleKind $ l.Types vars)
labelToArity f AInt = (Const (f.op (Here TyInt)) Int)
labelToArity f Neg  = [f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Sub  = [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Add  = [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Mul  = [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Div  = [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Mod  = [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Abs  = [f.op (Here TyInt)] :=> (f.op (Here TyInt))
labelToArity f Leq  =
  [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (There (Here TyBool)))
labelToArity f Geq  =
  [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (There (Here TyBool)))
labelToArity f Lt   =
  [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (There (Here TyBool)))
labelToArity f Gt   =
  [f.op (Here TyInt), f.op (Here TyInt)] :=> (f.op (There (Here TyBool)))

0
IntSig : (IntNeed .ops) .Signature SingleKind vars
IntSig f sys = CoProd (arity . labelToArity {f})

IntSigMap : {f : l |= IntNeed .ops} -> (IntSig f sys).RSortedFamilyFunctor
IntSigMap = CoProdMap (\x => ArityMap (labelToArity f x))

IntSigStrength : {f : l |= IntNeed .ops} -> (IntSig f sys).PointedClosedStrength
IntSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm SingleKind NoSortVar IntSig (SelfFullfill .op (Here TyInt))
  [<("x" :- Op (Here TyInt))]
term0 = Op (Add ** Pack {ty' = ()} [Var (%% "x"), Op (AInt ** Pack {ty' = ()} 3)])

IntsRelAlg : RelativeAlgebra _ (IntSig .Hom {collate = SingleKind})
  MVar SerialisedCoalg SerialisedPoint Base
IntsRelAlg = MkRelativeAlgebra
  { alg = \x => case x of
        (AInt ** Pack x) => \_ => cast x
        (Neg ** snd) => ?huh_2
        (Sub ** snd) => ?huh_3
        (Add ** (Pack [x, y])) => \ps => x ps ++ "+" ++ y ps
        (Mul ** snd) => ?huh_5
        (Div ** snd) => ?huh_6
        (Mod ** snd) => ?huh_7
        (Abs ** snd) => ?huh_8
        (Leq ** snd) => ?huh_9
        (Geq ** snd) => ?huh_10
        (Lt ** snd) => ?huh_11
        (Gt ** snd) => ?huh_12
  , val = \v, names => lookup names v
  , menv = \meta => const (meta.snd.fst)
  }

serialiseInts : HomSorting .Serialiser (HomTerm SingleKind NoSortVar IntSig)
serialiseInts = serialiseTerm IntSigStrength IntSigMap ?aIntsRelAlg

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm SingleKind NoSortVar IntSig s ctx -> String
test term = serialiseInts term ctx SerialisedPoint (setupNames ps)

main : IO ()
main = putStrLn (test term0)

{-
prettyInts : Serialiser HomSorting (HomTerm IntSig SingleKind) Var
prettyInts = ?todo -- pretty IntSigStrength IntsRelAlg IntSigMap

testTerm : HomTerm FiniteUnit IntSig (SelfFullfill .op (Here TyInt)) [<]
testTerm = Op (Add ** Pack {ty' = ()}
  [Op (AInt ** Pack {ty' = ()} 1), Op (AInt ** Pack {ty' = ()} 2)])

test : Strings ((SelfFullfill {a = IntNeed .ops}) .op (Here TyInt)) [<]
test = let shed = prettyInts testTerm ?wo ?wow in ?rest
