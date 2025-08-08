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

labelToArity : {0 sys : SortingSystemOver b s (l.Types ())} ->
  (f : l |= IntNeed .ops) -> IntOps -> Arity b (l.Types ())
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
IntSig : (IntNeed .ops) .Signature FiniteUnit
IntSig f sys = CoProd (arity . labelToArity {f})

IntSigMap : {f : l |= IntNeed .ops} -> (IntSig f sys).RSortedFamilyFunctor
IntSigMap = CoProdMap (\x => ArityMap (labelToArity f x))

IntSigStrength : {f : l |= IntNeed .ops} -> (IntSig f sys).PointedClosedStrength
IntSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm FiniteUnit IntSig (HomFullfill .get (Here TyInt))
  [<("x" :- Op (Here TyInt))]
term0 = Op (Add ** Pack {ty' = ()} [Var (%% "x"), Op (AInt ** Pack {ty' = ()} 3)])

IntsRelAlg : RelativeAlgebra _ (IntSig .Hom {collate = FiniteUnit})
  Var SerialisedCoalg SerialisedPoint Base
IntsRelAlg = MkRelativeAlgebra
  { alg = \x => case x of
        (AInt ** Pack x) => \_ => Str (cast x)
        (Neg ** snd) => ?huh_2
        (Sub ** snd) => ?huh_3
        (Add ** (Pack [x, y])) => \ps =>
             let (Str x') = x ps
                 (Str y') = y ps
             in Str (x' ++ "+" ++ y')
        (Mul ** snd) => ?huh_5
        (Div ** snd) => ?huh_6
        (Mod ** snd) => ?huh_7
        (Abs ** snd) => ?huh_8
        (Leq ** snd) => ?huh_9
        (Geq ** snd) => ?huh_10
        (Lt ** snd) => ?huh_11
        (Gt ** snd) => ?huh_12
  , val = \(x, y) => \ps => let (Str s) = y ps in Str s
  , menv = ?wut2
  }

serialiseInts : HomSorting .Serialiser (HomTerm FiniteUnit IntSig)
serialiseInts = serialiseTerm IntSigStrength IntSigMap ?aIntsRelAlg

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm FiniteUnit IntSig s ctx -> String
test term = let (Str s) = serialiseInts term ctx SerialisedPoint ps in s

main : IO ()
main = putStrLn (test term0)

{-
prettyInts : Serialiser HomSorting (HomTerm IntSig FiniteUnit) Var
prettyInts = ?todo -- pretty IntSigStrength IntsRelAlg IntSigMap

testTerm : HomTerm FiniteUnit IntSig (HomFullfill .get (Here TyInt)) [<]
testTerm = Op (Add ** Pack {ty' = ()}
  [Op (AInt ** Pack {ty' = ()} 1), Op (AInt ** Pack {ty' = ()} 2)])

test : Strings ((HomFullfill {a = IntNeed .ops}) .get (Here TyInt)) [<]
test = let shed = prettyInts testTerm ?wo ?wow in ?rest
