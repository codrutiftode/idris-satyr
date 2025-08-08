module Language.SMT.Quantifiers

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
import MAST.Combinator.Shift
import MAST.Sorted.Core

import Data.List.Quantifiers

public export
data QuantOps = Forall | Exists

public export
labelToArity : {0 sys : SortingSystemOver b s (l.Types ())} ->
  (f : l |= CoreNeed .ops) ->
  QuantOps -> Arity b (l.Types ())
labelToArity f _ =
  CoProd (\x => CoProd (\a => [([<(x, a)], f.get TyBool)] ::=> f.get TyBool))

public export
0
QuantSig : (CoreNeed .ops) .Signature FiniteUnit
QuantSig f sys = CoProd (arity . labelToArity {sys} f)

public export
QuantSigMap : {f : l |= CoreNeed .ops} -> (QuantSig f sys).RSortedFamilyFunctor
QuantSigMap = CoProdMap (\x => ArityMap (labelToArity {sys} f x))

public export
QuantSigStrength : {f : l |= CoreNeed .ops} -> (QuantSig f sys).PointedClosedStrength
QuantSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm FiniteUnit QuantSig (HomFullfill .get TyBool) [<("x" :- HomFullfill .get TyBool)]
term0 = Op (Forall ** ("y" ** 
  (HomFullfill .get TyBool ** Pack {ty' = ()} [Var (?helpo)]))) 
  -- Op (Forall ** ("y" ** (Op TyBool ** Pack {ty' = ()} [Var (%% "x")])))

QuantRelAlg : RelativeAlgebra HomSorting (QuantSig .Hom {collate = FiniteUnit})
  Var SerialisedCoalg SerialisedPoint Base
QuantRelAlg = MkRelativeAlgebra
  { alg = \x => case x of
      (Forall ** (name ** (ty ** Pack [body]))) => \ps =>
        let Str bodyStr = body (S ps)
            shed = ?helpoo
        in Str $ "forall " ++ name ++ ". " ++ bodyStr
      (Exists ** snd) => ?hope_2
  , val = \(x, y) => \ps => ?hope
  , menv = ?wut2
  }

serialiseQuant : HomSorting .Serialiser (HomTerm FiniteUnit QuantSig)
serialiseQuant = serialiseTerm
  (QuantSigStrength {f = HomFullfill, sys = HomSorting})
  (QuantSigMap {f = HomFullfill, sys = HomSorting})
  QuantRelAlg

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm FiniteUnit QuantSig s ctx -> String
test term = let (Str s) = serialiseQuant term ctx SerialisedPoint ps in s

main : IO ()
main = putStrLn (test term0)
