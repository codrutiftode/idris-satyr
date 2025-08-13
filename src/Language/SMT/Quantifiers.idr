module Language.SMT.Quantifiers

import Debug.Trace

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
labelToArity : {0 sys : SortingSystemOver b s sort} ->
  (r : CoreReq sort) ->
  QuantOps -> Arity b sort
labelToArity r _ =
  CoProd (\x => CoProd (\a => [([<(x, a)], r.bool)] ::=> r.bool))

public export
0
QuantSig : CoreReq .Signature
QuantSig sys r = CoProd (arity . labelToArity {sys} r)

public export
QuantSigMap : (r : CoreReq sys.Sort) -> (QuantSig sys r).RSortedFamilyFunctor
QuantSigMap r = CoProdMap (\x => ArityMap (labelToArity {sys} r x))

public export
QuantSigStrength : (r : CoreReq sys.Sort) -> (QuantSig sys r).PointedClosedStrength
QuantSigStrength r = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} r x))

QuantRelAlg : RelativeAlgebra (HomSorting sort)
  (QuantSig (HomSorting sort) r)
  MVar SerialisedCoalg SerialisedPoint Base
QuantRelAlg = MkRelativeAlgebra
  { alg = \case
      (Forall ** (name ** (ty ** Pack [body]))) => \names =>
        let mangled = mangle name names
        in "(forall "
            ++ mangleSchema mangled
            ++ " "
            ++ body (S mangled names)
            ++ ")"
      (Exists ** (name ** (ty ** Pack [body]))) => \names =>
        let mangled = mangle name names
        in "(exists "
            ++ mangleSchema mangled
            ++ " "
            ++ body (S mangled names)
            ++ ")"
  , val = \v, names => lookup names v
  , menv = \meta => const (meta.snd.fst)
  }

serialiseQuant : (r : CoreReq sort) -> (HomSorting sort) .Serialiser (HomTerm QuantSig r)
serialiseQuant r = serialiseTerm
  (QuantSigStrength {r, sys = HomSorting sort})
  (QuantSigMap {r, sys = HomSorting sort})
  QuantRelAlg

data TheSorts : Type where
  BoolS : TheSorts

Fulfill : CoreReq TheSorts
Fulfill = CoreFulfill BoolS

term0 : HomTerm QuantSig Fulfill BoolS [<("x" :- BoolS)]
term0 = Op (Forall ** ("x" **
  (BoolS ** Pack {ty' = ()} [Var (%% "x")])))

term1 : HomTerm QuantSig Fulfill BoolS [<("x" :- BoolS)]
term1 = Op (Forall ** ("x" **
  (BoolS ** Pack {ty' = ()} [
    Op (Exists ** ("x" ** (BoolS ** Pack {ty' = ()} [Var (Here .toVar)])))
  ])))

term2 : HomTerm QuantSig Fulfill BoolS [<("x" :- BoolS), ("x" :- BoolS), ("x" :- BoolS)]
term2 = Var (Here .toVar)

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm QuantSig Fulfill s ctx -> String
test term = serialiseQuant Fulfill term ctx SerialisedPoint (setupNames ps)

main : IO ()
main = putStrLn (test term0)
