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
labelToArity : {0 sys : SortingSystemOver b s (SingleKind $ l.Types vars)} ->
  (f : l |= CoreNeed .ops) ->
  QuantOps -> Arity b (SingleKind $ l.Types vars)
labelToArity f _ =
  CoProd (\x => CoProd (\a => [([<(x, a)], f.op TyBool)] ::=> f.op TyBool))

public export
0
QuantSig : (CoreNeed .ops) .Signature SingleKind vars
QuantSig f sys = CoProd (arity . labelToArity {sys} f)

public export
QuantSigMap : {f : l |= CoreNeed .ops} -> (QuantSig f sys).RSortedFamilyFunctor
QuantSigMap = CoProdMap (\x => ArityMap (labelToArity {sys} f x))

public export
QuantSigStrength : {f : l |= CoreNeed .ops} -> (QuantSig f sys).PointedClosedStrength
QuantSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm SingleKind NoSortVar QuantSig (Op TyBool) [<("x" :- Op TyBool)]
term0 = Op (Forall ** ("y" **
  (Op TyBool ** Pack {ty' = ()} [Var (%% "y")])))

term1 : HomTerm SingleKind NoSortVar QuantSig (Op TyBool) [<("x" :- Op TyBool)]
term1 = Op (Forall ** ("x" **
  (Op TyBool ** Pack {ty' = ()} [
    Op (Exists ** ("x" ** (Op TyBool ** Pack {ty' = ()} [Var (Here .toVar)])))
  ])))

term2 : HomTerm SingleKind NoSortVar QuantSig (Op TyBool) [<("x" :- Op TyBool), ("x" :- Op TyBool), ("x" :- Op TyBool)]
term2 = Var (Here .toVar)

QuantRelAlg : RelativeAlgebra HomSorting 
  (QuantSig .Hom {collate = SingleKind} {vars = NoSortVar})
  MVar SerialisedCoalg SerialisedPoint Base
QuantRelAlg = MkRelativeAlgebra
  { alg = \case
      (Forall ** (name ** (ty ** Pack [body]))) => \names =>
        let mangled = mangle name names
        in "(forall \{mangleSchema mangled} \{body (S mangled names)})"
      (Exists ** (name ** (ty ** Pack [body]))) => \names =>
        let mangled = mangle name names
        in "(exists \{mangleSchema mangled} \{body (S mangled names)})"
  , val = \v, names => lookup names v
  , menv = \meta => const (meta.snd.fst)
  }

serialiseQuant : HomSorting .Serialiser (HomTerm SingleKind NoSortVar QuantSig)
serialiseQuant = serialiseTerm
  (QuantSigStrength {f = SelfFullfill, sys = HomSorting})
  (QuantSigMap {f = SelfFullfill, sys = HomSorting})
  QuantRelAlg

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm SingleKind NoSortVar QuantSig s ctx -> String
test term = serialiseQuant term ctx SerialisedPoint (setupNames ps)

main : IO ()
main = putStrLn (test term0)
