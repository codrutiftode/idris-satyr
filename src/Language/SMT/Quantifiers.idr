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

term0 : HomTerm FiniteUnit QuantSig (Op TyBool) [<("x" :- Op TyBool)]
term0 = Op (Forall ** ("y" **
  (Op TyBool ** Pack {ty' = ()} [Var (%% "y")])))

term1 : HomTerm FiniteUnit QuantSig (Op TyBool) [<("x" :- Op TyBool)]
term1 = Op (Forall ** ("y" **
  (Op TyBool ** Pack {ty' = ()} [
    Op (Exists ** ("x" ** (Op TyBool ** Pack {ty' = ()} [Var (Here .toVar)])))
  ])))

term2 : HomTerm FiniteUnit QuantSig (Op TyBool) [<("x_2" :- Op TyBool), ("x" :- Op TyBool), ("x" :- Op TyBool)]
term2 = Var ((Here).toVar)

QuantRelAlg : RelativeAlgebra HomSorting (QuantSig .Hom {collate = FiniteUnit})
  Var SerialisedCoalg SerialisedPoint Base
QuantRelAlg = MkRelativeAlgebra
  { alg = \case
      (Forall ** (name ** (ty ** Pack [body]))) => \names =>
        let mangled = mangle name names
        in Str "forall \{mangled.fst}. \{(body (S mangled names)).str}"
      (Exists ** (name ** (ty ** Pack [body]))) => \names =>
        let mangled = mangle name names
        in Str "exists \{mangled.fst}. \{(body (S mangled names)).str}"
  , val = \v, names => lookup names v
  , menv = \sth => \arg => ?wut2_1
  }

serialiseQuant : HomSorting .Serialiser (HomTerm FiniteUnit QuantSig)
serialiseQuant = serialiseTerm
  (QuantSigStrength {f = HomFullfill, sys = HomSorting})
  (QuantSigMap {f = HomFullfill, sys = HomSorting})
  QuantRelAlg

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm FiniteUnit QuantSig s ctx -> String
test term = (serialiseQuant term ctx SerialisedPoint (setupNames ps)).str

main : IO ()
main = putStrLn (test term0)
