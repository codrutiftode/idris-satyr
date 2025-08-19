module Language.SMT.TestInts

import Language.SMT.Signature
import Language.SMT.Arity
import Language.SMT.Core
import Language.SMT.Serialise

import Data.List.Quantifiers

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Modality
import MAST.Presheaf
import MAST.Combinator.List
import MAST.Combinator.Restrict
import MAST.Combinator.Extend
import MAST.Combinator.List.Quantifiers
import MAST.Combinator.CoProd
import MAST.Combinator.Prod
import MAST.Combinator.Const
import MAST.Combinator.Compose
import MAST.Simple.Core

public export
data TestIntsOps = AInt | Add

public export
record IntsReq (sort : Type) where
  constructor IntsFulfill
  bool, int : sort

public export
labelToArity : {0 sys : SortingSystemOver b s sort} ->
  (r : IntsReq sort) -> TestIntsOps -> Arity b sort
labelToArity r AInt = Const r.int Int
labelToArity r Add  = [r.int, r.int] :=> r.int

public export
0
TestIntsSig : IntsReq .Signature
TestIntsSig sys r = CoProd (arity . labelToArity {sys} r)

public export
TestIntsSigMap : {sys : SortingSystemOver b s sort} ->
  (r : IntsReq sort) ->
  (TestIntsSig sys r).RSortedFamilyFunctor
TestIntsSigMap r = CoProdMap (\x => ArityMap (labelToArity {sys} r x))

public export
TestIntsStrength : {sys : SortingSystemOver b s sort} ->
  (r : IntsReq sort) ->
  (TestIntsSig sys r).PointedClosedStrength
TestIntsStrength r = CoProdPointedClosedStrength
  (\x => ArityStrength (labelToArity {sys} r x))

public export
TestIntsSigSerialise : {r : _} -> (TestIntsSig sys r) SerialiseTarget -|> SerialiseTarget
TestIntsSigSerialise (AInt ** (Pack x)) =
  ([<] ** (Z, const (cast x), \((%%) {pos = _} name) impossible))
TestIntsSigSerialise (Add ** (Pack [x, y])) =
  case (x, y) of
    ((dtx1 ** (ndtx1, s1, ren1)), (dtx2 ** (ndtx2, s2, ren2))) =>
      (dtx1 ++ dtx2 ** (concatNames ndtx1 ndtx2,
        \ns => "(+ " ++ s1 (namesR ns) ++ " " ++ s2 (namesL ns) ++ ")",
          pair ren1 ren2))

data IntSorts : Type where
  IntS, BoolS : IntSorts

Fulfill : IntsReq IntSorts
Fulfill = IntsFulfill BoolS IntS

SerialiseVal : Var -|> (SerialiseTarget . (HomSorting IntSorts).fst)
SerialiseVal {ty} v = ([<("x" :- ty)] **
  (S ("x", 0) Z, \ns => lookup ns (Here  .toVar),
    \((%%) {pos = Here} _) => v))

RelAlg : RelativeAlgebra (HomSorting IntSorts)
  (TestIntsSig (HomSorting IntSorts) Fulfill) MVar
  SerialiseParamCoalg SerialiseParamPoint SerialiseTarget
RelAlg = MkRelativeAlgebra
  { alg = TestIntsSigSerialise
  , val = SerialiseVal
  , menv = ?wowo
  }

serialiseTestInts : (HomSorting IntSorts).Serialiser (HomTerm TestIntsSig Fulfill)
serialiseTestInts = serialiseTerm
  (TestIntsStrength Fulfill)
  (TestIntsSigMap Fulfill)
  RelAlg

term0 : HomTerm TestIntsSig Fulfill IntS [<("huh" :- IntS)]
term0 = Op (Add ** Pack {ty' = ()} [Var (%% "huh"), Op (AInt ** Pack {ty' = ()} 2)])

term1 : HomTerm TestIntsSig Fulfill IntS [<("a" :- IntS), ("b" :- IntS)]
term1 = Op (Add ** Pack {ty' = ()} [Var (%% "a"), Var (%% "b")])

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm TestIntsSig Fulfill s ctx -> String
test t =
  let (dtx ** (ns, s, ren)) = serialiseTestInts t ctx id
      nctx : Names ctx = cast ps
  in s (mangleGlobal (NamesCovPsh ren nctx))
