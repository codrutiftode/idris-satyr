module Language.SMT.TestInts

import Language.SMT.Signature
import Language.SMT.Arity
import Language.SMT.Core
import Language.SMT.Serialise
import Language.SMT.SerialiseArity

import Data.List.Quantifiers
import Data.String
import Data.Singleton

import Language.SMT.Names

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Modality
import MAST.Presheaf
import MAST.Simple.Core

import Language.SMT.Combinator.Restrict
import Language.SMT.Combinator.Extend
import Language.SMT.Combinator.Const
import Language.SMT.Combinator.Compose
import Language.SMT.Combinator.CoProd
import Language.SMT.Combinator.List.Quantifiers
import Language.SMT.Combinator.Shift

%hide Data.List.sort

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

foo : (op : TestIntsOps) -> ArityMetadata (labelToArity {sys} r op)
foo AInt = cast
foo Add = \args => "(+ \{joinBy " " (cast args)})"

public export
TestIntsSerialiseAlg : {sys : SortingSystemOver b s sort} ->
  {r : _} -> (TestIntsSig sys r).SerialiseAlgebra
TestIntsSerialiseAlg = CoProdSerialise (\op =>
    AritySerialise {sys} (labelToArity {sys} r op)
    (foo op))

data IntSorts : Type where
  IntS, BoolS : IntSorts

Fulfill : IntsReq IntSorts
Fulfill = IntsFulfill BoolS IntS

TestIntsMeta : MVar -|> Strings
TestIntsMeta (_, Z, m) = ""
TestIntsMeta (Val (ctx :< (x :- ty)), (S n ns), m) =
  "(+ \{TestIntsMeta {ty} (Val ctx, ns, m)} \{mangleSchema n})"

TestIntsSerialiser : {sys, r : _} -> sys.Serialiser (Term sys (TestIntsSig sys r) MVar)
TestIntsSerialiser = serialiser (MkSerialiseWithAction
  { alg = (TestIntsSerialiseAlg {sys, r}).alg
  , meta = TestIntsMeta {ty}
  , isMVar = MVarValid
  , oMap = TestIntsSigMap {sys} r
  , oStrength = TestIntsStrength {sys} r
  })

term0 : HomTerm TestIntsSig Fulfill MVar IntS [<("x" :- IntS)]
term0 = Op (Add ** Pack {ty' = ()} [Var (%% "x"), Op (AInt ** Pack {ty' = ()} 2)])

term1 : HomTerm TestIntsSig Fulfill MVar IntS [<("a" :- IntS), ("b" :- IntS)]
term1 = Op (Add ** Pack {ty' = ()} [Var (%% "a"), Var (%% "b")])

test : {ctx : IntSorts .Ctx} -> {s : IntSorts} -> {auto ps : PS ctx} ->
  HomTerm TestIntsSig Fulfill MVar s ctx -> String
test = runSerialiser TestIntsSerialiser
