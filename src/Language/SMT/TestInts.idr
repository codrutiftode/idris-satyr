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

opSerialise : (op : TestIntsOps) -> ArityMetadata (labelToArity {sys} r op)
opSerialise AInt = cast
opSerialise Add = \args => "(+ \{joinBy " " (cast args)})"

public export
TestIntsSerialiseAlg : {sys : SortingSystemOver b s sort} ->
  {r : _} -> (TestIntsSig sys r).SerialiseAlgebra
TestIntsSerialiseAlg = CoProdSerialise (\op =>
    AritySerialise {sys} (labelToArity {sys} r op)
    (opSerialise op))

data IntSorts : Type where
  IntS, BoolS : IntSorts

Fulfill : IntsReq IntSorts
Fulfill = IntsFulfill BoolS IntS

public export
infixr 3 =|>

public export
0
(=|>) : (src,tgt : sort.SortedFamilyOver bindable) -> Type
(src =|> tgt) = (ty : sort) -> (0 ctx : bindable.Ctx) -> src ty ctx -> tgt ty ctx

implicate : src =|> tgt -> src -|> tgt
implicate f x = f ty ctx x

0
MVar' : sort.SortedFamilyOver b
MVar' s ctx = (Singleton s, MVar s ctx)

record Gadget a where
  constructor MkGadget
  theA : a

TestIntsMenv' : {0 sys : SortingSystemOver b s sort} -> (MVar' {sort,b} -|> Strings {sort,b})
TestIntsMenv' (ty, (_, Z, m)) = ""
TestIntsMenv' (ty, (Val (ctx :< (x :- ty')), (S n ns), m)) =
  let (Val ty) = ty
  in "(+ \{TestIntsMenv' {sys, ty} (Val ty, (Val ctx, ns, m))} \{mangleSchema n})"

TestIntsMenv : {0 sys : SortingSystemOver b s sort} -> (MVar {sort,b} -|> Strings {sort,b})
TestIntsMenv (_, Z, m) = ""
TestIntsMenv (Val (ctx :< (x :- ty')), (S n ns), m) =
  "(+ \{TestIntsMenv {sys, ty} (Val ctx, ns, m)} \{mangleSchema n})"

TestIntsMenv'' : {0 sys : SortingSystemOver b s sort} ->
  Gadget (MVar {sort,b} -|> Strings {sort,b})

MVarValid' : sys.IsMVar MVar'
MVarValid' = IsMvar
  { info = snd
  , updateNames = \ns => \(ty, (params,_,str)) => (ty, (params,ns,str))
  }

mkMetaSerialise : (meta : mvar =|> Strings) ->
  (isMVar : sys.IsMVar mvar) ->
  sys.MetaSerialise mvar
mkMetaSerialise meta isMVar = MkMetaSerialise
  { meta = implicate meta
  , isMVar
  }

TestIntsMeta : {0 sys : SortingSystemOver b s sort} -> sys.MetaSerialise MVar
TestIntsMeta = mkMetaSerialise
  (\ty, ctx => TestIntsMenv {sys, ty, ctx})
  (MVarValid {sys})

{-
public export
TestIntsSerialiseAction : {sys, r : _} ->
  sys.SerialiseWithAction (TestIntsSig sys r) MVar
TestIntsSerialiseAction = (MkSerialiseWithAction
  { alg = TestIntsSerialiseAlg {sys, r}
  , meta = TestIntsMeta
  , oMap = TestIntsSigMap {sys} r
  , oStrength = TestIntsStrength {sys} r
  })

TestIntsSerialiser : {sys, r : _} -> sys.Serialiser (Term sys (TestIntsSig sys r) MVar)
TestIntsSerialiser = serialiser TestIntsSerialiseAction

term0 : HomTerm TestIntsSig Fulfill MVar IntS [<("x" :- IntS)]
term0 = Op (Add ** Pack {ty' = ()} [Var (%% "x"), Op (AInt ** Pack {ty' = ()} 2)])

term1 : HomTerm TestIntsSig Fulfill MVar IntS [<("a" :- IntS), ("b" :- IntS)]
term1 = Op (Add ** Pack {ty' = ()} [Var (%% "a"), Var (%% "b")])

test : {ctx : IntSorts .Ctx} -> {s : IntSorts} -> {auto ps : PS ctx} ->
  HomTerm TestIntsSig Fulfill MVar s ctx -> String
test = runSerialiser TestIntsSerialiser
