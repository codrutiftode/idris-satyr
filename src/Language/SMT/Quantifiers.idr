module Language.SMT.Quantifiers

import Debug.Trace
import Data.Singleton

import Language.SMT.Signature
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
import Data.SnocList
import Data.String
%hide Data.List.sort

public export
data QuantOps = Forall | Exists

public export
labelToArity : {0 sys : SortingSystemOver b s sort} ->
  (r : CoreReq sort) ->
  QuantOps -> Arity b sort
labelToArity r _ =
  CoProd (\x => CoProd (\a : b => [([<(x, a)], r.bool), ([<(x, a)], r.bool)] ::=> r.bool))

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

second : {b : _} -> c ~> (a ++ b) -> c ~> b
second {b = [<]} f ((%%) {pos = _} name) impossible
second {b = (ctx :< (v :- ty))} f ((%%) {pos = Here} v) = f (Here .toVar)
second {b = (ctx :< (v :- ty))} f ((%%) {pos = (There x)} name) =
  second {b = ctx} (f . ThereVar) (x .toVar)

(.extOf) : (ctx : sort.Ctx) -> Var s ctx -> sort.extension
[<].extOf ((%%) {pos = _} name) impossible
(ctx :< (_ :- ty)).extOf ((%%) {pos = Here} name) = name :- ty
(ctx :< ext).extOf ((%%) {pos = (There x)} name) = ctx.extOf x.toVar

total
copair : {dtx : sort.Ctx} -> (Var s ctx -> c) -> (Var s dtx -> c) -> Var s (ctx ++ dtx) -> c
copair {dtx = [<]} f g v = f v
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = Here} x) = g ((%%) x)
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = (There y)} name) =
  copair {dtx} f (g . ThereVar) (y .toVar)

{-
data Thin : (ctx : sort.Ctx) -> Type where
  Zero : Thin [<]
  Keep : (x : sort.extension) -> Thin ctx -> Thin (ctx :< x)
  Drop : Thin ctx -> Thin (ctx :< x)

thinLeft : {b : sort.Ctx} -> (ctx : sort.Ctx) -> (a ++ b) ~> ctx -> Thin ctx
thinLeft [<] ren = Zero
thinLeft (ctx :< (x :- ty)) ren =
  let rest = thinLeft ctx (ren . ThereVar)
  in copair
      (const $ Keep (x :- ty) rest)
      (const $ Drop rest)
      (ren (Here .toVar))

thinLeft' : {x : sort.extension} -> (ctx : sort.Ctx) -> (a :< x) ~> ctx -> Thin ctx
thinLeft' ctx ren = thinLeft {b = [<x]} ctx ren

thinRight : {b : sort.Ctx} -> (ctx : sort.Ctx) -> (a ++ b) ~> ctx -> Thin ctx
thinRight [<] ren = Zero
thinRight (ctx :< (x :- ty)) ren =
  let rest = thinRight ctx (ren . ThereVar)
  in copair
      (const $ Drop rest)
      (const $ Keep (x :- ty) rest)
      (ren (Here .toVar))

thin : {0 ctx : sort.Ctx} -> Thin ctx -> sort.Ctx
thin Zero = [<]
thin (Keep x t) = (thin t) :< x
thin (Drop t) = thin t

filterLeft : {b : sort.Ctx} -> (ctx : sort.Ctx) -> (a ++ b) ~> ctx -> sort.Ctx
filterLeft ctx ren = thin (thinLeft ctx ren)

filterRight : {b : sort.Ctx} -> (ctx : sort.Ctx) -> (a ++ b) ~> ctx -> sort.Ctx
filterRight ctx ren = thin (thinRight ctx ren)

filterNames : Names ctx -> (t : Thin ctx) -> Names (thin t)
filterNames Z Zero = Z
filterNames (S z ns) (Keep (x :- ty) t) = S z (filterNames ns t)
filterNames (S _ ns) (Drop t) = filterNames ns t
-}

data Thins : (ctx, dtx : sort.Ctx) -> Type where
  Id   : ctx `Thins` ctx
  Keep : ctx `Thins` dtx -> (ctx :< x) `Thins` (dtx :< x)
  Drop : ctx `Thins` dtx -> ctx        `Thins` (dtx :< x)

data Div : (ctx : sort.Ctx) -> (a,b : sort.Ctx) -> Type where
  Lin : Div [<] a b
  Left : (e : sort.extension) -> Var e.ofType a -> Div ctx a b -> Div (ctx :< e) a b
  Right : (e : sort.extension) -> Var e.ofType b -> Div ctx a b-> Div (ctx :< e) a b

record (.Part) (dtx : sort.Ctx) (l : sort.Ctx) where
  constructor MkPart
  context : sort.Ctx
  label : l ~> context
  thin : context `Thins` dtx

-- compl : Div ctx a b -> ctx.Part a -> ctx.Part b ->

label : {b : sort.Ctx} -> (ctx : sort.Ctx) -> (a ++ b) ~> ctx -> Div ctx a b
label [<] ren = [<]
label (ctx :< (x :- ty)) ren =
  let rest = label ctx (ren . ThereVar)
  in copair
    (\v => (Left (x :- ty) v rest))
    (\v => (Right (x :- ty) v rest))
    (ren (Here .toVar))

label' : {x : sort.extension} -> (ctx : sort.Ctx) -> (a :< x) ~> ctx -> Div ctx a [<x]
label' = label {b = [<x]}

renIntoOne : Var (x.ofType) b -> b ~> [<x]
renIntoOne y ((%%) {pos = Here} name) = y
renIntoOne y ((%%) {pos = (There _)} name) impossible

dropLeft : {ctx : sort.Ctx} -> Div ctx a b -> ctx.Part b
dropLeft x = ?dropLeft_rhs
-- dropLeft [<] = ([<] ** \(%% _) impossible)
-- dropLeft (Left e y d) = dropLeft d
-- dropLeft (Right (x :- ty) y d) =
--     let (dtx ** ren) = dropLeft d
--     in (dtx :< (x :- ty) ** pair {rgt = [<(x :- ty)]} ren (renIntoOne y))

dropRight : {ctx : sort.Ctx} -> Div ctx a b -> (dtx : sort.Ctx ** a ~> dtx)
-- dropRight [<] = ([<] ** \(%% _) impossible)
-- dropRight (Left (x :- ty) y d) =
--     let (dtx ** ren) = dropRight d
--     in (dtx :< (x :- ty) ** pair {rgt = [<(x :- ty)]} ren (renIntoOne y))
-- dropRight (Right e y d) = dropRight d

-- filterNew : (ctx : sort.Ctx) ->
--   (a ++ b) ~> ctx ->

filterLeft : {b : sort.Ctx} ->
  (ctx : sort.Ctx) ->
  (a ++ b) ~> ctx ->
  ctx.Part a
-- filterLeft ctx ren = dropRight (label ctx ren)

filterLeft' : {x : sort.extension} ->
  (ctx : sort.Ctx) ->
  (a :< x) ~> ctx ->
  ctx.Part a
filterLeft' ctx ren = filterLeft {b = [<x]} ctx ren

filterRight : {b : sort.Ctx} ->
  (ctx : sort.Ctx) ->
  (a ++ b) ~> ctx ->
  ctx.Part b
-- filterRight ctx ren = dropLeft (label ctx ren)

filterRight' : {x : sort.extension} ->
  (ctx : sort.Ctx) ->
  (a :< x) ~> ctx ->
  ctx.Part [<x]
filterRight' = filterRight

data Compl : a `Thins` c -> b `Thins` c -> Type where
  Zero : Compl Id Id
  KeepLeft : Compl t1 t2 -> Compl (Keep t1) (Drop t2)
  KeepRight : Compl t1 t2 -> Compl (Drop t1) (Keep t2)

-- TODO: should go into MAST?
LinTerminal : ctx ~> [<]
LinTerminal (%% _) impossible

filterA : {ctx : sort.Ctx} ->
  Div ctx a b ->
  ctx.Part a
filterA [<] = MkPart [<] LinTerminal Id
filterA (Left e v d) =
  let pa = filterA d
  in MkPart (pa.context :< e) (pair pa.label (renIntoOne v)) (Keep pa.thin)
filterA (Right e v d) =
  let pa = filterA d
  in MkPart pa.context pa.label (Drop pa.thin)

filterB : {ctx : sort.Ctx} ->
  Div ctx a b ->
  ctx.Part b
filterB [<] = MkPart [<] LinTerminal Id
filterB (Left e v d) =
  let pb = filterB d
  in MkPart pb.context pb.label (Drop pb.thin)
filterB (Right e v d) =
  let pb = filterB d
  in MkPart (pb.context :< e) (pair pb.label (renIntoOne v)) (Keep pb.thin)

-- filter : {ctx : sort.Ctx} ->
--   Div ctx a b ->
--   (ctx.Part a, ctx.Part b)
-- filter [<] = (MkPart [<] LinTerminal Id, MkPart [<] LinTerminal Id)
-- filter (Left e v d) =
--   let (pa, pb) = filter d
--   in (MkPart (pa.context :< e) (pair pa.label (renIntoOne v)) (Keep pa.thin),
--       MkPart pb.context pb.label (Drop pb.thin))
-- filter (Right e v d) =
--   let (pa, pb) = filter d
--   in (MkPart pa.context pa.label (Drop pa.thin),
--       MkPart (pb.context :< e) (pair pb.label (renIntoOne v)) (Keep pb.thin))

filtersCompl : {ctx : sort.Ctx} -> (div : Div ctx a b) ->
  Compl (filterA div).thin (filterB div).thin
filtersCompl [<] = Zero
filtersCompl (Left e v d) = KeepLeft (filtersCompl d)
filtersCompl (Right e v d) = KeepRight (filtersCompl d)


namesFromCompl : {t1 : a `Thins` c} ->
  {t2 : b `Thins` c} ->
  Compl t1 t2 ->
  Names a ->
  Names b ->
  Names c
namesFromCompl Zero na nb = na
namesFromCompl (KeepLeft c) (S a na) nb = S a (namesFromCompl c na nb)
namesFromCompl (KeepRight c) na (S b nb) = S b (namesFromCompl c na nb)

combineNames : {ctx, b : sort.Ctx} ->
  {ren : (a ++ b) ~> ctx} ->
  Names (filterA {a,b} (label ctx ren)).context ->
  Names (filterB {a,b} (label ctx ren)).context ->
  Names ctx
combineNames = namesFromCompl (filtersCompl (label ctx ren))

filterNames : {ctx : sort.Ctx} ->
  Names ctx -> (div : Div ctx a b) -> Names (filterA div).context
filterNames Z [<] = Z
filterNames (S z ns) (Left (x :- ty) v d) = S z (filterNames ns d)
filterNames (S _ ns) (Right (x :- ty) v d) = filterNames ns d

{-

-- fill : (ctx : sort.Ctx) -> Thin ctx ->
-- fill : (t : Thin ctx) -> Fill t -> sort.Ctx

trace : ctx ~> (thin {ctx} t)
trace v = ?trace_rhs_0

-- huh : (t : Thin ctx) -> (trace v)

bar : {ctx : _} -> (ren : (a ++ b) ~> ctx) -> b ~> filterRight {a,b} ctx ren
bar {ctx = [<]} ren ((%%) {pos = _} name) impossible
bar {ctx = (ctx :< (x :- ty))} ren v =
  let shed = trace v in ?bar_rhs_2

-}

printNames : Names ctx -> String
printNames = joinBy " " . cast . map mangleSchema . toSnoc

foo : {ctx, b : sort.Ctx} -> {ren : (a ++ b) ~> ctx} ->
  Names b -> Names (filterB {a,b} (label ctx ren)).context
foo = NamesCovPsh (filterB {a,b} (label ctx ren)).label

public export
total
QuantSigSerialise : (QuantSig sys r) SerialiseTarget -|> SerialiseTarget
QuantSigSerialise (Forall ** (name ** (ty ** Pack [body1, body2]))) =
  case (body1, body2) of
    ((dtx1 ** (ndtx1, s1, ren1)), (dtx2 ** (ndtx2, s2, ren2))) =>
      ((filterA (label' dtx1 ren1)).context ++ (filterA (label' dtx2 ren2)).context
        ** (concatNames (filterNames ndtx1 (label' dtx1 ren1))
                        (filterNames ndtx2 (label' dtx2 ren2)),
             \ns =>
                let mangled = mangle name ns
                    namesDtx1 = combineNames {ren = ren1} (namesR ns) (foo (S mangled Z))
                    namesDtx2 = combineNames (namesL ns) (foo (S mangled Z))
                in "(forall " ++ mangleSchema mangled
                   ++ ":" ++ s1 namesDtx1 ++ s2 namesDtx2 ++ ")",
             pair (filterA (label' dtx1 ren1)).label
                  (filterA (label' dtx2 ren2)).label))
QuantSigSerialise (Exists ** (name ** (ty ** Pack [body1, body2]))) =
  case (body1, body2) of
    ((dtx1 ** (ndtx1, s1, ren1)), (dtx2 ** (ndtx2, s2, ren2))) =>
      ((filterA (label' dtx1 ren1)).context ++ (filterA (label' dtx2 ren2)).context
        ** (concatNames (filterNames ndtx1 (label' dtx1 ren1))
                        (filterNames ndtx2 (label' dtx2 ren2)),
             \ns =>
                let mangled = mangle name ns
                    namesDtx1 = combineNames (namesR ns) (foo (S mangled Z))
                    namesDtx2 = combineNames (namesL ns) (foo (S mangled Z))
                in "(exists " ++ mangleSchema mangled
                   ++ ":" ++ s1 namesDtx1 ++ s2 namesDtx2 ++ ")",
             pair (filterA (label' dtx1 ren1)).label
                  (filterA (label' dtx2 ren2)).label))
-- QuantSigSerialise (Forall ** (name ** (ty ** Pack [body]))) = \names =>
--      let mangled = mangle name names
--      in "(forall "
--          ++ mangleSchema mangled
--          ++ " "
--          ++ body (S mangled names)
--          ++ ")"
-- QuantSigSerialise (Exists ** (name ** (ty ** Pack [body]))) = \names =>
--      let mangled = mangle name names
--      in "(exists "
--          ++ mangleSchema mangled
--          ++ " "
--          ++ body (S mangled names)
--          ++ ")"

QuantSigMeta : (sys : SortingSystemOver a b sort) ->
  {s : sort} -> {0 ctx : b.Ctx} ->
  MVar s ctx -> SerialiseTarget s ctx

QuantSigVal : (sys : SortingSystemOver b s sort) ->
  SerialiseParam -|> (SerialiseTarget . sys.fst)
QuantSigVal sys {ty} v = ([<("_" :- ty)] **
  (S ("_", 0) Z, \ns => mangleSchema (lookupName ns (Here  .toVar)),
    \((%%) {pos = Here} _) => v))

serialiseQuant : (r : CoreReq sort) -> (HomSorting sort) .Serialiser (HomTerm QuantSig r)
serialiseQuant r = serialiseActionTerm {sys = HomSorting sort}
  (QuantSigStrength {r, sys = HomSorting sort})
  (QuantSigMap {r, sys = HomSorting sort})
  ?metaTODO
  (MkTraverseAction
    { alg = QuantSigSerialise
    , val = QuantSigVal (HomSorting sort)
    , action = SerialiseAction (HomSorting sort)
    }
  )

-- serialiseQuant r = ?hmm (QuantSigSerialise {sys = HomSorting sort})
--   (QuantSigStrength {r, sys = HomSorting sort})
--   (QuantSigMap {r, sys = HomSorting sort})

data TheSorts : Type where
  BoolS : TheSorts

Fulfill : CoreReq TheSorts
Fulfill = CoreFulfill BoolS

term0 : HomTerm QuantSig Fulfill BoolS [<("x" :- BoolS)]
term0 = Op (Forall ** ("x" ** (BoolS ** Pack {ty' = ()}
  [Var $ Here .toVar, Var $ (There Here) .toVar])))

{-
term1 : HomTerm QuantSig Fulfill BoolS [<("x" :- BoolS)]
term1 = Op (Forall ** ("x" **
  (BoolS ** Pack {ty' = ()} [
    Op (Exists ** ("x" ** (BoolS ** Pack {ty' = ()} [Var (Here .toVar)])))
  ])))
-}

term2 : HomTerm QuantSig Fulfill BoolS [<("a" :- BoolS), ("a" :- BoolS), ("a" :- BoolS)]
term2 = Var ((Here) .toVar)

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm QuantSig Fulfill s ctx -> String
test t =
  let (dtx ** (ns, s, ren)) = serialiseQuant Fulfill t ctx id
      nctx : Names ctx = cast ps
  in s (NamesCovPsh ren (mangleGlobal nctx))

test2 : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm QuantSig Fulfill s ctx -> SnocList String
test2 t =
  let (dtx ** (ns, s, ren)) = serialiseQuant Fulfill t ctx id
      nctx : Names ctx = cast ps
      names = map mangleSchema (toSnoc (NamesCovPsh ren (mangleGlobal nctx)))
  in names

main : IO ()
main = putStrLn (test term0)
