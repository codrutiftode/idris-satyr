module Language.SMT.Serialise

import Language.SMT.Signature
import Language.SMT.Names

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Presheaf
import MAST.Signature
import MAST.Initiality
import Data.String
import Data.List1
import Data.Singleton

import Data.SnocList.Quantifiers

%hide Data.List.sort

-- BEGIN: should move to MAST
ctxToSnoc : sort.Ctx -> SnocList (sort.extension)
ctxToSnoc [<] = [<]
ctxToSnoc (ctx :< ext) = ctxToSnoc ctx :< ext

public export
copair : {dtx : sort.Ctx} -> (Var s ctx -> c) -> (Var s dtx -> c) -> Var s (ctx ++ dtx) -> c
copair {dtx = [<]} f g v = f v
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = Here} x) = g ((%%) x)
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = (There y)} name) =
  copair {dtx} f (g . ThereVar) (y .toVar)

-- NEXT: Should be moved to MAST?
public export
CtxProdFlat : SnocList (sort.Ctx) -> sort.Ctx
CtxProdFlat = foldl (++) [<]
-- END: should move to MAST

||| A sorted family of meta-variables
public export
0
MVar : sort.SortedFamilyOver b
MVar s ctx = (Singleton ctx, Names ctx, String)

public export
SerialiseParam : sort.SortedFamilyOver sort
SerialiseParam = Var

public export
SerialiseParamCoalg : SerialiseParam .SortedBoxCoalgebraStructure
SerialiseParamCoalg v ren = ren v

public export
SerialiseParamPoint : Point SerialiseParam
SerialiseParamPoint = id


-- TODO: refactor into diamondtx and document diamondtx
public export
0
SerialiseTarget : sort.SortedFamilyOver b
SerialiseTarget s ctx =
  (dtx : b.Ctx ** (Names dtx, Names dtx -> String, ctx ~> dtx))

public export
0
SerialiseTargetPsh : SerialiseTarget .SortedPresheafStructure
SerialiseTargetPsh ren (dtx ** (ns, s, ro)) = (dtx ** (ns, s, ren . ro))

-- TODO: do we really need the record; can we use a type def instead?
public export
record (.SerialiseAlgebra) (o : (sort, b) ====> (sort', b')) where
  constructor MkSerialiseAlgebra
  alg : o SerialiseTarget -|> SerialiseTarget

public export
0
(.Serialiser) : (0 sys : SortingSystemOver fstSort sndSort sort) ->
  (syn : sys.RSortedFamily) -> Type
sys.Serialiser syn = syn -|> (SerialiseTarget <-# SerialiseParam)

public export
serialise : (synAlg : Algebra sys o mvar syn) ->
  (fold : FamInitial sys synAlg) ->
  (strength : o.PointedClosedStrength) ->
  RelativeAlgebra sys o mvar SerialiseParamCoalg SerialiseParamPoint SerialiseTarget ->
  sys.Serialiser syn
serialise synAlg fold strength relAlg = fold .traverse
  { synAlg,
    point = SerialiseParamPoint,
    coalg = SerialiseParamCoalg} strength relAlg

public export
serialiseAction : (synAlg : Algebra sys o mvar syn) ->
  (fold : FamInitial sys synAlg) ->
  (strength : o.PointedClosedStrength) ->
  (meta : mvar -|> SerialiseTarget) ->
  (act : TraverseAction sys o SerialiseTarget SerialiseParam) ->
  sys.Serialiser syn
serialiseAction synAlg fold strength meta act =
  fold.traverseAction {synAlg,
    point = SerialiseParamPoint,
    coalg = SerialiseParamCoalg} meta strength act

public export
partial
serialiseTerm :
  {sys : SortingSystemOver fstSort sndSort sort} ->
  (strength : o.PointedClosedStrength) ->
  o.RSortedFamilyFunctor ->
  RelativeAlgebra sys o mvar SerialiseParamCoalg SerialiseParamPoint SerialiseTarget ->
  sys.Serialiser (Term sys o mvar)
serialiseTerm strength oMap relAlg =
  serialise TermAlgebra (TermInitial oMap) strength relAlg

public export
record (.IsMVar)
  (sys : SortingSystemOver b s sort)
  (mvar : sys.RSortedFamily) where
  constructor IsMvar
  info : mvar -|> MVar
  updateNames : {ty : sort} -> {ctx : b.Ctx} ->
                Names ctx -> mvar ty ctx -> mvar ty ctx

public export
MVarValid : sys.IsMVar MVar
MVarValid = IsMvar
  { info = id
  , updateNames = \ns, (params,_,str) => (params,ns,str)
  }

public export
record (.SerialiseWithAction)
  (sys : SortingSystemOver b s sort)
  (o : sys.RSortedFamilyFun)
  (mvar : sys.RSortedFamily) where
  constructor MkSerialiseWithAction
  meta : mvar -|> Strings
  isMVar : sys.IsMVar mvar
  alg : o SerialiseTarget -|> (SerialiseTarget {b,sort})
  oStrength : o.PointedClosedStrength
  oMap : o.RSortedFamilyFunctor

public export
buildMetaMap : sys.IsMVar mvar ->
  (mvar -|> Strings) ->
  mvar -|> SerialiseTarget
buildMetaMap {ctx} isMVar toStr m with (isMVar.info m)
  _ | ((Val ctx), names, x) =
      (ctx ** (names, \ns => toStr {ty} (isMVar.updateNames ns m), id))

public export
serialiseActionTerm :
  {sys : SortingSystemOver fstSort sndSort sort} ->
  (strength : o.PointedClosedStrength) ->
  o.RSortedFamilyFunctor ->
  (mvar -|> SerialiseTarget) ->
  TraverseAction sys o SerialiseTarget SerialiseParam ->
  sys.Serialiser (Term sys o mvar)
serialiseActionTerm strength oMap meta act =
  serialiseAction TermAlgebra (TermInitial oMap) strength meta act

-- TODO: refactor into a general tabulation function.
-- maybe upstream to MAST; maybe upstream a version for SnocLists to Contrib
-- but keep specialised version.
mapVar : (ctx : sort.Ctx) ->
  ({s : sort} -> Var s ctx -> (dtx : sort.Ctx ** p dtx)) ->
  (xs : SnocList (sort.Ctx) ** All p xs)
mapVar [<] f = ([<] ** [<])
mapVar (ctx :< (x :- s)) f =
  let (xs ** all) = mapVar ctx (f . ThereVar)
      (dtx ** pdtx) = f (Here .toVar)
  in (xs :< dtx ** (all :< pdtx))

CtxProd : (ctx : sort.Ctx) ->
  {0 p : sort.Ctx -> Type} ->
  ({s : sort} -> Var s ctx -> (dtx : sort.Ctx ** p dtx)) -> sort.Ctx
CtxProd ctx f = CtxProdFlat $ fst $ mapVar ctx f

0
Target : b.Family
Target ctx = (dtx : b.Ctx ** (String, Names dtx, Names dtx -> String, ctx ~> dtx))

insert : String -> SerialiseTarget s -||> Target
insert str (dtx ** (n,s,r)) = (dtx ** (str,n,s,r))

0
Iterate : (p : sort.Ctx -> Type) -> (0 ctx : sort.Ctx) -> Type
Iterate p ctx =
  (dtx : sort.Ctx) ->
  (f : ({s : sort} -> Var s dtx -> Target ctx)) ->
  p (CtxProd dtx f)

public export
0
ProdFlat : (f : sort.Ctx -> Type) -> (xs : SnocList (sort.Ctx)) -> Type
ProdFlat f xs = All f xs -> f (CtxProdFlat xs)

public export
NamesProdFlat : {xs : SnocList (sort.Ctx)} -> ProdFlat Names xs
NamesProdFlat [<] = Z
NamesProdFlat (x :< y) = concatNames (NamesProdFlat x) y

NamesProd : Iterate Names ctx
NamesProd dtx f =
  NamesProdFlat $ mapProperty (fst . snd) $ snd (mapVar dtx f)

public export
RenProdFlat : {xs : SnocList (sort.Ctx)} -> ProdFlat (ctx ~>) xs
RenProdFlat [<] = LinTerminal
RenProdFlat (x :< ren) = copair (RenProdFlat x) ren

RenProd : Iterate (ctx ~>) ctx
RenProd dtx f =
  RenProdFlat $ mapProperty (snd . snd . snd) $ snd (mapVar dtx f)

letString : String -> String -> String
letString a b = "(let (\{a}) \{b})"

varBinding : String -> String -> String -> String
varBinding others var term = "\{others} (\{var} \{term})"

StringProdFlat : {xs : SnocList (sort.Ctx)} ->
  All (\x => (String, Names x -> String)) xs -> Names (CtxProdFlat xs) -> String
StringProdFlat [<] ns = ""
StringProdFlat (ts :< (varName, t)) ns =
  varBinding (StringProdFlat ts (namesR ns)) varName (t (namesL ns))

public export
StringProdFlat' : {xs : SnocList (sort.Ctx)} ->
  All (\x => Names x -> String) xs -> Names (CtxProdFlat xs) -> SnocList String
StringProdFlat' [<] ns = [<]
StringProdFlat' (ts :< t) ns =
  (StringProdFlat' ts (namesR ns)) :< (t (namesL ns))

StringProd : (dtx : sort.Ctx) ->
  Names dtx ->
  (f : ({s : sort} -> Var s dtx -> Target ctx)) ->
  Names (CtxProd dtx f) -> String
StringProd dtx ndtx f =
  StringProdFlat $ mapProperty (\y => (y.fst, y.snd.snd.fst)) $ snd (mapVar dtx f)

-- TODO: refactor so that we use SerialiseTarget instead of Target,
-- and zip the variable names with their terms when let-binding.
public export
(.SerialiseAction) : (sys : SortingSystemOver b s sort) ->
  SerialiseTarget <#> (SerialiseTarget . sys.fst) -|> SerialiseTarget {b}
sys.SerialiseAction (dtx `Evidence` ((dtx' ** (ndtx', u, ro)), env)) =
  (CtxProd dtx' varToTarget
    ** (NamesProd dtx' varToTarget,
        \ns => letString (StringProd dtx' ndtx' varToTarget ns) (u ndtx'),
        RenProd dtx' varToTarget))
   where
   varToTarget : {s : b} -> Var s dtx' -> Target ctx
   varToTarget v = insert {s} (lookup ndtx' v) (env (ro v))

public export
(.SerialiseVal) : (sys : SortingSystemOver b s sort) ->
  SerialiseParam -|> (SerialiseTarget . sys.fst)
sys.SerialiseVal {ty} v = ([<("_" :- ty)] **
  (S ("_", 0) Z, \ns => mangleSchema (lookupName ns (Here  .toVar)),
    \((%%) {pos = Here} _) => v))

public export
serialiser :
  {sys : SortingSystemOver fstSort sndSort sort} ->
  sys.SerialiseWithAction o mvar ->
  sys.Serialiser (Term sys o mvar)
serialiser (MkSerialiseWithAction meta isMVar alg oStrength oMap) =
  serialiseAction TermAlgebra (TermInitial oMap) oStrength
    (buildMetaMap isMVar meta)
    (MkTraverseAction
    { alg = alg
    , val = sys.SerialiseVal
    , action = sys.SerialiseAction {ty}
    })
