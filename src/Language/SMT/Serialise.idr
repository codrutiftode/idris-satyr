module Language.SMT.Serialise

import Language.SMT.Signature

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
public export
toSubst : (0 p : sort.SortedFamilyOver b) -> p.substNamed ctx dtx -> p.subst ctx dtx
toSubst _ f x = f x.pos

ctxToSnoc : sort.Ctx -> SnocList (sort.extension)
ctxToSnoc [<] = [<]
ctxToSnoc (ctx :< ext) = ctxToSnoc ctx :< ext

public export
copair : {dtx : sort.Ctx} -> (Var s ctx -> c) -> (Var s dtx -> c) -> Var s (ctx ++ dtx) -> c
copair {dtx = [<]} f g v = f v
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = Here} x) = g ((%%) x)
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = (There y)} name) =
  copair {dtx} f (g . ThereVar) (y .toVar)

public export
LinTerminal : ctx ~> [<]
LinTerminal (%% _) impossible
-- END: should move to MAST

public export
Name : Type
Name = (String, Int)

public export
data Names : sort.Ctx -> Type where
  Z : Names [<]
  S : Name -> Names ctx -> Names (ctx :< (x :- ty))

public export
toSnoc : Names ctx -> SnocList Name
toSnoc Z = [<]
toSnoc (S n ns) = toSnoc ns :< n

public export
concatNames : {b : _} -> Names a -> Names b -> Names (a ++ b)
concatNames {b = [<]} x Z = x
concatNames {b = (ctx :< (v :- s))} x (S d ns) = S d (concatNames x ns)

public export
findLast : String -> Names ctx -> Maybe Name
findLast str Z = Nothing
findLast str (S n ns) =
  if str == n.fst then Just n else findLast str ns

public export
mangleSchema : Name -> String
mangleSchema (s,d) = "\{s}." ++ if d == 0 then "" else cast d

public export
mangle : String -> Names ctx -> Name
mangle str names = case findLast str names of
  Nothing => (str, 0)
  Just n  => (str, n.snd + 1)

public export
mangleGlobal : Names ctx -> Names ctx
mangleGlobal Z = Z
mangleGlobal (S n ns) = let mangled = mangleGlobal ns
                        in S (mangle n.fst mangled) mangled

public export
Cast (PS ctx) (Names ctx) where
  cast Z = Z
  cast (S {str} x) = S (str, 0) (cast x)

public export
setupNames : PS ctx -> Names ctx
setupNames = mangleGlobal . cast

public export
lookupNamed : (ps : Names ctx) -> Strings .substNamed ctx ctx
lookupNamed (S n _) Here = (mangleSchema n)
lookupNamed (S _ ps) (There v) = lookupNamed ps v

public export
lookup : (ps : Names ctx) -> Strings .subst ctx ctx
lookup ps = toSubst {ctx} Strings (lookupNamed ps)

public export
lookupNameNamed : (ps : Names ctx) -> (const $ const Name) .substNamed ctx ctx
lookupNameNamed (S n _) Here = n
lookupNameNamed (S _ ps) (There v) = lookupNameNamed ps v

public export
lookupName : (ps : Names ctx) -> (const $ const Name) .subst ctx ctx
lookupName ps = toSubst {ctx} (const $ const Name) (lookupNameNamed ps)

public export
NamesCovPsh : {b : _} -> a ~> b -> Names a -> Names b
NamesCovPsh {b = [<]} f x = Z
NamesCovPsh {b = (ctx :< (v :- ty))} f x =
  S (lookupName x (f (Here .toVar))) (NamesCovPsh (\v' => f (ThereVar v')) x)

public export
namesR : {a, b : _} -> Names (a ++ b) -> Names a
namesR x = NamesCovPsh (weakr _ _) x

public export
namesL : {a, b : _} -> Names (a ++ b) -> Names b
namesL x = NamesCovPsh (weakl _ _) x

public export
SerialiseParam : sort.SortedFamilyOver sort
SerialiseParam s ctx = Var s ctx

public export
SerialiseParamCoalg : SerialiseParam .SortedBoxCoalgebraStructure
SerialiseParamCoalg v ren = ren v

public export
SerialiseParamPoint : Point SerialiseParam
SerialiseParamPoint = id

public export
0
SerialiseTarget : sort.SortedFamilyOver b
SerialiseTarget s ctx =
  (dtx : b.Ctx ** (Names dtx, Names dtx -> String, ctx ~> dtx))

public export
SerialiseTargetPsh : SerialiseTarget .SortedPresheafStructure
SerialiseTargetPsh ren (dtx ** (ns, s, ro)) = (dtx ** (ns, s, ren . ro))

public export
0
(.Serialiser) : (0 sys : SortingSystemOver fstSort sndSort sort) -> (syn : sys.RSortedFamily) -> Type
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
serialiseTerm :
  {sys : SortingSystemOver fstSort sndSort sort} ->
  (strength : o.PointedClosedStrength) ->
  o.RSortedFamilyFunctor ->
  RelativeAlgebra sys o mvar SerialiseParamCoalg SerialiseParamPoint SerialiseTarget ->
  sys.Serialiser (Term sys o mvar)
serialiseTerm strength oMap relAlg =
  serialise TermAlgebra (TermInitial oMap) strength relAlg

-- (-|>-) : {sys : SortingSystemOver fstSort sndSort sort} ->
--          sys.RSortedFamily -> sys.RSortedFamily -> Type
-- a -|>- b = ?wh

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

-- TODO: should be moved to MAST
public export
CtxProd : SnocList (sort.Ctx) -> sort.Ctx
CtxProd = foldl (++) [<]

mapVar : (ctx : sort.Ctx) -> ({s : sort} -> Var s ctx -> a) -> SnocList a
mapVar [<] f = [<]
mapVar (ctx :< (x :- s)) f = (mapVar ctx (f . ThereVar)) :< f (Here .toVar)

NamesProd : {xs : SnocList (sort.Ctx)} -> All Names xs -> Names (CtxProd xs)
NamesProd [<] = Z
NamesProd (x :< y) = concatNames (NamesProd x) y

RenProd : {xs : SnocList (sort.Ctx)} -> All (ctx ~>) xs -> ctx ~> (CtxProd xs)
RenProd [<] = LinTerminal
RenProd (x :< ren) = copair (RenProd x) ren

NamesLeft : {a, b : sort.Ctx} -> Names (a ++ b) -> Names a
NamesLeft = NamesCovPsh (weakr a b)

NamesRight : {a, b : sort.Ctx} -> Names (a ++ b) -> Names b
NamesRight = NamesCovPsh (weakl a b)

mapVar' : (ctx : sort.Ctx) ->
  ({s : sort} -> Var s ctx -> (dtx : sort.Ctx ** p dtx)) ->
  (xs : SnocList (sort.Ctx) ** All p xs)
mapVar' [<] f = ([<] ** [<])
mapVar' (ctx :< (x :- s)) f =
  let (xs ** all) = mapVar' ctx (f . ThereVar)
      (dtx ** pdtx) = f (Here .toVar)
  in (xs :< dtx ** (all :< pdtx))

CtxProd' : (ctx : sort.Ctx) ->
  {0 p : sort.Ctx -> Type} ->
  ({s : sort} -> Var s ctx -> (dtx : sort.Ctx ** p dtx)) -> sort.Ctx
CtxProd' ctx f = CtxProd $ fst $ mapVar' ctx f

CtxProd0 : (ctx : sort.Ctx) ->
  {0 p : sort.Ctx -> Type} ->
  ({s : sort} -> Var s ctx -> sort.Ctx) -> sort.Ctx
CtxProd0 ctx f = CtxProd $ mapVar ctx f

CtxProd'' : (ctx : sort.Ctx) ->
  ({s : sort} -> Var s ctx -> sort.Ctx) -> sort.Ctx
CtxProd'' ctx f = CtxProd' {p = Singleton} ctx (\y => (f y ** Val (f y)))

NamesProd' : (ctx : sort.Ctx) ->
  (f : ({s : sort} -> Var s ctx -> (dtx : sort.Ctx ** Names dtx))) ->
  Names (CtxProd' ctx f)
NamesProd' ctx f = NamesProd $ snd $ (mapVar' ctx f)

Drop1 : SerialiseTarget {b = sort} s ctx -> sort.Ctx
Drop1 (dtx ** (ns, rest)) = dtx

0
Target : b.Family
Target ctx = (dtx : b.Ctx ** (String, Names dtx, Names dtx -> String, ctx ~> dtx))

insert : String -> SerialiseTarget s -||> Target
insert str (dtx ** (n,s,r)) = (dtx ** (str,n,s,r))

NamesProd'' : (0 ctx : sort.Ctx) ->
  (dtx : sort.Ctx) ->
  (f : ({s : sort} -> Var s dtx -> Target ctx)) ->
  Names (CtxProd' dtx f)
NamesProd'' ctx dtx f =
  NamesProd $ mapProperty (fst . snd) $ snd (mapVar' dtx f)

RenProd' : (0 ctx : sort.Ctx) ->
  (dtx : sort.Ctx) ->
  (f : ({s : sort} -> Var s dtx -> Target ctx)) ->
  ctx ~> (CtxProd' dtx f)
RenProd' ctx dtx f =
  RenProd $ mapProperty (snd . snd . snd) $ snd (mapVar' dtx f)

StringProd : {xs : SnocList (sort.Ctx)} -> All (\x => (String, Names x -> String)) xs -> Names (CtxProd xs) -> String
StringProd [<] ns = ""
StringProd (ts :< (varName, t)) ns =
  "\{StringProd ts (NamesLeft ns)} (\{varName} \{t (NamesRight ns)})"

StringProd' : (dtx : sort.Ctx) ->
  Names dtx ->
  (f : ({s : sort} -> Var s dtx -> Target ctx)) ->
  Names (CtxProd' dtx f) -> String
StringProd' dtx ndtx f =
  StringProd $ mapProperty (\y => (y.fst, y.snd.snd.fst)) $ snd (mapVar' dtx f)

public export
SerialiseAction : (sys : SortingSystemOver b s sort) ->
  SerialiseTarget <#> (SerialiseTarget . sys.fst) -|> SerialiseTarget {b}
SerialiseAction sys (dtx `Evidence` ((dtx' ** (ndtx', u, ro)), env)) =
  (CtxProd' dtx' shed
    ** (NamesProd'' ctx dtx' shed,
        \ns => "(let ("
               ++ StringProd' dtx' ndtx'
                  shed ns
               ++ ") \{u ndtx'})",
        RenProd' ctx dtx' shed))
   where
   shed : {s : b} -> Var s dtx' -> Target ctx
   shed v = insert {s} (lookup ndtx' v) (env (ro v))

||| A sorted family of meta-variables
public export
0
MVar : sort.SortedFamilyOver b
MVar s ctx = (theCtx : Singleton ctx ** (Names ctx, String))

public export
serialiseMeta : ({0 ctx : b.Ctx} -> String -> Names ctx -> String) ->
  MVar {b} -|> SerialiseTarget {b}
serialiseMeta toStr (Val ctx ** (names, m)) =
             (ctx ** (names, toStr m, id))

-- TODO: refactor the names of serialising functions
{-
public export
serialiser : {sys : SortingSystemOver fstSort sndSort sort} ->
  (alg : o SerialiseTarget -|> SerialiseTarget) ->
  (strength : o.PointedClosedStrength) ->
  o.RSortedFamilyFunctor ->
  sys.Serialiser (Term sys o MVar)
serialiser alg strength oMap =
  serialise TermAlgebra (TermInitial oMap) strength (makeRelativeAlgebra alg)
