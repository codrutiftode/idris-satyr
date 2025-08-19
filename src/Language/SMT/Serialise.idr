module Language.SMT.Serialise

import Language.SMT.Signature

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST.Initiality
import Data.String
import Data.List1
import Data.Singleton

%hide Data.List.sort

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

-- TODO: should move to MAST
public export
toSubst : (0 p : sort.SortedFamilyOver b) -> p.substNamed ctx dtx -> p.subst ctx dtx
toSubst _ f x = f x.pos

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
  (meta : mvar -|> SerialiseTarget) ->
  TraverseAction sys o SerialiseTarget SerialiseParam ->
  sys.Serialiser (Term sys o mvar)
serialiseActionTerm strength oMap meta act =
  serialiseAction TermAlgebra (TermInitial oMap) strength meta act

public export
SerialiseAction : (sys : SortingSystemOver b s sort) ->
  SerialiseTarget <#> (SerialiseTarget . sys.fst) -|> SerialiseTarget
SerialiseAction sys (fst `Evidence` snd) = ?what2_0

-- serialiseMeta : MVar -|> SerialiseTarget
-- serialiseMeta m names = ?serialiseMetap_rhs

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
