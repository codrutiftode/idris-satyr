module Language.SMT.Serialise

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST.Initiality
import Data.String
import Data.List1
import Debug.Trace

%hide Data.List.sort

public export
data Strings : sort.SortedFamilyOver b where
  Str : String -> Strings s ctx

public export
(.str) : Strings s ctx -> String
(Str s).str = s

public export
Name : Type
Name = (String, Int)

public export
data Names : sort.Ctx -> Type where
  Z : Names [<]
  S : Name -> Names ctx -> Names (ctx :< (x :- ty))

public export
findNames : String -> Names ctx -> Bool
findNames str Z = False
findNames str (S (s,d) ns) =
  if str == s then True else findNames s ns

public export
lengthNames : Names ctx -> Int
lengthNames Z = 0
lengthNames (S _ psm) = 1 + lengthNames psm

public export
mangleSchema : Name -> String
mangleSchema (s,d) = "\{s}_" ++ cast d

public export
getName : Name -> Name
getName (s, d) = (mangleSchema (s, d), d)

public export
getMax : Names ctx -> Int
getMax Z = 0
getMax (S (x, z) names) =
  let max = getMax names
  in if max > z then max else z

public export
mangle : String -> Names ctx -> Name
mangle str names = case findNames str names of
  False => (str, 0)
  True  => let d = cast (lengthNames names) + getMax names + 1
           in getName (str, d)

public export
hasCollision : Names ctx -> Bool
hasCollision Z = False
hasCollision (S n ns) = case findNames n.fst ns of
  True => True
  False => hasCollision ns

public export
doMangleGlobal : Names ctx -> Names ctx
doMangleGlobal Z = Z
doMangleGlobal (S n ns) = S (getName n) (doMangleGlobal ns)

public export
mangleGlobal : Names ctx -> Names ctx
mangleGlobal Z = Z
mangleGlobal (S n ns) = S (mangle n.fst ns) ns

public export
extractLabel : String -> Maybe Int
extractLabel str = parsePositive (last (split (\x => x == '_') str))

public export
setupLabels : Names ctx -> Names ctx
setupLabels Z = Z
setupLabels (S (str,d) ns) = case extractLabel str of
  Just d' => S (str,d') (setupLabels ns)
  Nothing => S (str,d) (setupLabels ns)

public export
originalNames : PS ctx -> Names ctx
originalNames Z = Z
originalNames (S {str} x) = S (str, 0) (originalNames x)

public export
setupNames : PS ctx -> Names ctx
setupNames = mangleGlobal . originalNames

public export
toSubst : (0 p : sort.SortedFamilyOver b) -> p.substNamed ctx dtx -> p.subst ctx dtx
toSubst _ f x = f x.pos

public export
lookupNamed : (ps : Names ctx) -> Strings .substNamed ctx ctx
lookupNamed (S (str,_) _) Here = Str str
lookupNamed (S _ ps) (There v) = let (Str s) = lookupNamed ps v in Str s

public export
lookup : (ps : Names ctx) -> Strings .subst ctx ctx
lookup ps = toSubst Strings (lookupNamed ps)

public export
Serialised : sort.SortedFamilyOver sort
Serialised s ctx = Var s ctx

public export
SerialisedCoalg : Serialised .SortedBoxCoalgebraStructure
SerialisedCoalg v ren = ren v

public export
SerialisedPoint : Point Serialised
SerialisedPoint = id

public export
Base : sort.SortedFamilyOver b
Base s ctx = Names ctx -> Strings s ctx

public export
0
(.Serialiser) : (0 sys : SortingSystemOver fstSort sndSort sort) -> (syn : sys.RSortedFamily) -> Type
sys.Serialiser syn = syn -|> (Base <-# Serialised)

public export
serialise : (synAlg : Algebra sys o mvar syn) ->
  (fold : FamInitial sys synAlg) ->
  (strength : o.PointedClosedStrength) ->
  RelativeAlgebra sys o mvar SerialisedCoalg SerialisedPoint Base ->
  sys.Serialiser syn
serialise synAlg fold strength relAlg = fold .traverse
  { synAlg = synAlg,
    point = SerialisedPoint,
    coalg = SerialisedCoalg} strength relAlg

public export
serialiseTerm :
  {sys : SortingSystemOver fstSort sndSort sort} ->
  (strength : o.PointedClosedStrength) ->
  o.RSortedFamilyFunctor ->
  RelativeAlgebra sys o mvar SerialisedCoalg SerialisedPoint Base ->
  sys.Serialiser (Term sys o mvar)
serialiseTerm strength oMap relAlg =
  serialise TermAlgebra (TermInitial oMap) strength relAlg
