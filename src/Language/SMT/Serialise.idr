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

%hide Data.List.sort

public export
Name : Type
Name = (String, Int)

public export
data Names : sort.Ctx -> Type where
  Z : Names [<]
  S : Name -> Names ctx -> Names (ctx :< (x :- ty))

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
