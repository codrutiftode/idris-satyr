module Language.SMT.Serialise

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Signature
import MAST.Initiality

public export
data Strings : sort.SortedFamilyOver b where
  Str : String -> Strings s ctx

data PSM : sort.Ctx -> Type where
  Z : PSM [<]
  S : (mangled : String) -> PSM ctx -> PSM (ctx :< (x :- ty))

public export
toSubst : (0 p : sort.SortedFamilyOver b) -> p.substNamed ctx dtx -> p.subst ctx dtx
toSubst _ f x = f x.pos

public export
lookupNamed : (ps : PS ctx) -> Strings .substNamed ctx ctx
lookupNamed (S {str} _) Here = Str str
lookupNamed (S ps) (There v) = let (Str s) = lookupNamed ps v in Str s

public export
lookup : (ps : PS ctx) -> Strings .subst ctx ctx
lookup ps = toSubst Strings (lookupNamed ps)

public export
Serialised : sort.SortedFamilyOver sort
Serialised s ctx = (Var s ctx, PS ctx -> Strings s ctx)

public export
SerialisedCoalg : Serialised .SortedBoxCoalgebraStructure
SerialisedCoalg (v, n) ren = (ren v, \ps => lookup ps (ren v))

public export
SerialisedPoint : Point Serialised
SerialisedPoint v = (v, \ps => lookup ps v)

public export
Base : sort.SortedFamilyOver b
Base s ctx = PS ctx -> Strings s ctx

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
