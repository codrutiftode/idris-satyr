module Language.SMT.Core

import Data.DPair

import MAST.Core
import MAST.Substitution
import MAST.Signature
import MAST.Initiality

import MAST.Simple.Core
import MAST.Simple.Combinator.Either
import MAST.Simple.Combinator.List.Quantifiers

data TyCore : Type where
  TyBool : TyCore
  
data TyInts : Type where
  TyInt : TyInts
  
-- data LetSig : (sort,b) ====> (sort,b) where
--   Let : {a, b : sort} -> 
--         (x : String) ->
--         fam a ctx ->
--         fam b (ctx :< (x :- a)) ->
--         BindersSig fam b ctx

-- coreSortingSystem : SortingSystemOver TyInts TyCore (Either TyInts TyCore)
-- coreSortingSystem = EitherSortingSystem

-- data QuantSig : (sort,bnd) ====> (sort,bnd) where
--   Forall,
--   Exists : (x : String) ->
--            (s : sort) ->
--            fam TyBool (ctx :< (x :- s)) ->
--            QuantSig fam TyBool ctx          

CoreNeed : SimpleSig
CoreNeed x = TyCore

CoreNeedSig : Signature
CoreNeedSig = MkSignature
  { ops = CoreNeed
  , map = \_ => \case
      TyBool => TyBool
  }

public export
infixr 4 |=

record (|=) (l, r : SimpleSig) where
  constructor Fullfill
  alpha : {0 x : Type} -> r x -> l x

(.TypesAlgebra) : (o : SimpleSig) -> o.algebra
o.TypesAlgebra = (o.free Void).algebra

0
(.Types) : (o : SimpleSig) -> Type
o.Types = o.TypesAlgebra.carrier

algebraFunctor : (l |= r) -> l.algebraOn a -> r.algebraOn a
algebraFunctor f lalg = lalg . f.alpha

(.get) : {l : SimpleSig} -> (l |= r) -> r.algebraOn (l.Types)
f.get = algebraFunctor f (l.TypesAlgebra.roll)

data CoreSig : (f : (l |= CoreNeed)) -> 
  l.Types.HomogeneousFamily -> l.Types.HomogeneousFamily where
  Eq   : fam a ctx ->
         fam a ctx ->
         CoreSig f fam (f.get TyBool) ctx
  ABool : Bool -> CoreSig f fam (f.get TyBool) ctx

HomoSortingSystem : SortingSystemOver a a a
HomoSortingSystem = MkSortingSystemOver
  { fst = id
  , snd = id
  , copair = \f,_,z => f z  
  }

-- CoProdFullfill : List ((need : Need ** Fullfill need)) -> 

IntNeed : SimpleSig
IntNeed x = TyInts

IntNeedSig : Signature
IntNeedSig = MkSignature 
  { ops = IntNeed
  , map = \_ => \case
      TyInt => TyInt
  }

-- 0  
-- term : {ctx : ((CoreFullfill IntNeedSig) .Types).Ctx} -> 
--   Term HomoSortingSystem (CoreSig (CoreFullfill IntNeedSig)) 
--   Var ((CoreFullfill IntNeedSig) .get TyBool) ctx
-- term = Op $ And (Op $ ABool True) (Op $ ABool False)


data IntSig : (f : (l |= IntNeed)) -> 
  l.Types.HomogeneousFamily -> l.Types.HomogeneousFamily where
  Add : fam (f.get TyInt) ctx ->
        fam (f.get TyInt) ctx ->
        IntSig f fam (f.get TyInt) ctx
  Num : Int -> IntSig f fam (f.get TyInt) ctx

0
IntsCoreTypesSig : SimpleSig
IntsCoreTypesSig = (Any [IntNeedSig, CoreNeedSig]).ops

0
IntsCoreTypes : Type
IntsCoreTypes = IntsCoreTypesSig .Types

0
IntsCoreFun : Type
IntsCoreFun = IntsCoreTypes .HomogeneousFamily -> 
              IntsCoreTypes .HomogeneousFamily

-- TODO: move to mast combinators
-- namespace Any
Any : List ((sort,bind) ====> (sort,bind)) -> (sort,bind) ====> (sort,bind)
Any fs x ty ctx = Any (\f => f x ty ctx) fs

0
IntsCore : IntsCoreFun
IntsCore = Any [CoreSig (Fullfill $ There . Here),
                IntSig (Fullfill Here)]

0
term1 : {ctx : IntsCoreTypes .Ctx} ->
  Term HomoSortingSystem IntsCore
  Var ((Fullfill $ There . Here) .get TyBool) ctx
term1 = Op $ Here (Eq (Op $ (There . Here) $ Num 3) 
                      (Op $ (There . Here) $ Num 4))

-- CoreSig : sort.HomogeneousFamily -> sort.HomogeneousFamily
-- CoreSig fam s ctx = (i : Int ** case i of
--   0 => (fam s ctx, fam s ctx)
--   _ => ?left)

  -- Not      : fam TyBool ctx -> CoreSig fam TyBool ctx

  -- (==>), (&&), 
  -- (||), Xor : fam TyBool ctx -> 
  --             fam TyBool ctx ->
  --             CoreSig fam TyBool ctx 

  -- (==), (!=) : fam a ctx ->
  --              fam a ctx ->
  --              CoreSig fam TyBool ctx

  -- Ite : fam TyBool ctx -> fam a ctx -> 
  --       fam a ctx -> CoreSig fam a ctx


