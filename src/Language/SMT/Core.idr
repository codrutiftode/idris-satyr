module Language.SMT.Core

import Data.DPair

import MAST.Core
import MAST.Substitution
import MAST.Signature
import MAST.Initiality

import MAST.Simple.Core
import MAST.Simple.Combinator.Either

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
  , map = \_ => id
  }

0
Fullfill : (r : SimpleSig) -> Type
Fullfill r = (l : SimpleSig ** ({0 x : Type} -> r x -> l x))

(.TypesAlgebra) : (f : Fullfill r) -> f.fst.algebra
f.TypesAlgebra = (f.fst.free Void).algebra

0
(.Types) : (f : Fullfill r) -> Type
f.Types = f.TypesAlgebra.carrier

algebraFunctor : (f : Fullfill r) -> (f.fst.algebraOn a) -> r.algebraOn a
algebraFunctor f lalg = lalg . f.snd

(.get) : (f : Fullfill r) -> r.algebraOn (f.Types)
f.get = algebraFunctor f (f.TypesAlgebra.roll)

data CoreSig : (f : Fullfill CoreNeed) -> 
  f.Types.HomogeneousFamily -> f.Types.HomogeneousFamily where
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

0
CoreFullfill : (other : Signature) -> Fullfill CoreNeed
CoreFullfill other = ((Either CoreNeedSig other).ops ** Left)

IntNeed : SimpleSig
IntNeed x = TyInts

IntNeedSig : Signature
IntNeedSig = MkSignature 
  { ops = IntNeed
  , map = \_ => id
  }

0  
term : {ctx : ((CoreFullfill IntNeedSig) .Types).Ctx} -> 
  Term HomoSortingSystem (CoreSig (CoreFullfill IntNeedSig)) 
  Var ((CoreFullfill IntNeedSig) .get TyBool) ctx
-- term = Op $ And (Op $ ABool True) (Op $ ABool False)

0
IntFullfill : (other : Signature) -> Fullfill IntNeed
IntFullfill other = ((Either other IntNeedSig).ops ** Right)

data IntSig : (f : Fullfill IntNeed) -> 
  f.Types.HomogeneousFamily -> f.Types.HomogeneousFamily where
  Add : fam (f.get TyInt) ctx ->
        fam (f.get TyInt) ctx ->
        IntSig f fam (f.get TyInt) ctx
  Num : Int -> IntSig f fam (f.get TyInt) ctx

0
IntsCoreFun : Type
IntsCoreFun = ((CoreFullfill IntNeedSig).Types).HomogeneousFamily -> 
           ((CoreFullfill IntNeedSig).Types).HomogeneousFamily

0
comboFun : (a : Bool) -> IntsCoreFun
comboFun False = CoreSig (CoreFullfill IntNeedSig)
comboFun True = IntSig (IntFullfill CoreNeedSig)

0
IntsCoreTypes : Type
IntsCoreTypes = (CoreFullfill IntNeedSig).Types

0
IntsCore : IntsCoreFun
IntsCore = CoProd comboFun

0
term1 : {ctx : IntsCoreTypes .Ctx} -> 
  Term HomoSortingSystem IntsCore
  Var ((CoreFullfill IntNeedSig) .get TyBool) ctx
term1 = Op $ (False ** (Eq (Op (True ** Num 3)) (Op (True ** Num 4))))

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


