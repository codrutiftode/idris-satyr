module Language.SMT.Core

import Data.DPair

import Language.SMT.Fullfill

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality

import MAST.Simple.Core
import MAST.Simple.Combinator.Either
import MAST.Simple.Combinator.List.Quantifiers

%hide Builtin.DPair.DPair.(.fst)
%hide Builtin.DPair.DPair.(.snd)

%hide Data.DPair.Exists.Exists.(.fst)
%hide Data.DPair.Subset.Subset.(.fst)
%hide Data.DPair.Exists.Exists.(.snd)
%hide Data.DPair.Subset.Subset.(.snd)

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

CoreNeed : Signature
CoreNeed = MkSignature
  { ops = \x => TyCore
  , map = \_ => \case
      TyBool => TyBool
  }
  
0
(.Signature) : (need : SimpleSig) -> Type
need.Signature = 
  {0 l : SimpleSig} -> 
  {0 fstSort, sndSort : Type} ->
  (f : (l |= need)) -> 
  (sys : SortingSystemOver fstSort sndSort l.Types) ->
  sys.RSortedFamilyFun
  
HomSorting : SortingSystemOver a Void a
HomSorting = MkSortingSystemOver
  { fst = id
  , snd = \x impossible
  , copair = \f, _ => f
  }
  
0
(.Hom) : (sig : need.Signature) -> (HomSorting {a = need.Types}) .RSortedFamilyFun
sig.Hom = sig (Fullfill id) HomSorting

HomFullfill : a |= a
HomFullfill = Fullfill {alpha = id}

data CoreSig : (CoreNeed .ops) .Signature where
  Eq   : fam a ctx ->
         fam a ctx ->
         CoreSig f sys fam (f.get TyBool) ctx
  And  : fam (f.get TyBool) ctx ->
         fam (f.get TyBool) ctx ->
         CoreSig f sys fam (f.get TyBool) ctx
  ABool : Bool -> CoreSig f sys fam (f.get TyBool) ctx

-- CoProdFullfill : List ((need : Need ** Fullfill need)) -> 

IntNeed : Signature
IntNeed = MkSignature 
  { ops = \x => TyInts
  , map = \_ => \case
      TyInt => TyInt
  }

-- 0  
-- term : {ctx : ((CoreFullfill IntNeedSig) .Types).Ctx} -> 
--   Term HomoSortingSystem (CoreSig (CoreFullfill IntNeedSig)) 
--   Var ((CoreFullfill IntNeedSig) .get TyBool) ctx
-- term = Op $ And (Op $ ABool True) (Op $ ABool False)

{-

Signatures structure:

- quantifiers : forall, exists
- binders : let, (lambda?)
* integer arithmetic:
  - linear / non-linear
  -
-}

data QuantSig : (CoreNeed .ops) .Signature where
  Forall, 
  Exists : (x : String) ->
           (a : fstSort) ->
           fam (f.get TyBool) (ctx :< (x :- a)) ->
           QuantSig f sys fam (f.get b) ctx

data IntSig : (IntNeed .ops) .Signature where
  Add : fam (f.get TyInt) ctx ->
        fam (f.get TyInt) ctx ->
        IntSig f sys fam (f.get TyInt) ctx
  Let : {a : fstSort} -> (sys.fst %| fam) a ctx -> IntSig f sys fam (f.get TyInt) ctx
  Num : Int -> IntSig f sys fam (f.get TyInt) ctx

0
CoreIntNeed : Signature
CoreIntNeed = Any [IntNeed, CoreNeed]

{-
Plan:
- Combine quantifiers and integers
- Implement functoriality / strength
- Implement multiple signatures
-}

0
HomTerm : (sig : need.Signature) -> (need.Types).SortedFamilyOver (need.Types)
HomTerm sig = Term HomSorting (sig.Hom) Var

term : HomTerm IntSig (HomFullfill .get TyInt) [<]
term = Op $ Add (Op $ Num 3) (Op $ Num 4)

0
IntsCoreTypes : Type
IntsCoreTypes = (CoreIntNeed .ops).Types

-- A sorting system dummy test
IntsCoreSortingSystem : SortingSystemOver 
  ((IntNeed .ops).Types) 
  ((CoreNeed .ops).Types) 
  IntsCoreTypes
IntsCoreSortingSystem = MkSortingSystemOver
  { fst = \case (Op x) => Op $ Here x 
  , snd = \case (Op x) => Op $ (There . Here) x
  , copair = \f, g => \case
       (Op (Here x)) => f (Op x)
       (Op (There (Here x))) => g (Op x)
  }

0
IntsCore : {sys : SortingSystemOver fstSort sndSort IntsCoreTypes} ->
           sys.RSortedFamilyFun
IntsCore = Any [CoreSig (Fullfill $ There . Here) sys,
                IntSig (Fullfill Here) sys]

0
term1 : Term IntsCoreSortingSystem IntsCore
  ?mvarr ((Fullfill $ There . Here) .get TyBool) [<("x" :- (Op $ TyInt))]
term1 = Op $ Here (Eq (Var $ %% "x")
                      (Op $ (There . Here) $ Num 3))
   
0
term2 : Term IntsCoreSortingSystem (IntsCore {sys = IntsCoreSortingSystem})
  ?mvarr2 ((Fullfill $ Here) .get TyInt) [<("x" :- (Op $ TyInt))]
term2 = Op $ (There . Here) $ (Let {a = Op _} (Op $ (There . Here) $ Num 3))

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


