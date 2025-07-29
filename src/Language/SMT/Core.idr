module Language.SMT.Core

import Data.DPair

import Language.SMT.Fullfill
import Language.SMT.Signature

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Combinator.List

import MAST.Simple.Core
import MAST.Simple.Combinator.Either
import MAST.Simple.Combinator.List.Quantifiers

%hide Builtin.DPair.DPair.(.fst)
%hide Builtin.DPair.DPair.(.snd)

%hide Data.DPair.Exists.Exists.(.fst)
%hide Data.DPair.Subset.Subset.(.fst)
%hide Data.DPair.Exists.Exists.(.snd)
%hide Data.DPair.Subset.Subset.(.snd)

{-

Signatures structure:

- quantifiers : forall, exists
- binders : let, (lambda?)
* integer arithmetic:
  - linear / non-linear
  -
-}

public export
data TyCore : Type where
  TyBool : TyCore

public export
CoreNeed : Signature
CoreNeed = MkSignature
  { ops = \x => TyCore
  , map = \_ => \case
      TyBool => TyBool
  }

data CoreSig : (CoreNeed .ops) .Signature where
  Eq   : {a : l.Types} ->
         fam a ctx ->
         fam a ctx ->
         CoreSig f sys fam (f.get TyBool) ctx
  And  : fam (f.get TyBool) ctx ->
         fam (f.get TyBool) ctx ->
         CoreSig f sys fam (f.get TyBool) ctx
  ABool : Bool -> CoreSig f sys fam (f.get TyBool) ctx
  
CoreSigMap : (CoreSig .Hom).RSortedFamilyFunctor
CoreSigMap = MkRSortedFamilyFunctor
  { map = \f => \case
         (Eq x y) => Eq (f x) (f y)
         (And x y) => And (f x) (f y)
         (ABool x) => ABool x
  }  

ExtendOne : (s0 : sort) -> ((), b) ====> (sort, b)
ExtendOne s0 = Extend (const s0)

public export
infix 5 .@

0
(.@) : (s0 : sort) -> (sort, b) ====> ((), b)
(.@) s0 x = (const s0) %| x

All : List ((sort,b) ====> (sort',b')) -> (sort,b) ====> (sort',b')
All fs x ty ctx = All (\f => f x ty ctx) fs

0
BoolSig, AndSig : (CoreNeed .ops).Signature
BoolSig f sys = Const (\s => \ctx => Bool)
AndSig  f sys =
  All [ExtendOne (f.get TyBool) . ((f.get TyBool) .@), 
       ExtendOne (f.get TyBool) . ((f.get TyBool) .@)]

BoolSigMap : (BoolSig f sys).RSortedFamilyFunctor
BoolSigMap = MkRSortedFamilyFunctor (\_ => id)

-- AndSigMap : (AndSig f sys).RSortedFamilyFunctor
-- AndSigMap = MkRSortedFamilyFunctor (\f => mapProperty f)
 
data CoreOps = ABool' | And'

0  
CoreSig' : (CoreNeed .ops) .Signature  
CoreSig' f sys = CoProd (\x : CoreOps => case x of
   ABool' => BoolSig f sys
   And'   => AndSig f sys)

0
CoreSigMap' : (CoreSig' f sys).RSortedFamilyFunctor  
CoreSigMap' = CoProdMap ?weijfo_0 -- CoProdMap {a = CoreOps} ?a ?b

term0 : HomTerm CoreSig' (HomFullfill .get TyBool) [<]
term0 = Op (And' ** 
  [Pack {ty' = ()} (Op (ABool' ** False)), 
   Pack {ty' = ()} (Op (ABool' ** False))])

{-
0
CoreIntNeed : Signature
CoreIntNeed = Any [IntNeed, CoreNeed]

0
CoreIntTypes : Type
CoreIntTypes = (CoreIntNeed .ops).Types

0
IntsCore : {sys : SortingSystemOver fstSort sndSort CoreIntTypes} ->
           sys.RSortedFamilyFun
IntsCore = Any [CoreSig (Fullfill $ There . Here) sys,
                IntSig (Fullfill Here) sys]

term : HomTerm IntSig (HomFullfill .get TyInt) [<]
term = Op $ Add (Op $ Num 3) (Op $ Num 4)
