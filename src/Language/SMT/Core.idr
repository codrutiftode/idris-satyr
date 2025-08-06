module Language.SMT.Core

import Language.SMT.Fullfill
import Language.SMT.Signature
import Language.SMT.Arity

import Data.List.Quantifiers

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Modality
import MAST.Presheaf
import MAST.Combinator.List
import MAST.Combinator.Restrict
import MAST.Combinator.Extend
import MAST.Combinator.List.Quantifiers
import MAST.Combinator.CoProd
import MAST.Combinator.Prod
import MAST.Combinator.Const
import MAST.Combinator.Compose
import MAST.Sorted.Core

%hide Builtin.DPair.DPair.(.fst)
%hide Builtin.DPair.DPair.(.snd)
%hide Data.DPair.Exists.Exists.(.fst)
%hide Data.DPair.Subset.Subset.(.fst)
%hide Data.DPair.Exists.Exists.(.snd)
%hide Data.DPair.Subset.Subset.(.snd)

public export
data TyCore : Type where
  TyBool : TyCore

public export
CoreNeed : Signature ()
CoreNeed = MkSignature
  { ops = \x => \_ => TyCore
  , map = \_ => \case
      TyBool => TyBool
  }

data CoreOps = ABool | Not | Implies | And | Or | Xor | Eq | Distinct | Ite

labelToArity : {0 sys : SortingSystemOver b s (l.Types ())} ->
  (f : l |= CoreNeed .ops) -> CoreOps -> Arity b (l.Types ())
labelToArity f ABool    = (Const (f.get TyBool) Bool)
labelToArity f Not      = [f.get TyBool] :=> (f.get TyBool)
labelToArity f Implies  = [f.get TyBool, f.get TyBool] :=> (f.get TyBool)
labelToArity f And      = [f.get TyBool, f.get TyBool] :=> (f.get TyBool)
labelToArity f Or       = [f.get TyBool, f.get TyBool] :=> (f.get TyBool)
labelToArity f Xor      = [f.get TyBool, f.get TyBool] :=> (f.get TyBool)
labelToArity f Eq       = CoProd (\a => [a, a] :=> (f.get TyBool))
labelToArity f Distinct = CoProd (\a => [a, a] :=> (f.get TyBool))
labelToArity f Ite      = CoProd (\a => [f.get TyBool, a, a] :=> a)

0
CoreSig : (CoreNeed .ops) .Signature FiniteUnit
CoreSig f sys = CoProd (arity . labelToArity {f, sys})

CoreSigMap : {f : l |= CoreNeed .ops} -> (CoreSig f sys).RSortedFamilyFunctor
CoreSigMap = CoProdMap (\x => ArityMap (labelToArity f x))

CoreSigStrength : {f : l |= CoreNeed .ops} -> (CoreSig f sys).PointedClosedStrength
CoreSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity f x))

term0 : HomTerm FiniteUnit CoreSig (HomFullfill .get TyBool) [<]
term0 = Op (And ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)])

term1 : HomTerm FiniteUnit CoreSig (HomFullfill .get TyBool) [<]
term1 = Op (Eq ** (Op TyBool ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)]))

CoreSigBoxLift : {f : l |= CoreNeed .ops} -> BoxLift (CoreSig f sys)
CoreSigBoxLift = PresheafToBoxLift $ CoProdPsh (\x => ArityPsh (labelToArity {sys} f x))

substitution : {ty : _ } ->
  (HomTerm FiniteUnit CoreSig) ty ctx ->
  (HomSorting .fst %| HomTerm FiniteUnit CoreSig).subst dtx ctx ->
  (HomTerm FiniteUnit CoreSig) ty dtx
substitution t sub =
  (.subst) {o = CoreSig HomFullfill HomSorting}
    {synAlg = TermAlgebra}
    {sys = HomSorting}
    (TermInitial (CoreSigMap {sys = HomSorting}))
    (CoreSigMap {sys = HomSorting}) (CoreSigBoxLift {sys = HomSorting})
    (CoreSigStrength {sys = HomSorting}) t dtx sub

term2 : HomTerm FiniteUnit CoreSig (HomFullfill .get TyBool) [<("x" :- Op TyBool)]
term2 = Op (And ** Pack {ty' = ()} [Op (ABool ** Pack {ty' = ()} False), Var (%% "x")])

testSub : (HomSorting .fst %| HomTerm FiniteUnit CoreSig).subst [<] [<("x" :- Op TyBool)]
testSub ((%%) {pos = Here} "x")   = Op (ABool ** Pack {ty' = ()} True)
testSub ((%%) {pos = (There y)} x) impossible

test : HomTerm FiniteUnit CoreSig (HomFullfill .get TyBool) [<]
test = substitution term2 testSub

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
