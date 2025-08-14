module Language.SMT.Core

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
%hide MAST.Core.(.Fam)

data CoreOps = ABool | Not | Implies | And | Or | Xor | Eq | Distinct | Ite

public export
record CoreReq (sort : Type) where
  constructor CoreFulfill
  bool : sort

labelToArity : {0 sys : SortingSystemOver b s sort} ->
  CoreReq sort -> CoreOps -> Arity b sort
labelToArity r ABool    = (Const r.bool Bool)
labelToArity r Not      = [r.bool] :=> r.bool
labelToArity r Implies  = [r.bool, r.bool] :=> (r.bool)
labelToArity r And      = [r.bool, r.bool] :=> (r.bool)
labelToArity r Or       = [r.bool, r.bool] :=> (r.bool)
labelToArity r Xor      = [r.bool, r.bool] :=> (r.bool)
labelToArity r Eq       = CoProd (\a => [a, a] :=> (r.bool))
labelToArity r Distinct = CoProd (\a => [a, a] :=> (r.bool))
labelToArity r Ite      = CoProd (\a => [r.bool, a, a] :=> a)

0
CoreSig : CoreReq .Signature
CoreSig sys r = CoProd (arity . labelToArity {sys} r)

CoreSigMap : (r : CoreReq sys.Sort) -> (CoreSig sys r).RSortedFamilyFunctor
CoreSigMap r = CoProdMap (\x => ArityMap (labelToArity r x))

CoreSigStrength : (r : CoreReq sys.Sort) -> (CoreSig sys r).PointedClosedStrength
CoreSigStrength r = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity r x))

CoreSigBoxLift : (r : CoreReq sys.Sort) -> BoxLift (CoreSig sys r)
CoreSigBoxLift r = PresheafToBoxLift $
  CoProdPsh (\x => ArityPsh (labelToArity {sys} r x))

{-
term0 : HomTerm SingleKind NoSortVar CoreSig (Op TyBool) [<]
term0 = Op (And ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)])

term1 : HomTerm SingleKind NoSortVar CoreSig (Op TyBool) [<]
term1 = Op (Eq ** (Op TyBool ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)]))
-}

{-
substitution : {ty : _ } ->
  (HomTerm SingleKind NoSortVar CoreSig) ty ctx ->
  (HomSorting .fst %| HomTerm SingleKind NoSortVar CoreSig).subst dtx ctx ->
  (HomTerm SingleKind NoSortVar CoreSig) ty dtx
substitution t sub =
  (.subst) {o = CoreSig SelfFullfill HomSorting}
    {synAlg = TermAlgebra}
    {sys = HomSorting}
    (TermInitial (CoreSigMap {sys = HomSorting}))
    (CoreSigMap {sys = HomSorting}) (CoreSigBoxLift {sys = HomSorting})
    (CoreSigStrength {sys = HomSorting}) t dtx sub

term2 : HomTerm SingleKind NoSortVar CoreSig (SelfFullfill .op TyBool) [<("x" :- Op TyBool)]
term2 = Op (And ** Pack {ty' = ()} [Op (ABool ** Pack {ty' = ()} False), Var (%% "x")])

testSub : (HomSorting .fst %| HomTerm SingleKind NoSortVar CoreSig).subst [<] [<("x" :- Op TyBool)]
testSub ((%%) {pos = Here} "x")   = Op (ABool ** Pack {ty' = ()} True)
testSub ((%%) {pos = (There y)} x) impossible

test : HomTerm SingleKind NoSortVar CoreSig (SelfFullfill .op TyBool) [<]
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

term : HomTerm IntSig (SelfFullfill .get TyInt) [<]
term = Op $ Add (Op $ Num 3) (Op $ Num 4)
