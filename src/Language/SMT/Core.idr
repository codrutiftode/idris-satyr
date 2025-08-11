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
%hide MAST.Core.(.Fam)

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

labelToArity : {0 sys : SortingSystemOver b s (SingleKind $ l.Types vars)} ->
  (f : l |= CoreNeed .ops) ->
  CoreOps -> Arity b (l.Types vars ())
labelToArity f ABool    = (Const (f.op TyBool) Bool)
labelToArity f Not      = [f.op TyBool] :=> (f.op TyBool)
labelToArity f Implies  = [f.op TyBool, f.op TyBool] :=> (f.op TyBool)
labelToArity f And      = [f.op TyBool, f.op TyBool] :=> (f.op TyBool)
labelToArity f Or       = [f.op TyBool, f.op TyBool] :=> (f.op TyBool)
labelToArity f Xor      = [f.op TyBool, f.op TyBool] :=> (f.op TyBool)
labelToArity f Eq       = CoProd (\a => [a, a] :=> (f.op TyBool))
labelToArity f Distinct = CoProd (\a => [a, a] :=> (f.op TyBool))
labelToArity f Ite      = CoProd (\a => [f.op TyBool, a, a] :=> a)

0
CoreSig : (CoreNeed .ops) .Signature SingleKind vars
CoreSig f sys = CoProd (arity . labelToArity {f, sys})

CoreSigMap : {f : l |= CoreNeed .ops} -> (CoreSig f sys).RSortedFamilyFunctor
CoreSigMap = CoProdMap (\x => ArityMap (labelToArity f x))

CoreSigStrength : {f : l |= CoreNeed .ops} -> (CoreSig f sys).PointedClosedStrength
CoreSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity f x))

term0 : HomTerm SingleKind NoSortVar CoreSig (Op TyBool) [<]
term0 = Op (And ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)])

term1 : HomTerm SingleKind NoSortVar CoreSig (Op TyBool) [<]
term1 = Op (Eq ** (Op TyBool ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)]))

CoreSigBoxLift : {f : l |= CoreNeed .ops} -> BoxLift (CoreSig f sys)
CoreSigBoxLift = PresheafToBoxLift $ CoProdPsh (\x => ArityPsh (labelToArity {sys} f x))

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
