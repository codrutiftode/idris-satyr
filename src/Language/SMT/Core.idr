module Language.SMT.Core

import Data.DPair
import Data.List1
import Data.List
import Data.Nat

import Language.SMT.Fullfill
import Language.SMT.Signature
import Language.SMT.Arity

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Combinator.List

import MAST.Simple.Core
import MAST.Simple.Combinator.Either
import MAST.Simple.Combinator.List.Quantifiers

%hide Data.List.sort
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

data CoreOps = ABool | Not | Implies | And | Or | Xor | Eq | Distinct | Ite

labelToArity : (f : l |= CoreNeed .ops) -> CoreOps -> Arity (l.Types)
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
CoreSig : (CoreNeed .ops) .Signature
CoreSig f sys = CoProd (arity . labelToArity {f})

CoreSigMap : {f : l |= CoreNeed .ops} -> (CoreSig f sys).RSortedFamilyFunctor
CoreSigMap = CoProdMap (\x => ArityMap (labelToArity f x))

CoreSigStrength : {f : l |= CoreNeed .ops} -> (CoreSig f sys).ClosedStrength
CoreSigStrength = CoProdClosedStrength (\x => ArityStrength (labelToArity f x))

term0 : HomTerm CoreSig (HomFullfill .get TyBool) [<]
term0 = Op (And ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)])

term1 : HomTerm CoreSig (HomFullfill .get TyBool) [<]
term1 = Op (Eq ** (Op TyBool ** Pack {ty' = ()}
  [Op (ABool ** Pack {ty' = ()} False), Op (ABool ** Pack {ty' = ()} False)]))

data Strings : sorts.SortedFamilyOver bind where
  Str : String -> Strings s ctx

{-
term1 : IO ()
term1 = let map = (CoreSigMap {f = HomFullfill, sys = HomSorting}).map
            func : Strings -|> Strings = \case (Str v) => Str (v ++ "!")
            shed2 = map {p = Strings, q = Strings}
                    func (Eq ** (Op TyBool ** Pack {ty' = ()} [Str {s = Op TyBool, ctx = [<]} "one", Str {ctx = [<]} "two"]))
            in case shed2 of (ABool ** t) => putStrLn "fail"
                             (Not ** t)   => putStrLn "fail"
                             (And ** t) => putStrLn "fail"
                             (Eq ** (i ** Pack [Str x, Str y])) => putStrLn x >> putStrLn y
                             (Or ** t) => putStrLn "fail"
                             (Xor ** t) => putStrLn "fail"
                             (Implies ** t) => putStrLn "fail"
                             (Distinct ** t) => putStrLn "fail"
                             (Ite ** t) => putStrLn "fail"

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
