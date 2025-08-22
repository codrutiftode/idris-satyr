module Language.SMT.Quantifiers

import Debug.Trace
import Data.Singleton

import Language.SMT.Signature
import Language.SMT.Arity
import Language.SMT.Core
import Language.SMT.Serialise
import Language.SMT.SerialiseAlg
import Language.SMT.Names
import Language.SMT.SerialiseArity

import Language.SMT.Combinator.Restrict
import Language.SMT.Combinator.Extend
import Language.SMT.Combinator.Const
import Language.SMT.Combinator.Compose
import Language.SMT.Combinator.CoProd
import Language.SMT.Combinator.List.Quantifiers
import Language.SMT.Combinator.Shift

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Modality
import MAST.Sorted.Core

import Data.List.Quantifiers
import Data.SnocList
import Data.String
%hide Data.List.sort

public export
data QuantOps = Forall | Exists

public export
labelToArity : {0 sys : SortingSystemOver b s sort} ->
  (r : CoreReq sort) ->
  QuantOps -> Arity b sort
labelToArity r _ =
  CoProd (\x =>
  CoProd (\a : b =>
  [([<(x, a)], r.bool), ([<(x, a)], r.bool)] ::=> r.bool))

public export
0
QuantSig : CoreReq .Signature
QuantSig sys r = CoProd (arity . labelToArity {sys} r)

public export
QuantSigMap : (r : CoreReq sys.Sort) -> (QuantSig sys r).RSortedFamilyFunctor
QuantSigMap r = CoProdMap (\x => ArityMap (labelToArity {sys} r x))

public export
QuantSigStrength : (r : CoreReq sys.Sort) -> (QuantSig sys r).PointedClosedStrength
QuantSigStrength r = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} r x))

public export
total
QuantSigSerialiseAlg : (QuantSig sys r) SerialiseTarget -|> SerialiseTarget
QuantSigSerialiseAlg (Forall ** (name ** (ty ** Pack [body1, body2]))) =
  case (body1, body2) of
    ((dtx1 ** (ndtx1, s1, ren1)), (dtx2 ** (ndtx2, s2, ren2))) =>
      ((filterA (label' dtx1 ren1)).context ++ (filterA (label' dtx2 ren2)).context
        ** (concatNames (filterNames ndtx1 (label' dtx1 ren1))
                        (filterNames ndtx2 (label' dtx2 ren2)),
             \ns =>
                let mangled = mangle name ns
                    namesDtx1 = combineNames (namesR ns) (findBoundNames (S mangled Z))
                    namesDtx2 = combineNames (namesL ns) (findBoundNames (S mangled Z))
                in "(forall " ++ mangleSchema mangled
                   ++ ":" ++ s1 namesDtx1 ++ s2 namesDtx2 ++ ")",
             pair (filterA (label' dtx1 ren1)).label
                  (filterA (label' dtx2 ren2)).label))
QuantSigSerialiseAlg (Exists ** (name ** (ty ** Pack [body1, body2]))) =
  case (body1, body2) of
    ((dtx1 ** (ndtx1, s1, ren1)), (dtx2 ** (ndtx2, s2, ren2))) =>
      ((filterA (label' dtx1 ren1)).context ++ (filterA (label' dtx2 ren2)).context
        ** (concatNames (filterNames ndtx1 (label' dtx1 ren1))
                        (filterNames ndtx2 (label' dtx2 ren2)),
             \ns =>
                let mangled = mangle name ns
                    namesDtx1 = combineNames (namesR ns) (findBoundNames (S mangled Z))
                    namesDtx2 = combineNames (namesL ns) (findBoundNames (S mangled Z))
                in "(exists " ++ mangleSchema mangled
                   ++ ":" ++ s1 namesDtx1 ++ s2 namesDtx2 ++ ")",
             pair (filterA (label' dtx1 ren1)).label
                  (filterA (label' dtx2 ren2)).label))

QuantSigMeta : MVar -|> Strings
QuantSigMeta (_, Z, m) = ""
QuantSigMeta (Val (ctx :< (x :- ty)), (S n ns), m) =
  "(+ \{QuantSigMeta {ty} (Val ctx, ns, m)} \{mangleSchema n})"

serialiseQuant : {sys : SortingSystemOver fstSort sndSort sort} ->
  (r : CoreReq sort) -> sys .Serialiser (Term sys (QuantSig sys r) MVar)
serialiseQuant r = serialiser (MkSerialiseWithAction
  { alg = QuantSigSerialiseAlg {sys}
  , meta = QuantSigMeta {ty}
  , isMVar = MVarValid
  , oMap = QuantSigMap {sys} r
  , oStrength = QuantSigStrength {sys} r
  })

Interpolation QuantOps where
  interpolate Forall = "forall"
  interpolate Exists = "exists"

QuantSerialise : QuantOps -> (b -> String) ->
  String -> b -> SnocList String -> String
QuantSerialise op toStr x ty args =
  let argsStr = joinBy " " (cast (args))
  in "(\{op} ((\{x} \{toStr ty})) \{argsStr})"

newSerialiseAlg : {sys : SortingSystemOver b s sort} ->
  (b -> String) ->
  (r : CoreReq sort) -> (QuantSig sys r).SerialiseAlgebra
newSerialiseAlg toStr r = CoProdSerialise (\x => arityAlg {sys} (labelToArity {sys} r x)
  (QuantSerialise x toStr))

newSerialiser : {sys : SortingSystemOver fstSort sndSort sort} ->
  (fstSort -> String) ->
  (r : CoreReq sort) -> sys .Serialiser (Term sys (QuantSig sys r) MVar)
newSerialiser toStr r = serialiser (MkSerialiseWithAction
  { alg = (newSerialiseAlg {sys} toStr r).alg
  , meta = QuantSigMeta {ty}
  , isMVar = MVarValid
  , oMap = QuantSigMap {sys} r
  , oStrength = QuantSigStrength {sys} r
  })

data TheSorts : Type where
  BoolS : TheSorts

Fulfill : CoreReq TheSorts
Fulfill = CoreFulfill BoolS

term0 : HomTerm QuantSig Fulfill MVar BoolS [<("x" :- BoolS)]
term0 = Op (Forall ** ("x" ** (BoolS ** Pack {ty' = ()}
  [Var $ Here .toVar, Var $ (There Here) .toVar])))

term1 : HomTerm QuantSig Fulfill MVar BoolS [<("b" :- BoolS)]
term1 = Op (Forall ** ("y" ** (BoolS ** Pack {ty' = ()}
  [Var $ Here .toVar,
   MVar ([<("y" :- BoolS)] `Evidence`
     ((Val [<("y" :- BoolS)], S ("y", 0) Z, "m"), \case
       ((%%) {pos = Here} _) =>
         Op (Forall ** ("z" ** (BoolS **
           Pack {ty' = ()} [Var ((There Here).toVar), Var (%% "z")]
           )))))])))

term2 : HomTerm QuantSig Fulfill MVar BoolS [<("a" :- BoolS), ("a" :- BoolS), ("a" :- BoolS)]
term2 = Var ((Here) .toVar)

term3 : HomTerm QuantSig Fulfill MVar BoolS [<("x" :- BoolS)]
term3 = Op (Forall ** ("x" ** (BoolS ** Pack {ty' = ()}
  [Var $ Here .toVar, Op (Exists ** ("y" ** (BoolS **
    Pack {ty' = ()} [Var $ Here .toVar, Var $ Here .toVar])))])))

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm QuantSig Fulfill MVar s ctx -> String
test t =
  let (dtx ** (ns, s, ren)) = newSerialiser (\BoolS => "bool") Fulfill t ctx id
      nctx : Names ctx = cast ps
  in s (NamesCovPsh ren (mangleGlobal nctx))

main : IO ()
main = putStrLn (test term0)
