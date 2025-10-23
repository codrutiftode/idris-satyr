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
  [([<(x, a)], r.bool)] ::=> r.bool))

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

{-
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
-}



{-
serialiseQuant : {sys : SortingSystemOver fstSort sndSort sort} ->
  (r : CoreReq sort) -> sys .Serialiser (Term sys (QuantSig sys r) MVar)
serialiseQuant r = serialiser (MkSerialiseWithAction
  { alg = QuantSigSerialiseAlg {sys}
  , meta = QuantSigMeta {ty}
  , isMVar = MVarValid
  , oMap = QuantSigMap {sys} r
  , oStrength = QuantSigStrength {sys} r
  })
-}

Interpolation QuantOps where
  interpolate Forall = "forall"
  interpolate Exists = "exists"

QuantSerialise : QuantOps -> SnocList String -> String
QuantSerialise op args = "(\{op} \{joinBy " " (cast (args))})"

-- QuantSerialise' : QuantOps -> (b -> String) ->
--   (x : String) -> (a : b) ->
--   (SnocList String -> String,
--    All (const $ (dtx : b .Ctx) -> Names dtx -> String -> String) [([<(x, a)], r.bool),
--                                                                  ([<(x, a)], r.bool)])

newSerialiseAlg : {sys : SortingSystemOver b s sort} ->
  (b -> String) ->
  (r : CoreReq sort) -> (QuantSig sys r).SerialiseAlgebra
newSerialiseAlg toStr r = CoProdSerialise (\op =>
  AritySerialise {sys} (labelToArity {sys} r op)
    (\x, s =>
      (QuantSerialise op,
      [\dtx, (S n Z), body => "((\{mangleSchema n} \{toStr s})) \{body}"])))

menv : MVar -|> Strings
menv  (_, Z, m) = ""
menv  (Val (ctx :< (x :- ty)), (S n ns), m) =
  "(+ \{menv {ty} (Val ctx, ns, m)} \{mangleSchema n})"

public export
QuantSigMeta : sys.MetaSerialise MVar
QuantSigMeta = MkMetaSerialise
  { meta = ?aMenv -- TODO: connect this to menv above
  , isMVar = MVarValid
  }

public export
QuantSigSerialiseAction : {sys, r : _} -> sys.SortSerialiser ->
  sys.SerialiseWithAction (QuantSig sys r) MVar
QuantSigSerialiseAction toStr = (MkSerialiseWithAction
  { alg = newSerialiseAlg {sys} toStr r
  , meta = QuantSigMeta
  , oMap = QuantSigMap {sys} r
  , oStrength = QuantSigStrength {sys} r
  })

QuantSigSerialiser : {sys : SortingSystemOver fstSort sndSort sort} ->
  sys.SortSerialiser ->
  (r : CoreReq sort) -> sys .Serialiser (Term sys (QuantSig sys r) MVar)
QuantSigSerialiser toStr r = serialiser (QuantSigSerialiseAction toStr)

data TheSorts : Type where
  BoolS : TheSorts

Fulfill : CoreReq TheSorts
Fulfill = CoreFulfill BoolS

term0 : HomTerm QuantSig Fulfill MVar BoolS [<("x" :- BoolS)]
term0 = Op (Forall ** ("x" ** (BoolS ** Pack {ty' = ()}
  [Var $ Here .toVar])))

term1 : HomTerm QuantSig Fulfill MVar BoolS [<("b" :- BoolS)]
term1 = Op (Forall ** ("y" ** (BoolS ** Pack {ty' = ()}
  [MVar ([<("y" :- BoolS)] `Evidence`
     ((Val [<("y" :- BoolS)], S ("y", 0) Z, "m"), \case
       ((%%) {pos = Here} _) =>
         Op (Forall ** ("z" ** (BoolS **
           Pack {ty' = ()} [Var ((There Here).toVar)]
           )))))])))

term2 : HomTerm QuantSig Fulfill MVar BoolS [<("a" :- BoolS), ("a" :- BoolS), ("a" :- BoolS)]
term2 = Var ((There $ There Here) .toVar)

term3 : HomTerm QuantSig Fulfill MVar BoolS [<("y" :- BoolS)]
term3 = Op (Forall ** ("x" ** (BoolS ** Pack {ty' = ()}
  [Op (Exists ** ("x" ** (BoolS **
    Pack {ty' = ()} [Var $ (There (There Here)) .toVar])))])))

test : {ctx : _} -> {s : _} -> {auto ps : PS ctx} -> HomTerm QuantSig Fulfill MVar s ctx -> String
test = runSerialiser (QuantSigSerialiser (\BoolS => "bool") Fulfill)

main : IO ()
main = putStrLn (test term0)
