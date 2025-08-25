module Language.SMT.SerialiseArity

import Language.SMT.Arity
import Language.SMT.Serialise
import Language.SMT.Signature
import Language.SMT.Names

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Modality
import MAST.Presheaf
import MAST.Signature
import MAST.Initiality

import MAST.Simple.Combinator.List.Quantifiers

import Data.Singleton
import Data.List.Quantifiers
import Data.List.Elem

import Language.SMT.Combinator.Restrict
import Language.SMT.Combinator.Extend
import Language.SMT.Combinator.Const
import Language.SMT.Combinator.Compose
import Language.SMT.Combinator.CoProd
import Language.SMT.Combinator.List.Quantifiers
import Language.SMT.Combinator.Shift

public export
0
ArityMetadata : Arity b sort -> Type
ArityMetadata (Const _ ty) = ty -> String
ArityMetadata (CoProd {arg} f) = (i : arg) -> ArityMetadata (f i)
ArityMetadata (xs :=> ret) = SnocList String -> String
ArityMetadata (as ::=> ret) =
  (SnocList String -> String,
  All (\a => Singleton (cast {to = b.Ctx} a.fst) ->
             Names (cast {to = b.Ctx} a.fst) ->
             String ->
             String) as)

nodeAlg : {xs : List sort} ->
  (SnocList String -> String) ->
  (Node xs).SerialiseAlgebra
nodeAlg {xs = []} toStr = ConstSerialise (const $ const ()) (const $ toStr [<])
nodeAlg {xs = [x]} toStr = RestrictSerialise (const x)
nodeAlg {xs = xs@(x :: y :: _)} toStr = AllSerialise
                                  (mapIntoComposite (\t =>
                                  RestrictSerialise (const t)) xs)
                                  toStr

-- TODO: could be moved to MAST?
snocListHasPS : (vars : SnocList (String, b)) -> PS (cast {to = b.Ctx} vars)
snocListHasPS [<] = Z
snocListHasPS (sx :< (x, s)) = S {str = x} (snocListHasPS sx)

allToPairs : (xs : List a) -> All p xs -> List (t ** p t)
allToPairs [] [] = []
allToPairs (x :: xs) (px :: pxs) = (x ** px) :: allToPairs xs pxs

allElem : (xs : List a) -> All (`Elem` xs) xs
allElem [] = []
allElem (x :: xs) = Here :: mapProperty There (allElem xs)

mapIntoAll' : (xs : List a) -> (f : (x : a) -> Elem x xs -> p x) -> All p xs
mapIntoAll' xs f = zipPropertyWith (\(Val x), elem => f x elem) (remember xs) (allElem xs)

(.mapIntoComposite') :
  (xs : List a) ->
  (prf : (x : a) -> Elem x xs -> (f . g) x) ->
  All f (map g xs)
xs.mapIntoComposite' prf = ripple (mapIntoAll' xs prf)

public export
AritySerialise : {sys : SortingSystemOver b s sort} ->
  (a : Arity b sort) ->
  ArityMetadata a ->
  (arity a).SerialiseAlgebra
AritySerialise (Const ret y) m = ComposeSerialise
                             (ExtendSerialise (const ret))
                             (ConstSerialise (const $ const y) m)
                             (ExtendMap (const ret))
AritySerialise (CoProd f)    m = CoProdSerialise (\a => AritySerialise {sys} (f a) (m a))
AritySerialise (xs :=> ret)  m = ComposeSerialise
                             (ExtendSerialise (const ret))
                             (nodeAlg m)
                             (ExtendMap (const ret))
AritySerialise (as ::=> ret) m = ComposeSerialise
                             (ExtendSerialise (const ret))
                             (AllSerialise
                               (as.mapIntoComposite'
                                (\(vars, subRet), elem =>
                                ComposeSerialise
                                    (ShiftSerialise (cast {to = b.Ctx} vars)
                                     (cast $ snocListHasPS vars)
                                     (indexAll elem m.snd))
                                   (RestrictSerialise (const subRet))
                                   (ShiftMap (cast vars))
                                ))
                                m.fst)
                             (ExtendMap (const ret))

{-
public export
serialiseArity : {sys : SortingSystemOver b s sort} ->
  (a : Arity b sort) ->
  ArityMetadata a ->
  (meta : MVar {b,sort} -|> Strings) ->
  sys.Serialiser (Term sys (arity a) MVar)
serialiseArity a m meta = serialiser {sys}
  (MkSerialiseWithAction
  { alg = AritySerialise {sys} a m
  , meta = meta {ty}
  , isMVar = MVarValid
  , oMap = ArityMap a
  , oStrength = ArityStrength a
  })
