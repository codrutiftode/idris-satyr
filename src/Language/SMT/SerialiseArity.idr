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

import Data.Singleton
import Data.List.Quantifiers

import Language.SMT.Combinator.Restrict
import Language.SMT.Combinator.Extend
import Language.SMT.Combinator.Const
import Language.SMT.Combinator.Compose
import Language.SMT.Combinator.CoProd
import Language.SMT.Combinator.List.Quantifiers
import Language.SMT.Combinator.Shift

public export
0
Metadata : Arity b sort -> Type
Metadata (Const _ ty) = ty -> String
Metadata (CoProd {arg} f) = (i : arg) -> Metadata (f i)
Metadata (xs :=> ret) = SnocList String -> String
Metadata (as ::=> ret) = SnocList String -> String

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
snocListHasPS (sx :< (x, s)) = S (snocListHasPS sx)

public export
arityAlg : {sys : SortingSystemOver b s sort} ->
  (a : Arity b sort) ->
  Metadata a ->
  (arity a).SerialiseAlgebra
arityAlg (Const ret y) m = ComposeSerialise
                             (ExtendSerialise (const ret))
                             (ConstSerialise (const $ const y) m)
                             (ExtendMap (const ret))
arityAlg (CoProd f)    m = CoProdSerialise (\a => arityAlg {sys} (f a) (m a))
arityAlg (xs :=> ret)  m = ComposeSerialise
                             (ExtendSerialise (const ret))
                             (nodeAlg m)
                             (ExtendMap (const ret))
arityAlg (as ::=> ret) m = ComposeSerialise
                             (ExtendSerialise (const ret))
                             (AllSerialise
                               (mapIntoComposite (\(vars, subRet) =>
                                ComposeSerialise
                                   (ShiftSerialise (cast vars)
                                     (cast $ snocListHasPS vars))
                                   (RestrictSerialise (const subRet))
                                   (ShiftMap (cast vars))) as)
                                m)
                             (ExtendMap (const ret))

{-
public export
serialiseArity : {sys : SortingSystemOver b s sort} ->
  (a : Arity b sort) ->
  Metadata a ->
  (meta : MVar {b,sort} -|> Strings) ->
  sys.Serialiser (Term sys (arity a) MVar)
serialiseArity a m meta = serialiser {sys}
  (MkSerialiseWithAction
  { alg = arityAlg {sys} a m
  , meta = meta {ty}
  , isMVar = MVarValid
  , oMap = ArityMap a
  , oStrength = ArityStrength a
  })
