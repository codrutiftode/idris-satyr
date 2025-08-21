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

import MAST.Combinator.Restrict
import MAST.Combinator.Extend
import MAST.Combinator.List.Quantifiers
import MAST.Combinator.CoProd
import MAST.Combinator.Prod
import MAST.Combinator.Const
import MAST.Combinator.Compose
import MAST.Combinator.Shift

Metadata : Arity b sort -> Type
Metadata (Const _ ty) = ty -> String
Metadata (CoProd f) = ?Metadata_rhs_1
Metadata (xs :=> ret) = ?Metadtaa_rhs_2
Metadata (as ::=> ret) = ?Metadata_rhs_3

arityAlg : {sys : SortingSystemOver b s sort} ->
  (a : Arity b sort) ->
  Metadata a ->
  (arity a) SerialiseTarget -|> SerialiseTarget
arityAlg (Const ret y) m (Pack x) = ([<] ** (Z, const (m x), LinTerminal))
arityAlg (CoProd f)    m x = ?serialiseArity_rhs_1
arityAlg (xs :=> ret)  m (Pack x) =
  (?left_0 ** ?left_1)
arityAlg (as ::=> ret) m x = ?serialiseArity_rhs_3

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
