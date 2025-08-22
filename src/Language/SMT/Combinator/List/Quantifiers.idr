module Language.SMT.Combinator.List.Quantifiers

import Language.SMT.Serialise
import Language.SMT.Names

import Data.SnocList
import Data.List.Quantifiers
import Data.SnocList.Quantifiers

import MAST.Core
import MAST.Signature
import MAST.Substitution
import MAST.Simple.Combinator.List.Quantifiers

import public MAST.Combinator.List.Quantifiers

snocToAll : (xs : SnocList (y : a ** p y)) -> All p (map (.fst) xs)
snocToAll [<] = [<]
snocToAll (xs :< x) = snocToAll xs :< x.snd

toSnoc : List a -> SnocList a
toSnoc = cast

namespace All
  public export
  AllSerialise : (All (.SerialiseAlgebra) fs) ->
    (toStr : SnocList String -> String) ->
    (All fs).SerialiseAlgebra
  AllSerialise algs toStr = MkSerialiseAlgebra
    (\t => let args = toSnoc $ forget $ zipPropertyWith (\alg, f => alg.alg f) algs t
           in
             (CtxProdFlat (map fst args) **
               (NamesProdFlat (mapProperty fst (snocToAll args))
               , \ns =>
                  toStr $ StringProdFlat' (mapProperty (fst . snd) (snocToAll args)) ns
               , RenProdFlat (mapProperty (snd . snd) (snocToAll args))
               )
             )
    )
