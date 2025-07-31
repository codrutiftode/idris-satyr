module Language.SMT.Arity

import public Data.Nat
import Data.List.Quantifiers

import MAST.Core
import MAST.Signature
import MAST.Tensor

import MAST.Simple.Combinator.List.Quantifiers

public export
infixr 3 :=>

public export
data Arity : Type -> Type where
  Const : (ret : sort) -> Type -> Arity sort
  (:=>) : (xs : List sort) ->
          {auto _ : NonZero (length xs)} ->
          (ret : sort) -> Arity sort
  CoProd : ((a : sort) -> (Arity sort)) -> Arity sort

public export
0
arity : Arity sort -> (sort,b) ====> (sort,b)
arity (Const ret ty) = ExtendOne ret . Const (\_,_ => ty)
arity ([x] :=> ret)  = ExtendOne ret . (x .@)
arity (xs  :=> ret)  = ExtendOne ret . All (map (.@) xs)
arity (CoProd f)     = CoProd (arity . f)

public export
mapIntoAll : (f : (x : a) -> p x) -> (l : List a) -> All p l
mapIntoAll f l = mapProperty (\case (Val x) => f x) (remember l)

public export
ArityMap : (a : Arity sort) -> (arity a).RSortedFamilyFunctor
ArityMap (Const ret x) = (ExtendMap (const ret))
                         `ComposeMap` (ConstMap (\_,_ => x))
ArityMap (CoProd f)     = CoProdMap (\a => ArityMap (f a))
ArityMap ([x] :=> ret) = (ExtendMap (const ret))
                         `ComposeMap` (RestrictMap (const x))
ArityMap ((x :: y :: xs) :=> ret) =
                         (ExtendMap (const ret))
                         `ComposeMap` AllMap (ripple (mapIntoAll (\t =>
                            RestrictMap (const t)) (x :: y :: xs)))

public export
ArityStrength : (a : Arity sort) -> (arity a).ClosedStrength
ArityStrength (Const ret x) = ComposeClosedStrength
                                (ExtendClosedStrength (const ret))
                                (ConstClosedStrength (\_,_ => x))
                                (ExtendMap (const ret))
ArityStrength (CoProd f)    = CoProdClosedStrength (\a => ArityStrength (f a))
ArityStrength ([x] :=> ret) = ComposeClosedStrength
                                (ExtendClosedStrength (const ret))
                                (RestrictClosedStrength (const x))
                                (ExtendMap (const ret))
ArityStrength ((x :: y :: xs) :=> ret) =
                              ComposeClosedStrength
                                (ExtendClosedStrength (const ret))
                                (AllClosedStrength
                                  (ripple (mapIntoAll (\t =>
                                    RestrictClosedStrength (const t)) (x :: y :: xs))))
                                (ExtendMap (const ret))
