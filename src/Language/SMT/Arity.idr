module Language.SMT.Arity

import public Data.Nat
import Data.List.Quantifiers

import MAST.Core
import MAST.Signature
import MAST.Tensor
import MAST.Initiality
import MAST.Modality
import MAST.Substitution
import MAST.Presheaf

import MAST.Combinator.Restrict
import MAST.Combinator.Extend
import MAST.Combinator.List.Quantifiers
import MAST.Combinator.CoProd
import MAST.Combinator.Prod
import MAST.Combinator.Const
import MAST.Combinator.Compose
import MAST.Combinator.Shift

import MAST.Simple.Combinator.List.Quantifiers

public export
infixr 3 :=>, ::=>

public export
data Arity : Type -> Type -> Type where
  Const   : (ret : sort) -> Type -> Arity b sort
  CoProd  : ((a : arg) -> (Arity b sort)) -> Arity b sort
  (:=>)   : (xs : List sort) ->
            (ret : sort) ->
            Arity b sort
  (::=>) : (as : List (SnocList (String, b), sort)) ->
           {auto _ : NonZero (length as)} ->
           (ret : sort) -> Arity b sort

public export
toCtx : SnocList (String, b) -> b.Ctx
toCtx [<] = [<]
toCtx (xs :< (x, s)) = toCtx xs :< (x :- s)

public export
0
arity : Arity b sort -> (sort,b) ====> (sort,b)
arity (Const ret ty) = ExtendOne ret . Const (\_,_ => ty)
arity ([] :=> ret)   = ExtendOne ret . Const (\_,_ => ())
arity ([x] :=> ret)  = ExtendOne ret . (x .@)
arity (xs  :=> ret)  = ExtendOne ret . All (map (.@) xs)
arity (CoProd f)     = CoProd (arity . f)
arity (as ::=> ret)  =
  ExtendOne ret . All (map (\t => ((toCtx t.fst).|>) . (t.snd.@)) as)

public export
mapIntoAll : (f : (x : a) -> p x) -> (l : List a) -> All p l
mapIntoAll f l = mapProperty (\case (Val x) => f x) (remember l)

public export
ArityMap : (a : Arity b sort) -> (arity a).RSortedFamilyFunctor
ArityMap (Const ret x) = (ExtendMap (const ret))
                         `ComposeMap` (ConstMap (\_,_ => x))
ArityMap (CoProd f) = CoProdMap (\a => ArityMap (f a))
ArityMap ([] :=> ret) = (ExtendMap (const ret))
                         `ComposeMap` (ConstMap (\_,_ => ()))
ArityMap ([x] :=> ret) = (ExtendMap (const ret))
                         `ComposeMap` (RestrictMap (const x))
ArityMap ((x :: y :: xs) :=> ret) =
                         (ExtendMap (const ret))
                         `ComposeMap` AllMap (ripple (mapIntoAll (\t =>
                            RestrictMap (const t)) (x :: y :: xs)))
ArityMap (as ::=> ret) = (ExtendMap (const ret))
                         `ComposeMap`
                         AllMap (ripple (mapIntoAll (\(vars, subRet) =>
                           (ShiftMap (toCtx vars))
                           `ComposeMap` (RestrictMap (const subRet))) as))

public export
ArityStrength : (a : Arity b sort) -> (arity a).PointedClosedStrength
ArityStrength (CoProd f)    = CoProdPointedClosedStrength (\a => ArityStrength (f a))
ArityStrength (Const ret x) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (ConstPointedClosedStrength (\_,_ => x) (\_,_ => id))
                                (ExtendMap (const ret))
ArityStrength ([] :=> ret) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (ConstPointedClosedStrength (\_,_ => ()) (\_,_ => id))
                                (ExtendMap (const ret))
ArityStrength ([x] :=> ret) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (RestrictPointedClosedStrength (const x))
                                (ExtendMap (const ret))
ArityStrength ((x :: y :: xs) :=> ret) =
                          ComposePointedClosedStrength
                            (ExtendPointedClosedStrength (const ret))
                            (AllPointedClosedStrength
                             (ripple (mapIntoAll (\t =>
                              RestrictPointedClosedStrength (const t)) (x :: y :: xs))))
                              (ExtendMap (const ret))
ArityStrength (as ::=> ret) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (AllPointedClosedStrength
                                  (ripple (mapIntoAll (\(vars, subRet) =>
                                    ComposePointedClosedStrength
                                      (ShiftPointedClosedStrength (toCtx vars))
                                      (RestrictPointedClosedStrength (const subRet))
                                      (ShiftMap (toCtx vars))) as)))
                                (ExtendMap (const ret))

public export
ArityPsh : (a : Arity b sort) -> PresheafLifting (arity a)
ArityPsh (Const ret x) = ComposePsh
                               (ExtendPsh (const ret))
                               (ConstPsh (\_,_ => x) (\_ => id))
ArityPsh ([] :=> ret) = ComposePsh
                               (ExtendPsh (const ret))
                               (ConstPsh (\_,_ => ()) (\_ => id))
ArityPsh ([x] :=> ret) = ComposePsh
                               (ExtendPsh (const ret))
                               (RestrictPsh (const x))
ArityPsh ((x :: y :: xs) :=> ret) =
                    ComposePsh
                    (ExtendPsh (const ret))
                    (AllPsh (ripple
                      (mapIntoAll (\t => \0 p => RestrictPsh (const t))
                        (x :: (y :: xs)))))
ArityPsh (CoProd f) = CoProdPsh (\a => ArityPsh (f a))
ArityPsh (as ::=> ret) = ComposePsh
                           (ExtendPsh (const ret))
                           (AllPsh (ripple {g = (\t => ((toCtx t.fst).|>) . (t.snd.@))}
                             (mapIntoAll (\(vars, subRet) =>
                               ComposePsh
                                 (ShiftPsh (toCtx vars))
                                 (RestrictPsh (const subRet))) as)))
