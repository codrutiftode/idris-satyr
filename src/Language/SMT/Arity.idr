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
  ||| An AST Leaf tagged by elements of a given set `ret`
  Const   : (ret : sort) -> Type -> Arity b sort
  ||| Any one node of the given indexed family of nodes
  CoProd  : ((a : arg) -> (Arity b sort)) -> Arity b sort
  ||| A finitely-branching node of sort `ret` and sub-trees as in `xs`
  (:=>)   : (xs : List sort) ->
            (ret : sort) ->
            Arity b sort
  ||| A finitely-branching node of sort `ret` and sub-trees as in `as`,
  ||| each of which may bind some variables of given sorts
  (::=>) : (as : List (SnocList (String, b), sort)) ->
             (ret : sort) -> Arity b sort

-- Why is this here? Should be in MAST.
-- TODO: upstream to MAST
public export
Cast (SnocList (String, b)) b.Ctx where
  cast [<] = [<]
  cast (xs :< (x, s)) = cast xs :< (x :- s)

||| A single-sorted non-binding AST node taking sub-terms of the given list of sorts
Node : List sort -> (sort, b) ====> ((),b)
Node [] = Const $ const $ const ()
Node [x] = (@. x)
Node xs@(x :: y :: _) = All (map (flip (@.)) xs)


||| The signature functor of a binding signature
public export
0
arity : Arity b sort -> (sort,b) ====> (sort,b)
arity (Const ret ty) = ExtendOne ret . Const (\_,_ => ty)
arity (xs :=> ret)   = ExtendOne ret . Node xs
arity (CoProd f)     = CoProd (arity . f)
arity (as ::=> ret)  =
  ExtendOne ret . All (map (\t => ((cast t.fst).|>) . (@. t.snd)) as)

-- These Should be in MAST or even better, contrib or All/Any stdlib
public export
mapIntoAll : (f : (x : a) -> p x) -> (l : List a) -> All p l
mapIntoAll prf xs = mapProperty (\case (Val x) => prf x) (remember xs)

-- This seems to be a useful special case
public export
mapIntoComposite :
  (prf : (x : a) -> (f . g) x) -> (xs : List a) -> All f (map g xs)
mapIntoComposite prf xs = ripple (mapIntoAll prf xs)

||| The functorial action of the (single-sorted) Node signature functor
public export
NodeMap : (xs : List sort) -> (Node xs).RSortedFamilyFunctor
NodeMap [] = ConstMap (\_,_ => ())
NodeMap [x] = RestrictMap (const x)
NodeMap xs@(x :: y :: _) = AllMap $ mapIntoComposite (\t =>
                            RestrictMap (const t)) xs

||| The functorial action of the signature functor the given binding signature
||| induces
public export
ArityMap : (a : Arity b sort) -> (arity a).RSortedFamilyFunctor
ArityMap (Const ret x) = (ExtendMap (const ret))
                         `ComposeMap` (ConstMap (\_,_ => x))
ArityMap (CoProd f) = CoProdMap (\a => ArityMap (f a))
ArityMap (xs :=> ret) = (ExtendMap (const ret)) `ComposeMap` NodeMap xs
ArityMap (as ::=> ret) = (ExtendMap (const ret))
                         `ComposeMap`
                         AllMap (mapIntoComposite (\(vars, subRet) =>
                           (ShiftMap (cast vars))
                           `ComposeMap` (RestrictMap (const subRet))) as)

||| The tensorial strength of the (single-sorted) Node signature functor
public export
NodeStrength : (xs : List sort) -> (Node xs).PointedClosedStrength
NodeStrength [] = ConstPointedClosedStrength (const $ const ()) (\_,_ => id)
NodeStrength [x] = RestrictPointedClosedStrength (const x)
NodeStrength xs@(_ :: _ :: _) = AllPointedClosedStrength
                              $ mapIntoComposite (\t =>
                                RestrictPointedClosedStrength (const t)) xs


||| The tensorial strength of the signature functor the given binding signature
||| induces
public export
ArityStrength : (a : Arity b sort) -> (arity a).PointedClosedStrength
ArityStrength (CoProd f)    = CoProdPointedClosedStrength (\a => ArityStrength (f a))
ArityStrength (Const ret x) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (ConstPointedClosedStrength (\_,_ => x) (\_,_ => id))
                                (ExtendMap (const ret))
ArityStrength (xs :=> ret) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (NodeStrength xs)
                                (ExtendMap (const ret))
ArityStrength (as ::=> ret) = ComposePointedClosedStrength
                                (ExtendPointedClosedStrength (const ret))
                                (AllPointedClosedStrength
                                  (mapIntoComposite (\(vars, subRet) =>
                                    ComposePointedClosedStrength
                                      (ShiftPointedClosedStrength (cast vars))
                                      (RestrictPointedClosedStrength (const subRet))
                                      (ShiftMap (cast vars))) as))
                                (ExtendMap (const ret))

||| Lifting of presheaf structure from input sub-term presheaf to
||| Node signature output presheaf
public export
NodePsh : (xs : List sort) -> PresheafLifting (Node xs)
NodePsh [] = ConstPsh (const $ const ()) (\_ => id)
NodePsh [x] = RestrictPsh (const x)
NodePsh xs@(_ :: _ :: _) = AllPsh
                         $ mapIntoComposite
                         (\t => RestrictPsh (const t)) xs

||| Lifting of presheaf structure from input sub-term presheaf to
||| signature output presheaf
public export
ArityPsh : (a : Arity b sort) -> PresheafLifting (arity a)
ArityPsh (Const ret x) = ComposePsh
                               (ExtendPsh (const ret))
                               (ConstPsh (\_,_ => x) (\_ => id))
ArityPsh (xs :=> ret) = ComposePsh
                               (ExtendPsh (const ret))
                               (NodePsh xs)
ArityPsh (CoProd f) = CoProdPsh (\a => ArityPsh (f a))
ArityPsh (as ::=> ret) = ComposePsh
                           (ExtendPsh (const ret))
                           (AllPsh (ripple {g = (\t => ((cast t.fst).|>) . (@. t.snd))}
                             (mapIntoAll (\(vars, subRet) =>
                               ComposePsh
                                 (ShiftPsh (cast vars))
                                 (RestrictPsh (const subRet))) as)))
