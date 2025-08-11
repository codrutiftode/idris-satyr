module Language.SMT.Fullfill

import MAST.Sorted.Core

public export
infixr 4 |=

||| Functor `l` fullfills need `r` when we have
||| a natural transformation `alpha` from `r` to `l`
public export
record (|=) (l, r : sort.SortedSig) where
  constructor Fullfill
  alpha : {0 x : sort.Fam} -> r x -/> l x

||| Sorts without sort variables
public export
NoSortVar : sort.Fam
NoSortVar = const Void

||| Free algebra of `o` over `var`
public export
(.TypesAlgebra) : (0 o : sort.SortedSig) -> (0 var : sort.Fam) -> o.algebra
o.TypesAlgebra var = (o.free var).algebra

||| Carrier of free algebra of `o` over `var'
public export
0
(.Types) : (o : sort.SortedSig) -> (var : sort.Fam) -> sort.Fam
o.Types var = (o.TypesAlgebra var).carrier

||| A fullfillment induces a functor from `l`-algebras to `r`-algebras
public export
algebraFunctor : (l |= r) -> l.algebraOn a -> r.algebraOn a
algebraFunctor f lalg = lalg . f.alpha

||| Use a fullfillment to use `r` operations on `l` types
public export
(.op) : (l |= r) -> r.algebraOn (l.Types var)
f.op = algebraFunctor f ((l.TypesAlgebra var).roll)

||| A functor fullfills its own need
public export
SelfFullfill : a |= a
SelfFullfill = Fullfill {alpha = id}
