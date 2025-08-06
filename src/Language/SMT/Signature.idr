module Language.SMT.Signature

import Language.SMT.Fullfill

import MAST.Signature
import MAST.Core
import MAST.Initiality

import MAST.Sorted.Core
import Data.List.Quantifiers
%hide MAST.Core.(.Fam)

public export
0
Finite : (sort : Type) -> Type
Finite sort = sort.Fam -> Type

public export
FiniteUnit : Finite ()
FiniteUnit x = x ()

public export
0
(.Signature) : (need : sort.SortedSig) -> (collate : Finite sort) -> Type
need.Signature collate =
  {l : sort.SortedSig} ->
  {0 fstSort, sndSort : Type} ->
  (f : (l |= need)) ->
  (sys : SortingSystemOver fstSort sndSort (collate l.Types)) ->  
  sys.RSortedFamilyFun

public export
HomSorting : SortingSystemOver a Void a
HomSorting = MkSortingSystemOver
  { fst = id
  , snd = \x impossible
  , copair = \f, _ => f
  }

public export
0
(.Hom) : {collate : Finite sort} -> (sig : need.Signature collate) -> 
  (HomSorting {a = collate need.Types}) .RSortedFamilyFun
sig.Hom = sig (Fullfill id) HomSorting

public export
HomFullfill : a |= a
HomFullfill = Fullfill {alpha = id}

public export
0
HomTerm : (collate : Finite sort) -> (sig : need.Signature collate) -> 
  (collate need.Types).SortedFamilyOver (collate need.Types)
HomTerm collate sig = Term HomSorting (sig.Hom {collate}) Var
