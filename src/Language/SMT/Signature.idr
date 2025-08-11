module Language.SMT.Signature

import Language.SMT.Fullfill

import MAST.Signature
import MAST.Core
import MAST.Initiality

import MAST.Sorted.Core
import Data.List.Quantifiers
%hide MAST.Core.(.Fam)

||| Collate all the types in the family into one
public export
0
Collate : (sort : Type) -> Type
Collate sort = (fam : sort.Fam) -> Type

||| Special case when the family only has one index, i.e. ()
public export
SingleKind : Collate ()
SingleKind x = x ()

||| A Satyr signature, with a way to `collate` the sorts for all kinds,
||| and a family of sort variables `vars`
public export
0
(.Signature) : (need : sort.SortedSig) ->
  (collate : Collate sort) ->
  (vars : sort.Fam) ->
  Type
need.Signature collate vars =
  {l : sort.SortedSig} ->
  {0 fstSort, sndSort : Type} ->
  (f : (l |= need)) ->
  (sys : SortingSystemOver fstSort sndSort (collate (l.Types vars))) ->
  sys.RSortedFamilyFun

-- TODO: Should be moved to MAST?
||| A sorting system where all sorts are first-class
public export
HomSorting : SortingSystemOver a Void a
HomSorting = MkSortingSystemOver
  { fst = id
  , snd = \x impossible
  , copair = \f, _ => f
  }

||| Instantiate a signature with homogeneous sorting
public export
0
(.Hom) : {collate : Collate sort} -> (sig : need.Signature collate vars) ->
  (HomSorting {a = collate (need.Types vars)}) .RSortedFamilyFun
sig.Hom = sig (Fullfill id) HomSorting

||| Constant sorted family of strings
public export
Strings : sort.SortedFamilyOver b
Strings s ctx = String

||| A sorted family of meta-variables
public export
MVar : sort.SortedFamilyOver bindable
MVar = Strings

||| Homogeneous term in the signature
public export
0
HomTerm : (collate : Collate sort) ->
  (vars : sort.Fam) ->
  (sig : need.Signature collate vars) ->
  (collate (need.Types vars)).SortedFamilyOver (collate (need.Types vars))
HomTerm collate vars sig = Term HomSorting (sig.Hom {collate}) MVar
