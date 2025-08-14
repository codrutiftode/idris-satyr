|||
module Language.SMT.Signature

import MAST.Signature
import MAST.Core
import MAST.Initiality

import MAST.Sorted.Core
import Data.List.Quantifiers
%hide MAST.Core.(.Fam) -- Maybe we ought to rename MAST.Sorted.Core.(.SimpleFam)
  -- TODO: Upstream this ^ comment to MAST.

-- TODO: should be moved to MAST
public export
0
(.Sort) : (sys : SortingSystemOver fstSort sndSort sort) -> Type
sys.Sort = sort

||| A Satyr signature
public export
0
(.Signature) : (req : Type -> Type) -> Type
(.Signature) req =
  {0 fstSort, sndSort, sort : Type} ->
  (sys : SortingSystemOver fstSort sndSort sort) ->
  (r : req sort) ->
  sys.RSortedFamilyFun

-- TODO: Should be moved to MAST?
||| A sorting system where all sorts are first-class
public export
HomSorting : (0 a : Type) -> SortingSystemOver a Void a
HomSorting a = MkSortingSystemOver
  { fst = id
  , snd = \x impossible
  , copair = \f, _ => f
  }

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
HomTerm : (sig : req.Signature) -> (r : req sort) -> sort.SortedFamilyOver sort
HomTerm sig r = Term (HomSorting sort) (sig (HomSorting sort) r) MVar
