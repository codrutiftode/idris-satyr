|||
module Language.SMT.Signature

import MAST.Signature
import MAST.Core
import MAST.Initiality

import MAST.Sorted.Core
import Data.List.Quantifiers
%hide MAST.Core.(.Fam) -- Maybe we ought to rename MAST.Sorted.Core.(.SimpleFam)
  -- TODO: Upstream this ^ comment to MAST.

-- Note: It might make more sense to impose requirement on the sorting
-- system, i.e., the requirement can range over the first and second
-- class sorts separately. So far we have not needed this level of
-- generality, and so we stay simpler.

||| A Satyr signature, parameterised by a `req`uirement type family.
||| It imposes additional structure on the given overall sort, and
||| the constructors this signature supports might require this additional
||| structure.
|||
||| The `req sort` argument requires downstream code to fulfill the requirement
||| for their parameter `sort`.
|||
||| NB: It's plausible requirements should be parameterised by the sorting
||| system if you need this functionality, file an issue request.
-- TODO: we might want this definition to work harder, and perhaps package
-- functors, presheaf lifting, strength, parser, serialiser, checker, ...
public export
0
(.Signature) : (req : Type -> Type) -> Type
req.Signature =
  {0 fstSort, sndSort, sort : Type} ->
  (sys : SortingSystemOver fstSort sndSort sort) ->
  (r : req sort) ->
  sys.RSortedFamilyFun

-- TODO: Should be moved to MAST
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

||| Homogeneous term in the signature
public export
0
HomTerm : (sig : req.Signature) -> (r : req sort) ->
          (mvar : sort.SortedFamilyOver sort) ->
          sort.SortedFamilyOver sort
HomTerm sig r mvar = Term (HomSorting sort) (sig (HomSorting sort) r) mvar
