module Language.SMT.Signature

import Language.SMT.Fullfill

import MAST.Signature
import MAST.Core
import MAST.Initiality

import MAST.Simple.Core

public export
0
(.Signature) : (need : SimpleSig) -> Type
need.Signature =
  {l : SimpleSig} ->
  {0 fstSort, sndSort : Type} ->
  (f : (l |= need)) ->
  (sys : SortingSystemOver fstSort sndSort l.Types) ->  
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
(.Hom) : (sig : need.Signature) -> (HomSorting {a = need.Types}) .RSortedFamilyFun
sig.Hom = sig (Fullfill id) HomSorting

public export
HomFullfill : a |= a
HomFullfill = Fullfill {alpha = id}

public export
0
HomTerm : (sig : need.Signature) -> (need.Types).SortedFamilyOver (need.Types)
HomTerm sig = Term HomSorting (sig.Hom) Var -- (sig.Hom) Var
