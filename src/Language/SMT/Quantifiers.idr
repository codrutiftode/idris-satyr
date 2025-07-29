module Language.SMT.Quantifiers

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Core

import MAST.Core
import MAST.Signature

import MAST.Simple.Core

data QuantSig : (CoreNeed .ops) .Signature where
  Forall, 
  Exists : (x : String) ->
           (a : fstSort) ->
           fam (f.get TyBool) (ctx :< (x :- a)) ->
           QuantSig f sys fam (f.get b) ctx
