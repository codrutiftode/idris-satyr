module Language.SMT.Ints

import Language.SMT.Signature
import Language.SMT.Fullfill

import MAST.Core
import MAST.Simple.Core
import MAST.Signature

%hide Builtin.DPair.DPair.(.fst)
%hide Builtin.DPair.DPair.(.snd)

data TyInts : Type where
  TyInt : TyInts
  
IntNeed : Signature
IntNeed = MkSignature 
  { ops = \x => TyInts
  , map = \_ => \case
      TyInt => TyInt
  }  
  
data IntSig : (IntNeed .ops) .Signature where
  Add : fam (f.get TyInt) ctx ->
        fam (f.get TyInt) ctx ->
        IntSig f sys fam (f.get TyInt) ctx
  Let : {a : fstSort} -> (sys.fst %| fam) a ctx -> IntSig f sys fam (f.get TyInt) ctx
  Num : Int -> IntSig f sys fam (f.get TyInt) ctx
