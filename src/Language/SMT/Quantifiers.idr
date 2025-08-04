module Language.SMT.Quantifiers

import Language.SMT.Signature
import Language.SMT.Fullfill
import Language.SMT.Arity
import Language.SMT.Core

import MAST.Core
import MAST.Substitution
import MAST.Tensor
import MAST.Signature
import MAST.Initiality
import MAST.Modality
import MAST.Combinator.List
import MAST.Combinator.Restrict
import MAST.Combinator.Extend
import MAST.Combinator.List.Quantifiers
import MAST.Combinator.CoProd
import MAST.Combinator.Prod
import MAST.Combinator.Const
import MAST.Combinator.Compose
import MAST.Combinator.Shift
import MAST.Simple.Core
import MAST.Simple.Combinator.List.Quantifiers

public export
data QuantOps = Forall | Exists

public export
labelToArity : {0 sys : SortingSystemOver b s l.Types} ->
  (f : l |= CoreNeed .ops) ->
  QuantOps -> Arity b (l.Types)
labelToArity f _ =
  CoProd (\x => CoProd (\a => [([<(x, a)], f.get TyBool)] ::=> f.get TyBool))

public export
0
QuantSig : (CoreNeed .ops) .Signature
QuantSig f sys = CoProd (arity . labelToArity {sys} f)

public export
QuantSigMap : {f : l |= CoreNeed .ops} -> (QuantSig f sys).RSortedFamilyFunctor
QuantSigMap = CoProdMap (\x => ArityMap (labelToArity {sys} f x))

public export
QuantSigStrength : {f : l |= CoreNeed .ops} -> (QuantSig f sys).PointedClosedStrength
QuantSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm QuantSig (HomFullfill .get TyBool) [<]
term0 = Op (Forall ** ("y" ** (Op TyBool ** Pack {ty' = ()} [Var (%% "y")])))
