module Language.SMT.Functions

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
FunNeed : Signature
FunNeed = MkSignature
  { ops = \x => Either (x, x) ()
  , map = \f => \case
                   Left (x, y) => Left (f x, f y)
                   Right () => Right ()
  }

public export
data FunOps = App | Fun

public export
labelToArity : {sys : SortingSystemOver fstSort sndSort l.Types} ->
  (f : l |= FunNeed .ops) -> FunOps -> Arity fstSort (l.Types)
labelToArity f App = CoProd (\s1 : fstSort =>
                     CoProd (\s2 : l.Types =>
                     [f.get (Left (sys.fst s1, s2)), sys.fst s1] :=> s2))
labelToArity f Fun = CoProd (\s1 : fstSort =>
                     CoProd (\s2 : l.Types =>
                     Const (f.get (Left (sys.fst s1, s2))) String))

public export
0
FunSig : (FunNeed .ops) .Signature
FunSig f sys = CoProd (arity . labelToArity {sys} f)

public export
FunSigMap : {sys : SortingSystemOver b s l.Types} ->
  {f : l |= FunNeed .ops} -> (FunSig f sys).RSortedFamilyFunctor
FunSigMap = CoProdMap (\x => ArityMap (labelToArity {sys} f x))

public export
FunSigStrength : {sys : SortingSystemOver b s l.Types} ->
  {f : l |= FunNeed .ops} -> (FunSig f sys).PointedClosedStrength
FunSigStrength = CoProdPointedClosedStrength (\x => ArityStrength (labelToArity {sys} f x))

term0 : HomTerm FunSig (Op (Right ())) [<("x" :- Op (Right ()))]
term0 = Op (App ** (Op $ Right () ** (Op $ Right () **
  Pack {ty' = ()}
   [Op (Fun ** (Op $ Right () ** (Op $ Right () ** Pack {ty' = ()} "f"))),
   Var (%% "x")])))
