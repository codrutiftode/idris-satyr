module Language.SMT.Fullfill

import MAST.Simple.Core
import MAST.Simple.Combinator.Either
import MAST.Simple.Combinator.List.Quantifiers

public export
infixr 4 |=

public export
record (|=) (l, r : SimpleSig) where
  constructor Fullfill
  alpha : {0 x : Type} -> r x -> l x

public export
-- Note: in general, might want to have a type for variables other than Void
(.TypesAlgebra) : (o : SimpleSig) -> o.algebra
o.TypesAlgebra = (o.free Void).algebra

public export
0
(.Types) : (o : SimpleSig) -> Type
o.Types = o.TypesAlgebra.carrier

public export
algebraFunctor : (l |= r) -> l.algebraOn a -> r.algebraOn a
algebraFunctor f lalg = lalg . f.alpha

public export
(.get) : {l : SimpleSig} -> (l |= r) -> r.algebraOn (l.Types)
f.get = algebraFunctor f (l.TypesAlgebra.roll)
