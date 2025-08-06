module Language.SMT.Fullfill

import MAST.Sorted.Core
-- import MAST.Simple.Core
-- import MAST.Simple.Combinator.Either
-- import MAST.Simple.Combinator.List.Quantifiers

public export
infixr 4 |=

public export
record (|=) (l, r : sort.SortedSig) where
  constructor Fullfill
  alpha : {0 x : sort.Fam} -> r x -/> l x

public export
VoidFam : sort.Fam
VoidFam = const Void

public export
-- Note: in general, might want to have a type for variables other than Void
(.TypesAlgebra) : (0 o : sort.SortedSig) -> o.algebra
o.TypesAlgebra = (o.free VoidFam).algebra

public export
0
(.Types) : (o : sort.SortedSig) -> sort.Fam
o.Types = o.TypesAlgebra.carrier

public export
algebraFunctor : (l |= r) -> l.algebraOn a -> r.algebraOn a
algebraFunctor f lalg = lalg . f.alpha

public export
(.get) : (l |= r) -> r.algebraOn (l.Types)
f.get = algebraFunctor f (l.TypesAlgebra.roll)
