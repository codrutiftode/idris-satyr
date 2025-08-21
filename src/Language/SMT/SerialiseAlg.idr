module Language.SMT.SerialiseAlg

import MAST.Core
import MAST.Substitution
import Language.SMT.Names

-- TODO: duplicated definition
-- TODO: remove this one and move to MAST
public export
copair : {dtx : sort.Ctx} -> (Var s ctx -> c) -> (Var s dtx -> c) -> Var s (ctx ++ dtx) -> c
copair {dtx = [<]} f g v = f v
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = Here} x) = g ((%%) x)
copair {dtx = dtx :< (x :- s)} f g ((%%) {pos = (There y)} name) =
  copair {dtx} f (g . ThereVar) (y .toVar)

public export
data Thins : (ctx, dtx : sort.Ctx) -> Type where
  Id   : ctx `Thins` ctx
  Keep : ctx `Thins` dtx -> (ctx :< x) `Thins` (dtx :< x)
  Drop : ctx `Thins` dtx -> ctx        `Thins` (dtx :< x)

public export
data Div : (ctx : sort.Ctx) -> (a,b : sort.Ctx) -> Type where
  Lin : Div [<] a b
  Left : (e : sort.extension) -> Var e.ofType a -> Div ctx a b -> Div (ctx :< e) a b
  Right : (e : sort.extension) -> Var e.ofType b -> Div ctx a b-> Div (ctx :< e) a b

public export
record (.Part) (dtx : sort.Ctx) (l : sort.Ctx) where
  constructor MkPart
  context : sort.Ctx
  label : l ~> context
  thin : context `Thins` dtx

public export
label : {b : sort.Ctx} -> (ctx : sort.Ctx) -> (a ++ b) ~> ctx -> Div ctx a b
label [<] ren = [<]
label (ctx :< (x :- ty)) ren =
  let rest = label ctx (ren . ThereVar)
  in copair
    (\v => (Left (x :- ty) v rest))
    (\v => (Right (x :- ty) v rest))
    (ren (Here .toVar))

public export
label' : {x : sort.extension} -> (ctx : sort.Ctx) -> (a :< x) ~> ctx -> Div ctx a [<x]
label' = label {b = [<x]}

public export
renIntoOne : Var (x.ofType) b -> b ~> [<x]
renIntoOne y ((%%) {pos = Here} name) = y
renIntoOne y ((%%) {pos = (There _)} name) impossible

public export
data Compl : a `Thins` c -> b `Thins` c -> Type where
  Zero : Compl Id Id
  KeepLeft : Compl t1 t2 -> Compl (Keep t1) (Drop t2)
  KeepRight : Compl t1 t2 -> Compl (Drop t1) (Keep t2)

public export
filterA : {ctx : sort.Ctx} ->
  Div ctx a b ->
  ctx.Part a
filterA [<] = MkPart [<] LinTerminal Id
filterA (Left e v d) =
  let pa = filterA d
  in MkPart (pa.context :< e) (pair pa.label (renIntoOne v)) (Keep pa.thin)
filterA (Right e v d) =
  let pa = filterA d
  in MkPart pa.context pa.label (Drop pa.thin)

public export
filterB : {ctx : sort.Ctx} ->
  Div ctx a b ->
  ctx.Part b
filterB [<] = MkPart [<] LinTerminal Id
filterB (Left e v d) =
  let pb = filterB d
  in MkPart pb.context pb.label (Drop pb.thin)
filterB (Right e v d) =
  let pb = filterB d
  in MkPart (pb.context :< e) (pair pb.label (renIntoOne v)) (Keep pb.thin)

public export
filtersCompl : {ctx : sort.Ctx} -> (div : Div ctx a b) ->
  Compl (filterA div).thin (filterB div).thin
filtersCompl [<] = Zero
filtersCompl (Left e v d) = KeepLeft (filtersCompl d)
filtersCompl (Right e v d) = KeepRight (filtersCompl d)

public export
namesFromCompl : {t1 : a `Thins` c} ->
  {t2 : b `Thins` c} ->
  Compl t1 t2 ->
  Names a ->
  Names b ->
  Names c
namesFromCompl Zero na nb = na
namesFromCompl (KeepLeft c) (S a na) nb = S a (namesFromCompl c na nb)
namesFromCompl (KeepRight c) na (S b nb) = S b (namesFromCompl c na nb)

public export
combineNames : {ctx, b : sort.Ctx} ->
  {ren : (a ++ b) ~> ctx} ->
  Names (filterA {a,b} (label ctx ren)).context ->
  Names (filterB {a,b} (label ctx ren)).context ->
  Names ctx
combineNames = namesFromCompl (filtersCompl (label ctx ren))

public export
filterNames : {ctx : sort.Ctx} ->
  Names ctx -> (div : Div ctx a b) -> Names (filterA div).context
filterNames Z [<] = Z
filterNames (S z ns) (Left (x :- ty) v d) = S z (filterNames ns d)
filterNames (S _ ns) (Right (x :- ty) v d) = filterNames ns d

public export
findBoundNames : {ctx, b : sort.Ctx} -> {ren : (a ++ b) ~> ctx} ->
  Names b -> Names (filterB {a,b} (label ctx ren)).context
findBoundNames = NamesCovPsh (filterB {a,b} (label ctx ren)).label
