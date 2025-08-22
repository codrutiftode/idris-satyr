module Language.SMT.Names

import Language.SMT.Signature

import MAST.Core
import MAST.Substitution

public export
Name : Type
Name = (String, Int)

public export
data Names : sort.Ctx -> Type where
  Z : Names [<]
  S : Name -> Names ctx -> Names (ctx :< (x :- ty))

public export
Cast (Names ctx) (SnocList Name) where
  cast Z = [<]
  cast (S n ns) = cast ns :< n

public export
concatNames : {b : _} -> Names a -> Names b -> Names (a ++ b)
concatNames {b = [<]} x Z = x
concatNames {b = (ctx :< (v :- s))} x (S d ns) = S d (concatNames x ns)

public export
Cast (PS ctx) (Names ctx) where
  cast Z = Z
  cast (S {str} x) = S (str, 0) (cast x)

public export
psToNames : PS ctx -> Names ctx
psToNames Z = Z
psToNames (S {str} x) = S (str, 0) (psToNames x)

public export
findLast : String -> Names ctx -> Maybe Name
findLast str Z = Nothing
findLast str (S n ns) =
  if str == fst n then Just n else findLast str ns

public export
mangleSchema : Name -> String
mangleSchema (s,d) = "\{s}." ++ if d == 0 then "" else cast d

public export
mangle : String -> Names ctx -> Name
mangle str names = case findLast str names of
  Nothing => (str, 0)
  Just n  => (str, snd n + 1)

||| Mangle all the names of `a` in the scope containing the names of `b`
public export
mangleGlobalInScope : {ctx : sort.Ctx} -> {0 dtx : sort.Ctx} ->
  (a : Names ctx) -> (b : Names dtx) -> Names ctx
mangleGlobalInScope Z scope = Z
mangleGlobalInScope (S n ns) scope =
  let mangled = mangleGlobalInScope ns scope
  in S (mangle (fst n) (concatNames scope mangled)) mangled

||| Mangle all the names of `a` in an empty scope
public export
mangleGlobal : {ctx : sort.Ctx} -> Names ctx -> Names ctx
mangleGlobal a = mangleGlobalInScope a Z

public export
setupNames : {ctx : sort.Ctx} -> PS ctx -> Names ctx
setupNames = mangleGlobal . cast

lookupNamed : (ps : Names ctx) -> Strings .substNamed ctx ctx
lookupNamed (S n _) Here = (mangleSchema n)
lookupNamed (S _ ps) (There v) = lookupNamed ps v

public export
lookup : (ps : Names ctx) -> Strings .subst ctx ctx
lookup ps = fromEnvNamed {ctx} Strings (lookupNamed ps)

lookupNameNamed : (ps : Names ctx) -> (const $ const Name) .substNamed ctx ctx
lookupNameNamed (S n _) Here = n
lookupNameNamed (S _ ps) (There v) = lookupNameNamed ps v

public export
lookupName : (ps : Names ctx) -> (const $ const Name) .subst ctx ctx
lookupName ps = fromEnvNamed {ctx} (const $ const Name) (lookupNameNamed ps)

public export
NamesCovPsh : {b : _} -> a ~> b -> Names a -> Names b
NamesCovPsh {b = [<]} f x = Z
NamesCovPsh {b = (ctx :< (v :- ty))} f x =
  S (lookupName x (f (Here .toVar))) (NamesCovPsh (\v' => f (ThereVar v')) x)

public export
namesR : {a, b : _} -> Names (a ++ b) -> Names a
namesR x = NamesCovPsh (weakr _ _) x

public export
namesL : {a, b : _} -> Names (a ++ b) -> Names b
namesL x = NamesCovPsh (weakl _ _) x
