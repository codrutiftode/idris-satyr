module Language.SMT.Parser

import Language.SMT.Lexer

import Decidable.Equality

import Flap.Parser
import MAST.Core
import MAST.Initiality
import MAST.Signature
import MAST.Substitution
import MAST.Combinator.Restrict

%hide MAST.Core.infixr.(:-)

exampleTerm : String
exampleTerm = """
sat
(
  (define-fun a () Int
    3)
  (define-fun f ((x!0 Int)) Int
    (+ 1 x!0))
)
"""

-- Note: should this be moved to MAST?
record (.RPointedSortedFamily) (sys : SortingSystemOver fstSort sndSort sort) where
  constructor MkRPointedSortedFamily
  sortedFam : sys.RSortedFamily
  point : Point (sortedFam . sys.fst)

public export
record Function (sys : SortingSystemOver fstSort sndSort sort)
  (f : sys.RPointedSortedFamily) where
  constructor MkFunction
  ret : sort
  ctx : fstSort.Ctx
  body : f.sortedFam ret ctx

public export
SatAssignment : (sys : SortingSystemOver fstSort sndSort sort) ->
  (f : sys.RPointedSortedFamily) -> Type
SatAssignment sys f = List (String, Function sys f)

public export
data SMTResult : (sys : SortingSystemOver fstSort sndSort sort) ->
  (f : sys.RPointedSortedFamily) -> Type where
  Sat : SatAssignment sys f -> SMTResult sys f
  Unsat, Unknown : SMTResult sys f

public export
record (.ParserState) (sys : SortingSystemOver fstSort sndSort sort)
  (embed : sort' -> sort) where
  ret : sort'
  ctx : fstSort.Ctx
  names : PS ctx
  decEq : DecEq fstSort

0
TermParser : (sys : SortingSystemOver fstSort sndSort sort) ->
  (embed : sort' -> sort) ->
  (locked : SnocList String) ->
  Type
TermParser sys embed locked =
  {f : sys.RPointedSortedFamily} ->
  Parser (sys.ParserState embed) String SMTToken False
    (map (\name => name :- (False, (\s => f.sortedFam (embed s.ret) s.ctx))) locked)
    [<]
    (\s => f.sortedFam (embed s.ret) s.ctx)

ListTermParser : (sys : SortingSystemOver fstSort sndSort sort) ->
  (embed : sort' -> sort) ->
  (locked : SnocList String) ->
  Type

-- TODO: only compares sorts, should compare names too
getVar : (dec : DecEq sort) =>
  (ctx : sort.Ctx) -> PS ctx -> (s : sort) -> String -> Maybe (ctx.var s)
getVar [<] Z s target = Nothing
getVar (ctx :< (_ :- s')) (S {str = name} names) s target =
  case (decEq s' s, name == target) of
    ((Yes Refl), True) => Just (Here .toVar)
    _                  => ThereVar <$> getVar ctx names s target

asVar : (f : sys.RPointedSortedFamily) ->
  {s : sys.ParserState sys.fst} ->
  String ->
  Either String (f.sortedFam (sys.fst s.ret) s.ctx)
asVar f name = case (getVar {dec = s.decEq} s.ctx s.names s.ret name) of
  Nothing  => Left "Variable \{name} out of scope."
  (Just v) => Right $ f.point v

atomicTerm : TermParser sys sys.fst [<"open"]
atomicTerm =
  OneOf
  [ Map (asVar f) (match Name)
  , enclose (match LB) (match RB) (Var $ %%% "open")
  ]

sortedVarExpr : Parser () String SMTToken False [<] [<] (const (String, fstSort))

defineFunExpr : Parser () String SMTToken False [<] [<] (const (String, Function sys f))
defineFunExpr = (\((name, args), ret) => (name, MkFunction ?res ?b ?c))
  <$> (enclose (match LB) (match RB)
        (match KDefFun *>
         match Name
         <**> (match LB *> (star sortedVarExpr) <* match RB)
         <**> match Name))

satTerm : Parser () String SMTToken False [<] [<] (const (SatAssignment sys f))
satTerm = match KSat *>
  enclose (match LB) (match RB) (star defineFunExpr)

unknownTerm : Parser () String SMTToken False [<] [<] (const ())
unknownTerm = match KUnknown

unsatTerm : Parser () String SMTToken False [<] [<] (const ())
unsatTerm = match KUnsat

mainTerm : Parser () String SMTToken False [<] [<] (const (SMTResult sys f))
mainTerm = (\case
  Left x          => Sat x
  Right (Left _)  => Unsat
  Right (Right _) => Unknown)
  <$> (satTerm <||> (unsatTerm <||> unknownTerm))
