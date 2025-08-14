module Language.SMT.Parser

import Language.SMT.Lexer

import Decidable.Equality

import Flap.Parser
import MAST.Core
import MAST.Initiality
import MAST.Signature
import MAST.Substitution

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

data (.varNamePos) : type.Ctx -> (x : String) -> Type where
  Done  : [<].varNamePos x
  Keep  : ctx.varNamePos x -> (ctx :< (x :- s)).varNamePos x
  Drop  : ctx.varNamePos x -> (ctx :< (x' :- s)).varNamePos x

Vars : (name : String) -> sort.Family
Vars = flip (.varNamePos)

data RawTerm : (sys : SortingSystemOver fstSort sndSort both) ->
  sys.RSortedFamilyFun -> sys.Fst.Ctx -> Type where
  Var : (name : String) -> Vars name -||> RawTerm sys o
  Op  : o (const $ RawTerm sys o) () -||> RawTerm sys o

-- Note: should this be moved to MAST?
record (.RPointedFamily) (sys : SortingSystemOver fstSort sndSort sort) where
  constructor MkRPointedSortedFamily
  fam : sys.RFamily
  point : (name : String) -> Vars name -||> fam

public export
record Function (sys : SortingSystemOver fstSort sndSort sort)
  (fam : sys.RFamily) where
  constructor MkFunction
  ret : sort
  ctx : fstSort.Ctx
  body : fam ctx

public export
SatAssignment : (sys : SortingSystemOver fstSort sndSort sort) ->
  (f : sys.RFamily) -> Type
SatAssignment sys f = List (String, Function sys f)

public export
data SMTResult : (sys : SortingSystemOver fstSort sndSort sort) ->
  (f : sys.RFamily) -> Type where
  Sat : SatAssignment sys f -> SMTResult sys f
  Unsat, Unknown : SMTResult sys f

public export
record (.ParserState) (sys : SortingSystemOver fstSort sndSort sort) where
  constructor MkParserState
  ret : sort
  ctx : fstSort.Ctx
  names : PS ctx
  decEq : DecEq fstSort

0
(.ParserExpr) : (sys : SortingSystemOver fstSort sndSort sort) -> Type
sys.ParserExpr = sys.RPointedFamily -> sys.ParserState -> Type

ParsedTerm : sys.ParserExpr
ParsedTerm f s = f.fam s.ctx

0
ParsedSort : sys.ParserExpr
ParsedSort f s = sys.Sort

0
ParserTy : (sys : SortingSystemOver fstSort sndSort sort) ->
  (locked : SnocList (String, sys.ParserExpr)) ->
  (0 return : sys.ParserExpr) ->
  Type
ParserTy sys locked return =
  {f : sys.RPointedFamily} ->
  Parser (sys.ParserState) String SMTToken False
    (map (\(name, expr) => name :- (False, (\s => expr f s))) locked)
    [<]
    (return f)

0
TermParser : (sys : SortingSystemOver fstSort sndSort sort) ->
  (locked : SnocList (String, sys.ParserExpr)) ->
  Type
TermParser sys locked = ParserTy sys locked ParsedTerm

getVar : (ctx : sort.Ctx) -> PS ctx -> (name : String) -> Maybe (Vars name ctx)
getVar [<] Z name = Nothing
getVar (ctx :< (_ :- ty)) (S {str = name'} names) name =
  case decEq name name' of
    (Yes Refl) => Just (Keep !(getVar ctx names name))
    (No  _)    => Just (Drop !(getVar ctx names name))

asVar : (f : sys.RPointedFamily) ->
  {s : sys.ParserState} ->
  String ->
  Either String (f.fam s.ctx)
asVar f name = case (getVar s.ctx s.names name) of
  Nothing  => Left "Variable \{name} out of scope."
  (Just v) => Right $ f.point name v

atomicTerm : TermParser sys [<("open", ParsedTerm)]
atomicTerm =
  OneOf
  [ Map (asVar f) (match Name)
  , enclose (match LB) (match RB) (Var $ %%% "open")
  ]

-- sortExpr : ParserTy sys [<("sort", (const $ const sys.Sort))] (const $ const sys.Sort)

sortedVarExpr : ParserTy sys [<] (const $ const (String, sys.Fst))

toCtx : (sx : SnocList (String, sys.Fst)) -> sys.Fst.Ctx
toCtx [<] = [<]
toCtx (sx :< x) = toCtx {sys} sx :< (fst x :- snd x)

getNames : (sx : SnocList (String, sys.Fst)) -> PS (toCtx {sys} sx)
getNames [<] = Z
getNames (sx :< x) = S {str = fst x} (getNames sx)

updateState : sys .ParserState ->
  (newCtx : List (String, sys.Fst)) ->
  (newRet : sys.Sort) ->
  sys .ParserState
updateState prev newCtx newRet = MkParserState
  { ret = newRet
  , ctx = toCtx {sys} (cast newCtx)
  , names = getNames (cast newCtx)
  , decEq = prev.decEq
  }

0
GlobalVars : SnocList (String, sys.ParserExpr)
GlobalVars = [<("body", ParsedTerm), ("sort", ParsedSort)]

defineFunExpr : ParserTy sys GlobalVars (\f,s => (String, Function sys f.fam))
defineFunExpr =
  (\([((name, args), ret), body]) =>
    (name, MkFunction ret (toCtx {sys} (cast args)) body))
  <$> (enclose (match LB) (match RB)
        (match KDefFun *>
          (Seq (Update
            (match Name
            <**> (enclose (match LB) (match RB)
                   (star (rename Id (Drop (Drop Id)) (sortedVarExpr {f}))))
            <**> (Var $ %%% "sort"))
            (Just (\prev => \((name, ctx), ret) => updateState prev ctx ret))
            [Var $ %%% "body"])
          )
        )
      )

satTerm : ParserTy sys GlobalVars (\f => const (SatAssignment sys f.fam))
satTerm = match KSat *>
  enclose (match LB) (match RB) (star (weaken (S (S Z)) defineFunExpr))

unknownTerm : ParserTy sys GlobalVars (const $ const ())
unknownTerm = match KUnknown

unsatTerm : ParserTy sys GlobalVars (const $ const ())
unsatTerm = match KUnsat

mainTerm : ParserTy sys GlobalVars (\f => const (SMTResult sys f.fam))
mainTerm = (\case
  Left x          => Sat x
  Right (Left _)  => Unsat
  Right (Right _) => Unknown)
  <$> (satTerm <||> (unsatTerm <||> unknownTerm))
