module Language.SMT.Lexer

import Text.Lexer

public export
data SMTToken =
    LB
  | RB
  | Name
  | Number
  | Space
  | KSat
  | KUnsat
  | KUnknown
  | KDefFun
  | KForall
  | KLet
  | KExists

public export
toNat : SMTToken -> Nat
toNat LB       = 0
toNat RB       = 1
toNat Name     = 2
toNat Number   = 3
toNat Space    = 4
toNat KUnsat   = 5
toNat KSat     = 6
toNat KUnknown = 7
toNat KDefFun  = 8
toNat KForall  = 9
toNat KLet     = 10
toNat KExists  = 11

public export
Eq SMTToken where
  k1 == k2 = toNat k1 == toNat k2

public export
TokenKind SMTToken where
  TokType Name   = String
  TokType Number = Int
  TokType _      = ()

  tokValue LB       = const ()
  tokValue RB       = const ()
  tokValue Name     = id
  tokValue Number   = cast
  tokValue Space    = const ()
  tokValue KUnsat   = const ()
  tokValue KSat     = const ()
  tokValue KUnknown = const ()
  tokValue KDefFun  = const ()
  tokValue KForall  = const ()
  tokValue KLet     = const ()
  tokValue KExists  = const ()

-- Lexer
isPara : Char -> Bool
isPara x = x == '(' || x == ')'

nameLexer : Lexer
nameLexer = some $ pred (\x => not (isSpace x || isPara x))

public export
tokenMap : TokenMap (Token SMTToken)
tokenMap = toTokenMap
           [(is '(', LB),
            (is ')', RB),
            (exact "define-fun", KDefFun),
            (exact "let", KLet),
            (exact "forall", KForall),
            (exact "exists", KExists),
            (exact "sat", KSat),
            (exact "unsat", KUnsat),
            (exact "unknown", KUnknown),
            (digits, Number),
            (nameLexer, Name),
            (space <|> newline, Space)]

public export
filterSpaces : List (WithBounds (Token SMTToken)) ->
               List (WithBounds (Token SMTToken))
filterSpaces = filter (\x => x.val.kind /= Space)

public export
lex : String -> List (WithBounds $ Token SMTToken)
lex = filterSpaces . fst . lex tokenMap
