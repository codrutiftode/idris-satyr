module Language.SMT.Combinator.Shift

import Data.List.Quantifiers
import Data.SnocList.Quantifiers
import Data.Singleton
import Data.DPair

import Language.SMT.Serialise
import Language.SMT.SerialiseAlg
import Language.SMT.Names

import MAST.Core
import MAST.Substitution
import MAST.Signature

import public MAST.Combinator.Shift

import Language.SMT.Combinator.List.Quantifiers

public export
AllShiftSerialise :
  {ctxs : List (sort.Ctx)} ->
  (All (.SerialiseAlgebra) (map (.|>) ctxs)) ->
  (All (map (.|>) ctxs)).SerialiseAlgebra

public export
ShiftSerialise : (ctx' : b.Ctx) ->
  Names ctx' ->
  (Singleton ctx' -> Names ctx' -> String -> String) ->
  (ctx' .|>).SerialiseAlgebra
ShiftSerialise ctx' nctx' toStr = MkSerialiseAlgebra
  (\(dtx ** (ndtx, s, ren)) =>
    ((filterA (label dtx ren)).context **
      (filterNames ndtx (label dtx ren)
      , \ns =>
          let mangled = mangleGlobalInScope nctx' ns
              mangledNdtx = combineNames ns (findBoundNames mangled)
          in toStr (Val ctx') mangled (s mangledNdtx)
      , (filterA (label dtx ren)).label
      )
    )
  )
