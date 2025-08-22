module Language.SMT.Combinator.Shift

import Language.SMT.Serialise
import Language.SMT.SerialiseAlg
import Language.SMT.Names

import MAST.Core
import MAST.Substitution
import MAST.Signature

import public MAST.Combinator.Shift

public export
ShiftSerialise : (ctx' : b.Ctx) -> Names ctx' -> (ctx' .|>).SerialiseAlgebra
ShiftSerialise ctx' nctx' = MkSerialiseAlgebra
  (\(dtx ** (ndtx, s, ren)) =>
    ((filterA (label dtx ren)).context **
      (filterNames ndtx (label dtx ren)
      , \ns =>
          let mangled = mangleGlobalInScope nctx' ns
              mangledNdtx = combineNames ns (findBoundNames mangled)
          in s mangledNdtx
      , (filterA (label dtx ren)).label
      )
    )
  )
