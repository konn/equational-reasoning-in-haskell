{-# LANGUAGE CPP, PatternSynonyms, TemplateHaskell, ViewPatterns #-}
module Proof.Internal.THCompat where
import Language.Haskell.TH

import GHC.Exts (Constraint)

mkDataD :: Cxt -> Name -> [TyVarBndr] -> [Con] -> [Name] -> Dec
mkDataD ctx name tvbndrs cons names =
  DataD ctx name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        Nothing cons (map ConT names)
#else
        cons names
#endif


typeName :: Type -> Name
typeName (VarT n) = n
typeName (ConT n) = n
typeName (PromotedT n) = n
typeName (TupleT n) = tupleTypeName n
typeName (UnboxedTupleT n) = unboxedTupleTypeName n
typeName ArrowT = ''(->)
typeName EqualityT = ''(~)
typeName ListT = ''[]
typeName (PromotedTupleT n) = tupleDataName n
typeName PromotedNilT = '[]
typeName PromotedConsT = '(:)
typeName ConstraintT = ''Constraint
typeName _ = error "No names!"

pattern DataDCompat ctx name tvbndrs cons names <-
  DataD ctx name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        _ cons (map typeName -> names)
#else
        cons names
#endif

pattern NewtypeDCompat ctx name tvbndrs con names <-
  NewtypeD ctx name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        _ con (map typeName -> names)
#else
        con names
#endif
