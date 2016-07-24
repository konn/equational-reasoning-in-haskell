{-# LANGUAGE CPP, PatternSynonyms #-}
module Proof.Internal.THCompat where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

mkDataD :: Cxt -> Name -> [TyVarBndr] -> [Con] -> [Name] -> Dec
mkDataD cxt name tvbndrs cons names =
  DataD cxt name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        Nothing
#endif
        cons names

pattern DataDCompat cxt name tvbndrs cons names =
  DataD cxt name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        _
#endif
        cons names

pattern NewtypeDCompat cxt name tvbndrs con names =
  NewtypeD cxt name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        _
#endif
        con names
