{-# LANGUAGE CPP, PatternSynonyms, TemplateHaskell, ViewPatterns #-}
{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
module Proof.Internal.THCompat where
import Language.Haskell.TH
import Language.Haskell.TH.Extras

import GHC.Exts (Constraint)

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 802
import GHC.Generics
import Data.Data
#endif

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 802
data DerivClause = DerivClause (Maybe DerivStrategy) Cxt
                 deriving (Eq, Data, Ord, Show, Generic)
data  DerivStrategy = StockStrategy
                    | AnyclassStrategy
                    | NewtypeStrategy
                    deriving (Eq, Data, Ord, Show, Generic)
#endif

dcToNames :: DerivClause -> [Name]
dcToNames (DerivClause _ ct) = map headOfType ct

dcToCxt :: DerivClause -> Cxt
dcToCxt (DerivClause _ ct) = ct


mkDataD :: Cxt -> Name -> [TyVarBndr] -> [Con] -> [DerivClause] -> Dec
mkDataD ctx name tvbndrs cons dc =
  DataD ctx name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        Nothing cons 
#if __GLASGOW_HASKELL__ < 802
        (concatMap dcToCxt dc)
#else
        dc
#endif
#else
        cons (concatMap dcToNames dc)
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

pattern DataDCompat :: Cxt -> Name -> [TyVarBndr] -> [Con] -> [DerivClause] -> Dec
pattern DataDCompat ctx name tvbndrs cons dcs <-
  DataD ctx name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        _ cons 
#if __GLASGOW_HASKELL__ < 802
        (pure . DerivClause Nothing -> dcs)
#else 
        dcs
#endif
#else
        cons (DerivClause Nothing . map ConT -> dc)
#endif

pattern NewtypeDCompat :: Cxt -> Name -> [TyVarBndr] -> Con -> [DerivClause] -> Dec
pattern NewtypeDCompat ctx name tvbndrs con dcs <-
  NewtypeD ctx name tvbndrs
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
        _ con
#if __GLASGOW_HASKELL__ < 802
        (pure . DerivClause Nothing -> dcs)
#else
        dcs
#endif
#else
        con
        (DerivClause Nothing . map ConT -> dcs)
#endif
