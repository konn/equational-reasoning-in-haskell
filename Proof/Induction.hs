{-# LANGUAGE DataKinds, ExplicitNamespaces, FlexibleContexts, GADTs #-}
{-# LANGUAGE PolyKinds, RankNTypes, TemplateHaskell, TypeFamilies   #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, ViewPatterns      #-}
module Proof.Induction (genInduction) where
import Proof.Internal.THCompat

import Control.Monad           (forM, replicateM)
import Data.Either             (rights)
import Data.Singletons         (Sing)
import Language.Haskell.TH     (Clause, Con (ForallC, InfixC, NormalC, RecC))
import Language.Haskell.TH     (TypeQ, appT, appT, appsE, appsE, arrowT, arrowT)
import Language.Haskell.TH     (clause, clause, conP, conP, cxt, cxt, forallT)
import Language.Haskell.TH     (funD, funD, mkName, nameBase, newName)
import Language.Haskell.TH     (normalB, normalB, promotedT, promotedT, reify)
import Language.Haskell.TH     (sigD, sigD, varE, varE, varP, varP, varT, varT)
import Language.Haskell.TH     (Dec, Info (TyConI), Name, Q)
import Language.Haskell.TH     (Type (AppT, ConT, PromotedT, SigT))
import Language.Haskell.TH.Lib (plainTV)

-- | @genInduction ''Type "inductionT"@ defines the induction scheme for @Type@ named @inductionT@.
genInduction :: Name -> String -> Q [Dec]
genInduction typ fname0 = do
  let fname = mkName fname0
  TyConI (normalizeDec -> DataDCompat _ dName _ dCons _) <- reify typ
  p <- newName "p"
  ans <- mapM (buildCase fname (length dCons) dName p) $ zip [0..] dCons
  let (cls, ts) = unzip ans
  t <- newName "t"
  sig <- sigD fname $ forallT [plainTV p, plainTV t] (cxt []) $
           foldr toT ([t| Sing $(varT t) -> $(varT p) $(varT t) |]) $ map return ts
  dec <- funD fname (map return cls)
  return [sig, dec]

buildCase :: Name -> Int -> Name -> Name -> (Int, Con) -> Q (Clause, Type)
buildCase _ _ _ _ (_, ForallC _ _ _) = error "Existential types are not supported yet."
buildCase fname size dName p (nth, dCon) = do
  let paramTs = extractParams dCon
      conName = extractName dCon
      sName = mkName $ 'S' : nameBase conName
      ssName = mkName $ 's' : nameBase conName
  eparams <- forM paramTs $ \ty ->
    case getTyConName ty of
      Just nm | nm == dName -> Right <$> newName "t"
      _       -> Left <$> newName "a"
  xs <- replicateM (length paramTs) $ newName "x"
  let subCases = [[t| Sing $(varT t) -> $(varT p) $(varT t) |] | t <- rights eparams ]
  params <- mapM (either varT varT) eparams
  let promCon = foldl appT (promotedT conName) (map return params)
      tbdy | null subCases = foldr toT ([t| $(varT p `appT` promCon) |]) subCases
           | otherwise   = foldr toT ([t| Sing $(promCon) -> $(varT p `appT` promCon) |]) subCases
  sig <- if null params then tbdy else forallT (map (either plainTV plainTV) eparams) (cxt []) tbdy
  cs <- replicateM size $ newName "case"
  let body | null subCases = varE (cs !! nth)
           | otherwise = appsE $ varE (cs !! nth) :
               replicate (length subCases) (appsE $ varE fname : map varE cs)
               ++ [ appsE (varE ssName : map varE xs)]
  cl <- clause (map varP cs ++ [conP sName $ map varP xs]) (normalB body) []
  return (cl, sig)
  where
    extractName (NormalC n _)  = n
    extractName (RecC n _)     = n
    extractName (InfixC _ n _) = n
    extractName _              = error "I don't know name!"
    extractParams (NormalC _ sts)          = map snd sts
    extractParams (RecC _ vsts)            = map (\(_,_,c) -> c) vsts
    extractParams (InfixC (_, t) _ (_, s)) = [t,s]
    extractParams _                        = []

toT :: TypeQ -> TypeQ -> TypeQ
a `toT` b = arrowT `appT` a `appT` b

getTyConName :: Type -> Maybe Name
getTyConName (AppT a _)    = getTyConName a
getTyConName (SigT a _)    = getTyConName a
getTyConName (ConT nam)    = Just nam
getTyConName (PromotedT n) = Just n
getTyConName _             = Nothing

normalizeDec :: Dec -> Dec
normalizeDec d@DataDCompat {} = d
normalizeDec (NewtypeDCompat ctx name tvbs con names) = mkDataD ctx name tvbs [con] names
normalizeDec _ = error "not data definition."
