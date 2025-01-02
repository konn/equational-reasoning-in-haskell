{-# LANGUAGE CPP #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module Proof.Propositional.TH where

import Control.Arrow (Kleisli (..), second)
import Control.Monad (forM, zipWithM)
import Data.Foldable (asum)
import Data.Functor (void)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Type.Equality ((:~:) (..))
import Language.Haskell.TH (
  DecsQ,
  Lit (CharL, IntegerL),
  Name,
  Q,
  TypeQ,
  isInstance,
  newName,
  ppr,
 )
import Language.Haskell.TH.Desugar (DClause (..), DCon (..), DConFields (..), DCxt, DDec (..), DExp (..), DForallTelescope (..), DInfo (..), DLetDec (DFunD), DPat (DConP, DVarP), DPred, DTyVarBndr (..), DType (..), Overlap (Overlapping), desugar, dsReify, expandType, substTy, sweeten)
import Proof.Propositional.Empty
import Proof.Propositional.Inhabited

#if MIN_VERSION_th_desugar(1,18,0)
import Language.Haskell.TH.Desugar (dLamE, dCaseE)
#else
import Language.Haskell.TH.Desugar (DMatch)
#endif

mkDInstanceD ::
  Maybe Overlap ->
  DCxt ->
  DType ->
  [DDec] ->
  DDec
mkDInstanceD ovl ctx dtype ddecs = DInstanceD ovl Nothing ctx dtype ddecs

{- | Macro to automatically derive @'Empty'@ instance for
  concrete (variable-free) types which may contain products.
-}
refute :: TypeQ -> DecsQ
refute tps = do
  tp <- expandType =<< desugar =<< tps
  let Just (_, tyName, args) = splitType tp
      mkInst dxt cls =
        return $
          sweeten
            [ mkDInstanceD
                (Just Overlapping)
                dxt
                (DAppT (DConT ''Empty) (foldl DAppT (DConT tyName) args))
                [DLetDec $ DFunD 'eliminate cls]
            ]
  if tyName == ''(:~:)
    then do
      let [l, r] = args
      v <- newName "_v"
      dist <- compareType l r
      case dist of
        NonEqual -> mkInst [] [DClause [] $ dLamE' [v] (dCaseE (DVarE v) [])]
        Equal -> fail $ "Equal: " ++ show (ppr $ sweeten l) ++ " ~ " ++ show (ppr $ sweeten r)
        Undecidable ->
          fail $
            "No enough info to check non-equality: "
              ++ show (ppr $ sweeten l)
              ++ " ~ "
              ++ show (ppr $ sweeten r)
    else do
      (dxt, cons) <- resolveSubsts args . fromJust =<< dsReify tyName
      Just cls <- sequence <$> mapM buildRefuteClause cons
      mkInst dxt cls

#if !MIN_VERSION_th_desugar(1,18,0)
dCaseE :: DExp -> [DMatch] -> DExp
dCaseE = DCaseE
#endif

dLamE' :: [Name] -> DExp -> DExp
#if MIN_VERSION_th_desugar(1,18,0)
dLamE' = dLamE . map DVarP
#else
dLamE' = DLamE
#endif

{- | Macro to automatically derive @'Inhabited'@ instance for
  concrete (variable-free) types which may contain sums.
-}
prove :: TypeQ -> DecsQ
prove tps = do
  tp <- expandType =<< desugar =<< tps
  let Just (_, tyName, args) = splitType tp
      mkInst dxt cls =
        return $
          sweeten
            [ mkDInstanceD
                (Just Overlapping)
                dxt
                (DAppT (DConT ''Inhabited) (foldl DAppT (DConT tyName) args))
                [DLetDec $ DFunD 'trivial cls]
            ]
  isNum <- isInstance ''Num [sweeten tp]

  if
    | isNum -> mkInst [] [DClause [] $ DLitE $ IntegerL 0]
    | tyName == ''Char -> mkInst [] [DClause [] $ DLitE $ CharL '\NUL']
    | tyName == ''(:~:) -> do
        let [l, r] = args
        dist <- compareType l r
        case dist of
          NonEqual -> fail $ "Equal: " ++ show (ppr $ sweeten l) ++ " ~ " ++ show (ppr $ sweeten r)
          Equal -> mkInst [] [DClause [] $ DConE 'Refl]
          Undecidable ->
            fail $
              "No enough info to check non-equality: "
                ++ show (ppr $ sweeten l)
                ++ " ~ "
                ++ show (ppr $ sweeten r)
    | otherwise -> do
        (dxt, cons) <- resolveSubsts args . fromJust =<< dsReify tyName
        Just cls <- asum <$> mapM buildProveClause cons
        mkInst dxt [cls]

buildClause ::
  Name ->
  (DType -> Q b) ->
  (DType -> b -> DExp) ->
  (Name -> [Maybe DExp] -> Maybe DExp) ->
  (Name -> [b] -> [DPat]) ->
  DCon ->
  Q (Maybe DClause)
buildClause clsName genPlaceHolder buildFactor flattenExps toPats (DCon _ _ cName flds _) = do
  let tys = fieldsVars flds
  varDic <- mapM genPlaceHolder tys
  fmap (DClause $ toPats cName varDic) . flattenExps cName <$> zipWithM tryProc tys varDic
  where
    tryProc ty name = do
      isEmpty <- isInstance clsName . (: []) $ sweeten ty
      return $
        if isEmpty
          then Just $ buildFactor ty name
          else Nothing

buildRefuteClause :: DCon -> Q (Maybe DClause)
buildRefuteClause =
  buildClause
    ''Empty
    (const $ newName "_x")
    (const $ (DVarE 'eliminate `DAppE`) . DVarE)
    (const asum)
    (\cName ps -> [DConP cName [] $ map DVarP ps])

buildProveClause :: DCon -> Q (Maybe DClause)
buildProveClause =
  buildClause
    ''Inhabited
    (const $ return ())
    (const $ const $ DVarE 'trivial)
    (\con args -> foldl DAppE (DConE con) <$> sequence args)
    (const $ const [])

fieldsVars :: DConFields -> [DType]
fieldsVars (DNormalC _ fs) = map snd fs
fieldsVars (DRecC fs) = map (\(_, _, c) -> c) fs

resolveSubsts :: [DType] -> DInfo -> Q (DCxt, [DCon])
resolveSubsts args info =
  case info of
    DTyConI (DDataD _ cxt _ tvbs _ dcons _) _ -> do
      let dic = M.fromList $ zip (map dtvbToName tvbs) args
      (cxt,) <$> mapM (substDCon dic) dcons
    -- (DTyConI (DOpenTypeFamilyD n) _) ->  return []
    -- (DTyConI (DClosedTypeFamilyD _ ddec2) minst) ->  return []
    -- (DTyConI (DDataFamilyD _ ddec2) minst) ->  return []
    -- (DTyConI (DDataInstD _ ddec2 ddec3 ddec4 ddec5 ddec6) minst) ->  return []
    (DTyConI _ _) -> fail "Not supported data ty"
    _ -> fail "Please pass data-type"

type SubstDic = Map Name DType

substDCon :: SubstDic -> DCon -> Q DCon
substDCon dic (DCon forall'd cxt conName fields mPhantom) =
  DCon forall'd cxt conName
    <$> substFields dic fields
    <*> substTy dic mPhantom

substFields :: SubstDic -> DConFields -> Q DConFields
substFields
  subst
  (DNormalC fixi fs) =
    DNormalC fixi
      <$> mapM (runKleisli $ second $ Kleisli $ substTy subst) fs
substFields subst (DRecC fs) =
  DRecC <$> forM fs (\(a, b, c) -> (a,b,) <$> substTy subst c)

splitType :: DType -> Maybe ([Name], Name, [DType])
splitType (DConstrainedT _ t) = splitType t
splitType (DForallT (unTelescope -> vs) t) =
  (\(a, b, c) -> (map dtvbToName vs ++ a, b, c)) <$> splitType t
splitType (DAppT t1 t2) = (\(a, b, c) -> (a, b, c ++ [t2])) <$> splitType t1
splitType (DSigT t _) = splitType t
splitType (DVarT _) = Nothing
splitType (DConT n) = Just ([], n, [])
splitType DArrowT = Just ([], ''(->), [])
splitType (DLitT _) = Nothing
splitType DWildCardT = Nothing
splitType (DAppKindT _ _) = Nothing

data EqlJudge = NonEqual | Undecidable | Equal
  deriving (Read, Show, Eq, Ord)

instance Semigroup EqlJudge where
  NonEqual <> _ = NonEqual
  Undecidable <> NonEqual = NonEqual
  Undecidable <> _ = Undecidable
  Equal <> m = m

instance Monoid EqlJudge where
  mappend = (<>)
  mempty = Equal

compareType :: DType -> DType -> Q EqlJudge
compareType t0 s0 = do
  t <- expandType t0
  s <- expandType s0
  compareType' t s

compareType' :: DType -> DType -> Q EqlJudge
compareType' (DSigT t1 t2) (DSigT s1 s2) =
  (<>) <$> compareType' t1 s1 <*> compareType' t2 s2
compareType' (DSigT t _) s =
  compareType' t s
compareType' t (DSigT s _) =
  compareType' t s
compareType' (DVarT t) (DVarT s)
  | t == s = return Equal
  | otherwise = return Undecidable
compareType' (DVarT _) _ = return Undecidable
compareType' _ (DVarT _) = return Undecidable
compareType' DWildCardT _ = return Undecidable
compareType' _ DWildCardT = return Undecidable
compareType' (DConstrainedT tCxt t) (DConstrainedT sCxt s) = do
  pd <- compareCxt tCxt sCxt
  bd <- compareType' t s
  return (pd <> bd)
compareType' DConstrainedT {} _ = return NonEqual
compareType' (DForallT (unTelescope -> tTvBs) t) (DForallT (unTelescope -> sTvBs) s)
  | length tTvBs == length sTvBs = do
      let dic = M.fromList $ zip (map dtvbToName sTvBs) (map (DVarT . dtvbToName) tTvBs)
      s' <- substTy dic s
      bd <- compareType' t s'
      return bd
  | otherwise = return NonEqual
compareType' DForallT {} _ = return NonEqual
compareType' (DAppT t1 t2) (DAppT s1 s2) =
  (<>) <$> compareType' t1 s1 <*> compareType' t2 s2
compareType' (DConT t) (DConT s)
  | t == s = return Equal
  | otherwise = return NonEqual
compareType' (DConT _) _ = return NonEqual
compareType' DArrowT DArrowT = return Equal
compareType' DArrowT _ = return NonEqual
compareType' (DLitT t) (DLitT s)
  | t == s = return Equal
  | otherwise = return NonEqual
compareType' (DLitT _) _ = return NonEqual
compareType' _ _ = return NonEqual

compareCxt :: DCxt -> DCxt -> Q EqlJudge
compareCxt l r = mconcat <$> zipWithM comparePred l r

comparePred :: DPred -> DPred -> Q EqlJudge
comparePred DWildCardT _ = return Undecidable
comparePred _ DWildCardT = return Undecidable
comparePred (DVarT l) (DVarT r)
  | l == r = return Equal
comparePred (DVarT _) _ = return Undecidable
comparePred _ (DVarT _) = return Undecidable
comparePred (DSigT l t) (DSigT r s) =
  (<>) <$> compareType' t s <*> comparePred l r
comparePred (DSigT l _) r = comparePred l r
comparePred l (DSigT r _) = comparePred l r
comparePred (DAppT l1 l2) (DAppT r1 r2) = do
  l2' <- expandType l2
  r2' <- expandType r2
  (<>) <$> comparePred l1 r1 <*> compareType' l2' r2'
comparePred (DAppT _ _) _ = return NonEqual
comparePred (DConT l) (DConT r)
  | l == r = return Equal
  | otherwise = return NonEqual
comparePred (DConT _) _ = return NonEqual
comparePred (DForallT _ _) (DForallT _ _) = return Undecidable
comparePred (DForallT {}) _ = return NonEqual
comparePred _ _ = fail "Kind error: Expecting type-level predicate"

substPred :: SubstDic -> DPred -> Q DPred
substPred dic (DAppT p1 p2) = DAppT <$> substPred dic p1 <*> (expandType =<< substTy dic p2)
substPred dic (DSigT p knd) = DSigT <$> substPred dic p <*> (expandType =<< substTy dic knd)
substPred dic prd@(DVarT p)
  | Just (DVarT t) <- M.lookup p dic = return $ DVarT t
  | Just (DConT t) <- M.lookup p dic = return $ DConT t
  | otherwise = return prd
substPred _ t = return t

dtvbToName :: DTyVarBndr flag -> Name
dtvbToName (DPlainTV n _) = n
dtvbToName (DKindedTV n _ _) = n

unTelescope :: DForallTelescope -> [DTyVarBndr ()]
unTelescope (DForallVis vis) = map void vis
unTelescope (DForallInvis vis) = map void vis
