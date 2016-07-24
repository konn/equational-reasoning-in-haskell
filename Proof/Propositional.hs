{-# LANGUAGE DataKinds, EmptyCase, ExplicitForAll, ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances, GADTs, KindSignatures, PolyKinds      #-}
{-# LANGUAGE TemplateHaskell, TypeOperators                           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Provides type synonyms for logical connectives.
module Proof.Propositional
       ( type (/\), type (\/), Not, exfalso, orIntroL
       , orIntroR, orElim, andIntro, andElimL
       , andElimR, orAssocL, orAssocR
       , andAssocL, andAssocR, IsTrue(..)
       ) where
import Data.Void

type a /\ b = (a, b)
type a \/ b = Either a b
type Not a  = a -> Void

infixr 2 \/
infixr 3 /\

exfalso :: a -> Not a -> b
exfalso a neg = absurd (neg a)

orIntroL :: a -> a \/ b
orIntroL = Left

orIntroR :: b -> a \/ b
orIntroR = Right

orElim :: a \/ b -> (a -> c) -> (b -> c) -> c
orElim aORb aTOc bTOc = either aTOc bTOc aORb

andIntro :: a -> b -> a /\ b
andIntro = (,)

andElimL :: a /\ b -> a
andElimL = fst

andElimR :: a /\ b -> b
andElimR = snd

andAssocL :: a /\ (b /\ c) -> (a /\ b) /\ c
andAssocL (a,(b,c)) = ((a,b), c)

andAssocR :: (a /\ b) /\ c -> a /\ (b /\ c)
andAssocR ((a,b),c) = (a,(b,c))

orAssocL :: a \/ (b \/ c) -> (a \/ b) \/ c
orAssocL (Left a)          = Left (Left a)
orAssocL (Right (Left b))  = Left (Right b)
orAssocL (Right (Right c)) = Right c

orAssocR :: (a \/ b) \/ c -> a \/ (b \/ c)
orAssocR (Left (Left a))  = Left a
orAssocR (Left (Right b)) = Right (Left b)
orAssocR (Right c)        = Right (Right c)


-- | Utility type to convert type-level (@'Bool'@-valued) predicate function
--   into concrete witness data-type.
data IsTrue (b :: Bool) where
  Witness :: IsTrue 'True

