{-# LANGUAGE DataKinds, DeriveDataTypeable, EmptyCase, ExplicitForAll     #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleInstances, GADTs, KindSignatures #-}
{-# LANGUAGE LambdaCase, PolyKinds, StandaloneDeriving, TemplateHaskell   #-}
{-# LANGUAGE TypeOperators                                                #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Provides type synonyms for logical connectives.
module Proof.Propositional
       ( type (/\), type (\/), Not, exfalso, orIntroL
       , orIntroR, orElim, andIntro, andElimL
       , andElimR, orAssocL, orAssocR
       , andAssocL, andAssocR, IsTrue(..)
       , Empty(..), withEmpty, withEmpty'
       , refute
       , Inhabited (..), withInhabited
       , prove
       ) where
import Proof.Propositional.Empty
import Proof.Propositional.Inhabited
import Proof.Propositional.TH

import Data.Data          (Data)
import Data.Type.Equality ((:~:))
import Data.Typeable      (Typeable)
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

deriving instance Show (IsTrue b)
deriving instance Eq   (IsTrue b)
deriving instance Ord  (IsTrue b)
deriving instance Read (IsTrue 'True)
deriving instance Typeable IsTrue
deriving instance Data (IsTrue 'True)

instance {-# OVERLAPPABLE #-} (Inhabited a, Empty b) => Empty (a -> b) where
  eliminate f = eliminate (f trivial)

refute [t| 0 :~: 1 |]
refute [t| () :~: Int |]

prove [t| Bool |]
prove [t| Int |]
prove [t| Integer |]
prove [t| Word |]
prove [t| Double |]
prove [t| Float |]
prove [t| Char |]
prove [t| Ordering |]
prove [t| forall a. [a] |]
prove [t| Rational |]
prove [t| forall a. Maybe a |]
prove [t| forall n. n :~: n |]
prove [t| IsTrue 'True |]

instance Empty (IsTrue 'False) where
  eliminate = \ case {}
