{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Proof.Propositional.Empty (Empty (..), withEmpty, withEmpty') where

import Data.Void (Void, absurd)
import GHC.Generics
import Unsafe.Coerce (unsafeCoerce)

{- | Type-class for types without inhabitants, dual to @'Proof.Propositional.Inhabited'@.
  Current GHC doesn't provide selective-instance,
  hence we don't @'Empty'@ provide instances
  for product types in a generic deriving (DeriveAnyClass).

  To derive an instance for each concrete types,
  use @'Proof.Propositional.refute'@.

  Since 0.4.0.0.
-}
class Empty a where
  eliminate :: a -> x
  default eliminate :: (Generic a, GEmpty (Rep a)) => a -> x
  eliminate = geliminate . from

class GEmpty f where
  geliminate :: f a -> x

instance (GEmpty f) => GEmpty (M1 i t f) where
  geliminate (M1 a) = geliminate a

instance (GEmpty f, GEmpty g) => GEmpty (f :+: g) where
  geliminate (L1 a) = geliminate a
  geliminate (R1 b) = geliminate b

instance (Empty c) => GEmpty (K1 i c) where
  geliminate (K1 a) = eliminate a

instance GEmpty V1 where
  geliminate = \case {}

deriving instance (Empty a, Empty b) => Empty (Either a b)

deriving instance Empty Void

newtype MagicEmpty e a = MagicEmpty ((Empty e) => a)

{- | Giving falsity witness by proving @'Void'@ from @a@.
  See also 'withEmpty''.

  Since 0.4.0.0
-}
withEmpty :: forall a b. (a -> Void) -> ((Empty a) => b) -> b
withEmpty neg k = unsafeCoerce (MagicEmpty k :: MagicEmpty a b) (absurd . neg)

{- | Giving falsity witness by showing @a@ entails everything.
  See also 'withEmpty'.

  Since 0.4.0.0
-}
withEmpty' :: forall a b. (forall c. a -> c) -> ((Empty a) => b) -> b
withEmpty' neg k = unsafeCoerce (MagicEmpty k :: MagicEmpty a b) neg
