{-# LANGUAGE DataKinds, DefaultSignatures, DeriveAnyClass, EmptyCase #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GADTs, KindSignatures, LambdaCase, PolyKinds            #-}
{-# LANGUAGE StandaloneDeriving, TupleSections, TypeOperators        #-}
module Proof.Propositional.Inhabited where
import GHC.Generics

-- | Types with at least one inhabitant, dual to @'Proof.Propositional.Empty'@.
-- | Current GHC doesn't provide selective-instance,
--   hence we don't @'Empty'@ provide instances
--   for sum types in a generic deriving (DeriveAnyClass).
--
--   To derive an instance for each concrete types,
--   use @'Proof.Propositional.prove'@.
--
--   Since 0.4.0.0.
class Inhabited a where
  trivial :: a

  default trivial :: (Generic a, GInhabited (Rep a)) => a
  trivial = to gtrivial

class GInhabited f where
  gtrivial :: f a

instance GInhabited f => GInhabited (M1 i t f) where
  gtrivial = M1 gtrivial

instance (GInhabited f, GInhabited g) => GInhabited (f :*: g) where
  gtrivial = gtrivial :*: gtrivial

instance Inhabited c => GInhabited (K1 i c) where
  gtrivial = K1 trivial

instance GInhabited U1 where
  gtrivial = U1

deriving instance Inhabited ()
deriving instance (Inhabited a, Inhabited b) => Inhabited (a, b)
deriving instance (Inhabited a, Inhabited b, Inhabited c) => Inhabited (a, b, c)
deriving instance (Inhabited a, Inhabited b, Inhabited c, Inhabited d) => Inhabited (a, b, c, d)

instance Inhabited b => Inhabited (a -> b) where
  trivial = const trivial
