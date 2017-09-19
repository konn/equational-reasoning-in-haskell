{-# LANGUAGE DataKinds, DefaultSignatures, DeriveAnyClass, EmptyCase  #-}
{-# LANGUAGE ExplicitNamespaces, FlexibleContexts, FlexibleInstances  #-}
{-# LANGUAGE GADTs, KindSignatures, LambdaCase, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TupleSections   #-}
{-# LANGUAGE TypeOperators                                            #-}
module Proof.Propositional.Inhabited (Inhabited(..), withInhabited) where
import GHC.Generics
import Unsafe.Coerce (unsafeCoerce)

-- | Types with at least one inhabitant, dual to @'Proof.Propositional.Empty'@.
--   Currently, GHC doesn't provide a selective-instance,
--   hence we can't generically derive @'Inhabited'@ instances
--   for sum types (i.e. by @DeriveAnyClass@).
--
--   To derive an instance for each concrete types,
--   use @'Proof.Propositional.prove'@.
--
--   Since 0.4.0.0.
class Inhabited a where
  -- | A /generic/ inhabitant of type @'a'@, which means that
  --   one cannot assume anything about the value of @'trivial'@
  --   except that it
  --
  --   * is of type @a@, and
  --   * doesn't contain any partial values.
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

newtype MagicInhabited a b = MagicInhabited (Inhabited a => b)

withInhabited :: forall a b. a -> (Inhabited a => b) -> b
withInhabited wit k = unsafeCoerce (MagicInhabited k :: MagicInhabited a b) wit
