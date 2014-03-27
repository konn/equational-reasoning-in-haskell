{-# LANGUAGE CPP, DataKinds, FlexibleContexts, GADTs, PolyKinds, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TypeFamilies     #-}
{-# LANGUAGE TypeOperators, TypeSynonymInstances                       #-}
module Proof.Equational (
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
                         (:~:)(..), (:=:)
#else
                         (:=:)(..), (:~:)
#endif
                        , sym, trans
                        , Equality(..), Preorder(..), reflexivity'
                        ,(:\/:), (:/\:), (=<=), (=>=), (=~=), Leibniz(..)
                        , Reason(..), because, by, (===), start, byDefinition
                        , admitted, Proxy(..), cong, cong'
                        , Proposition(..), (:~>), FromBool (..)
                          -- * Conversion between equalities
                        , fromRefl, fromLeibniz, reflToLeibniz, leibnizToRefl
                          -- * Coercion
                        , coerce, coerce'
                          -- * Re-exported modules
                        , module Data.Singletons, module Data.Proxy
                        ) where
import Data.Proxy
import Data.Singletons
import Unsafe.Coerce
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 707
import Data.Type.Equality hiding (apply)
#endif

infix 4 :=:
type a :\/: b = Either a b
infixr 2 :\/:

type a :/\: b = (a, b)
infixr 3 :/\:

#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ < 707
data a :=: b where
  Refl :: a :=: a
type (:~:) = (:=:)
infix 4 :~:
trans :: a :=: b -> b :=: c -> a :=: c
trans Refl Refl = Refl

sym :: a :=: b -> b :=: a
sym Refl = Refl
#else
type (:=:) = (:~:)
#endif


data Leibniz a b = Leibniz { apply :: forall f. f a -> f b }

leibnizToRefl :: Leibniz a b -> a :=: b
leibnizToRefl eq = apply eq Refl

fromLeibniz :: (Preorder eq, SingI a) => Leibniz a b -> eq a b
fromLeibniz eq = apply eq (reflexivity sing)

fromRefl :: (Preorder eq, SingI b) => a :=: b -> eq a b
fromRefl Refl = reflexivity'

reflToLeibniz :: a :=: b -> Leibniz a b
reflToLeibniz Refl = Leibniz id

deriving instance Show (a :=: b)

class Preorder (eq :: k -> k -> *) where
  reflexivity  :: Sing a -> eq a a
  transitivity :: eq a b  -> eq b c -> eq a c

class Preorder eq => Equality (eq :: k -> k -> *) where
  symmetry     :: eq a b  -> eq b a

instance Preorder (:=:) where
  transitivity Refl Refl = Refl
  reflexivity  _         = Refl

instance Equality (:=:) where
  symmetry     Refl      = Refl

instance Preorder (->) where
  reflexivity _ = id
  transitivity = flip (.)

leibniz_refl :: Leibniz a a
leibniz_refl = Leibniz id

instance Preorder Leibniz where
  reflexivity _ = leibniz_refl
  transitivity (Leibniz aEqb) (Leibniz bEqc) = Leibniz $ bEqc . aEqb

instance Equality Leibniz where
  symmetry eq  = unFlip $ apply eq $ Flip leibniz_refl

newtype Flip f a b = Flip { unFlip :: f b a }

data Reason eq x y where
  Because :: Sing y -> eq x y -> Reason eq x y

reflexivity' :: (SingI x, Preorder r) => r x x
reflexivity' = reflexivity sing

by, because :: Sing y -> eq x y -> Reason eq x y
because = Because
by      = Because

infixl 4 ===, =<=, =~=, =>=
infix 5 `Because`
infix 5 `because`

(=<=) :: Preorder r => r x y -> Reason r y z -> r x z
eq =<= (_ `Because` eq') = transitivity eq eq'

(=>=) :: Preorder r => r y z -> Reason r x y -> r x z
eq =>= (_ `Because` eq') = transitivity eq' eq

(===) :: Equality eq => eq x y -> Reason eq y z -> eq x z
(===) = (=<=)

(=~=) :: Preorder r => r x y -> Sing y -> r x y
eq =~= _ = eq

start :: Preorder eq => Sing a -> eq a a
start = reflexivity

byDefinition :: (SingI a, Preorder eq) => eq a a
byDefinition = reflexivity sing

admitted :: Reason eq x y
admitted = undefined
{-# WARNING admitted "There are some goals left yet unproven." #-}

cong :: forall f a b. Proxy f -> a :=: b -> f a :=: f b
cong Proxy Refl = Refl

cong' :: (Sing m -> Sing (f m)) -> a :=: b -> f a :=: f b
cong' _ Refl =  Refl

-- | Type coercion. 'coerce' is using @unsafeCoerce a@.
-- So, please, please do not provide the @undefined@ as the proof.
-- Using this function instead of pattern-matching on equality proof,
-- you can reduce the overhead introduced by run-time proof.
coerce :: (a :=: b) -> f a -> f b
coerce Refl a = unsafeCoerce a
{-# INLINE coerce #-}

-- | Coercion for identity types.
coerce' :: a :=: b -> a -> b
coerce' Refl a = unsafeCoerce a
{-# INLINE coerce' #-}

class Proposition f where
  type OriginalProp f n :: *
  unWrap :: f n -> OriginalProp f n
  wrap   :: OriginalProp f n -> f n

type family   (xs :: [*]) :~> (a :: *) :: *
type instance '[]       :~> a = a
type instance (x ': xs) :~> a = x -> (xs :~> a)

infixr 1 :~>

class FromBool (c :: *) where
  type Predicate c :: Bool
  type Args c :: [*]
  fromBool :: Predicate c ~ True => Args c :~> c
