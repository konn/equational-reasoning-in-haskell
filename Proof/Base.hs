{-# LANGUAGE DataKinds, GADTs, TypeOperators, TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds, RankNTypes, TypeSynonymInstances, StandaloneDeriving #-}
module Proof.Base ((:=:)(..), Equality(..), Sing
                  ,(:\/:), (:/\:)
                  , Reason(..), because, (===), start, byDefinition
                  , admitted, Proxy(..), cong, cong'
                  , Wrappable(..), SingI (..), SingE(..), (:~>), Map ()
                  , SBool(..), (:&&:), (:||:), (%:&&), (%:||), FromBool (..)
                  ) where
import Singletons.Lib

infix 4 :=:
type a :\/: b = Either a b
infixr 2 :\/:

type a :/\: b = (a, b)
infixr 3 :/\:

data Proxy (a :: k) = Proxy

data a :=: b where
  Refl :: a :=: a

data Leibniz a b = Leibniz { apply :: forall f. f a -> f b }

deriving instance Show (a :=: b)

class Equality (eq :: k -> k -> *) where
  reflexivity  :: Proxy a -> eq a a
  symmetry     :: eq a b  -> eq b a
  transitivity :: eq a b  -> eq b c -> eq a c

instance Equality (:=:) where
  reflexivity  _         = Refl
  symmetry     Refl      = Refl
  transitivity Refl Refl = Refl

leibniz_refl = Leibniz id

instance Equality Leibniz where
  reflexivity _ = leibniz_refl
  symmetry eq  = unFlip $ apply eq $ Flip leibniz_refl
  transitivity (Leibniz aEqb) (Leibniz bEqc) = Leibniz $ bEqc . aEqb

newtype Flip f a b = Flip { unFlip :: f b a }

data Reason eq x y where
  Because :: Sing y -> eq x y -> Reason eq x y

by, because :: Sing y -> eq x y -> Reason eq x y
because = Because
by      = Because

infixl 4 ===
infix 5 `Because`
infix 5 `because`

(===) :: Equality eq => eq x y -> Reason eq y z -> eq x z
eq === (_ `Because` eq') = transitivity eq eq'


start :: Equality eq => Sing a -> eq a a
start _ = reflexivity Proxy

definition, byDefinition :: Equality eq => eq a a
byDefinition = reflexivity Proxy
definition = reflexivity Proxy


admitted :: Reason eq x y
admitted = undefined
{-# WARNING admitted "There are some goals left yet unproven." #-}

cong :: forall f a b. Proxy f -> a :=: b -> f a :=: f b
cong Proxy Refl = Refl

cong' :: (Sing m -> Sing (f m)) -> a :=: b -> f a :=: f b
cong' _ Refl =  Refl

class Wrappable f where
  type BaseType f n :: *
  unWrap :: f n -> BaseType f n
  wrap   :: BaseType f n -> f n

type family   (xs :: [*]) :~> (a :: *) :: *
type instance '[]       :~> a = a
type instance (x ': xs) :~> a = x -> (xs :~> a)

infixr 1 :~>

class FromBool (c :: *) where
  type Predicate c :: Bool
  type Args c :: [*]
  fromBool :: Predicate c ~ True => Args c :~> c

type family   Map (f :: k -> k') (xs :: [k]) :: [k']
type instance Map f '[] = '[]
type instance Map f (x ': xs) = f x ': Map f xs

infixr 5 :++:
type family (xs :: [k]) :++: (ys :: [k]) :: [k]
type instance '[] :++: xs = xs
type instance (x ': xs) :++: ys = x ': xs :++: ys
