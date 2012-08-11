{-# LANGUAGE DataKinds, GADTs, TypeOperators, TypeFamilies #-}
{-# LANGUAGE PolyKinds, RankNTypes, TypeSynonymInstances, StandaloneDeriving #-}
module Proof.Base ((:=:)(..), sym, trans, Sing
                  ,(:\/:), (:/\:)
                  , Reason(..), because, (===), start, byDefinition
                  , admitted, Proxy(..), cong, cong'
                  , Wrappable(..), SingI (..), SingE(..), (:~>), Map ()
                  , SBool(..), (:&&:), (:||:), (%&&), (%||), FromBool (..)
                  ) where

infix 4 :=:
type a :\/: b = Either a b
infixr 2 :\/:

type a :/\: b = (a, b)
infixr 3 :/\:

data a :=: b where
  Refl :: a :=: a

deriving instance Show (a :=: b)

sym :: a :=: b -> b :=: a
sym Refl = Refl

trans :: a :=: b -> b :=: c -> a :=: c
trans Refl Refl = Refl

data family Sing a
class SingI k where
  sing :: Sing k

class SingE s where
  type Demote s :: *
  fromSing :: Sing s -> Demote s

data Reason a x y where
  Because :: Sing y -> x :=: y -> Reason a x y

because :: Sing y -> x :=: y -> Reason a x y
because = Because

infixl 4 ===
infix 5 `Because`
infix 5 `because`

(===) :: x :=: y -> Reason a y z -> x :=: z
eq === (_ `Because` eq') = trans eq eq'

start :: Sing a -> a :=: a
start _ = Refl

byDefinition :: a :=: a
byDefinition = Refl

admitted :: Reason a x y
admitted = undefined
{-# WARNING admitted "There are some goals left yet unproven." #-}

data Proxy a = Proxy

cong :: forall f a b. Proxy f -> a :=: b -> f a :=: f b
cong Proxy Refl = Refl

cong' :: (Sing m -> Sing (f m)) -> a :=: b -> f a :=: f b
cong' _ Refl =  Refl

class Wrappable f where
  type BaseType f n :: *
  unWrap :: f n -> BaseType f n
  wrap   :: BaseType f n -> f n

data SBool (b :: Bool) where
  STrue  :: SBool True
  SFalse :: SBool False

type family   (b :: Bool) :||: (b' :: Bool) :: Bool
type instance True  :||: b = True
type instance False :||: b = b

type family   (b :: Bool) :&&: (b' :: Bool) :: Bool
type instance True  :&&: b = b
type instance False :&&: b = False

(%&&) :: SBool b -> SBool b' -> SBool (b :&&: b')
STrue  %&& b = b
SFalse %&& _ = SFalse

(%||) :: SBool b -> SBool b' -> SBool (b :||: b')
STrue  %|| _  = STrue
SFalse %|| b  = b

type family   (xs :: [*]) :~> (a :: *) :: *
type instance '[]       :~> a = a
type instance (x ': xs) :~> a = x -> (xs :~> a)

infixr 1 :~>

class FromBool (c :: *) where
  type Predicate c :: Bool
  type Args c :: [*]
  fromBool :: Predicate c ~ True => Args c :~> c

type family   Map f xs :: [*]
type instance Map f '[] = '[]
type instance Map f (x ': xs) = f x ': Map f xs

infixr 5 :++:
type family (xs :: [*]) :++: (ys :: [*]) :: [*]
type instance '[] :++: xs = xs
type instance (x ': xs) :++: ys = x ': xs :++: ys

