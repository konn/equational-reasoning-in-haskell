{-# LANGUAGE CPP, DataKinds, FlexibleContexts, GADTs, KindSignatures #-}
{-# LANGUAGE PolyKinds, RankNTypes, ScopedTypeVariables              #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilies, TypeOperators         #-}
{-# LANGUAGE TypeSynonymInstances, UndecidableInstances              #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 800
{-# LANGUAGE ConstrainedClassMethods, TypeFamilyDependencies #-}
#endif
module Proof.Equational ( (:~:)(..), (:=:)
                        , sym, trans
                        , Equality(..), Preorder(..), reflexivity'
                        , (:\/:), (:/\:), (=<=), (=>=), (=~=), Leibniz(..)
                        , Reason(..), because, by, (===), start, byDefinition
                        , admitted, Proxy(..), cong, cong'
                        , Proposition(..), HVec(..), FromBool (..)
                        , applyNAry, applyNAry', fromBool'
                          -- * Conversion between equalities
                        , fromRefl, fromLeibniz, reflToLeibniz, leibnizToRefl
                          -- * Coercion
                        , coerce, coerce', withRefl
                          -- * Re-exported modules
                        , module Data.Proxy
                        ) where
import Data.Proxy
import Data.Type.Equality hiding (apply)
import Unsafe.Coerce

infix 4 :=:
type a :\/: b = Either a b
infixr 2 :\/:

type a :/\: b = (a, b)
infixr 3 :/\:

type (:=:) = (:~:)

data Leibniz a b = Leibniz { apply :: forall f. f a -> f b }

leibnizToRefl :: Leibniz a b -> a :=: b
leibnizToRefl eq = apply eq Refl

fromLeibniz :: (Preorder eq) => Leibniz a b -> eq a b
fromLeibniz eq = apply eq (reflexivity Proxy)

fromRefl :: (Preorder eq) => a :=: b -> eq a b
fromRefl Refl = reflexivity'

reflToLeibniz :: a :=: b -> Leibniz a b
reflToLeibniz Refl = Leibniz id

class Preorder (eq :: k -> k -> *) where
  reflexivity  :: proxy a -> eq a a
  transitivity :: eq a b  -> eq b c -> eq a c

class Preorder eq => Equality (eq :: k -> k -> *) where
  symmetry     :: eq a b  -> eq b a

instance Preorder (:=:) where
  {-# SPECIALISE instance Preorder (:=:) #-}
  transitivity Refl Refl = Refl
  {-# INLINE[1] transitivity #-}

  reflexivity  _         = Refl
  {-# INLINE[1] reflexivity #-}

instance Equality (:=:) where
  {-# SPECIALISE instance Equality (:~:) #-}
  symmetry     Refl      = Refl
  {-# INLINE[1] symmetry #-}

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
  Because :: proxy y -> eq x y -> Reason eq x y

reflexivity' :: (Preorder r) => r x x
reflexivity' = reflexivity Proxy

by, because :: proxy y -> eq x y -> Reason eq x y
because = Because
by      = Because

infixl 4 ===, =<=, =~=, =>=
infix 5 `Because`
infix 5 `because`

(=<=) :: Preorder r => r x y -> Reason r y z -> r x z
eq =<= (_ `Because` eq') = transitivity eq eq'

{-# SPECIALISE INLINE[1] (=<=) :: x :~: y -> Reason (:~:) y z -> x :~: z #-}

(=>=) :: Preorder r => r y z -> Reason r x y -> r x z
eq =>= (_ `Because` eq') = transitivity eq' eq

{-# SPECIALISE INLINE[1] (=>=) :: y :~: z -> Reason (:~:) x y -> x :~: z #-}

(===) :: Equality eq => eq x y -> Reason eq y z -> eq x z
(===) = (=<=)
{-# SPECIALISE INLINE[1] (===) :: x :~: y -> Reason (:~:) y z -> x :~: z #-}

(=~=) :: r x y -> proxy y -> r x y
eq =~= _ = eq

start :: Preorder eq => proxy a -> eq a a
start = reflexivity

byDefinition :: (Preorder eq) => eq a a
byDefinition = reflexivity Proxy

admitted :: Reason eq x y
admitted = undefined
{-# WARNING admitted "There are some goals left yet unproven." #-}

cong :: forall f a b. Proxy f -> a :=: b -> f a :=: f b
cong Proxy Refl = Refl

cong' :: (pxy m -> pxy (f m)) -> a :=: b -> f a :=: f b
cong' _ Refl =  Refl

-- | Type coercion. 'coerce' is using @unsafeCoerce a@.
-- So, please, please do not provide the @undefined@ as the proof.
-- Using this function instead of pattern-matching on equality proof,
-- you can reduce the overhead introduced by run-time proof.
coerce :: (a :=: b) -> f a -> f b
coerce _ a = unsafeCoerce a
{-# INLINE[1] coerce #-}

-- | Coercion for identity types.
coerce' :: a :=: b -> a -> b
coerce' _ a = unsafeCoerce a
{-# INLINE[1] coerce' #-}

{-# RULES
"coerce/unsafeCoerce" [~1] forall xs.
  coerce xs = unsafeCoerce
"coerce'/unsafeCoerce" [~1] forall xs.
  coerce' xs = unsafeCoerce
  #-}

-- | Solves equality constraint without explicit coercion.
--   It has the same effect as @'Data.Type.Equality.gcastWith'@,
--   but some hacks is done to reduce runtime overhead.
withRefl :: forall a b r. a :~: b -> (a ~ b => r) -> r
withRefl _ r = case unsafeCoerce (Refl :: () :~: ()) :: a :~: b of
  Refl -> r
{-# NOINLINE withRefl #-}
{-# RULES
"withRefl/unsafeCoerce" [~1] forall x.
  withRefl x = unsafeCoerce
  #-}

class Proposition (f :: k -> *) where
  type OriginalProp (f :: k -> *) (n :: k) :: *
  unWrap :: f n -> OriginalProp f n
  wrap   :: OriginalProp f n -> f n

data HVec (xs :: [*]) where
  HNil :: HVec '[]
  (:-) :: x -> HVec xs -> HVec (x ': xs)

infixr 9 :-
type family (xs :: [*]) :~> (a :: *) :: * where
  '[]       :~> a = a
  (x ': xs) :~> a = x -> (xs :~> a)

infixr 1 :~>

data HVecView (xs :: [*]) :: * where
  HNilView  :: HVecView '[]
  HConsView :: Proxy t -> HVecView ts -> HVecView (t ': ts)

deriving instance Show (HVecView xs)

class KnownTypeList (xs :: [*]) where
  viewHVec' :: HVecView xs

instance KnownTypeList '[] where
  viewHVec' = HNilView

instance KnownTypeList ts => KnownTypeList (t ': ts) where
  viewHVec' = HConsView Proxy viewHVec'

newtype Magic (xs :: [*]) a = Magic { _viewHVec' :: KnownTypeList xs => a }

withKnownTypeList :: forall a xs. HVecView xs -> (KnownTypeList xs => a) -> a
withKnownTypeList xs f = (unsafeCoerce (Magic f :: Magic xs a) :: HVecView xs -> a) xs

apply' :: HVecView ts -> (HVec ts -> c) -> ts :~> c
apply' HNilView f = f HNil
apply' (HConsView Proxy ts) f = \a -> withKnownTypeList ts $
  apply' ts (\ts' -> f $ a :- ts')

applyNAry :: forall ts c. KnownTypeList ts => (HVec ts -> c) -> ts :~> c
applyNAry = apply' (viewHVec' :: HVecView ts)

applyNAry' :: KnownTypeList ts => proxy ts -> proxy' c -> (HVec ts -> c) -> ts :~> c
applyNAry' _ _ = applyNAry

class FromBool (c :: *) where
  type Predicate c :: Bool
  type Args c :: [*]
  fromBool :: Predicate c ~ 'True => HVec (Args c) -> c

fromBool' :: forall proxy c. (KnownTypeList (Args c), FromBool c , Predicate c ~ 'True) => proxy c -> Args c :~> c
fromBool' pxyc = applyNAry' (Proxy :: Proxy (Args c)) pxyc fromBool
