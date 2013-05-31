{-# LANGUAGE TypeOperators, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeFamilies, Rank2Types #-}
{-# LANGUAGE ConstraintKinds, StandaloneDeriving, TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances, TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Proof.List where
import Proof.Base
import Proof.Natural
import Data.Singletons
import Prelude hiding ((+))

singletons [d|
  insert :: Nat -> [Nat] -> [Nat]
  insert a []     = [a]
  insert a (b:bs) = if a <<= b then a:b:bs else b:insert a bs

  len :: [a] -> Nat
  len [] = Zero
  len (_:xs) = Succ (len xs)

  increasingB :: [Nat] -> Bool
  increasingB []  = True
  increasingB [_] = True
  increasingB (x:y:xs) = x <<= y && increasingB (y:xs)

  insSort :: [Nat] -> [Nat]
  insSort [] = []
  insSort (x:xs) = insert x (insSort xs)
 |]

inductionL :: p '[] -> (forall x xs. (SList xs -> p xs) -> SList (x ': xs) -> p (x ': xs))
           -> SList zs -> p zs
inductionL nilCase _        SNil         = nilCase
inductionL nilCase consCase (SCons x xs) = consCase (inductionL nilCase consCase) (sCons x xs)

inductionL' :: forall p zs. Wrappable p
            => Proxy p
            -> BaseType p '[]
            -> (forall x xs. (SList xs -> BaseType p xs) -> SList (x ': xs) -> BaseType p (x ': xs))
            -> SList zs -> BaseType p zs
inductionL' _ nilCase consCase = unWrap . inductionL (wrap nilCase) consCase'
  where
    consCase' :: (SList xs -> p xs) -> SList (x ': xs) -> p (x ': xs)
    consCase' h = wrap . consCase (unWrap . h)

type ConsCase p = forall n ns. (SList ns -> p ns) -> SList (n ': ns) -> p (n ': ns)

data Increasing (xs :: [Nat]) where
  NilIncreasing    :: Increasing '[]
  SingletonIncreasing :: Increasing '[x]
  ConsIncreasing   :: x :<=: y -> Increasing (y ': ys) -> Increasing (x ': y ': ys)

boolToPropIncreasing :: (IncreasingB xs ~ True) => SList xs -> Increasing xs
boolToPropIncreasing = inductionL NilIncreasing consCase
  where
    consCase :: ConsCase Increasing
    consCase _ (SCons x SNil) = SingletonIncreasing
    consCase hypo xs0@(SCons x (SCons y xs)) =
      case x %:<<= y of
        STrue  -> ConsIncreasing (boolToPropLe x y) (hypo (sCons y xs))
        _      -> bugInGHC

instance FromBool (Increasing xs) where
  type Predicate (Increasing xs) = IncreasingB xs
  type Args (Increasing xs) = '[Sing xs]
  fromBool = boolToPropIncreasing

insPreservesIncreasing :: Sing x -> SList xs -> Increasing xs -> Increasing (Insert x xs)
insPreservesIncreasing x SNil _ = SingletonIncreasing
insPreservesIncreasing (x :: Sing x) (SCons (y :: Sing y) ys) reason =
  case x %:<<= y of
    STrue  -> ConsIncreasing (boolToPropLe x y) reason
    SFalse -> -- x > y
      let yLEx = orIntroL (rev x y) :: y :<=: x
      in case reason of
           SingletonIncreasing -> ConsIncreasing yLEx SingletonIncreasing
           ConsIncreasing yLEz reason' ->
             case ys of
               SCons z zs ->
                 case x %:<<= z of
                   STrue  -> ConsIncreasing yLEx
                                (insPreservesIncreasing x ys reason')
                   SFalse -> ConsIncreasing yLEz
                                (insPreservesIncreasing x ys reason')
               _ -> bugInGHC
           _ -> bugInGHC

insSortIsIncreasing :: SList xs -> Increasing (InsSort xs)
insSortIsIncreasing SNil         = NilIncreasing
insSortIsIncreasing (SCons x xs) =
  insPreservesIncreasing x (sInsSort xs) (insSortIsIncreasing xs)

reflPerm' :: forall xs. SingI xs => Proxy (xs :: [Nat]) -> Permutation xs xs
reflPerm' Proxy = reflPerm sing

data Permutation (xs :: [Nat]) (ys :: [Nat]) where
  NilPerm   :: Permutation '[] '[]
  HeadPerm  :: Permutation xs ys -> Permutation (x ': xs) (x ': ys)
  SwapPerm  :: Permutation (x ': y ': xs) (y ': x ': xs)
  TransPerm :: Permutation xs ys -> Permutation ys zs -> Permutation xs zs

deriving instance Show (Permutation ns ms)

reflPerm :: SList xs -> Permutation xs xs
reflPerm SNil = NilPerm
reflPerm (SCons _ xs) = HeadPerm (reflPerm xs)

instance Preorder Permutation where
  transitivity = TransPerm
  reflexivity  = reflPerm

sHeadPerm :: SNat x -> Permutation xs ys -> Permutation (x ': xs) (x ': ys)
sHeadPerm _ = HeadPerm

insPermutation :: SNat x -> SList xs -> Permutation (x ': xs) (Insert x xs)
insPermutation _ SNil = HeadPerm NilPerm
insPermutation x (SCons y ys) =
  case x %:<<= y of
    STrue  -> reflPerm (sCons x (sCons y ys))
    SFalse ->
      start (sCons x (sCons y ys))
        ==> sCons y (sCons x ys)      `because` SwapPerm
        ==> sCons y (sInsert x ys)    `because` sHeadPerm y (insPermutation x ys)
        =~= (sInsert x (sCons y ys))

insSortPermutation :: SList xs -> Permutation xs (InsSort xs)
insSortPermutation SNil         = NilPerm
insSortPermutation (SCons x xs) =
  start (sCons x xs)
    ==> sCons x (sInsSort xs)   `because` HeadPerm (insSortPermutation xs)
    ==> sInsert x (sInsSort xs) `because` insPermutation x (sInsSort xs)
    =~= sInsSort (sCons x xs)
