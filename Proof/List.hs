{-# LANGUAGE TypeOperators, UndecidableInstances, ScopedTypeVariables #-}
{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeFamilies, Rank2Types #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Proof.List where
import Proof.Base
import Proof.Natural
import Singletons.Lib
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

data Increasing (xs :: [Nat]) where
  NilIncreasing    :: Increasing '[]
  SingletonIncreasing :: Increasing '[x]
  ConsIncreasing   :: x :<=: y -> Increasing (y ': ys) -> Increasing (x ': y ': ys)

boolToPropIncreasing :: (IncreasingB xs ~ True) => SList xs -> Increasing xs
boolToPropIncreasing SNil = NilIncreasing
boolToPropIncreasing (SCons x SNil) = SingletonIncreasing
boolToPropIncreasing xs0@(SCons x (SCons y xs)) =
  case x %:<<= y of
    STrue  -> ConsIncreasing (boolToPropLe x y) (boolToPropIncreasing (sCons y xs))
    _      -> bugInGHC

instance FromBool (Increasing xs) where
  type Predicate (Increasing xs) = IncreasingB xs
  type Args (Increasing xs) = '[Sing xs]
  fromBool = boolToPropIncreasing

insPreservesIncreasing :: Sing x -> SList xs -> Increasing xs -> Increasing (Insert x xs)
insPreservesIncreasing _ SNil _ = SingletonIncreasing
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

data Permutation (xs :: [Nat]) (ys :: [Nat]) where
  NilPerm   :: Permutation '[] '[]
  HeadPerm  :: Permutation xs ys -> Permutation (x ': xs) (x ': ys)
  SwapPerm  :: Permutation (x ': y ': xs) (y ': x ': xs)
  TransPerm :: Permutation xs ys -> Permutation ys zs -> Permutation xs zs

reflPerm :: SList xs -> Permutation xs xs
reflPerm SNil = NilPerm
reflPerm (SCons _ xs) = HeadPerm (reflPerm xs)

sHeadPerm :: SNat x -> Permutation xs ys -> Permutation (x ': xs) (x ': ys)
sHeadPerm _ = HeadPerm

insPermutation :: SNat x -> SList xs -> Permutation (x ': xs) (Insert x xs)
insPermutation _ SNil = HeadPerm NilPerm
insPermutation x (SCons y ys) =
  case x %:<<= y of
    STrue  -> reflPerm (sCons x (sCons y ys))
    SFalse -> SwapPerm `TransPerm` sHeadPerm y (insPermutation x ys)

insSortPermutation :: SList xs -> Permutation xs (InsSort xs)
insSortPermutation SNil         = NilPerm
insSortPermutation (SCons x xs) =
  HeadPerm (insSortPermutation xs)
    `TransPerm` insPermutation x (sInsSort xs)
