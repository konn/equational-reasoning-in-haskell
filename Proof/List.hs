{-# LANGUAGE DataKinds, PolyKinds, GADTs, TypeFamilies, MultiParamTypeClasses, FlexibleContexts #-}
{-# LANGUAGE TypeOperators, UndecidableInstances, ScopedTypeVariables, PatternGuards #-}
{-# LANGUAGE StandaloneDeriving, TypeSynonymInstances, FlexibleInstances, ConstraintKinds #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Proof.List where

import Proof.Base
import Proof.Natural

data IsSorted (xs :: [Nat]) where
  NilSorted    :: IsSorted '[]
  SingleSorted :: IsSorted '[x]
  ConsSorted   :: x :<=: y -> IsSorted (y ': ys) -> IsSorted (x ': y ': ys)

data instance Sing (xs :: [Nat]) where
  SNil  :: Sing ('[] :: [Nat])
  SCons :: Sing y -> Sing ys -> Sing (y ': ys :: [Nat])

deriving instance Show (SList xs)

type SList (xs :: [Nat]) = Sing xs

class SLIST (k :: [Nat]) where
  slist :: SList k

instance SLIST '[] where
  slist = SNil

instance (SingI x, SLIST xs) => SLIST (x ': xs) where
  slist = SCons sing slist

instance SingI ('[] :: [Nat]) where
  sing = SNil

instance (SingI x, SingI xs) => SingI (x ': xs :: [Nat]) where
  sing = SCons sing sing

instance SingE ('[] :: [Nat]) where
  type Demote ('[] :: [Nat]) = [Nat]
  fromSing SNil = []

instance (Demote x ~ Nat, Demote xs ~ [Nat], SingE x, SingE xs) => SingE (x ': xs :: [Nat]) where
  type Demote (x ': xs :: [Nat]) = [Nat]
  fromSing (SCons x xs) = fromSing x : fromSing xs

type family   Insert (n :: Nat) (xs :: [Nat]) :: [Nat]
type instance Insert n '[] = '[n]
type instance Insert n (x ': xs) = If (n :<<=: x) (n ': x ': xs)  (x ': Insert n xs)

type family If (p :: Bool) (a :: [Nat]) (b :: [Nat]) :: [Nat]
type instance If True  a b = a
type instance If False a b = b

sIf :: SBool b -> SList n -> SList m -> SList (If b n m)
sIf STrue  t _ = t
sIf SFalse _ f = f

sInsert :: SNat n -> SList xs -> SList (Insert n xs)
sInsert n SNil = SCons n SNil
sInsert n (SCons x xs) = sIf (n %<<= x) (SCons n (SCons x xs)) (SCons x (sInsert n xs))

consSorted :: forall x y ys. (x :<<=: y) ~ True
           => Sing x -> Sing (y ': ys)
           -> IsSorted (y ': ys) -> IsSorted (x ': y ': ys)
consSorted n (SCons m _) = ConsSorted (boolToPropLe n m)

consSortedI :: forall x y ys. ((x :<<=: y) ~ True, SingI x, SingI y)
           => IsSorted (y ': ys) -> IsSorted (x ': y ': ys)
consSortedI = ConsSorted (boolToPropLe (sing :: SNat x) (sing :: SNat y))

insHeadLe :: forall x y xs xs'. Insert x xs ~ (y ': xs')
          => Sing x -> Sing xs -> y :<=: x
insHeadLe _ SNil = Right Refl
insHeadLe n (SCons m _) =
  case n %<<= m of
    STrue  -> Right Refl
    SFalse -> Left $ rev n m

data ElemProof (n :: Nat) (ns :: [Nat]) where
  IsHeadElem :: ElemProof n (n ': ns)
  IsTailElem :: ElemProof n xs -> ElemProof n (x ': xs)

type family Length (xs :: [Nat]) :: Nat
type instance Length '[] = Zero
type instance Length (x ': xs)  = Succ (Length xs)

sLength :: SList xs -> SNat (Length xs)
sLength SNil = SZero
sLength (SCons _ xs) = SSucc $ sLength xs

consLenEq :: Sing x -> Sing y -> Sing xs -> Length (x ': xs) :=: Length (y ': xs)
consLenEq _ _ _ = Refl

lenInsEqLenCons :: Sing x -> Sing xs -> Length (Insert x xs) :=: Length (x ': xs)
lenInsEqLenCons _ SNil = Refl
lenInsEqLenCons n (SCons m xs) =
  case n %<<= m of
    STrue  -> Refl
    SFalse ->
        start (sLength (sInsert n (SCons m xs)))
          === sLength (SCons m (sInsert n xs))  `because` byDefinition
          === SSucc (sLength $ sInsert n xs)    `because` byDefinition
          === SSucc (sLength $ SCons n xs)      `because` cong' SSucc (lenInsEqLenCons n xs)
          === SSucc (sLength $ SCons m xs)      `because` cong' SSucc (consLenEq n m xs)
          === sLength (SCons n (SCons m xs))    `because` byDefinition

insLenPlusOne :: SNat x -> SList xs -> Length (Insert x xs) :=: Succ (Length xs)
insLenPlusOne _ SNil = Refl
insLenPlusOne n (SCons m xs) =
    case n %<<= m of
      STrue  -> Refl
      SFalse ->
        start (sLength (sInsert n (SCons m xs)))
          === sLength (SCons m (sInsert n xs))    `because` byDefinition
          === SSucc (sLength (sInsert n xs))      `because` byDefinition
          === SSucc (SSucc (sLength xs))          `because` cong' SSucc (insLenPlusOne n xs)
          === SSucc (sLength $ SCons m xs)        `because` byDefinition

fromIsSorted :: forall x y xs. IsSorted (x ': xs) -> ElemProof y xs -> x :<=: y
fromIsSorted reason proof = undefined

isHeadElem :: Sing x -> Sing (x ': xs) -> ElemProof x (x ': xs)
isHeadElem _ (SCons _ _) = IsHeadElem

insPreservesElem :: forall x y xs.
                    Sing x
                 -> Sing y
                 -> Sing xs
                 -> ElemProof x xs -> ElemProof x (Insert y xs)
insPreservesElem x y _ IsHeadElem =
  case y %<<= x of
    SFalse -> IsHeadElem
    STrue  -> IsTailElem IsHeadElem
insPreservesElem x y (SCons x' ys) (IsTailElem reason) =
  case y %<<= x' of
    SFalse  -> IsTailElem (insPreservesElem x y ys reason)
    STrue   -> IsTailElem (IsTailElem reason)
insPreservesElem _ _ _ _ = error "impossible!"

sortedElem :: IsSorted (x ': xs) -> ElemProof y xs -> x :<=: y
sortedElem (ConsSorted p _)             IsHeadElem       = p
sortedElem (ConsSorted xLEy restSorted) (IsTailElem pos) = leTrans xLEy (sortedElem restSorted pos)
sortedElem _ _ = error "impossible"

originalSortedElem :: Insert n xs ~ (y ': xs')
                   => Sing n
                   -> Sing y
                   -> SList xs
                   -> IsSorted xs
                   -> y :<: n -> ElemProof y xs
originalSortedElem n y (SCons y' ys) sorted _ =
   case n %<<= y' of
     SFalse -> IsHeadElem
     STrue  -> undefined
originalSortedElem n y SNil _ _ = error "impossible!"

{-
insPreservesIsSorted :: forall x xs. Sing x -> Sing xs -> IsSorted xs -> IsSorted (Insert x xs)
insPreservesIsSorted n SNil NilSorted    = SingleSorted
insPreservesIsSorted n (SCons y ys) reason
  | STrue <- n %<<= y = consSorted n (SCons y ys) reason
insPreservesIsSorted n (SCons y SNil) SingleSorted
  | SFalse <- n %<<= y = ConsSorted (Left $ rev n y) SingleSorted
insPreservesIsSorted n (SCons y ys) (ConsSorted yLEhd restSorted)
  | SFalse <- n %<<= y
  , SCons y' ys' <- sInsert n ys
  , r'<- insPreservesIsSorted n ys restSorted
  = ConsSorted (sortedElem (ConsSorted yLEhd restSorted) (originalSortedElem n y ys undefined)) r'
insPreservesIsSorted n _ _ = error "impossible! "
-}