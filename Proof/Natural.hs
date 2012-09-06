{-# LANGUAGE PolyKinds, DataKinds, TypeFamilies, TypeOperators, GADTs, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, Rank2Types, StandaloneDeriving, ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Proof.Natural where
import Proof.Base
import Singletons.Lib

singletons [d|
  data Nat = Zero | Succ Nat
           deriving (Show, Eq)
  (+) :: Nat -> Nat -> Nat
  n + Zero   = n
  n + Succ m = Succ (n + m)
  (*) :: Nat -> Nat -> Nat
  n * Zero   = Zero
  n * Succ m = n * m + n

  one :: Nat
  one = Succ Zero
  |]

infixl 6 %:+
infixl 6 :+

infixl 7 %:*
infixl 7 :*

deriving instance Show (SNat n)
deriving instance Eq (SNat n)

data EEq (a :: Nat) (b :: Nat) where
  EqZero :: EEq Zero Zero
  EqSucc :: EEq n m -> EEq (Succ n) (Succ m)

refl_eeq :: forall n. SingI n => EEq n n
refl_eeq = hoge (sing :: SNat n)
  where
    hoge :: SNat m -> EEq m m
    hoge SZero = EqZero
    hoge (SSucc n') = EqSucc $ hoge n'


induction :: p Zero
          -> (forall a. (SNat a -> p a) -> SNat (Succ a) -> p (Succ a))
          -> SNat c -> p c
induction baseCase _     SZero     = baseCase
induction baseCase hypo (SSucc n) = hypo (induction baseCase hypo) (SSucc n)


succCongEq :: n :=: m -> Succ n :=: Succ m
succCongEq Refl = Refl

plusSuccR :: SNat a -> SNat b -> a :+ Succ b :=: Succ (a :+ b)
plusSuccR _ _ = Refl

induction' :: forall p c. Wrappable p
           => Proxy p
           -> BaseType p Zero
           -> (forall a. (SNat a -> BaseType p a) -> SNat (Succ a) -> BaseType p (Succ a))
           -> SNat c -> BaseType p c
induction' _ base hypo = unWrap . induction (wrap base) hypo'
  where
    hypo' :: (SNat a -> p a) -> SNat (Succ a) -> p (Succ a)
    hypo' h = wrap . hypo (unWrap . h)

singletons [d|
  fact :: Nat -> Nat
  fact Zero     = one
  fact (Succ n) = Succ n * fact n
 |]

infer :: Proxy a
infer = Proxy

plusCongL :: SNat n -> m :=: m' -> n :+ m :=: n :+ m'
plusCongL _ Refl = Refl

plusCongR :: SNat n -> m :=: m' -> m :+ n :=: m' :+ n
plusCongR _ Refl = Refl

succPlusR :: SNat n -> SNat m -> n :+ Succ m :=: Succ (n :+ m)
succPlusR _ _ = Refl

newtype Assoc m n l = Assoc { getAssoc :: m :+ (n :+ l) :=: (m :+ n) :+ l }
instance Wrappable (Assoc m n) where
  type BaseType (Assoc m n) l = m :+ (n :+ l) :=: (m :+ n) :+ l
  unWrap = getAssoc
  wrap = Assoc

plusAssoc :: forall m n l. SNat m -> SNat n -> SNat l -> m :+ (n :+ l) :=: (m :+ n) :+ l
plusAssoc m n = induction' (Proxy :: Proxy (Assoc m n)) baseCase subStep
  where
    baseCase :: BaseType (Assoc m n) Zero
    baseCase = Refl
    subStep :: (SNat l' -> BaseType (Assoc m n) l')
            -> SNat (Succ l')
            -> BaseType (Assoc m n) (Succ l')
    subStep hypo (SSucc l) =
      start (m %:+ (n %:+ sSucc l))
        === sSucc (m %:+ (n %:+ l)) `because` byDefinition
        === sSucc ((m %:+ n) %:+ l) `because` cong infer (hypo l)
        === (m %:+ n) %:+ sSucc l   `because` byDefinition

newtype Comm m n = Comm { unComm :: m :+ n :=: n :+ m }
instance Wrappable (Comm m) where
  type BaseType (Comm m) n = m :+ n :=: n :+ m
  wrap = Comm
  unWrap = unComm

plusZeroL :: SNat m -> Zero :+ m :=: m
plusZeroL SZero = Refl
plusZeroL (SSucc m) =
  start (sZero %:+ (sSucc m))
    === sSucc (sZero %:+ m) `because` plusSuccR sZero m
    === sSucc m            `because` succCongEq (plusZeroL m)

newtype Prop0 m n = Prop0 { unProp0 :: m :+ Succ n :=: Succ m :+ n }

instance Wrappable (Prop0 m) where
  type BaseType (Prop0 m) n = m :+ Succ n :=: Succ m :+ n
  wrap = Prop0
  unWrap = unProp0

nPlusSuccm :: forall m n. SNat m -> SNat n -> m :+ Succ n :=: Succ m :+ n
nPlusSuccm m = induction' (Proxy :: Proxy (Prop0 m)) base cases
  where
    base :: m :+ Succ Zero :=: Succ m :+ Zero
    base = Refl
    cases :: (SNat n' -> m :+ Succ n' :=: Succ m :+ n')
          -> SNat (Succ n')
          -> m :+ Succ (Succ n') :=: Succ m :+ Succ n'
    cases hypo (SSucc n) =
      start (m %:+ sSucc (sSucc n))
        === sSucc (m %:+ sSucc n)  `because` byDefinition
        === sSucc (sSucc m %:+ n)  `because` cong' sSucc (hypo n)
        === sSucc m %:+ sSucc n    `because` byDefinition

plusComm :: forall m n. SNat m -> SNat n -> m :+ n :=: n :+ m
plusComm m = induction' (Proxy :: Proxy (Comm m)) base cases
  where
    base :: BaseType (Comm m) Zero
    base =
      start (m %:+ sZero)
        === m          `because` byDefinition
        === sZero %:+ m `because` symmetry (plusZeroL m)
    cases :: (SNat n' -> BaseType (Comm m) n')
          -> SNat (Succ n') -> BaseType (Comm m) (Succ n')
    cases hypo (SSucc n) =
      start (m %:+ sSucc n)
        === sSucc (m %:+ n) `because` byDefinition
        === sSucc (n %:+ m) `because` cong' sSucc (hypo n)
        === n %:+ sSucc m   `because` byDefinition
        === sSucc n %:+ m   `because` nPlusSuccm n m

newtype MultPlusDistr l m n =
    MultPlusDistr { unMultPlusDistr :: l :* (m :+ n) :=: l :* m :+ l :* n}

instance Wrappable (MultPlusDistr l m) where
  type BaseType (MultPlusDistr l m) n = l :* (m :+ n) :=: l :* m :+ l :* n
  wrap = MultPlusDistr
  unWrap = unMultPlusDistr

multPlusDistr :: forall n m l. SNat n -> SNat m -> SNat l -> n :* (m :+ l) :=: n :* m :+ n :* l
multPlusDistr n m = induction' (Proxy :: Proxy (MultPlusDistr n m)) Refl cases
  where
    cases :: (SNat l' -> BaseType (MultPlusDistr n m) l')
          -> SNat (Succ l') -> BaseType (MultPlusDistr n m) (Succ l')
    cases hypo (SSucc l) =
      start (n %:* (m %:+ sSucc l))
        === n %:* sSucc (m %:+ l)      `because` byDefinition
        === n %:* (m %:+ l) %:+ n       `because` byDefinition
        === (n %:* m %:+ n %:* l) %:+ n  `because` plusCongR n (hypo l)
        === n %:* m %:+ (n %:* l %:+ n)  `because` symmetry (plusAssoc (n %:* m) (n %:* l) n)
        === n %:* m %:+ n %:* sSucc l   `because` byDefinition

newtype MultAssoc l m n = MultAssoc { unMultAssoc :: l :* (m :* n) :=: (l :* m) :* n }

instance Wrappable (MultAssoc m n) where
  type BaseType (MultAssoc m n) l = m :* (n :* l) :=: (m :* n) :* l
  wrap = MultAssoc
  unWrap = unMultAssoc

timesComm :: forall n m l. SNat n -> SNat m -> SNat l -> n :* (m :* l) :=: (n :* m) :* l
timesComm n m = induction' (Proxy :: Proxy (MultAssoc n m)) base cases
  where
    base :: BaseType (MultAssoc n m) Zero
    base = Refl
    cases :: (SNat l' -> BaseType (MultAssoc n m) l')
          -> SNat (Succ l') -> BaseType (MultAssoc n m) (Succ l')
    cases hypo (SSucc l) =
      start (n %:* (m %:* sSucc l))
        === n %:* (m %:* l %:+ m)       `because` byDefinition
        === n %:* (m %:* l) %:+ n %:* m  `because` multPlusDistr n (m %:* l) m
        === (n %:* m) %:* l %:+ n %:* m  `because` plusCongR (n%:*m) (hypo l)
        === (n %:* m) %:* sSucc l      `because` byDefinition

newtype MultComm m n = MultComm { unMultComm :: m :* n :=: n :* m }

instance Wrappable (MultComm m) where
  type BaseType (MultComm m) n = m :* n :=: n :* m
  wrap = MultComm
  unWrap = unMultComm

multZeroL :: forall m. SNat m -> Zero :* m :=: Zero
multZeroL SZero = Refl
multZeroL (SSucc m) =
  start (sZero %:* sSucc m)
    === sZero %:* m %:+ sZero  `because` byDefinition
    === sZero %:* m            `because` byDefinition
    === sZero                  `because` multZeroL m

multZeroR :: SNat n -> n :* Zero :=: Zero
multZeroR _ = Refl

multOneR :: SNat n -> n :* Succ Zero :=: n
multOneR n =
  start (n %:* sOne)
    === n %:* sZero %:+ n `because` byDefinition
    === sZero %:+ n       `because` plusCongR n (multZeroR n)
    === n                `because` plusZeroL n

multOneL :: SNat n -> Succ Zero :* n :=: n
multOneL SZero = Refl
multOneL (SSucc n) =
  start (sOne  %:* sSucc n)
    === sOne %:* n %:+ sOne `because` byDefinition
    === n %:+ sOne          `because` cong' (%:+ sOne) (multOneL n)
    === sSucc n            `because` byDefinition

plusMultDistr :: forall n m l. SNat n -> SNat m -> SNat l
              -> (n :+ m) :* l :=: n :* l :+ m :* l
plusMultDistr _ _ SZero = Refl
plusMultDistr n m (SSucc l) =
  start ((n %:+ m) %:* sSucc l)
    === (n %:+ m) %:* l %:+ (n %:+ m)   `because` byDefinition
    === (n%:*l %:+ m%:*l) %:+ (n %:+ m)  `because` plusCongR (n %:+ m) (plusMultDistr n m l)
    === (n%:*l %:+ m%:*l) %:+ (m %:+ n)  `because` plusCongL (n%:*l %:+ m%:*l) (plusComm n m)
    === (n%:*l %:+ m%:*l %:+ m) %:+ n    `because` plusAssoc (n%:*l %:+ m%:*l) m n
    === (n%:*l %:+ (m%:*l %:+ m)) %:+ n  `because` plusCongR n (symmetry $ plusAssoc (n%:*l) (m%:*l) m)
    === (n%:*l %:+ (m%:*l %:+ m%:*sOne)) %:+ n
            `because` plusCongR n (plusCongL (n%:*l) $ plusCongL (m%:*l) $ symmetry $ multOneR m)
    === (n%:*l %:+ (m %:* sSucc l)) %:+ n
            `because` plusCongR n (plusCongL (n%:*l) $ symmetry $ multPlusDistr m l sOne)
    === ((m %:* sSucc l) %:+ n%:*l) %:+ n
            `because` plusCongR n (plusComm (n %:* l) (m %:* sSucc l))
    === ((m %:* sSucc l) %:+ n%:*l) %:+ n %:* sOne
            `because` plusCongL (m%:*sSucc l %:+ n%:*l) (symmetry $ multOneR n)
    === m %:* sSucc l %:+ (n%:*l %:+ n%:*sOne)
            `because` symmetry (plusAssoc (m %:* sSucc l) (n%:*l) (n %:* sOne))
    === m %:* sSucc l %:+ n %:* sSucc l
            `because` plusCongL (m %:* sSucc l) (symmetry $ multPlusDistr n l sOne)
    === n %:* sSucc l %:+ m %:* sSucc l   `because` plusComm (m %:* sSucc l) (n %:* sSucc l)

multComm :: forall n m. SNat n -> SNat m -> n :* m :=: m :* n
multComm n = induction' (Proxy :: Proxy (MultComm n)) base cases
  where
    base :: BaseType (MultComm n) Zero
    base = symmetry (multZeroL n)
    cases :: (SNat l -> BaseType (MultComm n) l)
          -> SNat (Succ l) -> BaseType (MultComm n) (Succ l)
    cases hypo (SSucc l) =
      start (n %:* sSucc l)
        === n %:* l %:+ n          `because` byDefinition
        === l %:* n %:+ n          `because` plusCongR n (hypo l)
        === l %:* n %:+ sOne %:* n  `because` plusCongL (l %:* n) (symmetry $ multOneL n)
        === (l %:+ sOne) %:* n     `because` symmetry (plusMultDistr l sOne n)
        === sSucc l %:* n         `because` byDefinition

data (a :: Nat) :<: (b :: Nat) where
  ZeroLtSucc :: Zero :<: Succ m
  SuccLtSucc :: n :<: m -> Succ n :<: Succ m
  
deriving instance Show (a :<: b)

singletons [d|
  (<<) :: Nat -> Nat -> Bool
  Zero   << Succ n = True
  n      << Zero   = False
  Succ n << Succ m = n << m
  (<<=) :: Nat -> Nat -> Bool
  Zero   <<= _      = True
  Succ n <<= Zero   = False
  Succ n <<= Succ m = n <<= m
 |]

type a :>> b = b :<< a
type a :> b  = b :<: a

type a :<=: b = a :<: b :\/: a :=: b

instance FromBool (n :<: m) where
  type Predicate (n :<: m) = n :<< m
  type Args (n :<: m) = '[Sing n, Sing m]
  fromBool = boolToPropLt

boolToPropLt :: (x :<< y) ~ True => SNat x -> SNat y -> x :<: y 
boolToPropLt SZero (SSucc _)     = ZeroLtSucc
boolToPropLt (SSucc n) (SSucc m) = SuccLtSucc $ boolToPropLt n m
boolToPropLt _ _         = bugInGHC

instance FromBool (n :<=: m) where
  type Predicate (n :<=: m) = n :<<= m
  type Args (n :<=: m) = '[Sing n, Sing m]
  fromBool = boolToPropLe

boolToPropLe :: (x :<<= y) ~ True => SNat x -> SNat y -> x :<=: y
boolToPropLe SZero SZero         = Right Refl
boolToPropLe SZero (SSucc _)     = Left ZeroLtSucc
boolToPropLe (SSucc n) (SSucc m) =
    case boolToPropLe n m of
      Left reason -> Left $ SuccLtSucc reason
      Right Refl  -> Right Refl
boolToPropLe _ _         = bugInGHC

rev :: (n :<<= m) ~ False => SNat n -> SNat m -> m :<: n
rev (SSucc _) SZero     = ZeroLtSucc
rev (SSucc n) (SSucc m) = SuccLtSucc $ rev n m
rev _         _         = bugInGHC

leTrans :: forall n m l. n :<=: m -> m :<=: l -> n :<=: l
leTrans (Right Refl) a = a
leTrans a (Right Refl) = a
leTrans (Left ZeroLtSucc) (Left (SuccLtSucc _)) = Left ZeroLtSucc
leTrans (Left (SuccLtSucc a)) (Left (SuccLtSucc b)) =
  case leTrans (Left a) (Left b) of
    Right Refl -> Right Refl
    Left le -> Left $ SuccLtSucc le
leTrans _ _ = bugInGHC


nLtSn :: SNat n -> n :<: Succ n
nLtSn SZero     = ZeroLtSucc
nLtSn (SSucc n) = SuccLtSucc (nLtSn n)

orIntroL :: a -> a :\/: b
orIntroL = Left

orIntroR :: b -> a :\/: b
orIntroR = Right

comparable :: SNat n -> SNat m -> n :<: m :\/: n :=: m :\/: m :<: n
comparable SZero SZero         = orIntroR (orIntroL Refl)
comparable SZero (SSucc _)     = orIntroL ZeroLtSucc
comparable (SSucc _) SZero     = orIntroR (orIntroR ZeroLtSucc)
comparable (SSucc n) (SSucc m) =
  case comparable n m of
    Left nLTm          -> orIntroL $ SuccLtSucc nLTm
    Right (Left Refl)  -> orIntroR $ orIntroL Refl
    Right (Right mLTn) -> orIntroR $ orIntroR $ SuccLtSucc mLTn
