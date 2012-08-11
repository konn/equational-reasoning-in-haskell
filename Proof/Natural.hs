{-# LANGUAGE PolyKinds, DataKinds, PolyKinds, TypeFamilies, TypeOperators, GADTs, FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables, PatternGuards, FlexibleContexts, Rank2Types, StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances, ViewPatterns, TypeSynonymInstances, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
module Proof.Natural where
import Proof.Base

data instance Sing (n :: Nat) where
  SZero :: Sing Zero
  SSucc :: Sing n -> Sing (Succ n)

deriving instance Show (SNat n)

type SNat (a :: Nat) = Sing a

instance SingI Zero where
  sing = SZero

instance SingI n => SingI (Succ n) where
  sing = SSucc sing

instance SingE Zero where
  type Demote Zero = Nat
  fromSing SZero = Zero

instance (Demote n ~ Demote (Succ n), SingE n) => SingE (Succ n) where
  type Demote (Succ n) = Nat
  fromSing (SSucc n) = Succ (fromSing n)

data Nat = Zero | Succ Nat
           deriving (Show, Eq)

induction :: p Zero
          -> (forall a. (SNat a -> p a) -> SNat (Succ a) -> p (Succ a))
          -> SNat c -> p c
induction baseCase _     SZero     = baseCase
induction baseCase hypo (SSucc n) = hypo (induction baseCase hypo) (SSucc n)

one :: Nat
one = Succ Zero

sOne :: SNat (Succ 'Zero)
sOne = SSucc SZero

infixl 6 :+:
infixl 6 %+
type family   (a :: Nat) :+: (b :: Nat) :: Nat
type instance n :+: Zero   = n
type instance n :+: Succ m = Succ (n :+: m)

(%+) :: SNat n -> SNat m -> SNat (n :+: m)
n %+ SZero = n
n %+ (SSucc m) = SSucc (n %+ m)

succCongEq :: n :=: m -> Succ n :=: Succ m
succCongEq Refl = Refl

plusSuccR :: SNat a -> SNat b -> a :+: Succ b :=: Succ (a :+: b)
plusSuccR _ _ = Refl

infixl 7 :*:
type family (n :: Nat) :*: (m :: Nat) :: Nat
type instance n :*: Zero   = Zero
type instance n :*: Succ m = n :*: m :+: n

type family Fact (m :: Nat) :: Nat
type instance Fact Zero = Succ Zero
type instance Fact (Succ n) = Succ n :*: Fact n

infixl 7 %*
(%*) :: SNat n -> SNat m -> SNat (n :*: m)
_ %* SZero   = SZero
n %* SSucc m = n %* m %+ n

induction' :: forall p c. Wrappable p
           => Proxy p
           -> BaseType p Zero
           -> (forall a. (SNat a -> BaseType p a) -> SNat (Succ a) -> BaseType p (Succ a))
           -> SNat c -> BaseType p c
induction' _ base cases = unWrap . induction (wrap base) cases'
  where
    cases' :: (SNat a -> p a) -> SNat (Succ a) -> p (Succ a)
    cases' hypo = wrap . cases (unWrap . hypo)

data SNatFact n = FactSNat (SNat (Fact n))

instance Wrappable SNatFact where
  type BaseType SNatFact n = SNat (Fact n)
  wrap   = FactSNat
  unWrap (FactSNat n) = n

fact :: SNat n -> SNat (Fact n)
fact = induction' (Proxy :: Proxy SNatFact) zero cases
  where
    zero :: SNat (Fact Zero)
    zero = SSucc SZero
    cases :: (SNat n -> SNat (Fact n)) -> SNat (Succ n) -> SNat (Fact (Succ n))
    cases hypo (SSucc n) =  SSucc n %* hypo n

newtype Assoc m n l = Assoc { getAssoc :: m :+: (n :+: l) :=: (m :+: n) :+: l }
instance Wrappable (Assoc m n) where
  type BaseType (Assoc m n) l = m :+: (n :+: l) :=: (m :+: n) :+: l
  unWrap = getAssoc
  wrap = Assoc

infer :: Proxy a
infer = Proxy

plusAssoc :: forall m n l. SNat m -> SNat n -> SNat l -> m :+: (n :+: l) :=: (m :+: n) :+: l
plusAssoc m n = induction' (Proxy :: Proxy (Assoc m n)) baseCase subStep
  where
    baseCase :: BaseType (Assoc m n) Zero
    baseCase = Refl
    subStep :: (SNat l' -> BaseType (Assoc m n) l')
            -> SNat (Succ l')
            -> BaseType (Assoc m n) (Succ l')
    subStep hypo (SSucc l) =
      start (m %+ (n %+ SSucc l))
        === SSucc (m %+ (n %+ l)) `because` byDefinition
        === SSucc ((m %+ n) %+ l) `because` cong infer (hypo l)
        === (m %+ n) %+ SSucc l   `because` byDefinition

newtype Comm m n = Comm { unComm :: m :+: n :=: n :+: m }
instance Wrappable (Comm m) where
  type BaseType (Comm m) n = m :+: n :=: n :+: m
  wrap = Comm
  unWrap = unComm

plusZeroL :: SNat m -> Zero :+: m :=: m
plusZeroL SZero = Refl
plusZeroL (SSucc m) =
  start (SZero %+ (SSucc m))
    === SSucc (SZero %+ m) `because` plusSuccR SZero m
    === SSucc m            `because` succCongEq (plusZeroL m)

plusCongL :: SNat n -> m :=: m' -> n :+: m :=: n :+: m'
plusCongL _ Refl = Refl

plusCongR :: SNat n -> m :=: m' -> m :+: n :=: m' :+: n
plusCongR _ Refl = Refl

newtype Prop0 m n = Prop0 { unProp0 :: m :+: Succ n :=: Succ m :+: n }

instance Wrappable (Prop0 m) where
  type BaseType (Prop0 m) n = m :+: Succ n :=: Succ m :+: n
  wrap = Prop0
  unWrap = unProp0

nPlusSuccm :: forall m n. SNat m -> SNat n -> m :+: Succ n :=: Succ m :+: n
nPlusSuccm m = induction' (Proxy :: Proxy (Prop0 m)) base cases
  where
    base :: m :+: Succ Zero :=: Succ m :+: Zero
    base = Refl
    cases :: (SNat n' -> m :+: Succ n' :=: Succ m :+: n')
          -> SNat (Succ n')
          -> m :+: Succ (Succ n') :=: Succ m :+: Succ n'
    cases hypo (SSucc n) =
      start (m %+ SSucc (SSucc n))
        === SSucc (m %+ SSucc n)  `because` byDefinition
        === SSucc (SSucc m %+ n)  `because` cong' SSucc (hypo n)
        === SSucc m %+ SSucc n    `because` byDefinition

plusComm :: forall m n. SNat m -> SNat n -> m :+: n :=: n :+: m
plusComm m = induction' (Proxy :: Proxy (Comm m)) base cases
  where
    base :: BaseType (Comm m) Zero
    base =
      start (m %+ SZero)
        === m          `because` byDefinition
        === SZero %+ m `because` sym (plusZeroL m)
    cases :: (SNat n' -> BaseType (Comm m) n')
          -> SNat (Succ n') -> BaseType (Comm m) (Succ n')
    cases hypo (SSucc n) =
      start (m %+ SSucc n)
        === SSucc (m %+ n) `because` byDefinition
        === SSucc (n %+ m) `because` cong' SSucc (hypo n)
        === n %+ SSucc m   `because` byDefinition
        === SSucc n %+ m   `because` nPlusSuccm n m

newtype MultPlusDistr l m n =
    MultPlusDistr { unMultPlusDistr :: l :*: (m :+: n) :=: l :*: m :+: l :*: n}

instance Wrappable (MultPlusDistr l m) where
  type BaseType (MultPlusDistr l m) n = l :*: (m :+: n) :=: l :*: m :+: l :*: n
  wrap = MultPlusDistr
  unWrap = unMultPlusDistr

multPlusDistr :: forall n m l. SNat n -> SNat m -> SNat l -> n :*: (m :+: l) :=: n :*: m :+: n :*: l
multPlusDistr n m = induction' (Proxy :: Proxy (MultPlusDistr n m)) Refl cases
  where
    cases :: (SNat l' -> BaseType (MultPlusDistr n m) l')
          -> SNat (Succ l') -> BaseType (MultPlusDistr n m) (Succ l')
    cases hypo (SSucc l) =
      start (n %* (m %+ SSucc l))
        === n %* SSucc (m %+ l)      `because` byDefinition
        === n %* (m %+ l) %+ n       `because` byDefinition
        === (n %* m %+ n %* l) %+ n  `because` plusCongR n (hypo l)
        === n %* m %+ (n %* l %+ n)  `because` sym (plusAssoc (n %* m) (n %* l) n)
        === n %* m %+ n %* SSucc l   `because` byDefinition

newtype MultAssoc l m n = MultAssoc { unMultAssoc :: l :*: (m :*: n) :=: (l :*: m) :*: n }

instance Wrappable (MultAssoc m n) where
  type BaseType (MultAssoc m n) l = m :*: (n :*: l) :=: (m :*: n) :*: l
  wrap = MultAssoc
  unWrap = unMultAssoc

timesComm :: forall n m l. SNat n -> SNat m -> SNat l -> n :*: (m :*: l) :=: (n :*: m) :*: l
timesComm n m = induction' (Proxy :: Proxy (MultAssoc n m)) base cases
  where
    base :: BaseType (MultAssoc n m) Zero
    base = Refl
    cases :: (SNat l' -> BaseType (MultAssoc n m) l')
          -> SNat (Succ l') -> BaseType (MultAssoc n m) (Succ l')
    cases hypo (SSucc l) =
      start (n %* (m %* SSucc l))
        === n %* (m %* l %+ m)       `because` byDefinition
        === n %* (m %* l) %+ n %* m  `because` multPlusDistr n (m %* l) m
        === (n %* m) %* l %+ n %* m  `because` plusCongR (n%*m) (hypo l)
        === (n %* m) %* SSucc l      `because` byDefinition

newtype MultComm m n = MultComm { unMultComm :: m :*: n :=: n :*: m }

instance Wrappable (MultComm m) where
  type BaseType (MultComm m) n = m :*: n :=: n :*: m
  wrap = MultComm
  unWrap = unMultComm

multZeroL :: forall m. SNat m -> Zero :*: m :=: Zero
multZeroL SZero = Refl
multZeroL (SSucc m) =
  start (SZero %* SSucc m)
    === SZero %* m %+ SZero  `because` byDefinition
    === SZero %* m           `because` byDefinition
    === SZero                `because` multZeroL m

multZeroR :: SNat n -> n :*: Zero :=: Zero
multZeroR _ = Refl

multOneR :: SNat n -> n :*: Succ Zero :=: n
multOneR n =
  start (n %* sOne)
    === n %* SZero %+ n `because` byDefinition
    === SZero %+ n      `because` plusCongR n (multZeroR n)
    === n               `because` plusZeroL n

multOneL :: SNat n -> Succ Zero :*: n :=: n
multOneL SZero = Refl
multOneL (SSucc n) =
  start (sOne  %* SSucc n)
    === sOne %* n %+ sOne `because` byDefinition
    === n %+ sOne         `because` cong' (%+ sOne) (multOneL n)
    === SSucc n           `because` byDefinition

plusMultDistr :: forall n m l. SNat n -> SNat m -> SNat l
              -> (n :+: m) :*: l :=: n :*: l :+: m :*: l
plusMultDistr _ _ SZero = Refl
plusMultDistr n m (SSucc l) =
  start ((n %+ m) %* SSucc l)
    === (n %+ m) %* l %+ (n %+ m)   `because` byDefinition
    === (n%*l %+ m%*l) %+ (n %+ m)  `because` plusCongR (n %+ m) (plusMultDistr n m l)
    === (n%*l %+ m%*l) %+ (m %+ n)  `because` plusCongL (n%*l %+ m%*l) (plusComm n m)
    === (n%*l %+ m%*l %+ m) %+ n    `because` plusAssoc (n%*l %+ m%*l) m n
    === (n%*l %+ (m%*l %+ m)) %+ n  `because` plusCongR n (sym $ plusAssoc (n%*l) (m%*l) m)
    === (n%*l %+ (m%*l %+ m%*sOne)) %+ n
            `because` plusCongR n (plusCongL (n%*l) $ plusCongL (m%*l) $ sym $ multOneR m)
    === (n%*l %+ (m %* SSucc l)) %+ n
            `because` plusCongR n (plusCongL (n%*l) $ sym $ multPlusDistr m l sOne)
    === ((m %* SSucc l) %+ n%*l) %+ n
            `because` plusCongR n (plusComm (n %* l) (m %* SSucc l))
    === ((m %* SSucc l) %+ n%*l) %+ n %* sOne
            `because` plusCongL (m%*SSucc l %+ n%*l) (sym $ multOneR n)
    === m %* SSucc l %+ (n%*l %+ n%*sOne)
            `because` sym (plusAssoc (m %* SSucc l) (n%*l) (n %* sOne))
    === m %* SSucc l %+ n %* SSucc l
            `because` plusCongL (m %* SSucc l) (sym $ multPlusDistr n l sOne)
    === n %* SSucc l %+ m %* SSucc l   `because` plusComm (m %* SSucc l) (n %* SSucc l)

multComm :: forall n m. SNat n -> SNat m -> n :*: m :=: m :*: n
multComm n = induction' (Proxy :: Proxy (MultComm n)) base cases
  where
    base :: BaseType (MultComm n) Zero
    base = sym (multZeroL n)
    cases :: (SNat l -> BaseType (MultComm n) l)
          -> SNat (Succ l) -> BaseType (MultComm n) (Succ l)
    cases hypo (SSucc l) =
      start (n %* SSucc l)
        === n %* l %+ n          `because` byDefinition
        === l %* n %+ n          `because` plusCongR n (hypo l)
        === l %* n %+ sOne %* n  `because` plusCongL (l %* n) (sym $ multOneL n)
        === (l %+ sOne) %* n     `because` sym (plusMultDistr l sOne n)
        === SSucc l %* n         `because` byDefinition

data (a :: Nat) :<: (b :: Nat) where
  ZeroLtSucc :: Zero :<: Succ m
  SuccLtSucc :: n :<: m -> Succ n :<: Succ m
  
deriving instance Show (a :<: b)

type family (n :: Nat) :<<: (m :: Nat) :: Bool
type instance Zero   :<<: Succ n = True
type instance n      :<<: Zero   = False
type instance Succ n :<<: Succ m = n :<<: m

type family   (n :: Nat) :<<=: (m :: Nat) :: Bool
type instance Zero   :<<=: n      = True
type instance Succ n :<<=: Zero   = False
type instance Succ n :<<=: Succ m = n :<<=: m

type a :>>: b = b :<<: a
type a :>: b  = b :<: a

type a :<=: b = a :<: b :\/: a :=: b

instance FromBool (n :<: m) where
  type Predicate (n :<: m) = n :<<: m
  type Args (n :<: m) = '[Sing n, Sing m]
  fromBool = boolToPropLt

boolToPropLt :: (x :<<: y) ~ True => SNat x -> SNat y -> x :<: y 
boolToPropLt SZero (SSucc _)     = ZeroLtSucc
boolToPropLt (SSucc n) (SSucc m) = SuccLtSucc $ boolToPropLt n m
boolToPropLt _ _         = error "could not be happen"

instance FromBool (n :<=: m) where
  type Predicate (n :<=: m) = n :<<=: m
  type Args (n :<=: m) = '[Sing n, Sing m]
  fromBool = boolToPropLe

boolToPropLe :: (x :<<=: y) ~ True => SNat x -> SNat y -> x :<=: y
boolToPropLe SZero SZero         = Right Refl
boolToPropLe SZero (SSucc _)     = Left ZeroLtSucc
boolToPropLe (SSucc n) (SSucc m) =
    case boolToPropLe n m of
      Left reason -> Left $ SuccLtSucc reason
      Right Refl  -> Right Refl
boolToPropLe _ _         = error "could not be happen"

rev :: (n :<<=: m) ~ False => SNat n -> SNat m -> m :<: n
rev (SSucc _) SZero     = ZeroLtSucc
rev (SSucc n) (SSucc m) = SuccLtSucc $ rev n m
rev _         _         = error "impossible!"

leTrans :: forall n m l. n :<=: m -> m :<=: l -> n :<=: l
leTrans (Right Refl) a = a
leTrans a (Right Refl) = a
leTrans (Left ZeroLtSucc) (Left (SuccLtSucc _)) = Left ZeroLtSucc
leTrans (Left (SuccLtSucc a)) (Left (SuccLtSucc b)) =
  case leTrans (Left a) (Left b) of
    Right Refl -> Right Refl
    Left le -> Left $ SuccLtSucc le
leTrans _ _ = error "impossible!"


(%<<) :: SNat n -> SNat m -> SBool (n :<<: m)
SZero   %<< SSucc _ = STrue
_       %<< SZero   = SFalse
SSucc m %<< SSucc n = m %<< n

(%<<=) :: SNat n -> SNat m -> SBool (n :<<=: m)
SZero   %<<= _       = STrue
SSucc _ %<<= SZero   = SFalse
SSucc n %<<= SSucc m = n %<<= m

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
