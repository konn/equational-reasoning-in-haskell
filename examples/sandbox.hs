{-# LANGUAGE DataKinds, GADTs, InstanceSigs, KindSignatures, RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables, StandaloneDeriving, TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies, TypeOperators, UndecidableInstances          #-}
module Main where
import Data.Singletons
import Data.Singletons.Prelude.Num ((%:-))
import Data.Singletons.TH
import Data.Type.Equality
import GHC.TypeLits
import Prelude                     hiding ((+))
import Proof.Equational
import Unsafe.Coerce               (unsafeCoerce)

singletons [d|
 data Peano = Z | S Peano
 |]

slowRefl :: SPeano n -> n :~: n
slowRefl SZ = Refl
slowRefl (SS n) =
  case slowRefl n of
    Refl -> Refl

type family FromInteger a where
  FromInteger 0 = 'Z
  FromInteger n = 'S (FromInteger (n - 1))

type family ToInteger a where
  ToInteger 'Z = 0
  ToInteger ('S n) = 1 + ToInteger n

sFromInteger :: Sing n -> SPeano (FromInteger n)
sFromInteger n =
  case (sing :: Sing 0) %~ n of
    Proved Refl -> SZ
    Disproved _ -> unsafeCoerce (SS (sFromInteger (n %:- (sing :: Sing 1))))


succFromCommute :: Sing  n -> ToInteger n + 1 :~: ToInteger ('S n)
succFromCommute _ = loop 1223456789
  where
    loop 0 = unsafeCoerce (Refl :: () :~: ())
    loop n = loop (n - 1)

trivial :: (ToInteger ('S (FromInteger 45)) ~ (ToInteger (FromInteger 45) + 1)) =>  ()
trivial = ()

main :: IO ()
main = act

act :: IO ()
act =
  let sn = sing :: Sing (FromInteger 45)
  in print $ withRefl (succFromCommute sn) trivial

