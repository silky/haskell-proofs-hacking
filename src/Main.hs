{-# language DataKinds            #-}
{-# language GADTs                #-}
{-# language PolyKinds            #-}
{-# language ScopedTypeVariables  #-}
{-# language TypeFamilies         #-}
{-# language TypeOperators        #-}
{-# language UndecidableInstances #-}

-- See: https://janmasrovira.gitlab.io/ascetic-slug/post/haskell-proofs/

module Main where

import Data.Kind

main :: IO ()
main = do
  putStrLn "hello world"


data a :~: b where
  Refl :: a :~: a

sym :: forall x y. (x :~: y) -> (y :~: x)
sym Refl = Refl


-- anyProof :: forall a. a
-- anyProof = anyProof

trans :: forall x y z. 
         (x :~: y)
      -> (y :~: z)
      -> (x :~: z)
trans Refl Refl = Refl

data Nat where
  Z :: Nat
  S :: Nat -> Nat

one :: Nat
one = S Z

two :: Nat
two = S one

type One = 'S 'Z
type Two = 'S One

type family (a :: Nat) :+: (b :: Nat) :: Nat where
  'Z :+: b   = b
  'S a :+: b = 'S (a :+: b)

onePlusOne :: (One :+: One) :~: Two
onePlusOne = Refl

-- nPlusZero :: (n :+: 'Z) :~: n
-- nPlusZero = Refl

data SNat (n :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

nPlusZero :: SNat n -> (n :+: 'Z) :~: n
nPlusZero SZ = Refl
nPlusZero (SS m) = congSuc (nPlusZero m)

congSuc :: a :~: b -> 'S a :~: 'S b
congSuc Refl = Refl

(.+.) :: SNat a -> SNat b -> SNat (a :+: b)
SZ .+. b    = b
SS a .+. b = SS (a .+. b)

