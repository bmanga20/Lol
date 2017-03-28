{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Crypto.Alchemy.Common where

import Crypto.Lol hiding (type S)
import Crypto.Lol.Types
import Data.Type.Natural

import Data.Singletons.Prelude hiding (Lookup)
import Data.Singletons.TH

singletons [d|
            -- Positive naturals (1, 2, ...) in Peano representation.
            data Depth = F Nat       -- one
                       | N Nat Depth -- successor
                       deriving (Show, Eq)
  |]

-- singletons exports (:!!), which takes a TypeLit index; we need a TypeNatural index
type family (xs :: [k1]) !! (d :: Depth) :: k1 where
  (x ': xs) !! ('F 'Z) = x
  (x ': xs) !! ('F ('S s)) = xs !! ('F s)

-- singletons exports Length, which returns a TypeLit; we need a TypeNatural
type family Length (a :: [k]) :: Nat where
  Length '[] = 'Z
  Length (x ': xs) = 'S (Length xs)

-- a type-lvel map from PT index to CT index
--type Lookup m m'map = FromJust (Lookup m m'map)
type family Lookup m map where
  Lookup m ( '(m,m') ': rest) = m'
  Lookup r ( '(m,m') ': rest) = Lookup r rest

-- concrete Z integer representation
type Z = Int64

-- a concrete Z_2^e data type
type Z2E e = ZqBasic ('PP '(Prime2, e)) Z
