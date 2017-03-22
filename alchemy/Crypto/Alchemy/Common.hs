{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds     #-}
{-# LANGUAGE TypeFamilies  #-}
{-# LANGUAGE TypeOperators #-}

module Crypto.Alchemy.Common where

import Crypto.Lol hiding (type S)
import Crypto.Lol.Types
import Data.Type.Natural

-- singletons exports (:!!), which takes a TypeLit index; we need a TypeNatural index
type family (xs :: [k1]) !! (d :: Nat) :: k1 where
  (x ': xs) !! 'Z = x
  (x ': xs) !! 'S s = xs !! s

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

class Compile inexpr outexpr a where
  type CompiledType inexpr a

  compile :: inexpr a -> outexpr (CompiledType inexpr a)