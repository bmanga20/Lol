{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Crypto.Alchemy.Common where

import Data.Singletons.Prelude
import Data.Singletons.TH
import Data.Type.Natural

-- | Depth of a computation.
singletons [d|
            data Depth = T Nat         -- depth of a Term
                       | L Depth Depth -- depth of a Lambda
                       deriving (Show, Eq)
  |]

type family Add1 d where
  Add1 ('T d) = 'T ('S d)

-- concrete Z integer representation
--type Z = Int64

-- a concrete Z_2^e data type
--type Z2E e = ZqBasic ('PP '(Prime2, e)) Z
