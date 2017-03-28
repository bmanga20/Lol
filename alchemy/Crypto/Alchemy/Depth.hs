{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

module Crypto.Alchemy.Depth where

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
