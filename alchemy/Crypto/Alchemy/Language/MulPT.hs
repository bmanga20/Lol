{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.MulPT where

import Crypto.Alchemy.Common
import Crypto.Lol hiding (Pos(..), type (*))
import Data.Type.Natural
import Data.Constraint

-- | Symantics for leveled plaintext operations of some depth @d@.

class (Applicative mon) => MulPT mon expr where

  type RingCtxPT expr (d :: Depth) (t :: Factored -> * -> *) (m :: Factored) zp :: Constraint

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').
  (*#) :: (RingCtxPT expr ('F d) t m zp, a ~ Cyc t m zp) =>
          -- CJP: generalize input depths?
          mon (expr ('F ('S d)) a -> expr ('F ('S d)) a -> expr ('F d) a)