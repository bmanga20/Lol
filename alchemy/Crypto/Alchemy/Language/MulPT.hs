{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.MulPT where

import Crypto.Alchemy.Common
import Crypto.Lol (Cyc)
import GHC.Exts

-- | Symantics for leveled plaintext operations of some depth @d@.

class (Applicative mon) => MulPT mon expr where

  type RingCtxPT expr (d :: Depth) a :: Constraint

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').
  (*#) :: (RingCtxPT expr d a, a ~ Cyc t m zp) =>
          -- CJP: generalize input depths?
          mon (expr (Add1 d) a -> expr (Add1 d) a -> expr d a)