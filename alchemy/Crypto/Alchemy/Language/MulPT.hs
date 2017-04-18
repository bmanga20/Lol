{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

module Crypto.Alchemy.Language.MulPT where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.Lam
import Crypto.Lol (Cyc)
import GHC.Exts

infixl 7 *#

-- | Symantics for leveled plaintext operations of some depth @d@.

class MulPT expr where

  type RingCtxPT expr (d :: Depth) a :: Constraint

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').
  (*#) :: (RingCtxPT expr d a, a ~ Cyc t m zp, Applicative i) =>
          -- CJP: generalize input depths?
          expr i (Add1 d) a -> expr i (Add1 d) a -> expr i d a