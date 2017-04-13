{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators #-}

module Crypto.Alchemy.Language.MulPT where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.Lam
import Crypto.Lol (Cyc)
import GHC.Exts

infixl 7 *#

-- | Symantics for leveled plaintext operations of some depth @d@.

class MulPT expr where

  type RingCtxPT (i :: * -> *) expr (d :: Depth) a :: Constraint

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').
  (*#) :: (RingCtxPT i expr d a, a ~ Cyc t m zp, Applicative j) =>
          -- CJP: generalize input depths?
          (i :. j) (expr (Add1 d) a) -> (i :. j) (expr (Add1 d) a) -> (i :. j) (expr d a)