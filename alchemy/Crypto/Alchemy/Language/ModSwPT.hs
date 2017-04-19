{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.ModSwPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc, Prime2, PrimePower(PP), Pos(..))
import Crypto.Lol.Types (ZqBasic)
import GHC.Exts

-- a concrete Z_2^e data type
type Z2E e i = ZqBasic ('PP '(Prime2, e)) i

-- | Symantics for leveled plaintext operations of some depth @d@.

class ModSwPT expr where

  type ModSwitchCtxPT expr (d :: Depth) a zp' :: Constraint

  -- | Plaintext multiplication.  Inputs must be one depth less than
  -- output (so we can't use 'Ring').
  modSwitchDec :: (ModSwitchCtxPT expr d a zp', a ~ Cyc t m zp,
                   zp' ~ Z2E e i, zp ~ Z2E ('S e) i, Applicative j)
               => expr j d a -> expr j d (Cyc t m zp')