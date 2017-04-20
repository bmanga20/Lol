{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.TunnelPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc, Factored, Linear)
import GHC.Exts

-- | Symantics for leveled plaintext operations of some depth @d@.

class TunnelPT expr where

  type TunnelCtxPT expr (d :: Depth) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  tunnelPT :: (TunnelCtxPT expr d t e r s zp, Applicative i)
           => Linear t zp e r s -> expr i d (Cyc t r zp) -> expr i d (Cyc t s zp)
