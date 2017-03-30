{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.TunnelPT where

import Crypto.Alchemy.Depth
import Crypto.Lol (Cyc, Factored, Linear)
import GHC.Exts

-- | Symantics for leveled plaintext operations of some depth @d@.

class (Applicative mon) => TunnelPT mon expr where

  type TunnelCtxPT expr (d :: Depth) (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  tunnelPT :: (TunnelCtxPT expr d t e r s zp)
           => Linear t zp e r s -> mon (expr d (Cyc t r zp) -> expr d (Cyc t s zp))
