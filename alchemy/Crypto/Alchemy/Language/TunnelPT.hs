{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Language.TunnelPT where

import Crypto.Lol (Cyc, Factored, Linear)
import GHC.Exts

-- | Symantics for leveled plaintext operations of some depth @d@.

class (Applicative mon) => TunnelPT mon expr where

  type TunnelCtxPT expr (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  tunnelPT :: (TunnelCtxPT expr t e r s zp)
           => Linear t zp e r s -> mon (expr (Cyc t r zp) -> expr (Cyc t s zp))
