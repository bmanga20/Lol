{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeOperators    #-}

module Crypto.Alchemy.Language.HomomTunnel where

import Crypto.Lol hiding (Pos(..), type (*))
import Data.Constraint

-- | Symantics for leveled plaintext operations of some depth @d@.

class (Applicative mon) => HomomTunnel mon expr where

  type TunnelCtxPT expr (t :: Factored -> * -> *) (e :: Factored) (r :: Factored) (s :: Factored) zp :: Constraint

  tunnelPT :: (TunnelCtxPT expr t e r s zp)
           => Linear t zp e r s -> mon (expr (Cyc t r zp) -> expr (Cyc t s zp))
