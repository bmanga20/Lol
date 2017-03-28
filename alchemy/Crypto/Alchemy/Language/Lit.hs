{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.Lit where

import GHC.Exts

-- | Expression literals.

class Lit expr where
  type LitCtx expr a :: Constraint
  -- | Embed a literal into an expression.
  lit :: (LitCtx expr a) => a -> expr a