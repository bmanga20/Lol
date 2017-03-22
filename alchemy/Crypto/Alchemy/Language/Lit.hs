{-# LANGUAGE TypeFamilies #-}
module Crypto.Alchemy.Language.Lit where


import Data.Constraint

class Lit expr where
  type LitCtx expr a :: Constraint
  lit :: (LitCtx expr a) => a -> expr a