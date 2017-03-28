{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Crypto.Alchemy.Language.Lam where

import Crypto.Alchemy.Common

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b


-- | Lambda abstraction and application for leveled computations.

class LambdaD expr where
  -- | Abstract.
  lamD :: (expr ('F da) a -> expr db b) -> expr ('N da db) (a -> b)

  -- | Apply.
  appD :: expr ('N da db) (a -> b) -> expr ('F da) a -> expr db b
