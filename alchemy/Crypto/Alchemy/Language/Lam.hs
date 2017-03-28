{-# LANGUAGE DataKinds #-}

module Crypto.Alchemy.Language.Lam where

import Crypto.Alchemy.Depth

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b


-- | Lambda abstraction and application for leveled computations.

class LambdaD expr where
  -- | Abstract.
  lamD :: (expr da a -> expr db b) -> expr ('L da db) (a -> b)

  -- | Apply.
  appD :: expr ('L da db) (a -> b) -> expr da a -> expr db b
