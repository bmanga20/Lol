{-# LANGUAGE RankNTypes, TypeInType  #-}

module Crypto.Alchemy.Lam where

import Data.Kind

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b


-- | Lambda abstraction and application for leveled computations.

class LambdaD (expr :: forall k . k -> * -> *) where
  -- | Abstract.
  lamD :: (expr da a -> expr db b) -> expr '(da,db) (a -> b)

  -- | Apply.
  appD :: expr '(da,db) (a -> b) -> expr da a -> expr db b