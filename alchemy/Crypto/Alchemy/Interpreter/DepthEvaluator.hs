{-# LANGUAGE ExplicitNamespaces         #-}
{-# LANGUAGE GADTSyntax                 #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE TypeInType                 #-}

module Crypto.Alchemy.Interpreter.DepthEvaluator where

import Crypto.Alchemy.Lam
import Crypto.Alchemy.PTLang
import Crypto.Lol hiding (type (*))
import Data.Kind

-- | Metacircular evaluator with depth.

newtype ID :: forall k . k -> * -> * where
 ID :: {unID :: a} -> ID d a
 deriving (Eq, Show)

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a

-- | Metacircular plaintext symantics.
instance SymPT ID where
  a +# b = ID $ unID a + unID b
  neg a = ID $ negate $ unID a
  a *# b = ID $ unID a * unID b
  addPublicPT a b = ID $ a + unID b
  mulPublicPT a b = ID $ a * unID b