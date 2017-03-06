{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE NoImplicitPrelude          #-}
{-# LANGUAGE PolyKinds                  #-}

module Crypto.Alchemy.Interpreter.DepthEvaluator where

import Crypto.Alchemy.Lam
import Crypto.Alchemy.PTLang
import Crypto.Lol

-- | Metacircular evaluator with depth.
newtype ID d a = ID { unID :: a }
  deriving (Eq, Show)

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a

-- | Metacircular plaintext symantics.
instance SymPT ID where
  a +# b = ID $ unID a + unID b
  a -# b = ID $ unID a - unID b
  a *# b = ID $ unID a * unID b