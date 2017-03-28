{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Crypto.Alchemy.Interpreter.PTEval where

import Control.Applicative
import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Lol

-- | Metacircular evaluator with depth.
newtype ID (d :: Depth) a = ID {unID :: a} deriving (Show, Eq, Functor)

-- | Metacircular plaintext symantics.
instance AddPT (ID d) where

  type AddPubCtxPT   (ID d) t m zp = (Additive (Cyc t m zp))
  type MulPubCtxPT   (ID d) t m zp = (Ring (Cyc t m zp))
  type AdditiveCtxPT (ID d) t m zp = (Additive (Cyc t m zp))

  a +# b = ID $ unID a + unID b
  negPT         = fmap negate
  addPublicPT a = fmap (a+)
  mulPublicPT a = fmap (a*)

instance (Applicative mon) => MulPT mon ID where

  type RingCtxPT ID d t m zp = (Ring (Cyc t m zp))

  (*#) = pure $ \a b -> ID $ unID a * unID b

instance (Applicative mon) => TunnelPT mon (ID d) where

  type TunnelCtxPT (ID d) t e r s zp = (e `Divides` r, e `Divides` s, CElt t zp)

  tunnelPT = pure . fmap . evalLin

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a

instance Lit (ID d) where
  type LitCtx (ID d) a = ()
  lit = ID
