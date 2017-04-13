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
import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Lol

-- | Metacircular evaluator with depth.
newtype ID (d :: Depth) a = ID {unID :: a} deriving (Show, Eq, Functor)


lift2 :: (Applicative i) => (a -> b -> c) -> i (ID d a) -> i (ID d' b) -> i (ID d'' c)
lift2 f a b = ID <$> (f <$> (unID <$> a) <*> (unID <$> b))

-- | Metacircular plaintext symantics.
instance AddPT ID where

  type AddPubCtxPT   i ID d a = (Additive a, Functor i)
  --type MulPubCtxPT   ID d a = (Ring a)
  type AdditiveCtxPT i ID d a = (Additive a, Applicative i)

  (+#) = lift2 (+)
  --negPT         = fmap negate
  addPublicPT a = fmap (fmap (a+))
  --mulPublicPT a = fmap (fmap (a*))

instance MulPT ID where

  type RingCtxPT i ID d a = (Ring a, Applicative i)

  (*#) = lift2 (*)
{-
instance ModSwPT ID where

  type ModSwitchCtxPT ID d (Cyc t m zp) zp' = (RescaleCyc (Cyc t) zp zp', Fact m)

  modSwitchDec = fmap rescaleDec

instance (Applicative mon) => TunnelPT mon ID where

  type TunnelCtxPT ID d t e r s zp = (e `Divides` r, e `Divides` s, CElt t zp)

  tunnelPT = pure . fmap . evalLin

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a
-}
instance Lit (ID d) where
  type LitCtx (ID d) a = ()
  lit = ID
