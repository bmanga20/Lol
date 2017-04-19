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
newtype ID i (d :: Depth) a = ID {unID :: i a} deriving (Show, Eq, Functor)

lift2 :: (Applicative i) => (a -> b -> c) -> (ID i d a) -> (ID i d' b) -> (ID i d'' c)
lift2 f a b = ID $ f <$> (unID a) <*> (unID b)

-- | Metacircular plaintext symantics.
instance AddPT ID where

  type AddPubCtxPT   ID d a = (Additive a)
  --type MulPubCtxPT   ID d a = (Ring a)
  type AdditiveCtxPT ID d a = (Additive a)

  (+#) = lift2 (+)
  negPT         = fmap (fmap negate)
  addPublicPT a = fmap (a+)
  mulPublicPT a = fmap (fmap (a*))

instance MulPT ID where

  type RingCtxPT ID d a = (Ring a)

  (*#) = lift2 (*)
{-
instance ModSwPT ID where

  type ModSwitchCtxPT ID d (Cyc t m zp) zp' = (RescaleCyc (Cyc t) zp zp', Fact m)

  modSwitchDec = fmap rescaleDec

instance (Applicative mon) => TunnelPT mon ID where

  type TunnelCtxPT ID d t e r s zp = (e `Divides` r, e `Divides` s, CElt t zp)

  tunnelPT = pure . fmap . evalLin
-}
-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f <*> unID a

instance (Applicative i) => Lit (ID i d) where
  type LitCtx (ID i d) a = ()
  lit = ID . pure
