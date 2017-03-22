{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTSyntax          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE UndecidableInstances #-}

module Crypto.Alchemy.Interpreter.PTEval where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.PT
import Crypto.Lol

-- EAC: Another data type that requires a CUSK (i.e., kind sigs for all vars)
-- | Metacircular evaluator with depth.
newtype ID (d :: k) (a :: *) = ID {unID :: a} deriving (Show, Eq)

-- | Metacircular lambda with depth.
instance LambdaD ID where
  lamD f   = ID $ unID . f . ID
  appD f a = ID $ unID f $ unID a

-- | Metacircular plaintext symantics.
instance SymPT ID where

  type AddPubCtxPT   ID d t m zp     = (Additive (Cyc t m zp))
  type MulPubCtxPT   ID d t m zp     = (Ring (Cyc t m zp))
  type AdditiveCtxPT ID d t m zp     = (Additive (Cyc t m zp))
  type RingCtxPT     ID d t m zp     = (Ring (Cyc t m zp))
  type TunnelCtxPT   ID d t e r s zp = (e `Divides` r, e `Divides` s, CElt t zp)

  a +# b = ID $ unID a + unID b
  neg a = ID $ negate $ unID a
  a *# b = ID $ unID a * unID b
  addPublicPT a b = ID $ a + unID b
  mulPublicPT a b = ID $ a * unID b
  tunnelPT linf = ID . evalLin linf . unID

instance Lit (ID d) where
  type LitCtx (ID d) a = ()
  lit = ID
