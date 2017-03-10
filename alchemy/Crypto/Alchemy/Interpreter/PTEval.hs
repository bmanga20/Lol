{-# LANGUAGE ExplicitNamespaces  #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTSyntax          #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE TypeOperators       #-}

module Crypto.Alchemy.Interpreter.PTEval where

import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.PT
import Crypto.Lol
import Crypto.Lol.Types.ZPP
import Crypto.Lol.Cyclotomic.Tensor

-- EAC: Another data type that requirs a CUSK (i.e., kind sigs for all vars)
-- | Metacircular evaluator with depth.
newtype ID (d :: k) (a :: *) = ID {unID :: a} deriving (Show, Eq)

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

  -- generates the tunnel functions at evaluation time
  tunnelPT :: forall e r s d t zp . (e ~ FGCD r s, e `Divides` r, e `Divides` s,
                                   CElt t zp, ZPP zp, TElt t (ZpOf zp))
           => ID d (Cyc t r zp) -> ID d (Cyc t s zp)
  tunnelPT =
    -- EAC: copy-pasted from PTTunnel instance in Crypto.Lol.Applications.HomomPRF
    -- we should find a real home for this code...
    let crts = proxy crtSet (Proxy::Proxy e)
        r = proxy totientFact (Proxy::Proxy r)
        e = proxy totientFact (Proxy::Proxy e)
        dim = r `div` e
        -- only take as many crts as we need
        -- otherwise linearDec fails
        linf = linearDec (take dim crts) :: Linear t zp e r s
    in ID . evalLin linf . unID
