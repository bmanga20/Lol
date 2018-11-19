{-|
Module      : Crypto.Lol.Applications.CCASecureEncryption
Description : Chosen Ciphertext-Secure Encryption from Section 6.3 of
              <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : cpeikert@alum.mit.edu
Stability   : experimental
Portability : POSIX

Chosen Ciphertext-Secure Encryption from Section 6.3 of
<http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
-}

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Lol.Applications.CCASecureEncryption where

import Control.Monad.Random

import Crypto.Lol
import Crypto.Lol.Applications.Trapdoor as TD hiding (PublicKey)
import qualified Crypto.Lol.Applications.Trapdoor as TD (PublicKey)

import Data.Set

import MathObj.Matrix as M hiding (zero)

import qualified Prelude (sum)

type SecretKey gad rq = Trapdoor gad rq

data PublicKey gad tag rq     = PK { a  :: TD.PublicKey gad tag rq
                                   , u  :: rq }
data Ciphertext gad tag rq    = CTxt { h  :: tag
                                     , b  :: LWEOutput gad rq
                                     , b' :: LWEOutput gad rq }

-- | Generate key pair using uniformly-random public parameter.
keyGen :: (r ~ LiftOf rq, Reduce r rq, Ring rq, Module ff rq,
          Gadget gad rq, RoundedGaussianCyc cm r,
          MonadRandom rnd, Random rq)
  => Int
  -> rnd (SecretKey gad rq, PublicKey gad ff rq)
keyGen = keyGen' =<< rndPublicParam -- takes integer value for mBar as input

-- | Generate key pair given pre-generated public parameter.
keyGen' :: (r ~ LiftOf rq, Reduce r rq, Ring rq, Module tag rq,
            Gadget gad rq, RoundedGaussianCyc cm r,
            Random rq, MonadRandom rnd)
  => PublicParam rq
  -> rnd (SecretKey gad rq, PublicKey gad tag rq)
keyGen' aBar = do
  (trap, a) <- trapGen aBar $ Tag zero
  u         <- getRandom
  return (trap, PK a u)

-- | Encrypt message using public key.
encrypt :: (Rescale msg rq, MonadRandom rnd, Random rq, Random tag)
  => PublicKey gad tag rq -> msg -> rnd (Ciphertext gad tag rq)
encrypt (PK a u) m = do
  h  <- trapTag
  s  <- lweSecret
  b  <- lweRandomError a h s
  b' <- lweRandomError u h s  -- What format/type will the matrix U be?
  return CTxt h b $ b' + rescale m

-- | Decrypt ciphertext using public key and secret key.
decrypt :: (Field tag, ZeroTestable tag, Ring rq, Correct gad rq, Module tag rq,
        Rescale rq msg)
  => PublicKey gad tag rq -> SecretKey gad rq -> Ciphertext gad tag rq
  -> Maybe msg
decrypt (PK a u) sk (CTxt h b b') = do
  (Sec s, e) <- lweInv a sk h b
  -- let shortError = errorSqNorm e < threshold
  return $ rescale $ b' - scale s u


-- SUBROUTINES --

errorSqNorm :: ((cm z) ~ LiftOf (cm zq), LiftCyc cm zq, GSqNormCyc cm z)
  => LWEError (cm zq) -> z
errorSqNorm (Err eBar e') = let sqNorm = Prelude.sum $ fmap (gSqNorm . liftCyc)
                            in sqNorm eBar + sqNorm e'

-- threshold ::
