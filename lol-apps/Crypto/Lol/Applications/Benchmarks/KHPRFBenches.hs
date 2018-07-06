{-|
Module      : Crypto.Lol.Applications.Benchmarks.KHPRFBenches
Description : Benchmarks for KeyHomomorphicPRF.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : bmanga@umich.edu
Stability   : experimental
Portability : POSIX

Benchmarks for KeyHomomorphicPRF.
-}

{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE NoImplicitPrelude     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Lol.Applications.Benchmarks.KHPRFBenches (khprfBenches) where

import Control.Applicative
import Control.DeepSeq
import Control.Monad.Random hiding (fromList, split)

import Crypto.Lol hiding (replicate)
import Crypto.Lol.Types
import Crypto.Lol.Applications.KeyHomomorphicPRF
import Crypto.Lol.Reflects

import Criterion.Main

type M = F64
type N = 1
type Q = 256
type P = 2
type Zq q = ZqBasic q Int64
type Rq t = Cyc t M (Zq Q)
type Rp t = Cyc t M (Zq P)

-- | left-spine tree with the given number of leaves
type family Left n where
  Left 'O       = 'Leaf
  Left ('S n')  = 'Intern (Left n') 'Leaf

-- | right-spine tree with the given number of leaves
type family Right n where
  Right 'O      = 'Leaf
  Right ('S n') = 'Intern 'Leaf (Right n')

type Complete0 = 'Leaf
type Complete1 = 'Intern Complete0 Complete0
type Complete2 = 'Intern Complete1 Complete1
type Complete3 = 'Intern Complete2 Complete2
type Complete4 = 'Intern Complete3 Complete3
type Complete5 = 'Intern Complete4 Complete4

khprfBenches :: forall ts rnd gad .
  (MonadRandom rnd, Random (Rq ts), Rescale (Rq ts) (Rp ts),
   Decompose gad (Rq ts), Reduce (DecompOf (Rq ts)) (Rq ts), 
   Reflects N Int, Gadget gad (Rq ts), NFData (Rp ts))
  => Proxy ts -> Proxy gad -> rnd Benchmark
khprfBenches _ _ = do
  key :: PRFKey N (Rq ts) <- genKey
  params :: PRFParams N gad (Rq ts) <- genParams
  let sc  = singFBT :: Sing Complete5
      sl  = singFBT :: Sing (Left  P32)
      sr  = singFBT :: Sing (Right P32)
      xs  = take 32 values
      x   = head xs
      prp = Proxy :: Proxy (Rp ts)
  return $ bgroup "KHPRF Benchmarks"
    [ bench "complete-solo"      $ prfBench          prp sc params key x
    , bench "left-solo"          $ prfBench          prp sl params key x
    , bench "right-solo"         $ prfBench          prp sr params key x
    , bench "complete-amortized" $ prfAmortizedBench prp sc params key xs
    , bench "left-amortized"     $ prfAmortizedBench prp sl params key xs
    , bench "right-amortized"    $ prfAmortizedBench prp sr params key xs
    ]

prfBench :: forall t n gad rq rp .
  (Rescale rq rp, Decompose gad rq, Reduce (DecompOf rq) rq,
   FBTC t, NFData rp)
  => Proxy rp
  -> SFBT t -> PRFParams n gad rq -> PRFKey n rq -> BitString (SizeFBT t)
  -> Benchmarkable
prfBench _ t p s x = nf (prf t p s :: _ -> Matrix rp) x

prfAmortizedBench :: forall t n gad rq rp .
    (Rescale rq rp, Decompose gad rq, Reduce (DecompOf rq) rq, NFData rp)
  => Proxy rp
  -> SFBT t -> PRFParams n gad rq -> PRFKey n rq -> [BitString (SizeFBT t)]
  -> Benchmarkable
prfAmortizedBench _ t p s xs =
  nf (run :: _ -> [Matrix rp]) (sequence $ prfAmortized t p s <$> xs)
