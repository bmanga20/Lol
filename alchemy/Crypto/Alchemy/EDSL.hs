{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.EDSL where

import Control.Applicative
import Control.Monad.Identity
import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.ModSwPT ()
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.DupRescale
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types
import Crypto.Lol.Cyclotomic.Tensor (TElt) -- EAC: I shouldn't need to explicitly import this
import Crypto.Lol.Types.ZPP -- EAC: I shouldn't need to explicitly import this...

import Data.Type.Natural


{-
(AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
 AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
 RingCtxPT ptexpr d a, Ring a, Applicative mon, LambdaD ptexpr)
-}
pt1 :: forall t m zp d ptexpr mon . (_)
  => mon (ptexpr ('L (Add1 d) ('L (Add1 d) d)) (Cyc t m zp -> Cyc t m zp -> Cyc t m zp))
pt1 = (\(*$) -> lamD $ \b -> lamD $ \a -> addPublicPT 2 $ a *$ (a +# b)) <$> (*#)

{-
(AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
 AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
 RingCtxPT ptexpr d a, Ring a, Applicative mon, LambdaD ptexpr)
-}
pt2 :: forall t m zp d ptexpr mon . (_)
  => Cyc t m zp -> Cyc t m zp -> mon (ptexpr d (Cyc t m zp))
pt2 a b = (\f -> appD (appD f $ lit a) $ lit b) <$> pt1

{-
(TunnelPTCtx' expr d mon t eru r u zp,
 TunnelPTCtx' expr d mon t eus u s zp,
 Monad mon, LambdaD expr)
-}
tunn1 :: forall t r u s zp d mon expr . (_)
  => Proxy u -> mon (expr ('L d d) (Cyc t r zp -> Cyc t s zp))
tunn1 _ = do
  tunnel1 <- tunnelPT' @u
  tunnel2 <- tunnelPT'
  return $ lamD $ \x -> tunnel2 $ tunnel1 x

type Zq q = ZqBasic q Int64

main :: IO ()
main = do
  -- print the unapplied PT function
  putStrLn $ unSPT $ runIdentity $ pt1 @CT @F4 @Int64 @('T 'Z)
  -- apply the PT function to arguments, then print it out
  putStrLn $ unSPT $ runIdentity $ pt2 @CT @F4 @Int64 7 11
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ unID $ runIdentity $ pt2 @CT @F4 @Int64 7 11
  -- compile the un-applied function to CT, then print it out
  (x,_) <- compile
         @'[ '(F4, F8) ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (pt1 @CT @F4 @(Zq 7) @('T 'Z))
  putStrLn $ unSCT x




  -- example with rescale de-duplication when tunneling
  -- print the unapplied PT function
  putStrLn $ unSPT $ runIdentity $ tunn1 @CT @H0 @H1 @H2 @(Zq PP8) @('T 'Z) Proxy
  -- compile the up-applied function to CT, then print it out
  (y,_) <- compile
         @'[ '(H0, H0'), '(H1,H1'), '(H2, H2') ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (tunn1 @CT @H0 @H1 @H2 @(Zq PP8) @('T 'Z) Proxy)
  putStrLn $ unSCT y
  -- compile the up-applied function to CT, then print it out after removing duplicate rescales
  (y',_) <- compile
         @'[ '(H0, H0'), '(H1,H1'), '(H2, H2') ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (tunn1 @CT @H0 @H1 @H2 @(Zq PP8) @('T 'Z) Proxy)
  putStrLn $ unSCT $ runDupRescale y'




type H0 = F4
type H1 = F2 * F7
type H2 = F7 * F13
type H0' = H0 * F7 * F13
type H1' = H1 * F13
type H2' = H2

-- EAC: This is copied from HomomPRF, but it needs a permanent home.
type TunnelPTCtx' expr d mon t e r s zp =
  (e ~ FGCD r s,                                     -- type restriction for simplicity
   TunnelPT mon expr, TunnelCtxPT expr d t e r s zp, -- call to tunnelPT
   e `Divides` r, e `Divides` s, CElt t zp,          -- linearDec
   ZPP zp, TElt t (ZpOf zp))                         -- crtSet
tunnelPT' :: forall s mon expr t r zp e d . (TunnelPTCtx' expr d mon t e r s zp)
  => mon (expr d (Cyc t r zp) -> expr d (Cyc t s zp))
tunnelPT' =
  let crts = proxy crtSet (Proxy::Proxy e)
      r = proxy totientFact (Proxy::Proxy r)
      e = proxy totientFact (Proxy::Proxy e)
      dim = r `div` e
      -- only take as many crts as we need
      -- otherwise linearDec fails
      linf = linearDec (take dim crts) :: Linear t zp e r s
  in tunnelPT linf