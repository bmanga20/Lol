{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
--{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}

--{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
--{-# OPTIONS_GHC -fno-warn-missing-signatures      #-}

module Crypto.Alchemy.EDSL where

import Control.Applicative
import Control.Monad.Identity
import Crypto.Alchemy.Depth
import Crypto.Alchemy.Interpreter.DupCT
import Crypto.Alchemy.Interpreter.DupPT
import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.ModSwPT ()
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Alchemy.Interpreter.EvalCT ()
import Crypto.Alchemy.Interpreter.DeepSeq
import Crypto.Alchemy.Interpreter.DupRescale
import Crypto.Alchemy.Interpreter.EvalPT
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types
import Crypto.Lol.Cyclotomic.Tensor (TElt) -- EAC: I shouldn't need to explicitly import this
import Crypto.Lol.Types.ZPP -- EAC: I shouldn't need to explicitly import this...

import Data.Type.Natural

-- EAC: We can get rid of signatures once #13524 is fixed (should be in 8.2)

pt1 :: forall t m zp d ptexpr i a .
  (a ~ Cyc t m zp, Applicative i, EnvLiftable ptexpr,
   AddPT ptexpr, MulPT ptexpr, LambdaD ptexpr,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a)
  => ptexpr i (Add1 d) a -> ptexpr i (Add1 d) a -> ptexpr i d a
pt1 a b = addPublicPT 2 $ a *# (a +# b)

-- we give a type signature for easy partial type application
pt1' :: forall t m zp d ptexpr i a .
  (a ~ Cyc t m zp, Applicative i, EnvLiftable ptexpr,
   AddPT ptexpr, MulPT ptexpr, LambdaD ptexpr,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a)
  => ptexpr i ('L (Add1 d) ('L (Add1 d) d)) (Cyc t m zp -> Cyc t m zp -> Cyc t m zp)
pt1' = lam2 $ pt1

pt1'' :: forall t m zp d ptexpr i a .
  (a ~ Cyc t m zp, Applicative i, EnvLiftable ptexpr,
   AddPT ptexpr, MulPT ptexpr, LambdaD ptexpr, Lit (ptexpr i (Add1 d)),
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, LitCtx (ptexpr i (Add1 d)) a)
  => a -> a -> ptexpr i d a
pt1'' a b = appD (appD pt1' (lit a)) (lit b)

tunn1 :: forall t r u s zp d expr i eru eus.
  (TunnelPTCtx' expr d t eru r u zp,
   TunnelPTCtx' expr d t eus u s zp,
   LambdaD expr, Applicative i)
  => Proxy u -> expr i ('L d d) (Cyc t r zp -> Cyc t s zp)
tunn1 _ = lam1 $ \x -> tunnelPT' $ tunnelPT' @u x

type Zq q = ZqBasic q Int64

-- EAC: probably would be useful to make a constraint syn
-- type AddditiveCtxPT' expr d a = (AddPT expr, AdditiveCtxPT expr d a)
-- and similarly for other associated constraint syns

main :: IO ()
main = do
  let (exp1a, exp1b) = dupPT $ pt1' @CT @F4 @(Zq 7) @('T 'Z)
      (exp2a, exp2b) = dupPT $ pt1'' @CT @F4 @Int64 7 11

  -- print the unapplied PT function
  putStrLn $ showPT exp1a
  -- apply the PT function to arguments, then print it out
  putStrLn $ showPT exp2a
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ evalPT exp2b
  -- compile the un-applied function to CT, then print it out
  (x,_) <- compile
         @'[ '(F4, F8) ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         exp1b
  putStrLn $ showCT x

  let (exp3a, exp3b) = dupPT $ tunn1 @CT @H0 @H1 @H2 @(Zq PP8) @('T 'Z) Proxy
  -- example with rescale de-duplication when tunneling
  -- print the unapplied PT function
  putStrLn $ showPT exp3a
  -- compile the up-applied function to CT, then print it out
  (y,_) <- compile
         @'[ '(H0, H0'), '(H1,H1'), '(H2, H2') ]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         exp3b
  -- compile once, interpret with multiple ctexprs!!
  let (z1,z2) = dupCT $ runDeepSeq y
  putStrLn $ showCT z1
  putStrLn $ showCT $ runDupRescale z2

type H0 = F8
type H1 = F4 * F7
type H2 = F2 * F7 * F13
type H0' = H0 * F7 * F13
type H1' = H1 * F13
type H2' = H2

-- EAC: This is copied from HomomPRF, but it needs a permanent home.
type TunnelPTCtx' expr d t e r s zp =
  (e ~ FGCD r s,                                     -- type restriction for simplicity
   TunnelPT expr, TunnelCtxPT expr d t e r s zp, -- call to tunnelPT
   e `Divides` r, e `Divides` s, CElt t zp,          -- linearDec
   ZPP zp, TElt t (ZpOf zp))                         -- crtSet

tunnelPT' :: forall s expr t r zp e d j . (TunnelPTCtx' expr d t e r s zp, Applicative j)
  => expr j d (Cyc t r zp) -> expr j d (Cyc t s zp)
tunnelPT' =
  let crts = proxy crtSet (Proxy::Proxy e)
      r = proxy totientFact (Proxy::Proxy r)
      e = proxy totientFact (Proxy::Proxy e)
      dim = r `div` e
      -- only take as many crts as we need
      -- otherwise linearDec fails
      linf = linearDec (take dim crts) :: Linear t zp e r s
  in tunnelPT linf
