{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.EDSL where

import Control.Applicative
import Control.Monad.Identity
import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.CT ()
--import Crypto.Alchemy.Language.IR ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.HomomTunnel ()
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2CT
--import Crypto.Alchemy.Interpreter.PT2IR
--import Crypto.Alchemy.Interpreter.IR2CT
import Crypto.Alchemy.Interpreter.ShowPT
--import Crypto.Alchemy.Interpreter.ShowIR
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..), type (*))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types

import Data.Type.Natural

-- EAC: Annoying that we need two AddPT constraints here!
pt1 :: forall a d ptexpr mon t m zp .
  (AddPT (ptexpr ('F d)), AddPT (ptexpr ('F ('S d))), MulPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT (ptexpr ('F d)) t m zp, AdditiveCtxPT (ptexpr ('F ('S d))) t m zp,
   RingCtxPT ptexpr ('F d) t m zp, Ring a, Applicative mon)
  => mon (ptexpr ('F ('S d)) a -> ptexpr ('F ('S d)) a -> ptexpr ('F d) a)
pt1 = (\star a b -> addPublicPT 2 $ a `star` (a +# b)) <$> (*#)

pt2 :: forall a d ptexpr mon t m zp .
  (AddPT (ptexpr ('F d)), AddPT (ptexpr ('F ('S d))), MulPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT (ptexpr ('F d)) t m zp, AdditiveCtxPT (ptexpr ('F ('S d))) t m zp,
   RingCtxPT ptexpr ('F d) t m zp, Ring a, Applicative mon, LambdaD ptexpr)
  => mon (ptexpr ('N ('S d) ('N ('S d) ('F d))) (a -> a -> a))
pt2 = (\f -> lamD $ lamD . f) <$> pt1

pt3 :: forall a d ptexpr mon t m zp .
  (AddPT (ptexpr ('F d)), AddPT (ptexpr ('F ('S d))), MulPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT (ptexpr ('F d)) t m zp, AdditiveCtxPT (ptexpr ('F ('S d))) t m zp,
   RingCtxPT ptexpr ('F d) t m zp, Ring a, Applicative mon, LambdaD ptexpr,
   Lit (ptexpr ('F ('S d))), LitCtx (ptexpr ('F ('S d))) (Cyc t m zp))
  => a -> a -> mon (ptexpr ('F d) a)
pt3 a b = (\f -> appD (appD f $ lit a) $ lit b) <$> pt2


type Zq q = ZqBasic q Int64

main :: IO ()
main = do
  -- print the unapplied PT function
  putStrLn $ unSPT $ runIdentity $ pt2 @(Cyc CT F4 Int64) @'Z
  -- apply the PT function to arguments, then print it out
  putStrLn $ unSPT $ runIdentity $ pt3 @(Cyc CT F4 Int64) 7 11
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ unID $ runIdentity $ pt3 @(Cyc CT F4 Int64) 7 11
  -- compile the un-applied function to CT, then print it out
  x <- compile
         @'[ '(F4, F8)]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (pt2 @(Cyc CT F4 (Zq 7)) @'Z)
  putStrLn $ unSCT x
{-
foo :: (MonadRandom rnd, SymCT ctexpr, Lambda ctexpr,
        AddPubCtxCT ctexpr CT F4 F8 (Zq 7) (Zq 7),
        AdditiveCtxCT ctexpr CT F4 F8 (Zq 7) (Zq 11, Zq 7),
        RingCtxCT ctexpr CT F4 F8 (Zq 7) (Zq 11, Zq 7),
        RescaleCtxCT ctexpr CT F4 F8 (Zq 7) (Zq 11, Zq 7) (Zq 7),
        KeySwitchCtxCT ctexpr TrivGad CT F4 F8 (Zq 7) (Zq 13, (Zq 11, Zq 7)) (Zq 11, Zq 7))
    => rnd (ctexpr (SHE.CT F4 (Zq 7) (Cyc CT F8 (Zq 11, Zq 7))
            -> SHE.CT F4 (Zq 7) (Cyc CT F8 (Zq 11, Zq 7))
            -> SHE.CT F4 (Zq 7) (Cyc CT F8 (Zq 7))))
foo = compile
         @'[ '(F4, F8)]
         @'[ Zq 7, (Zq 11, Zq 7) ]
         @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ]
         @TrivGad
         @Double
         1.0
         (pt2 @(Cyc CT F4 (Zq 7)) @'Z)
-}