{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}

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
import Crypto.Alchemy.Language.TunnelPT ()
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2CT
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types

import Data.Type.Natural

-- EAC: Annoying that we need two AddPT constraints here!
pt1 ::
  (AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, Applicative mon)
  => mon (ptexpr (Add1 d) a -> ptexpr (Add1 d) a -> ptexpr d a)
pt1 = (\star a b -> addPublicPT 2 $ a `star` (a +# b)) <$> (*#)

pt2 :: forall a d ptexpr mon t m zp .
  (AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, Applicative mon, LambdaD ptexpr)
  => mon (ptexpr ('L (Add1 d) ('L (Add1 d) d)) (a -> a -> a))
pt2 = (\f -> lamD $ lamD . f) <$> pt1

pt3 :: forall a d ptexpr mon t m zp .
  (AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
   RingCtxPT ptexpr d a, Ring a, Applicative mon, LambdaD ptexpr,
   Lit (ptexpr (Add1 d)), LitCtx (ptexpr (Add1 d)) (Cyc t m zp))
  => a -> a -> mon (ptexpr d a)
pt3 a b = (\f -> appD (appD f $ lit a) $ lit b) <$> pt2


type Zq q = ZqBasic q Int64

main :: IO ()
main = do
  -- print the unapplied PT function
  putStrLn $ unSPT $ runIdentity $ pt2 @(Cyc CT F4 Int64) @('T 'Z)
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
         (pt2 @(Cyc CT F4 (Zq 7)) @('T 'Z))
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