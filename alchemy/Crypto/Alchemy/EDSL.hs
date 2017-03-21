{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeInType       #-}

module Crypto.Alchemy.EDSL where

import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.IR ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.PT
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2IR
import Crypto.Alchemy.Interpreter.IR2CT ()
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowIR

import Crypto.Lol hiding (Pos(..), type (*))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Data.Kind
import Data.Type.Natural
import Crypto.Lol.Types

pt1 :: forall (ptexpr :: forall k . k -> * -> *) a t m zp d .
        (SymPT ptexpr, a ~ Cyc t m zp,
         AddPubCtxPT ptexpr d t m zp,
         AdditiveCtxPT ptexpr ('S d) t m zp,
         RingCtxPT ptexpr d t m zp,
         Ring a)
     => ptexpr ('S d) a -> ptexpr ('S d) a -> ptexpr d a
pt1 a b = addPublicPT 2 $ a *# (a +# b)

pt2 :: forall a d (ptexpr :: forall k . k -> * -> *) t m zp . (SymPT ptexpr, LambdaD ptexpr, a ~ Cyc t m zp,
        AddPubCtxPT ptexpr d t m zp,
        AdditiveCtxPT ptexpr ('S d) t m zp,
        RingCtxPT ptexpr d t m zp,
        Ring a) => ptexpr '( 'S d, '( 'S d, d)) (a -> a -> a)
pt2 = lamD $ lamD . pt1

pt3 :: forall a d (ptexpr :: forall k . k -> * -> *) t m zp . (SymPT ptexpr, LambdaD ptexpr, a ~ Cyc t m zp,
        d ~ 'Z,
        AddPubCtxPT ptexpr d t m zp,
        AdditiveCtxPT ptexpr ('S d) t m zp,
        RingCtxPT ptexpr d t m zp,
        LitCtxPT ptexpr ('S d) t m zp,
        Ring a) => a -> a -> ptexpr d a
pt3 a = appD (appD pt2 $ litPT a) . litPT

type Zq q = ZqBasic q Int64

main :: IO ()
main = do
  -- print the unapplied PT function
  putStrLn $ unSPT $ pt2 @(Cyc CT F4 Int64) @'Z
  -- apply the PT function to arguments, then print it out
  putStrLn $ unSPT $ pt3 @(Cyc CT F4 Int64) 7 11
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ unID  $ pt3 @(Cyc CT F4 Int64) 7 11
  -- compile the un-applied function to IR, then print it out
  putStrLn $ unSIR $ compilePT2IR $ pt2 @(Cyc CT F4 (Zq 7)) @'Z @(PT2IR ShowIR '[ '(F4, F8)] '[ Zq 7, (Zq 11, Zq 7) ])
