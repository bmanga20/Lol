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
import Crypto.Alchemy.Interpreter.PT2IR ()
import Crypto.Alchemy.Interpreter.IR2CT ()
import Crypto.Alchemy.Interpreter.ShowPT

import Crypto.Lol hiding (Pos(..), type (*))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Data.Kind
import Data.Type.Natural
--IR2CTMon (IR2CT I zq'map TrivGad Double)

foo1 :: forall (ptexpr :: forall k . k -> * -> *) a t m zp d .
        (SymPT ptexpr, a ~ Cyc t m zp,
         AddPubCtxPT ptexpr d t m zp,
         AdditiveCtxPT ptexpr ('S d) t m zp,
         RingCtxPT ptexpr d t m zp,
         Ring a)
     => ptexpr ('S d) a -> ptexpr ('S d) a -> ptexpr d a
foo1 a b = addPublicPT 2 $ a *# (a +# b)

foo2 :: forall (ptexpr :: forall k . k -> * -> *) a t m zp d . (SymPT ptexpr, LambdaD ptexpr, a ~ Cyc t m zp,
        AddPubCtxPT ptexpr d t m zp,
        AdditiveCtxPT ptexpr ('S d) t m zp,
        RingCtxPT ptexpr d t m zp,
        Ring a) => ptexpr ('S d) a -> ptexpr '( 'S d,d) (a -> a)
foo2 = lamD . foo1

foo3 :: forall a d (ptexpr :: forall k . k -> * -> *) t m zp . (SymPT ptexpr, LambdaD ptexpr, a ~ Cyc t m zp,
        AddPubCtxPT ptexpr d t m zp,
        AdditiveCtxPT ptexpr ('S d) t m zp,
        RingCtxPT ptexpr d t m zp,
        Ring a) => ptexpr '( 'S d, '( 'S d, d)) (a -> a -> a)
foo3 = lamD foo2

foo4 :: forall a d (ptexpr :: forall k . k -> * -> *) t m zp . (SymPT ptexpr, LambdaD ptexpr, a ~ Cyc t m zp,
        d ~ 'Z,
        AddPubCtxPT ptexpr d t m zp,
        AdditiveCtxPT ptexpr ('S d) t m zp,
        RingCtxPT ptexpr d t m zp,
        LitCtxPT ptexpr ('S d) t m zp,
        Ring a) => a -> a -> ptexpr d a
foo4 a = appD (appD foo3 $ litPT a) . litPT


main :: IO ()
main = do
  putStrLn $ unSPT $ foo3 @(Cyc CT F4 Int64) @'Z
  putStrLn $ unSPT $ foo4 @(Cyc CT F4 Int64) 7 11
  putStrLn $ show $ unID  $ foo4 @(Cyc CT F4 Int64) 7 11