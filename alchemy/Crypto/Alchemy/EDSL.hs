{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds        #-}
{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TypeInType       #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.EDSL where

import Control.Applicative
import Control.Monad.Identity
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State.Strict

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.IR ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.PT
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.PTEval
import Crypto.Alchemy.Interpreter.PT2IR
import Crypto.Alchemy.Interpreter.IR2CT
import Crypto.Alchemy.Interpreter.ShowPT
import Crypto.Alchemy.Interpreter.ShowIR
import Crypto.Alchemy.Interpreter.ShowCT

import Crypto.Lol hiding (Pos(..), type (*))
import Crypto.Lol.Cyclotomic.Tensor.CPP
import Crypto.Lol.Types

import Data.Dynamic
import Data.Kind
import Data.Type.Natural

pt1 :: forall (ptexpr :: forall k . k -> * -> *) a mon t m zp d .
  (SymPT mon ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d t m zp,
   AdditiveCtxPT ptexpr ('S d) t m zp,
   RingCtxPT ptexpr d t m zp,
   Ring a, Monad mon)
  => mon (ptexpr ('S d) a -> ptexpr ('S d) a -> ptexpr d a)
pt1 = do
  (addPub :: a -> ptexpr d a -> _) <- addPublicPT
  (star :: ptexpr ('S d) a -> _ -> _) <- (*#)
  (plus :: ptexpr ('S d) a -> _ -> _) <- (+#)
  return $ \a b -> addPub 2 $ a `star` (a `plus` b)

pt2 :: forall a d (ptexpr :: forall k . k -> * -> *) mon t m zp .
  (SymPT mon ptexpr, LambdaD ptexpr, a ~ Cyc t m zp,
   AddPubCtxPT ptexpr d t m zp,
   AdditiveCtxPT ptexpr ('S d) t m zp,
   RingCtxPT ptexpr d t m zp,
   Ring a, Monad mon)
  => mon (ptexpr '( 'S d, '( 'S d, d)) (a -> a -> a))
pt2 = do
  pt1' <- pt1
  return $ lamD $ lamD . pt1'

pt3 :: forall a d (ptexpr :: forall k . k -> * -> *) mon t m zp .
  (SymPT mon ptexpr, Lit (ptexpr ('S d)), LambdaD ptexpr, a ~ Cyc t m zp,
   d ~ 'Z,
   AddPubCtxPT ptexpr d t m zp,
   AdditiveCtxPT ptexpr ('S d) t m zp,
   RingCtxPT ptexpr d t m zp,
   LitCtx (ptexpr ('S d)) a,
   Ring a, Monad mon)
  => a -> a -> mon (ptexpr d a)
pt3 a b = do
  pt2' <- pt2
  return $ appD (appD pt2' $ lit a) $ lit b

type Zq q = ZqBasic q Int64

main :: IO ()
main = do
  -- print the unapplied PT function
  putStrLn $ unSPT $ runIdentity $ pt2 @(Cyc CT F4 Int64) @'Z
  -- apply the PT function to arguments, then print it out
  putStrLn $ unSPT $ runIdentity $ pt3 @(Cyc CT F4 Int64) 7 11
  -- apply the PT function to arguments and evaluate the function
  putStrLn $ show $ unID $ runIdentity $ pt3 @(Cyc CT F4 Int64) 7 11
  -- compile the un-applied function to IR, then print it out
  putStrLn $ unSIR $ compile $ runIdentity $ pt2 @(Cyc CT F4 (Zq 7)) @'Z @(PT2IR ShowIR '[ '(F4, F8)] '[ Zq 7, (Zq 11, Zq 7) ])
  -- compile the un-applied function to CT, then print it out
  x <- compileCT @'[ '(Zq 7, (Zq 11, Zq 7)), '((Zq 11, Zq 7), (Zq 13, (Zq 11, Zq 7))) ] @TrivGad @Double 1.0 $
         compileIR @'[ '(F4, F8)] @'[ Zq 7, (Zq 11, Zq 7) ] $
           pt2 @(Cyc CT F4 (Zq 7)) @'Z
  putStrLn $ unSCT x
  --putStrLn $ un

compileIR :: forall m'map zqs d irexpr a mon . (Compile (PT2IR irexpr m'map zqs d) irexpr a, Functor mon)
  => mon (PT2IR irexpr m'map zqs d a)
     -> mon (irexpr (CompiledType (PT2IR irexpr m'map zqs d) a))
compileIR a = compile <$> a

compileCT :: forall zq'map gad v ctexpr a rnd mon . (Compile (IR2CT ctexpr zq'map gad v) ctexpr a, MonadRandom rnd, mon ~ ReaderT v (StateT ([Dynamic],[Dynamic]) rnd))
  => v -> mon (IR2CT ctexpr zq'map gad v a)
     -> rnd (ctexpr (CompiledType (IR2CT ctexpr zq'map gad v) a))
compileCT v a = compile <$> (flip evalStateT ([],[]) $ flip runReaderT v a)
