{-# LANGUAGE ConstraintKinds     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes #-}
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
import Crypto.Alchemy.Interpreter.Duplicate
import Crypto.Alchemy.Language.CT ()
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.ModSwPT ()
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT
import Crypto.Alchemy.Interpreter.CTEval ()
import Crypto.Alchemy.Interpreter.DeepSeq
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

--(+^) :: (AddPT expr, AdditiveCtxPT i expr d a) =>
--  i (expr d a) -> j (expr d a) -> expr d a

pt1 :: (a ~ Cyc t m zp, Ring a,
        AddPT expr, AddPubCtxPT i expr d a, AdditiveCtxPT i expr (Add1 d) a,
        MulPT expr, RingCtxPT i expr d a, Applicative j)
  => (i :. j) (expr (Add1 d) a) -> (i :. j) (expr d a)
pt1 x = addPublicPT 2 $ x *# (x +# x)

pt1' :: (Applicative j, AppLiftable i, LambdaD expr,
         a ~ Cyc t m zp, Ring a,
         AddPT expr, AddPubCtxPT i expr d a, AdditiveCtxPT i expr (Add1 d) a,
         MulPT expr, RingCtxPT i expr d a)
  => (j :. i) (expr ('L (Add1 d) d) (a -> a))
pt1' = lamD $ var . pt1





pt2 :: (a ~ Cyc t m' zp, Ring a, AddPT expr, MulPT expr,
        AddPubCtxPT m expr d a, AdditiveCtxPT m expr (Add1 d) a, RingCtxPT m expr d a,
        Applicative x, Applicative y, Applicative xy, Applicative m, Extends x (m :. xy), Extends y (m :. xy))
  => x (expr (Add1 d) a) -> y (expr (Add1 d) a) -> (m :. xy) (expr d a)
pt2 x y =
  let x' = weakens x -- var $ liftJ x
      y' = weakens y
  in addPublicPT 2 $ x' *# (x' +# y')
{-
pt2' :: (a ~ Cyc t m' zp, Ring a, AddPT expr, MulPT expr,
        AddPubCtxPT m expr d a, AdditiveCtxPT m expr (Add1 d) a, RingCtxPT m expr d a,
        Applicative x, Applicative (yi :. yj), Applicative (yi :. yj), Applicative m, Extends x yi, Extends (yi :. yj) (m :. (yi :. yj)))
  => x (expr (Add1 d) a) -> (yi :. yj) (expr (Add1 d) a) -> (m :. (yi :. yj)) (expr d a)
pt2' = pt2

pt2'' :: (Applicative m, AppLiftable yi, Applicative x,
         a ~ Cyc t m' zp, Ring a, LambdaD expr,
         AddPT expr, AddPubCtxPT m expr d a, AdditiveCtxPT m expr (Add1 d) a,
         MulPT expr, Extends x yi, RingCtxPT m expr d a)
  => x (expr (Add1 d) a) -> (m :. yi) (expr ('L (Add1 d) d) (a -> a))
-- EAC: GHC doesn't like point-free here
pt2'' x = lamD $ pt2' $ liftJ x

y ~ (yi :. yj)
xy ~ (yi :. yj)
x -> x :. yj
-}
{-
pt2'' :: (Applicative m, AppLiftable xm, LambdaD expr,
         a ~ Cyc t m' zp, Ring a,
         AddPT expr, --AddPubCtxPT i expr d a, AdditiveCtxPT i expr (Add1 d) a,
         MulPT expr)--, RingCtxPT i expr d a)
  => (m :. xm) (expr ('L (Add1 d) ('L (Add1 d) d)) (a -> a -> a))
pt2'' = lamD pt2'
-}

{-
lamPT :: (Applicative m, AppLiftable i, Lambda repr) =>
       (forall j. AppLiftable j =>
        (i :. j) (repr a) -> (m :. (i :. j)) (repr b))
       -> (m :. i) (repr (a->b))
-}
{-
{-
(AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
 AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
 RingCtxPT ptexpr d a, Ring a, Applicative mon, LambdaD ptexpr)
-}
pt1 :: forall t m zp d ptexpr mon . (_)
  => mon (ptexpr ('L (Add1 d) ('L (Add1 d) d)) (Cyc t m zp -> Cyc t m zp -> Cyc t m zp))
pt1 = lamPT $ \b -> lamPT $ \a -> addPublicPT 2 $ var a *# (var a +# var b))

{-
(AddPT ptexpr, MulPT mon ptexpr, a ~ Cyc t m zp,
 AddPubCtxPT ptexpr d a, AdditiveCtxPT ptexpr (Add1 d) a,
 RingCtxPT ptexpr d a, Ring a, Applicative mon, LambdaD ptexpr)
-}
pt2 :: forall t m zp d ptexpr mon . (_)
  => Cyc t m zp -> Cyc t m zp -> mon (ptexpr d (Cyc t m zp))
pt2 a b = (\f -> appD (appD f $ lit a) $ lit b) <$> pt1
-}
{-
(TunnelPTCtx' expr d mon t eru r u zp,
 TunnelPTCtx' expr d mon t eus u s zp,
 Monad mon, LambdaD expr)

tunn1 :: forall t r u s zp d mon expr . (_)
  => Proxy u -> mon (expr ('L d d) (Cyc t r zp -> Cyc t s zp))
tunn1 _ = do
  tunnel1 <- tunnelPT' @u
  tunnel2 <- tunnelPT'
  return $ lamPT $ \x -> tunnel2 $ tunnel1 x
-}
type Zq q = ZqBasic q Int64
{-
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
-}
{-
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
  -- compile once, interpret with multiple ctexprs!!
  let (z1,z2) = duplicate $ runDeepSeq y
  putStrLn $ unSCT z1
  putStrLn $ unSCT $ runDupRescale z2

type H0 = F8
type H1 = F4 * F7
type H2 = F2 * F7 * F13
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
-}