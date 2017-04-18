{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE TypeFamilies, RankNTypes, ScopedTypeVariables          #-}

module Crypto.Alchemy.Interpreter.ShowPT where

import Control.Applicative

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT

unSPT :: (Functor i) => ShowPT i d a -> i String
unSPT (SPT a) = ($ 0) <$> a

newtype ShowPT i (d :: Depth) a = SPT {unSPT' :: i (Int -> String)}

lift2 :: forall i a b c d d' d'' . (Applicative i) => ((Int -> String) -> (Int -> String) -> (Int -> String)) -> (ShowPT i d a) -> (ShowPT i d' b) -> (ShowPT i d'' c)
lift2 f (SPT a) (SPT b) = SPT $ liftA2 f a b

instance AddPT ShowPT where
  type AddPubCtxPT   ShowPT d a = (Show a)
  --type MulPubCtxPT   ShowPT d a = (Show a)
  type AdditiveCtxPT ShowPT d a = ()

  (+#) = lift2 $ \a b i -> "( " ++ a i ++ " )" ++ " + " ++ "( " ++ b i ++ " )"
  --negPT (SPT a) = SPT $ \i -> "neg $ " ++ a i
  addPublicPT a (SPT c) = SPT $ (\b -> \i -> "( " ++ (show a) ++ " )" ++ " + " ++ "( " ++ b i ++ " )") <$> c
  --mulPublicPT a (SPT b) = SPT $ \i -> "( " ++ (show a) ++ " )" ++ " * " ++ "( " ++ b i ++ " )"

instance MulPT ShowPT where

  type RingCtxPT ShowPT d a = ()

  (*#) = lift2 (\a b i -> "( " ++ a i ++ " )" ++ " * " ++ "( " ++ b i ++ " )")

{-
instance ModSwPT ShowPT where

  type ModSwitchCtxPT ShowPT d a zp' = ()

  modSwitchDec (SPT a) = SPT $ \i -> "modSwitchDec $ " ++ a i

instance (Applicative mon) => TunnelPT mon ShowPT where

  type TunnelCtxPT ShowPT d t e r s zp = ()

  tunnelPT _ = pure $ \(SPT a) -> SPT $ \i -> "tunnel <FUNC> $ " ++ a i

instance LambdaD ShowPT where
  lamD f = SPT $ \i ->
    let x = "x" ++ show i
        (SPT b) = f $ SPT $ const x
    in "\\" ++ x ++ " -> " ++ (b $ i+1)
  appD (SPT f) (SPT a) = SPT $ \i -> "( " ++ f i ++ " ) " ++ a i
-}
instance (Applicative i) => Lit (ShowPT i d) where
  type LitCtx (ShowPT i d) a = (Show a)
  lit a = SPT $ pure $ const $ show a