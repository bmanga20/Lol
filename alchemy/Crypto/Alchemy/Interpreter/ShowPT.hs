{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Crypto.Alchemy.Interpreter.ShowPT where

import Crypto.Alchemy.Depth
import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.ModSwPT
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Language.TunnelPT

unSPT :: ShowPT d a -> String
unSPT (SPT a) = a 0

data ShowPT (d :: Depth) a = SPT (Int -> String)

instance AddPT (ShowPT) where
  type AddPubCtxPT   ShowPT d a = (Show a)
  type MulPubCtxPT   ShowPT d a = (Show a)
  type AdditiveCtxPT ShowPT d a = ()

  (SPT a) +# (SPT b) = SPT $ \i -> "( " ++ a i ++ " )" ++ " + " ++ "( " ++ b i ++ " )"
  negPT (SPT a) = SPT $ \i -> "neg $ " ++ a i
  addPublicPT a (SPT b) = SPT $ \i -> "( " ++ (show a) ++ " )" ++ " + " ++ "( " ++ b i ++ " )"
  mulPublicPT a (SPT b) = SPT $ \i -> "( " ++ (show a) ++ " )" ++ " * " ++ "( " ++ b i ++ " )"

instance (Applicative mon) => MulPT mon ShowPT where

  type RingCtxPT ShowPT d a = ()

  (*#) = pure $ \(SPT a) (SPT b) -> SPT $ \i -> "( " ++ a i ++ " )" ++ " * " ++ "( " ++ b i ++ " )"

instance ModSwPT ShowPT where

  type ModSwitchCtxPT ShowPT d a zp' = ()

  modSwitchDec (SPT a) = SPT $ \i -> "modSwitchDec $ " ++ a i

instance (Applicative mon) => TunnelPT mon (ShowPT d) where

  type TunnelCtxPT (ShowPT d) t e r s zp = ()

  tunnelPT _ = pure $ \(SPT a) -> SPT $ \i -> "tunnel <FUNC> $ " ++ a i

instance LambdaD ShowPT where
  lamD f = SPT $ \i ->
    let x = "x" ++ show i
        (SPT b) = f $ SPT $ const x
    in "\\" ++ x ++ " -> " ++ (b $ i+1)
  appD (SPT f) (SPT a) = SPT $ \i -> "( " ++ f i ++ " ) " ++ a i

instance Lit (ShowPT d) where
  type LitCtx (ShowPT d) a = (Show a)
  lit a = SPT $ \_ -> show a