{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE NoMonoLocalBinds #-} -- required for the LambdaD instance

module Crypto.Alchemy.Interpreter.DupPT where

import Crypto.Alchemy.Language.AddPT
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.Lit
import Crypto.Alchemy.Language.MulPT
import Crypto.Alchemy.Depth

dupPT :: Dup expr1 expr2 i d a -> (expr1 i d a, expr2 i d a)
dupPT (Dup a b) = (a,b)

data Dup expr1 expr2 (i :: * -> *) (d :: Depth) a = Dup {unDupA :: expr1 i d a, unDupB :: expr2 i d a}

instance (AddPT expr1, AddPT expr2) => AddPT (Dup expr1 expr2) where
  type AddPubCtxPT   (Dup expr1 expr2) d a = (AddPubCtxPT   expr1 d a, AddPubCtxPT   expr2 d a)
  type MulPubCtxPT   (Dup expr1 expr2) d a = (MulPubCtxPT   expr1 d a, MulPubCtxPT   expr2 d a)
  type AdditiveCtxPT (Dup expr1 expr2) d a = (AdditiveCtxPT expr1 d a, AdditiveCtxPT expr2 d a)

  (Dup a1 b1) +# (Dup a2 b2) = Dup (a1 +# a2) (b1 +# b2)
  negPT (Dup a b) = Dup (negPT a) (negPT b)
  addPublicPT a (Dup b c) = Dup (addPublicPT a b) (addPublicPT a c)
  mulPublicPT a (Dup b c) = Dup (mulPublicPT a b) (mulPublicPT a c)

instance (MulPT expr1, MulPT expr2) => MulPT (Dup expr1 expr2) where

  type RingCtxPT (Dup expr1 expr2) d a = (RingCtxPT expr1 d a, RingCtxPT expr2 d a)

  (Dup a1 b1) *# (Dup a2 b2) = Dup (a1 *# a2) (b1 *# b2)

instance (LambdaD expr1, LambdaD expr2) => LambdaD (Dup expr1 expr2) where
  lamD f =
    let fa x = unDupA $ f (flip Dup undefined x)
        fb x = unDupB $ f (Dup undefined x)
    in Dup (lamD fa) (lamD fb)

  appD (Dup fa fb) (Dup a b) = Dup (appD fa a) (appD fb b)

instance (EnvLiftable expr1, EnvLiftable expr2) => EnvLiftable (Dup expr1 expr2) where
  extendR (Dup a b) = Dup (extendR a) (extendR b)
  assocRL (Dup a b) = Dup (assocRL a) (assocRL b)
  assocLR (Dup a b) = Dup (assocLR a) (assocLR b)

instance (Lit (expr1 i d), Lit (expr2 i d)) => Lit (Dup expr1 expr2 i d) where
  type LitCtx (Dup expr1 expr2 i d) a = (LitCtx (expr1 i d) a, LitCtx (expr2 i d) a)
  lit a = Dup (lit a) (lit a)
