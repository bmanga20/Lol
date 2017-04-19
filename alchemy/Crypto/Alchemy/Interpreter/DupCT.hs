{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Interpreter.DupCT where

import Crypto.Alchemy.Language.CT
import Crypto.Alchemy.Language.Lam

dupCT :: Dup expr1 expr2 a -> (expr1 a, expr2 a)
dupCT (Dup a b) = (a,b)

data Dup expr1 expr2 a = Dup {unDupA :: expr1 a, unDupB :: expr2 a}

instance (SymCT expr1, SymCT expr2) => SymCT (Dup expr1 expr2) where
  type AdditiveCtxCT  (Dup expr1 expr2) ct     =
    (AdditiveCtxCT expr1 ct, AdditiveCtxCT expr2 ct)
  type RingCtxCT      (Dup expr1 expr2) ct     =
    (RingCtxCT expr1 ct, RingCtxCT expr2 ct)
  type ModSwitchCtxCT (Dup expr1 expr2) ct zp' =
    (ModSwitchCtxCT expr1 ct zp', ModSwitchCtxCT expr2 ct zp')
  type RescaleCtxCT   (Dup expr1 expr2) ct zq' =
    (RescaleCtxCT expr1 ct zq', RescaleCtxCT expr2 ct zq')
  type AddPubCtxCT    (Dup expr1 expr2) ct     =
    (AddPubCtxCT expr1 ct, AddPubCtxCT expr2 ct)
  type MulPubCtxCT    (Dup expr1 expr2) ct     =
    (MulPubCtxCT expr1 ct, MulPubCtxCT expr2 ct)
  type KeySwitchCtxCT (Dup expr1 expr2) ct zq' gad =
    (KeySwitchCtxCT expr1 ct zq' gad, KeySwitchCtxCT expr2 ct zq' gad)
  type TunnelCtxCT    (Dup expr1 expr2) t e r s e' r' s' zp zq gad =
    (TunnelCtxCT expr1 t e r s e' r' s' zp zq gad,
     TunnelCtxCT expr2 t e r s e' r' s' zp zq gad)

  (Dup a1 a2) +^ (Dup b1 b2) = Dup (a1 +^ b1) (a2 +^ b2)

  negCT (Dup a b) = Dup (negCT a) (negCT b)

  (Dup a1 a2) *^ (Dup b1 b2) = Dup (a1 *^ b1) (a2 *^ b2)

  modSwitchPT (Dup a b) = Dup (modSwitchPT a) (modSwitchPT b)

  rescaleCT (Dup a b) = Dup (rescaleCT a) (rescaleCT b)

  addPublicCT a (Dup b c) = Dup (addPublicCT a b) (addPublicCT a c)

  mulPublicCT a (Dup b c) = Dup (mulPublicCT a b) (mulPublicCT a c)

  keySwitchQuadCT a (Dup b c) = Dup (keySwitchQuadCT a b) (keySwitchQuadCT a c)

  tunnelCT a (Dup b c) = Dup (tunnelCT a b) (tunnelCT a c)


-- EAC: undefined is very suspect here. It seems to be due to the fact that the
-- (Dup a -> Dup b) function could in theory mix the two components together.
instance (Lambda expr1, Lambda expr2) => Lambda (Dup expr1 expr2) where
  lam f = Dup (lam $ unDupA . f . flip Dup undefined) (lam $ unDupB . f . Dup undefined)

  app (Dup fa fb) (Dup a b) = Dup (app fa a) (app fb b)