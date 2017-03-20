{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE NoImplicitPrelude       #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Crypto.Alchemy.Interpreter.IR2CT where

import Control.Applicative
import Control.DeepSeq
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State.Strict

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.IR
import Crypto.Alchemy.Language.CT
import Crypto.Lol hiding (type (*), type S)
import qualified Crypto.Lol as Lol (type (*))
import Crypto.Lol.Applications.SymmSHE hiding (tunnelCT)
import Crypto.Lol.Types.ZPP

import Crypto.Lol.Cyclotomic.Tensor

import Data.Dynamic
import Data.Kind
import Data.Maybe (mapMaybe)
import Data.Type.Natural


-- it's very annoying that
data IR2CT :: (* -> *)
           -> [(*,*)]
           -> *
           -> *
           -> * where
  I2CTerm  :: (ct ~ CT m zp (Cyc t m' zq),
               Ring (Lookup zq zq'map), -- REQUIRED to ensure that zq is a key in the map!
               -- KSHintCtx
               ToSDCtx t m' zp zq, AbsorbGCtx t m' zp zq,
               Typeable t, Typeable m', Typeable (LiftOf zp), Typeable zq, Typeable ksgad,
               z ~ LiftOf zp, ToInteger z,
               CElt t zp, CElt t z, CElt t zq, CElt t (DecompOf zq),
               NFElt zq, Reduce (DecompOf zq) zq, Reduce z zq,
               ZPP zp, TElt t (ZpOf zp),
               -- additional constraints needed for tunnelIR
               Decompose ksgad zq, Gadget ksgad zq,
               ToInteger z, Reduce z zq, CElt t z, Lift zp z)
    => KSDictList t z zq'map ksgad -> ctexpr ct -> IR2CT ctexpr zq'map ksgad ct

  I2CLam :: (IR2CT ctexpr zq'map ksgad a -> IR2CT ctexpr zq'map ksgad b)
         -> IR2CT ctexpr zq'map ksgad (a -> b)

newtype IR2CTMon (ir2ct :: (* -> *)) (mon :: * -> *) (a :: *) = IR2CTMon {unwrap :: mon (ir2ct a)}


instance (SymCT ctexpr, MonadReader v mon, ToRational v, NFData v, MonadState ([Dynamic],[Dynamic]) mon, MonadRandom mon)
  => SymIR (IR2CTMon (IR2CT ctexpr zq'map ksgad) mon) where

  keySwitchQuadIR a' = IR2CTMon $ do
    (I2CTerm ksdict (a :: ctexpr (CT m zp (Cyc t m' zq)))) <- unwrap a'
    (Hint hint) :: KSHint ksgad t m' zq <- getHint ksdict
    return $ I2CTerm ksdict $ keySwitchQuadCT hint a

  -- EAC: TODO Need to modSwitch up before tunneling, and down after.
  tunnelIR :: forall t e r s e' r' s' zp zq .
    (CElt t zp, CElt t zq, CElt t (DecompOf zq),
     Fact s, Fact s', ExtendLinIdx e r s e' r' s',
     e' `Divides` r', e' ~ (e Lol.* (r' / r)), e ~ FGCD r s,
     Ring zq, Random zq, NFElt zq, Reduce (DecompOf zq) zq,
     ToSDCtx t r' zp zq, AbsorbGCtx t r' zp zq,
     e `Divides` r, e `Divides` s, ZPP zp, CElt t zp, TElt t (ZpOf zp), Typeable s')
    => IR2CTMon (IR2CT ctexpr zq'map ksgad) mon (CT r zp (Cyc t r' zq))
       -> IR2CTMon (IR2CT ctexpr zq'map ksgad) mon (CT s zp (Cyc t s' zq))
  tunnelIR a' = IR2CTMon $ do
    (I2CTerm ksdict (a :: ctexpr (CT r zp (Cyc t r' zq)))) <- unwrap a'
    (skout :: SK (Cyc t s' (LiftOf zp))) <- getKey
    (sk :: SK (Cyc t r' (LiftOf zp))) <- getKey
    let crts = proxy crtSet (Proxy::Proxy e)
        r = proxy totientFact (Proxy::Proxy r)
        e = proxy totientFact (Proxy::Proxy e)
        dim = r `div` e
        -- only take as many crts as we need
        -- otherwise linearDec fails
        linf = linearDec (take dim crts) :: Linear t zp e r s
    thint :: TunnelInfo ksgad t e r s e' r' s' zp zq <- tunnelInfo linf skout sk
    return $ I2CTerm ksdict $ tunnelCT thint a


  --tunnelIR' = tunnelIR

-- retrieve the scaled variance parameter from the Reader
getSvar :: (MonadReader v mon) => mon v
getSvar = ask

-- retrieve a key from the state, or generate a new one otherwise
getKey :: (MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
           MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z))
  => mon (SK (Cyc t m' z))
getKey = keyLookup >>= \case
  (Just s) -> return s
  -- generate a key with the variance stored in the Reader monad
  Nothing -> genSK =<< getSvar

-- retrieve a hint from the state, or generate a new one otherwise
getHint :: forall v mon t z gad m' (zq :: *) map .
  (-- constraints for getKey
   MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
   MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z),
   Typeable (KSHint gad t m' zq), -- ks hint
   Typeable zq                    -- ks dict
   )
  => KSDictList t z map gad -> mon (KSHint gad t m' zq)
getHint ksdict = hintLookup >>= \case
  (Just h) -> return h
  Nothing -> case zq'Lookup ksdict of
    (KSDict (_::Proxy zq') :: KSDict t z zq gad) -> do
      sk :: SK (Cyc t m' z) <- getKey
      hint :: KSQuadCircHint gad (Cyc t m' zq') <- ksQuadCircHint sk
      return $ Hint hint

type KSDictList t z map gad = KSDictList' t z map gad (Length map)

data KSDictList' t z zq'map gad d where
  KSNil :: KSDictList' t z '[] gad 'Z
  KSCons :: (Typeable zq, '(zq,zq') ~ (zq'map !! d), zq' ~ (Lookup zq zq'map))
         => KSDict t z (zq :: *) gad -> KSDictList' t z zq'map gad d -> KSDictList' t z zq'map gad ('S d)

-- contains constraints to *generate* a hint,
-- plus constraints need to *use* a hint (we use these constraints to construct a KSHint below)
data KSDict t z zq gad where
  KSDict :: (Reduce z zq', Ring zq', Random zq',
             CElt t zq', Reduce (DecompOf zq') zq', Gadget gad zq',
             NFElt zq', CElt t (DecompOf zq'),
             -- needed to construct a KSHint
             RescaleCyc (Cyc t) zq' zq, RescaleCyc (Cyc t) zq zq',
             Decompose gad zq')
         => Proxy zq' -> KSDict t z zq gad

-- constraints needed to *use* a key switch hint
data KSHint gad t m' zq where
  Hint :: (RescaleCyc (Cyc t) zq' zq, RescaleCyc (Cyc t) zq zq',
           SwitchCtx gad t m' zq')
       => KSQuadCircHint gad (Cyc t m' zq') -> KSHint gad t m' zq


-- EAC: Very annoying: KSDictList can't expose `t`, because the Reader contents
-- go on, e.g., the context for the SymIR instance. Thus instead we have to
-- check that `t` matches, as well as `zq`.
-- This is really bad because there's no way the compiler can check that the
-- dictionaries were created for the right Tensor!
zq'Lookup :: forall t z (zq1 :: *) zq'map gad d . (Typeable zq1)
  => KSDictList' t z zq'map gad d -> KSDict t z zq1 gad
zq'Lookup KSNil = error "This can never happen"
zq'Lookup (KSCons d@(_::KSDict t z zq2 gad) rest) = case eqT @zq1 @zq2 of
  Nothing -> zq'Lookup rest
  (Just Refl) -> d

-- lookup a key in the state
keyLookup :: (Typeable a, MonadState ([Dynamic], [Dynamic]) mon) => mon (Maybe a)
keyLookup = (dynLookup . fst) <$> get

-- lookup a hint in the state
hintLookup :: (Typeable a, MonadState ([Dynamic], [Dynamic]) mon) => mon (Maybe a)
hintLookup = (dynLookup . snd) <$> get

-- lookup an item in a dynamic list
dynLookup :: (Typeable a) => [Dynamic] -> Maybe a
dynLookup = head . mapMaybe fromDynamic