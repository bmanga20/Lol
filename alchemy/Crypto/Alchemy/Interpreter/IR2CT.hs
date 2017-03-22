{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE NoImplicitPrelude       #-}
{-# LANGUAGE PartialTypeSignatures   #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Interpreter.IR2CT where

import Control.Applicative
import Control.DeepSeq
import Control.Monad.Random
import Control.Monad.Reader
import Control.Monad.State.Strict

import Crypto.Alchemy.Common
import Crypto.Alchemy.Language.IR
import Crypto.Alchemy.Language.Lam
import Crypto.Alchemy.Language.CT
import Crypto.Lol hiding (type (*), type S)
import qualified Crypto.Lol as Lol (type (*))
import Crypto.Lol.Applications.SymmSHE hiding (tunnelCT)

import Data.Dynamic
import Data.Kind
import Data.Maybe (mapMaybe)

type IR2CT' ctexpr zq'map ksgad v rnd = IR2CT ctexpr (ReaderT v (StateT ([Dynamic],[Dynamic]) rnd)) zq'map ksgad v

data IR2CT :: (* -> *) -> (* -> *) -> [(*,*)] -> * -> * -> * -> * where
  I2CTerm  :: (ct ~ CT m zp (Cyc t m' zq))
    => {unI2CTerm :: mon (ctexpr ct)} -> IR2CT ctexpr mon zq'map ksgad v ct

  I2CLam :: {unI2CLam :: IR2CT ctexpr mon zq'map ksgad v a -> IR2CT ctexpr mon zq'map ksgad v b}
         -> IR2CT ctexpr mon zq'map ksgad v (a -> b)

instance (Applicative mon) => Compile mon ctexpr (IR2CT ctexpr mon zq'map ksgad v (CT m zp (Cyc t m' zq))) where
  type CompiledType (IR2CT ctexpr mon zq'map ksgad v (CT m zp (Cyc t m' zq))) = CT m zp (Cyc t m' zq)
  compile = unI2CTerm

instance (Monad mon, Compile mon ctexpr (IR2CT ctexpr mon zq'map ksgad v b))
  => Compile mon ctexpr (IR2CT ctexpr mon zq'map ksgad v (CT m zp (Cyc t m' zq) -> b)) where
  type CompiledType (IR2CT ctexpr mon zq'map ksgad v (CT m zp (Cyc t m' zq) -> b)) =
    (CompiledType (IR2CT ctexpr mon zq'map ksgad v (CT m zp (Cyc t m' zq)))
     -> CompiledType (IR2CT ctexpr mon zq'map ksgad v b))


  -- expr ~ I2CTerm
  -- lam :: (expr a -> expr b) -> expr (a -> b)

  compile (I2CLam f) = lam $ \a -> compile $ f $ I2CTerm a



    --lam $ \(IR2CTMon term) -> compile $ IR2CTMon $ (unI2CLam <$> unwrap f) <*> (I2CTerm <$> term)
{-
compileIR2CT :: forall rnd mon v ctexpr zq'map ksgad a .
  (MonadRandom rnd, mon ~ ReaderT v (StateT ([Dynamic],[Dynamic]) rnd),
   Compile (IR2CTMon ctexpr mon) (IR2CTMon (IR2CT ctexpr zq'map ksgad v) mon a))
  => v -> IR2CTMon (IR2CT ctexpr zq'map ksgad v) mon a -> rnd (ctexpr (CompiledType (IR2CTMon (IR2CT ctexpr zq'map ksgad v) mon a)))
-- EAC: Not sure why I need the type sig on `pure a`
compileIR2CT v a = flip evalStateT ([],[]) $ flip runReaderT v $ unwrap $ compile a -- $ IR2CTMon (pure a :: mon _)
-}
instance (SymCT ctexpr, MonadReader v mon, ToRational v, NFData v, MonadState ([Dynamic],[Dynamic]) mon, MonadRandom mon)
  => SymIR (IR2CT ctexpr mon zq'map ksgad v) where

  type RescaleCtxIR   (IR2CT ctexpr mon zq'map ksgad v) t m m' zp zq' zq = (RescaleCtxCT ctexpr t m m' zp zq' zq)
  type AddPubCtxIR    (IR2CT ctexpr mon zq'map ksgad v) t m m' zp     zq = (AddPubCtxCT ctexpr t m m' zp zq)
  type MulPubCtxIR    (IR2CT ctexpr mon zq'map ksgad v) t m m' zp     zq = (MulPubCtxCT ctexpr t m m' zp zq)
  type KeySwitchCtxIR (IR2CT ctexpr mon zq'map ksgad v) t m m' zp     zq =
    (KeySwitchCtxCT ctexpr ksgad t m m' zp (Lookup zq zq'map) zq,
     GenSKCtx t m' (LiftOf zp) v, KSHintCtx ksgad t m' (LiftOf zp) (Lookup zq zq'map),
     Typeable (Cyc t m' (LiftOf zp)), Typeable (KSQuadCircHint ksgad (Cyc t m' (Lookup zq zq'map))))
  type TunnelCtxIR    (IR2CT ctexpr mon zq'map ksgad v) t e r s r' s' zp zq =
    (GenSKCtx t r' (LiftOf zp) v, Typeable (Cyc t r' (LiftOf zp)),
     GenSKCtx t s' (LiftOf zp) v, Typeable (Cyc t s' (LiftOf zp)),
     GenTunnelInfoCtx t e r s (e Lol.* (r' / r)) r' s' (LiftOf zp) zp zq ksgad,
     TunnelCtxCT ctexpr ksgad t e r s (e Lol.* (r' / r)) r' s' zp zq)

  rescaleIR (I2CTerm a) = I2CTerm $ rescaleCT <$> a

  addPublicIR a (I2CTerm b) = I2CTerm $ addPublicCT a <$> b

  mulPublicIR a (I2CTerm b) = I2CTerm $ mulPublicCT a <$> b

  keySwitchQuadIR (I2CTerm a') = I2CTerm $ do
    (a :: ctexpr (CT m zp (Cyc t m' zq))) <-  a'
    hint :: KSQuadCircHint ksgad (Cyc t m' (Lookup zq zq'map)) <- getHint (Proxy::Proxy zq'map) (Proxy::Proxy (LiftOf zp)) (Proxy::Proxy zq)
    return $ keySwitchQuadCT hint a

  -- EAC: TODO Need to modSwitch up before tunneling, and down after.
  tunnelIR linf (I2CTerm a') = I2CTerm $ do
    (a :: ctexpr (CT r zp (Cyc t r' zq))) <- a'
    (skout :: SK (Cyc t _ (LiftOf zp))) <- getKey
    (sk :: SK (Cyc t r' (LiftOf zp))) <- getKey
    thint :: TunnelInfo ksgad t e r s (e Lol.* (r' / r)) r' _ zp zq <- tunnelInfo linf skout sk
    return $ tunnelCT thint a

instance Lambda (IR2CT ctexpr mon zq'map ksgad v) where

  lam = I2CLam
  app (I2CLam f) = f

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
getHint :: forall v mon t z gad m' (zq :: *) zq' map .
  (-- constraints for getKey
   MonadReader v mon, MonadState ([Dynamic], [Dynamic]) mon,
   MonadRandom mon, GenSKCtx t m' z v, Typeable (Cyc t m' z),
   -- constraints for hintLookup
   Typeable (KSQuadCircHint gad (Cyc t m' zq')),
   -- constraints for ksQuadCircHint
   zq' ~ Lookup zq map, KSHintCtx gad t m' z zq')
  => Proxy map -> Proxy z -> Proxy zq -> mon (KSQuadCircHint gad (Cyc t m' zq'))
getHint _ _ _ = hintLookup >>= \case
  (Just h) -> return h
  Nothing -> do
    sk :: SK (Cyc t m' z) <- getKey
    ksQuadCircHint sk

-- lookup a key in the state
keyLookup :: (Typeable a, MonadState ([Dynamic], b) mon) => mon (Maybe a)
keyLookup = (dynLookup . fst) <$> get

-- lookup a hint in the state
hintLookup :: (Typeable a, MonadState (b, [Dynamic]) mon) => mon (Maybe a)
hintLookup = (dynLookup . snd) <$> get

-- lookup an item in a dynamic list
dynLookup :: (Typeable a) => [Dynamic] -> Maybe a
dynLookup = head . mapMaybe fromDynamic