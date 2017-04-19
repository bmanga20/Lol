{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Crypto.Alchemy.Language.Lam where

import Crypto.Alchemy.Depth

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b

class LambdaD expr where
  lamD :: (Applicative i) => (forall j . (Applicative j) => expr (i :. j) da a -> expr (i :. j) db b)
          -> expr i ('L da db) (a->b)

  appD :: (Applicative i) => (expr i ('L da db) (a->b)) -> (expr i da a) -> (expr i db b)

lam' :: (Functor m, Applicative i, Lambda expr) =>
  (forall j . (Applicative j) => (i :. j) (expr a) -> (m :. (i :. j)) (expr b))
    -> (m :. i) (expr (a -> b))
lam' f = fmap lam (J $ fmap unJ $ unJ $ f  (J $ pure id))


-- lam* first weakens repeatedly, then reassociates in one go
lam1 :: (Applicative i, LambdaD expr) =>
  (forall j . (Applicative j) => expr (i :. j) d1 a -> expr (i :. j) d2 b)
    -> expr i ('L d1 d2) (a -> b)
lam1 = lamD

lam2 :: (Applicative i, LambdaD expr, EnvLiftable expr) =>
  (forall j . (Applicative j) => expr (i :. j) d1 a -> expr (i :. j) d2 b -> expr (i :. j) d3 c)
    -> expr i ('L d1 ('L d2 d3)) (a -> b -> c)
lam2 f = lamD $ \x -> lamD $ \y ->
  let x' = assocLR $ extendR x -- embed from  (i . j1)       to (i . (j1 . j2))
      y' = assocLR y           -- embed from ((i . j1) . j2) to (i . (j1 . j2))
      z  = f x' y'
  in assocRL z  -- reassociate from (i . (j1 . j2)) to ((i . j1) . j2)
{-
lam3 :: (Applicative m, Applicative i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 d4))) (a -> b -> c -> d))
lam3 f = lamD $ \x -> lamD $ \y -> lamD $ \z ->
  let reassoc = assocLR . assocLR
      x' = reassoc $ weakenL $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . j3)))
      y' = reassoc $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = reassoc z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w = f (var x') (var y') (var z')
  in mapJ2 (assocRL . assocRL) w

lam4 :: (Applicative m, Applicative i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d) -> (m :. (i :. j)) (expr d5 e))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 ('L d4 d5)))) (a -> b -> c -> d -> e))
lam4 f = lamD $ \x -> lamD $ \y -> lamD $ \z -> lamD $ \w ->
  let reassoc = assocLR . assocLR . assocLR
      x' = reassoc $ weakenL $ weakenL $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . (j3 . j4)))
      y' = reassoc $ weakenL $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = reassoc $ weakenL z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w' = reassoc w
      u = f (var x') (var y') (var z') (var w')
  in mapJ2 (assocRL . assocRL . assocRL) u
-}


{-
-- lam*' weakens in one go, then reassociates repeatedly (same sigs as corresponding lam* function)
lam1' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b))
    -> (m :. i) (expr ('L d1 d2) (a -> b))
lam1' f = lamD $ f . var

lam2' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c))
    -> (m :. i) (expr ('L d1 ('L d2 d3)) (a -> b -> c))
lam2' f = lamD $ \x -> lamD $ \y ->
  let x' = assocLR $ weakenL x   -- embed from  i . j1       to m . (i . (j1 . j2))
      y' = assocLR y -- embed from (i . j1) . j2 to m . (i . (j1 . j2))
      z  = f (var x') (var y')
  in mapJ2 assocRL z  -- reassociate from m . (i . (j1 . j2)) to m . ((i . j1) . j2)

lam3' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 d4))) (a -> b -> c -> d))
lam3' f = lamD $ \x -> lamD $ \y -> lamD $ \z ->
  let x' = assocLR $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . j3)))
      y' = assocLR $ assocLR $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = assocLR $ assocLR z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w = f (var x') (var y') (var z')
  in mapJ2 (assocRL . assocRL) w

lam4' :: (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j . (Applicative j) => (m :. (i :. j)) (expr d1 a) -> (m :. (i :. j)) (expr d2 b) -> (m :. (i :. j)) (expr d3 c) -> (m :. (i :. j)) (expr d4 d) -> (m :. (i :. j)) (expr d5 e))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 ('L d4 d5)))) (a -> b -> c -> d -> e))
lam4' f = lamD $ \x -> lamD $ \y -> lamD $ \z -> lamD $ \w ->
  let x' = assocLR $ weakenL x -- embed from  i . j1              to m . (i . (j1 . (j2 . (j3 . j4)))
      y' = assocLR $ assocLR $ weakenL y     -- embed from (i . j1) . j2        to m . (i . (j1 . (j2 . j3)))
      z' = assocLR $ assocLR $ assocLR $ weakenL z   -- embed from ((i . j1) . j2) . j3 to m . (i . (j1 . (j2 . j3)))
      w' = assocLR $ assocLR $ assocLR $ w
      u = f (var x') (var y') (var z') (var w')
  in mapJ2 (assocRL . assocRL . assocRL) u



--Expected type: (:.) m (i'       :. j1) (expr d2 b) → (:.) m (i'       :. j1) (expr d3 c) → (:.) m (i'       :. j1) (expr d4 d)
--Actual   type: (:.) m ((i :. j) :. j1) (expr d2 b) → (:.) m ((i :. j) :. j1) (expr d3 c) → (:.) m ((i :. j) :. j1) (expr d4 d)

-- lam*Rec are very simple and make recursive calls
lam2Rec :: forall m i expr d1 d2 d3 a b c . (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall j' j . (Applicative j) => (m :. ((i :. j') :. j)) (expr d1 a) -> (m :. ((i :. j') :. j)) (expr d2 b) -> (m :. ((i :. j') :. j)) (expr d3 c))
    -> (m :. i) (expr ('L d1 ('L d2 d3)) (a -> b -> c))
lam2Rec f = lamPT $ \x -> lam1 $ f (var $ weakenL x)

lam3Rec :: forall m i expr d1 d2 d3 d4 a b c d . (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall i' j' j . (Applicative j, i' ~ (i :. j')) => (m :. (i' :. j)) (expr d1 a) -> (m :. (i' :. j)) (expr d2 b) -> (m :. (i' :. j)) (expr d3 c) -> (m :. (i' :. j)) (expr d4 d))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 d4))) (a -> b -> c -> d))
lam3Rec f = lamPT $ \x -> lam2 $ f (var $ weakenL x)

lam4Rec :: forall m i expr d1 d2 d3 d4 d5 a b c d e . (Applicative m, AppLiftable i, LambdaD expr) =>
  (forall i' j' j . (Applicative j, i' ~ (i :. j')) => (m :. (i' :. j)) (expr d1 a) -> (m :. (i' :. j)) (expr d2 b) -> (m :. (i' :. j)) (expr d3 c) -> (m :. (i' :. j)) (expr d4 d) -> (m :. (i' :. j)) (expr d5 e))
    -> (m :. i) (expr ('L d1 ('L d2 ('L d3 ('L d4 d5)))) (a -> b -> c -> d -> e))
lam4Rec f = lamPT $ \x -> lam3 $ f (var $ weakenL x)
-}

class EnvLiftable repr where
  extendR :: (Applicative i, Applicative j) => repr i (d :: Depth) a -> repr (i :. j) d a

  assocRL :: Functor m => repr (m :. (i1 :. i2)) (d :: Depth) a -> repr ((m :. i1) :. i2) d a

  assocLR :: Functor m => repr ((m :. i1) :. i2) (d :: Depth) a -> repr (m :. (i1 :. i2)) d a





weakenR :: (Applicative m,Applicative i,Applicative j) => (m :. i) (repr a) -> (m :. (i :. j)) (repr a)
weakenR = liftJ2

weakenL :: (Applicative m,Applicative i,Applicative j) => (m :. i) (repr a) -> ((m :. i) :. j) (repr a)
weakenL = liftJ
{-
assocRL :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
assocRL = jassocm2

assocLR :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
assocLR = jassocp2
-}
-- from TSCore.hs
appPT :: (Applicative m, Lambda repr) => m (repr (a->b)) -> m (repr a) -> m (repr b)
appPT f x = app <$> f <*> x

-- EAC: copied straight from TSCore.hs

-- Composition of two type constructors (kind * -> *)
newtype (i :. j) a = J{unJ:: i (j a)}

instance (Functor i, Functor j) => Functor (i :. j) where
  fmap f (J x) = J $ fmap (fmap f) x

instance (Applicative i, Applicative j) => Applicative (i :. j) where
  pure = J . pure . pure
  J f <*> J x = J $ (<*>) <$> f <*> x

liftJ :: (Applicative m, Applicative i) =>
          m a -> (m :. i) a
liftJ = J . fmap pure

-- A very common operation
mapJ2 :: Functor m => (i a -> j a) -> (m :. i) a -> (m :. j) a
mapJ2 f = J . fmap f . unJ

liftJ2 :: (Applicative m, Applicative i, Applicative j) =>
          (m :. i) a -> (m :. (i :. j)) a
liftJ2 = mapJ2 liftJ

-- Composition of applicatives, just like any composition, is
-- associative
-- Here are the witnesses

jassocp2 :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
jassocp2 (J (J mi1i2)) = J (fmap J mi1i2)
jassocm2 :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
jassocm2 (J mJi1i2) = J . J $ (fmap unJ mJi1i2)

-- Make a variable an expression
var :: Applicative m => i (repr a) -> (m :. i) (repr a)
var = J . pure
