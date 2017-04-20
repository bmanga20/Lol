{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TypeFamilies          #-}

{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}

module Crypto.Alchemy.Language.Lam where

import Crypto.Alchemy.Depth

-- | Lambda abstraction and application.

class Lambda expr where
  -- | Abstract a Haskell function into the object language.
  lam :: (expr a -> expr b) -> expr (a -> b)

  -- | Apply an abstraction.
  app :: expr (a -> b) -> expr a -> expr b

class LambdaD expr where
  -- Don't call lamD in top level code. Instead, try lam* below.
  lamD :: (Applicative i) => (forall j . (Applicative j) => expr (i :. j) da a -> expr (i :. j) db b)
          -> expr i ('L da db) (a->b)

  appD :: (Applicative i) => (expr i ('L da db) (a->b)) -> (expr i da a) -> (expr i db b)

-- Composition of two type constructors (kind * -> *)
newtype (i :. j) a = J{unJ:: i (j a)}

instance (Functor i, Functor j) => Functor (i :. j) where
  fmap f (J x) = J $ fmap (fmap f) x

instance (Applicative i, Applicative j) => Applicative (i :. j) where
  pure = J . pure . pure
  J f <*> J x = J $ (<*>) <$> f <*> x

-- lam* weakens in one go, then reassociates repeatedly (same sigs as corresponding lam* function)
lam1 :: (Applicative i, LambdaD expr) =>
  (forall j . (Applicative j) => expr (i :. j) d1 a -> expr (i :. j) d2 b)
    -> expr i ('L d1 d2) (a -> b)
lam1 = lamD

lam2 :: (Applicative i, LambdaD expr, EnvLiftable expr) =>
  (forall j . (Applicative j) => expr (i :. j) d1 a -> expr (i :. j) d2 b -> expr (i :. j) d3 c)
    -> expr i _ (a -> b -> c)
lam2 f = lamD $ \x -> lamD $ \y ->
  let x' = assocLR $ extendR x -- embed from  (i . j1)       to (i . (j1 . j2))
      y' = assocLR y           -- embed from ((i . j1) . j2) to (i . (j1 . j2))
      z  = f x' y'
  in assocRL z  -- reassociate from m . (i . (j1 . j2)) to m . ((i . j1) . j2)

lam3 :: (Applicative i, LambdaD expr, EnvLiftable expr) =>
  (forall j . (Applicative j) => expr (i :. j) d1 a -> expr (i :. j) d2 b -> expr (i :. j) d3 c -> expr (i :. j) d4 d)
    -> expr i _ (a -> b -> c -> d)
lam3 f = lamD $ \x -> lamD $ \y -> lamD $ \z ->
  let x' = assocLR $ extendR x           -- embed from   (i . j1)             to (i . (j1 . (j2 . j3)))
      y' = assocLR $ assocLR $ extendR y -- embed from  ((i . j1) . j2)       to (i . (j1 . (j2 . j3)))
      z' = assocLR $ assocLR z           -- embed from (((i . j1) . j2) . j3) to (i . (j1 . (j2 . j3)))
      w = f x' y' z'
  in assocRL $ assocRL w

lam4 :: (Applicative i, LambdaD expr, EnvLiftable expr) =>
  (forall j . (Applicative j) => expr (i :. j) d1 a -> expr (i :. j) d2 b -> expr (i :. j) d3 c -> expr (i :. j) d4 d -> expr (i :. j) d5 e)
    -> expr i _ (a -> b -> c -> d -> e)
lam4 f = lamD $ \x -> lamD $ \y -> lamD $ \z -> lamD $ \w ->
  let x' = assocLR $ extendR x                     -- embed from   (i . j1)             to (i . (j1 . (j2 . (j3 . j4)))
      y' = assocLR $ assocLR $ extendR y           -- embed from  ((i . j1) . j2)       to (i . (j1 . (j2 . (j3 . j4)))
      z' = assocLR $ assocLR $ assocLR $ extendR z -- embed from (((i . j1) . j2) . j3) to (i . (j1 . (j2 . (j3 . j4)))
      w' = assocLR $ assocLR $ assocLR $ w
      u = f x' y' z' w'
  in assocRL $ assocRL $ assocRL u

class EnvLiftable repr where
  extendR :: (Applicative i, Applicative j) => repr i (d :: Depth) a -> repr (i :. j) d a

  assocRL :: Functor m => repr (m :. (i1 :. i2)) (d :: Depth) a -> repr ((m :. i1) :. i2) d a

  assocLR :: Functor m => repr ((m :. i1) :. i2) (d :: Depth) a -> repr (m :. (i1 :. i2)) d a

liftJ :: (Applicative m, Applicative i) => m a -> (m :. i) a
liftJ = J . fmap pure

-- A very common operation
mapJ2 :: Functor m => (i a -> j a) -> (m :. i) a -> (m :. j) a
mapJ2 f = J . fmap f . unJ

jassocp2 :: Functor m => ((m :. i1) :. i2) a -> (m :. (i1 :. i2)) a
jassocp2 (J (J mi1i2)) = J (fmap J mi1i2)

jassocm2 :: Functor m => (m :. (i1 :. i2)) a -> ((m :. i1) :. i2) a
jassocm2 (J mJi1i2) = J . J $ (fmap unJ mJi1i2)

-- Make a variable an expression
var :: Applicative m => i (repr a) -> (m :. i) (repr a)
var = J . pure
