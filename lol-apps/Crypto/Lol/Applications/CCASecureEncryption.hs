{-|
Module      : Crypto.Lol.Applications.CCASecureEncryption
Description : Chosen Ciphertext-Secure Encryption from Section 6.3 of
              <http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
Copyright   : (c) Bogdan Manga, 2018
                  Chris Peikert, 2018
License     : GPL-3
Maintainer  : cpeikert@alum.mit.edu
Stability   : experimental
Portability : POSIX

Chosen Ciphertext-Secure Encryption from Section 6.3 of
<http://web.eecs.umich.edu/~cpeikert/pubs/efftrap.pdf [MP12]>.
-}

module Crypto.Lol.Applications.CCASecureEncryption where

import Crypto.Lol
import Crypto.Lol.Applications.TrapdoorGeneration

type Zq q = ZqBasic q Int64


gen

enc

dec


-- | Injective ring homomorphism from @R = Z_q[x]/f(x)@ to @Z_q^{n \times n}@
-- @h(a)@ represents multiplication by @a \in R@
h
