-- File: GoTuple
-- Description: This module defines operations on tuples, and some functions
-- available in Haskell but not in Gofer

module GoTuple where

------------------
--    TUPLES    --
------------------

doFst f (a,b) = (f a,  b)
doSnd f (a,b) = (  a,f b)

doFst3 f (a,b,c) = (f a,  b,  c)
doSnd3 f (a,b,c) = (  a,f b,  c)
doThd3 f (a,b,c) = (  a,  b,f c)

doFst4 f (a,b,c,d) = (f a,  b,  c,  d)
doSnd4 f (a,b,c,d) = (  a,f b,  c,  d)
doThd4 f (a,b,c,d) = (  a,  b,f c,  d)
doFth4 f (a,b,c,d) = (  a,  b,  c,f d)

fst4 (a,_,_,_) = a
snd4 (_,b,_,_) = b
thd4 (_,_,c,_) = c
fth4 (_,_,_,d) = d

doFst5 f (a,b,c,d,e) = (f a,  b,  c,  d,  e)
doSnd5 f (a,b,c,d,e) = (  a,f b,  c,  d,  e)
doThd5 f (a,b,c,d,e) = (  a,  b,f c,  d,  e)
doFth5 f (a,b,c,d,e) = (  a,  b,  c,f d,  e)
doFfh5 f (a,b,c,d,e) = (  a,  b,  c,  d,f e)

fst5 (a,_,_,_,_) = a
snd5 (_,b,_,_,_) = b
thd5 (_,_,c,_,_) = c
fth5 (_,_,_,d,_) = d
ffh5 (_,_,_,_,e) = e
               
doFst6 z (a,b,c,d,e,f) = (z a,  b,  c,  d,  e,  f)
doSnd6 z (a,b,c,d,e,f) = (  a,z b,  c,  d,  e,  f)
doThd6 z (a,b,c,d,e,f) = (  a,  b,z c,  d,  e,  f)
doFth6 z (a,b,c,d,e,f) = (  a,  b,  c,z d,  e,  f)
doFfh6 z (a,b,c,d,e,f) = (  a,  b,  c,  d,z e,  f)
doSxh6 z (a,b,c,d,e,f) = (  a,  b,  c,  d,  e,z f)

fst6 (a,_,_,_,_,_) = a
snd6 (_,b,_,_,_,_) = b
thd6 (_,_,c,_,_,_) = c
fth6 (_,_,_,d,_,_) = d
ffh6 (_,_,_,_,e,_) = e
sxh6 (_,_,_,_,_,f) = f
               

--------------------------------------------------------
-- GENERAL FUNCTIONS OF HASKELL, NOT PRESENT IN GOFER --
--------------------------------------------------------

  
replicate :: Int -> a -> [a]
replicate = copy
                
-- equality on triples
instance (Eq a, Eq b, Eq c) => Eq (a,b,c) where
         (a,b,c) == (a',b',c') = a==a' && b==b' && c==c'
 
instance (Ord a, Ord b, Ord c) => Ord (a,b,c) where
 (a1,b1,c1) <= (a2,b2,c2) = a1 < a2 || (a1 == a2 &&
                                        (b1 < b2 || (b1 == b2 && c1 <= c2)))

