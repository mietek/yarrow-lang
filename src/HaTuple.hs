-- File: HaTuple
-- Description: This module defines operations on tuples, and some other 
-- Haskell specific definitions

module HaTuple(doFst, doSnd,
               doFst3, doSnd3, doThd3,
               fst3, snd3, thd3,
               doFst4, doSnd4, doThd4, doFth4,
               fst4, snd4, thd4, fth4,
               doFst5, doSnd5, doThd5, doFth5, doFfh5,
               fst5, snd5, thd5, fth5, ffh5,
               doFst6, doSnd6, doThd6, doFth6, doFfh6, doSxh6,
               fst6, snd6, thd6, fth6, ffh6, sxh6,
               takeUntil, space, sort, ord, zip4) where

------------------
--    TUPLES    --
------------------

doFst f (a,b) = (f a,  b)
doSnd f (a,b) = (  a,f b)

doFst3 f (a,b,c) = (f a,  b,  c)
doSnd3 f (a,b,c) = (  a,f b,  c)
doThd3 f (a,b,c) = (  a,  b,f c)

fst3 ~(a,_,_) = a
snd3 ~(_,b,_) = b
thd3 ~(_,_,c) = c

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
-- GENERAL FUNCTIONS OF GOFER, NOT PRESENT IN HASKELL --
--------------------------------------------------------

takeUntil           :: (a -> Bool) -> [a] -> [a]
takeUntil p []       = []
takeUntil p (x:xs)
       | p x         = [x]
       | otherwise   = x : takeUntil p xs

space :: Int -> String
space n = replicate n ' '

sort                :: Ord a => [a] -> [a]
sort                 = foldr insert []

insert              :: Ord a => a -> [a] -> [a]
insert x []          = [x]
insert x (y:ys)
        | x <= y     = x:y:ys
        | otherwise  = y:insert x ys




-- The definition of 'ord' should be removed for HUGS !
ord :: Char -> Int           
ord = fromEnum    

zip4 :: [a] -> [b] -> [c] -> [d] -> [(a,b,c,d)]
zip4 (a:as) (b:bs) (c:cs) (d:ds) = (a,b,c,d) : zip4 as bs cs ds
zip4 _ _ _ _ = []
