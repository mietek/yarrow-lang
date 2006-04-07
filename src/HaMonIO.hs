-- File: HaMonIO
-- Description: This module defines IO monads, for use in Haskell

module HaMonIO(IOMonad(..), Imp,
               convertIOtoImp, goSte, performS,
               putLines, putLine, putLn)  where

import HaTuple
import General(plusCR)
import HaMonSt
import IO
import Paths(errS)

-----------------------
-- I O   M O N A D S --
-----------------------

class Monad m => IOMonad m where
    readFil :: String -> m String            -- file reading
    writeFil :: String -> String -> m ()     -- file writing
    appendFil :: String -> String -> m ()    -- file appending
    getLin :: m String                       -- read a line from input
    putSt :: String -> m ()                  -- output

instance IOMonad IO where
    readFil = readFile
    writeFil = writeFile
    appendFil = appendFile
    getLin = getLine
    putSt = putStr
    
------------------------------
-- An I/O State Error monad --
------------------------------
                            
-- The following type-constructor is called Imp because it allows
-- more-or-less imperative programming

data Imp s a = SIOSE (s -> IO (s,E a))

instance Functor (Imp s) where
     fmap f ~(SIOSE x) = SIOSE (\s -> fmap (doSnd (fmap f)) (x s))


instance Monad (Imp s) where
    return x = SIOSE (\s -> return (s,return x))
    ~(SIOSE x) >>= f = SIOSE (\st -> (x st) >>= \(st',x') ->
                                    handle x'
                                    (\s -> return (st',err s))
                                    (\x'' -> let (SIOSE f') = f x'' in
                                               f' st'))


instance IOMonad (Imp s) where
 readFil f =     convertIOtoImp (readFile f)     ("Can't find "++f)
 writeFil f s =  convertIOtoImp (writeFile f s)  ("Can't open "++f)
 appendFil f s = convertIOtoImp (appendFile f s) ("Can't find "++f)
 getLin =        convertIOtoImp getLine          "???"
 putSt s =       convertIOtoImp (putStr s)       "???"

-- convertIOtoImp com mess  executes com and catches any IO-errors, replacing
-- them by mess. All this is wrapped in an Imp-monad.
convertIOtoImp :: IO a -> String -> Imp s a
convertIOtoImp com mess = SIOSE (\state -> fmap (\x -> (state,x)) com')
                        where com' = catch (fmap return com)
                                           (\_ -> return (errS mess)) 
      
-- Imp has a state:

instance StateMonad Imp where
     update f = SIOSE (\s -> return (f s,return s))  -- is this what we want?
     fetch = update id
     set new = update' (\old -> new)
     update' f = SIOSE (\s -> return (f s,return ())) 
                 -- fmap (const ()) (update f)


instance PreErrorMonad (Imp a) where
  err e = SIOSE (\s -> return (s,err e))

instance ErrorSMonad (Imp a) where
    handleS ~(SIOSE x) hand f = 
                     SIOSE (\st -> (x st) >>= \(st',x') ->
                                   handle x'
                                   (\e -> let (SIOSE hand') = hand e in
                                          hand' st')
                                   (\x'' -> let (SIOSE f') = f x'' in
                                            f' st'))

-- goSte x s  executes x with initial state s
-- unhandled errors in x are ignored!
goSte :: Imp s a -> s -> IO a
goSte (SIOSE x) s = fmap (\(st,x') -> noErr (const "") x') (x s)


performS :: s -> State s a -> Imp b (a,s)
performS st sm = let (st',ea) = runState st sm in
                      handle ea
                      (\e -> err e)
                      (\a -> return (a,st'))

-- Simple IO functions
putLines :: IOMonad m => [String] -> m ()
putLines = maplComs putLine

putLine :: IOMonad m => String -> m ()
putLine = putSt . plusCR

putLn :: IOMonad m => m ()
putLn = putSt "\n"
