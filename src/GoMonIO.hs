-- File: GoMonIO
-- Description: TThis module defines IO monads, for use in Gofer

module GoMonIO where

-----------------------
-- I O   M O N A D S --
-----------------------

class Monad m => IOMonad m where
    putSt :: String -> m ()
    getLin :: m String
    readFil :: String -> m String            -- file reading
    writeFil :: String -> String -> m ()     -- file writing
    appendFil :: String -> String -> m ()    -- file appending
    readCha :: String -> m String            -- input
    appendCha :: String -> String -> m ()    -- output

------------------------------
-- An I/O State Error monad --
------------------------------
                            
-- The following type-constructor is called Imp because it allows
-- more-or-less imperative programming

-- state ------------------------------------|
-- input -----------------------------|      |
-- responses to world -----v          v      v
data Imp s a = SIOSE ((([Response],[String]),s)->
                         (([Response],[String]),[Request],s,E a))
-- responses to world --------^          ^         ^      ^  ^
-- rest of input lines ------------------|         |      |  |
-- requests to world ------------------------------|      |  |
-- state -------------------------------------------------|  |    
-- result ---------------------------------------------------| 

instance Functor (Imp s) where
     map f (SIOSE x) = SIOSE (\(ri,s) -> doFth4 (map f) (x (ri,s)))

instance Monad (Imp s) where
    result x = SIOSE (\(ri,s) -> (ri,[],s,result x))
    (SIOSE x) `bind` f = SIOSE (\(ri1,s1) -> hlp (x (ri1,s1)))
                           where hlp (ri2,req1,s2,x') = 
                                   doSnd4' (req1 ++) (hlp2 x')
                                      where hlp2 (Suc x'') = 
                                               let (SIOSE f') = f x'' in 
                                               f' (ri2,s2)
                                            hlp2 (Err s) = (ri2,[],s2,Err s)


doSnd4' f ~(a,b,c,d) = (  a,f b,  c,  d)
 
-- Imp has a state:
instance StateMonad Imp where
   fetch = update id
   update f = SIOSE (\(ri,s) -> (ri,[],f s,result s))  
   set new = update' (\old -> new)                       
   update' f = SIOSE (\(ri,s) -> (ri,[],f s,result ())) 
               --map (const ()) (update f)


instance PreErrorMonad (Imp a) where
  err e = SIOSE (\(ri,s) -> (ri,[],s,Err e))

instance ErrorSMonad (Imp a) where
  handleS (SIOSE x) hand f = SIOSE (\(ri1,s1) -> hlp (x (ri1,s1)))
                     where hlp (ri2,req1,s2,x) = doSnd4' (req1 ++) (hlp2 x)
                                                 where
                                                 hlp2 (Suc x') = 
                                                    let (SIOSE f') = f x' in
                                                    f' (ri2,s2)
                                                 hlp2 (Err s) =
                                                  let (SIOSE f') = hand s in
                                                  f' (ri2,s2)
-- compare to bind, but handleM does not pass the error, but handles it

instance IOMonad (Imp a) where
 getLin = SIOSE (\((res,(i:is)),s) -> ((res,is),[],s,return i))
     -- get produces no output and doesn't change the state
 putSt = appendCha stdout
 readFil f = SIOSE (\((~(res:ress),inp),s) -> 
                   let d (Str cont) = return cont
                       d _ = errS ("Can't find \""++f++"\"") in
                   ((ress,inp),[ReadFile f],s,d res))
 writeFil f cont =  SIOSE (\((~(res:ress),inp),s) -> 
                   let d Success = return ()
                       d _ = errS ("Can't open \""++f++"\"") in
                   ((ress,inp),[WriteFile f cont],s,d res))
 appendFil f cont =  SIOSE (\((~(res:ress),inp),s) -> 
                   let d Success = return ()
                       d _ = errS ("Can't find \""++f++"\"") in
                   ((ress,inp),[AppendFile f cont],s,d res))

 readCha f = SIOSE (\((~(res:ress),inp),s) ->
                   let d (Str cont) = return cont
                       d _ = errS ("Can't find channel \""++f++"\"") in
                   ((ress,inp),[ReadChan f],s,d res))
 appendCha f cont = SIOSE (\((~(res:ress),inp),s) -> 
                   let d Success = return ()
                       d _ = errS ("Can't open channel \""++f++"\"") in
                   ((ress,inp),[AppendChan f cont],s,d res))


-- goSte x s  executes x with initial state s
-- unhandled errors in x are ignored!
goSte :: Imp s () -> s -> Dialogue
goSte (SIOSE x) s ~((Str input):ress) = ReadChan stdin :
                                         snd4 (x ((ress,lines input),s))


performS :: PreErrorMonad (Imp b) => s -> State s a -> Imp b (a,s)
performS st (ST p) = let (st',ea) = p st in
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

