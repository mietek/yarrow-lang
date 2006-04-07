-- File: Paths
-- Description: This module defines paths in terms, used to indicate
--              subterms, some functions for term traversal, and 
--              some routines for creating errors.

module Paths(-- PATHS
             TermPath, dummyTermPath, emptyTermPath, Path, dummyPath,
             mkPathNonb, mkPathBindVar, mkPathBindTyp, mkPathBindSort,
             mkPathBindBody, mkPathBindSubterm, mkPathLetDef, 
             mkPathAppFun, mkPathAppArg,
             mkPathConVar, mkPathConTyp, mkPathConSort, mkPathConOther,
             mkPathConDef,
             isPathConVar, isPathConTyp, isPathConSort, isPathConOther,
             deconPathConOther,
             changeSubterm, findSubterm,

             -- TERM TRAVERSAL
             changeSubterms, changeSubterms0, Selector, 
             {- changeNumberedSubterms0, -}
             changePathNumberedSubterms,

             -- ERRORS
             errS, errP, eTI,
             genErrSuffix, genErr, genErrS, genErrT, genErrTI,
             internalErr, internalErrorString, admitNoErr
             ) where

--import General
import HaTuple
import Collect
import Basic
import HaMonSt

-----------------
--  P A T H S  --
-----------------                 

-- A TermPath indicates a subterm of a term.
-- A Path indicates a subterm of a term occurring somewhere in a context.
-- They are mainly useful in a graphical user interface.

type TermPath = [Int]
                  
dummyTermPath :: TermPath
dummyTermPath = [-1]

emptyTermPath :: TermPath                     
emptyTermPath = []

type Path = (Vari,TermPath)

dummyPath = ("",dummyTermPath)

-- paths are set up uniformly, so that given a path and a term, the indicated
-- subterm can be looked up independent of all actual term constructions.

-- First the path constructions for subterms

mkPath :: Int -> Path -> Path
mkPath n (v,p) = (v,p++[n])
 
-- For nonbinding nodes               
mkPathNonb :: Int -> Path -> Path
mkPathNonb n = mkPath n  -- n is index in list, from 0 onwards

-- For binding nodes
mkPathBindVar, mkPathBindTyp, mkPathBindSort, mkPathBindBody :: Path -> Path
mkPathBindSubterm :: Int -> Path -> Path
mkPathBindVar = mkPath 0        -- Presently, not used
mkPathBindTyp = mkPath 1
mkPathBindSort = mkPath 2       -- Presently, not used
mkPathBindBody = mkPath 3
mkPathBindSubterm n = mkPath (n+4)  -- n is index in list, from 0 onwards

-- Now, specifically for lambda-terms:
mkPathLetDef, mkPathAppFun, mkPathAppArg :: Path -> Path
mkPathLetDef = mkPathBindSubterm 0
mkPathAppFun = mkPathNonb 0   -- first element of the list
mkPathAppArg = mkPathNonb 1   -- second element of the list


-- Now the path constructions for context elements
mkPathConVar, mkPathConTyp, mkPathConSort :: Vari -> Path
mkPathConOther :: Vari -> Int -> Path
mkPathConDef :: Vari -> Path
mkPathConVar v = (v,[0])
mkPathConTyp v = (v,[1])
mkPathConSort v = (v,[2])
mkPathConOther v n = (v,[n+3])
mkPathConDef v = mkPathConOther v 0

isPathConVar, isPathConTyp, isPathConSort :: Int -> Bool
isPathConOther :: Int -> Bool
deconPathConOther :: Int -> (Bool, Int)
isPathConVar = (==0)
isPathConTyp = (==1)
isPathConSort = (==2)
isPathConOther = (>=3)
deconPathConOther p = (p>=3,p-3)

 

-- changeSubterm f vl term path  changes the subterm of term indicated by
--   path by function f.
-- vl is a list of forbidden variables (variables that already occur in
-- the context).
-- the function f gets as arguments the subterm, its sub-context w.r.t.
-- term, and a list of forbidden variables, which is extended by
-- the variables in the sub-context.
changeSubterm :: (Collection c, PreErrorMonad m) => 
                 ((Term,LContext,c Vari)->(Term,a)) -> 
                 c Vari -> Term -> TermPath -> m (Term,a)
changeSubterm = changeSubterm0 emptyLCon

changeSubterm0 :: (Collection c, PreErrorMonad m) => 
                 LContext -> ((Term,LContext,c Vari)->(Term,a)) ->
                 c Vari -> Term -> TermPath -> m (Term,a)
changeSubterm0 subCon f vl term [] = return (f (term,subCon,vl))
changeSubterm0 subCon f vl term (p:ps) | isNonb term = 
                  let (_,cat,ts) = deconstructNonb term in
                  changeSubterm1 subCon f vl p ts ps >>= \(ts',res) ->
                  return (mkNonb cat ts',res)
changeSubterm0 subCon f vl term (p:ps) | isBind term = 
   let (_,cat,ts,(v,t,s),u) = deconstructBind (changeNiceVar term vl) in
   case p of
      3 -> let vl' = add v vl
               subCon' = (v,((t,s),convBindToCont cat, ts)) `addC` subCon in
           changeSubterm0 subCon' f vl' u ps >>= \(u',res) ->
           return (mkBind cat ts (v,t,s) u',res)
      2 -> pathNotExistError  -- or return (mkSrt s, subCon)
      1 -> changeSubterm0 subCon f vl t ps >>= \(t',res) ->
           return (mkBind cat ts (v,t',s) u, res)
      0 -> pathNotExistError  -- or return (mkVr v, subCon)
      otherwise -> 
           changeSubterm1 subCon f vl (p-4) ts ps >>= \(ts', res) ->
           return (mkBind cat ts' (v,t,s) u, res)
changeSubterm0 _ _ _ _ _ = pathNotExistError
                                    
-- changeSubterm1 subCon f vl p ts ps  selects the p'th element of ts
changeSubterm1 :: (Collection c, PreErrorMonad m) => 
                   LContext -> ((Term,LContext,c Vari)->(Term,a)) ->
                   c Vari -> Int -> [Term] -> TermPath ->
                   m ([Term],a)
changeSubterm1 subCon f vl p ts ps = 
                  if p>= length ts then
                     pathNotExistError
                  else
                  changeSubterm0 subCon f vl (ts!!p) ps >>= \(t', res) ->
                  return (take p ts ++ [t'] ++ drop (p+1) ts, res)
                        

-- findSubterm vl term path  finds the subterm of term indicated by path,
-- and also delivers its sub-context w.r.t. term.
-- vl is a list of forbidden variables (variables that already occur in
-- the context).
findSubterm :: (Collection c, PreErrorMonad m, Functor m) => 
                c Vari -> Term -> TermPath -> m (Term,LContext)
findSubterm vl term path = let f (t,subCon,_) = (t,(t,subCon)) in
                           fmap snd (changeSubterm f vl term path)

pathNotExistError :: PreErrorMonad m => m a
pathNotExistError = errS "Indicated path does not exist"





---------------------------------
-- T E R M   T R A V E R S A L --
---------------------------------      

-- Probably these functions can be simplified by the use of monads, so
-- no explicit state has to be carried around. However, presently these
-- functions are used in a non-monadial setting.
-- A test with monads shows that this is much slower (under Gofer).

-- changeSubterms f res vl t  traverses t in a preorder order, 
--       applying f to each subterm.  
--       Function f has a state of type 'a'. f gets also as argument the
--       context of the subterm w.r.t. the total term
changeSubterms :: Collection c => ((Term,LContext,a)->(Term,a)) -> a -> 
                  c Vari -> Term -> (Term,a)
changeSubterms = changeSubterms0 emptyLCon

-- changeSubterms0  applies f to the node and applies changeSubterms1 to
--                  the result. That function distributes f over the children
--                  vl is a set of 'prohibited' variables: variables in 
--                  binders will get a name not occurring in vl.             
changeSubterms0 :: Collection c => 
                   LContext -> ((Term,LContext,a)->(Term,a)) ->  
                   a -> c Vari -> Term -> (Term,a)
changeSubterms0 subCon f res vl t =
        let (t',res') = f (t,subCon,res) in
        changeSubterms1 subCon f res' vl t'

changeSubterms1 :: Collection c => 
                   LContext -> ((Term,LContext,a)->(Term,a)) -> 
                   a -> c Vari -> Term -> (Term,a)
changeSubterms1 _ _ res _ bas | isBasic bas = (bas,res)
changeSubterms1 subCon f res vl term =
       let --foldChange :: a -> [Term] -> ([Term],a)
           foldChange res []  = ([],res)
           foldChange res (t:ts) = 
                    let (t',res') = changeSubterms0 subCon f res vl t in
                    doFst (t':) (foldChange res' ts) in
           if isBasic term then
               (term,res)
           else if isNonb term then
               let (_,cat,ts) = deconstructNonb term
                   (ts',res') = foldChange res ts in
               (mkNonb cat ts',res')
           else {- isBind term -}
               let (_,cat,ts,(v,t,s),u) = deconstructBind (changeVar term vl)
                   (ts',res') = foldChange res ts
                   (t',res'') = changeSubterms0 subCon f res' vl t
                   vl' = add v vl
                   subCon' = (v,((t,s),convBindToCont cat, ts)) `addC` subCon
                   (u',res''') = changeSubterms0 subCon' f res'' vl' u in
               (mkBind cat ts' (v,t',s) u', res''')
             
 
type Selector = Int -> Bool

-- changeNumberedSubterms f res select t  traverses t in a preorder
--        way, and applies f to each subterm. f states if a subterm could
--        be changed. All changeable terms are numbered, and f is only
--        applied to such terms selected by select.
--        This function can have unexpected results if the result of f
--        can be changed again by f.
changeNumberedSubterms :: Collection c =>
                          ((Term,LContext,a)->(Bool,Term,a)) -> 
                          a -> Selector -> c Vari -> Term -> (Term,a)
changeNumberedSubterms f res select vl =
           let -- fn :: (Term,LContext,(Int,a)) -> (Term,(Int,a))
               fn (t,subCon,(n,a)) = let (b,t',a') = f (t,subCon,a) in
                                     if b then
                                        if select n then
                                           (t',(n+1,a'))
                                        else
                                           (t,(n+1,a))
                                     else       
                                        (t,(n,a))
               resn = (1,res) in
           doSnd snd . changeSubterms fn resn vl
                          

-- changeNumberedSubterms0 is the same as changeNumberedSubterms, but
--         has no result other than the new term (no state).
--         No use is made of the local context of subterms.
changeNumberedSubterms0 :: Collection c =>
                           (Term->(Bool,Term)) -> Selector ->
                           c Vari -> Term -> Term
changeNumberedSubterms0 f select vl = 
         let f0 (t,_,_) = let (b,t') = f t in 
                          (b,t',()) in
         fst . changeNumberedSubterms f0 () select vl

-- changePathNumberedSubterms f (path,select) vl term
--         applies changeNumberedSubterms0 on the subterm of term
--         indicated by path.
changePathNumberedSubterms :: (Collection c, PreErrorMonad m, Functor m) => 
                              (Term->(Bool,Term)) -> (TermPath,Selector) ->
                              c Vari -> Term -> m Term
changePathNumberedSubterms f (path,select) vl term = 
      let f0 (t,locCon,vl') = (changeNumberedSubterms0 f select vl' t,()) in
      fmap fst (changeSubterm f0 vl term path)



-------------------------------
-- E R R O R S --
-------------------------------

errS :: PreErrorMonad m => String -> m a
errS s = err [ES s]

errP :: PreErrorMonad m => PlaceInfo -> String -> m a
errP pi s = err [EP pi, ES s]

eTI :: TermIT -> ErrorElem
eTI (t,IT pi _) = ETP (t,pi)

-- genErr etc. give an error in the standard format for errors during the
-- execution of commands
genErr :: PreErrorMonad m => Error -> m a
genErr er = err (er++[ES genErrSuffix])

genErrS :: PreErrorMonad m => String -> m a
genErrS s = genErr [ES s]

genErrT :: PreErrorMonad m => String -> Term -> String -> m a
genErrT s1 t s2 = genErr [ES s1, ET t, ES s2]
 
genErrTI :: PreErrorMonad m => String -> TermIT -> String -> m a
genErrTI s1 t s2 = genErr [ES s1, eTI t, ES s2]

genErrSuffix = " (error)"



-- internalErr  makes an error message for an internal error 
--              (that only occur as a result of some bug)
internalErr e = errS (internalErrorString ++ e)

internalErrorString = "PLEASE CONTACT Jan Zwanenburg\n" ++
                      "INTERNAL ERROR:\n"

admitNoErr :: E a -> a
admitNoErr = noErr (\mess -> internalErrorString ++ concat (map convert mess))
                where convert (ES s) = s++" "
                      convert (ET t) = "term "
                      convert (EP p) = "termit "
