-- File: GenComs
-- Description: this module holds the code for commands
--   that are available in both the prover and the main loop

module GenComs(handleTypeErr,
               getTermRet, getTypeRet, getSortRet, getDefRet, getLContextRet,
               getType, getSort,
               fetchTotalCon, listOptions, qSetPrecAndAss, qSetBinder,
               qSetLaTeX,
               qSetImplArgs, givePossibleImplArgs, giveType, giveNormalForm,
               qCheckType, qCheckConv, qCheckSubtype, qZMatch,
               getGoal1, getPath1, replaceTPath) where

import HaTuple
import General
import Basic
import Paths
import Collect
import HaMonSt
import PTSys
import SyntaxI
import Reduce
import Typing
import Matchin
import FancyTy
import ProvDat
import MainSta
import YarMsg

-----------------------
-- TYPING THE INPUT  --
-----------------------

-- This section holds a number of commands to do type-inference on the input.

handleTypeErr :: PreErrorMonad m => E a -> m a
handleTypeErr res = handle res err return
              
getTermRet :: (HasSyntax m, PreErrorMonad m) =>
              Context -> PseudoTermIT -> m (Term,PseudoTerm)
getTermRet cont term =
           fetchSyn >>= \si ->
           handleTypeErr (inferTermRet si cont term)

getTypeRet :: (HasSyntax m, PreErrorMonad m) => 
              Context -> PseudoTermIT -> m (Term, Term,Sort)
getTypeRet cont term =
           fetchSyn >>= \si ->
           handleTypeErr (inferTypeRet si cont term)

getSortRet :: (HasSyntax m, PreErrorMonad m) => 
              Context -> PseudoTermIT -> m (Term,Sort)
getSortRet cont term =
           fetchSyn >>= \si ->
           handleTypeErr (inferSortRet si cont term)

getDefRet :: (HasSyntax m, PreErrorMonad m) => 
              Context -> PseudoTermIT -> PseudoTermIT -> m (Term,Term,Sort)
getDefRet cont term typ =
           fetchSyn >>= \si ->
           handleTypeErr (checkDef si cont term typ)

getLContextRet :: (HasSyntax m, PreErrorMonad m) => 
                  Context -> LContext -> InfoTree -> InfoTree -> m LContext
getLContextRet cont lcon it1 it2 =
           fetchSyn >>= \si ->
           handle (lContOkRet si cont lcon it1 it2)       
           -- in case of error, remove 'at <var>' piece, which is 
           -- next-to-last
           (\er -> err (take (length er -2) er ++ [last er]))
           return

getType :: (HasSyntax m, PreErrorMonad m) => 
           Context -> Term -> m (Term,Sort)
getType cont term =
           fetchSyn >>= \si ->
           handleTypeErr (inferType si cont term)

getSort :: (HasSyntax m, PreErrorMonad m) => 
           Context -> Term -> m Sort
getSort cont term =
           fetchSyn >>= \si ->
           handleTypeErr (inferSort si cont term)



-- this routine delivers the global context as a total context
fetchTCon :: HasContext a => a Context
fetchTCon = fmap globToTot fetchCon


-- this routine delivers the combination of the global and local context
fetchTotalCon :: TaskId -> M Context
fetchTotalCon taskId =
                fetchCon >>= \globCon -> 
                let globCon' = globToTot globCon in
                if taskId == noTask then
                   return globCon'
                else
                fetchTacPaths taskId >>= \tacPaths ->
                if null tacPaths then
                  return globCon'
                else
                  getGoal1 taskId >>= \(_,(_,locCon,_)) ->
                  return (locCon `addLocG` globCon)

--------------------------------------
-- G E N E R A L   C O M M A N D S  --
--------------------------------------

-- This section is divided in a number of subsections, corresponding to
-- groups of commands.

              
---------------------
--     Options     --
---------------------

listOptions :: [(String,CodeOption)]
listOptions = [("i",optImplicit),
               ("s",optShowSort),
               ("p",optShowProofterm),
               ("r",optShowRedPath)]

----------------------------
--    Infix & Implicit    --
----------------------------

qSetPrecAndAss :: (Vari,Int,Assoc) -> M Result
qSetPrecAndAss (v,n,as) =
          if not (isOper v) then
             genErrS "Only operators can be used infix"
          else
          if n<1 || n>maxPrec then
              genErrS ("Precedence only in range 1.."++show maxPrec)
          else
             setPrec v (n,as) >>
             fmap RSyntaxInfoIs fetchSyn

qSetBinder :: Vari -> M Result
qSetBinder v =
             setBind v >>
             fmap RSyntaxInfoIs fetchSyn

qSetLaTeX :: (Vari,Int) -> M Result
qSetLaTeX (v,i) =
             setLatex v i >>
             fmap RSyntaxInfoIs fetchSyn

                               
qSetImplArgs :: (Vari,Int) -> M Result
qSetImplArgs (v,n) =
     fetchTCon >>= \c ->
     checkImplic v n >>
     setImplicit v n >>
     fmap RSyntaxInfoIs fetchSyn
 
givePossibleImplArgs :: Vari -> M [Int]
givePossibleImplArgs v =
           fetchTCon >>= \c ->
           getType c (mkVr v) >>= \(t,_) ->
           fetchSyn >>= \si ->
           let l = peelAll si c t
               getSort = snd.fst3.snd
               -- the n+1'th sort must be different from the first sort
               numOk n = getSort (l!!0) /= getSort (l!!n) in
           return (0:(filter numOk [1..length l-1]))

-- checkImplic c t  checks whether t can have n implicit arguments
checkImplic :: Vari -> Int -> M ()
checkImplic v n =
           givePossibleImplArgs v >>= \l ->
           if n `elem` l then
              skip
           else
              genErrS "Not always clear whether there are implicit arguments"


----------------------------------------------------------
-- C O N T E X T - S E N S I T I V E   C O M M A N D S  --
----------------------------------------------------------

getLContextDITRet :: (HasSyntax m, PreErrorMonad m) => 
                     Context -> LContext -> m LContext
getLContextDITRet c lc = 
           fetchSyn >>= \si ->
           handleTypeErr (lContOkRet si c lc dummyIT dummyIT)

-- giveType  gives the type and sort of a term in some local context
giveType :: TaskId -> (LContext,TermIT) -> M Result
giveType taskId (lCon0,term0) =
                fetchTotalCon taskId >>= \c ->
                getLContextDITRet c lCon0 >>= \lCon ->
                let cc = lCon `addLoc` c in
                getTypeRet cc term0 >>= \tts ->
                return (RTypeIs (tts,lCon))


-- giveNormalForm   gives the reduction path of a term in some local context
giveNormalForm :: Reduction -> TaskId -> (LContext,TermIT) -> M Result
giveNormalForm red taskId (lCon0,term0) = 
                fetchTotalCon taskId >>= \c ->
                getLContextDITRet c lCon0 >>= \lCon ->
                let cc = lCon `addLoc` c in
                getTermRet cc term0 >>= \(term,_) ->
                return (RReductionPathIs (redSeq red c term,lCon))

qCheckType :: TaskId -> (LContext,TermIT,TermIT) ->M Result
qCheckType taskId (lCon0,t1,t2) = 
                fetchTotalCon taskId >>= \c ->
                getLContextDITRet c lCon0 >>= \lCon ->
                let cc = lCon `addLoc` c in
                getTypeRet cc t1 >>= \(_,t1Typ,_) ->
                getTermRet cc t2 >>= \(t2',_) ->
                fetchSyn >>= \si ->
                return (RCheckIs (subtype si cc t1Typ t2',lCon))

qCheckConv :: TaskId -> (LContext,TermIT,TermIT) ->M Result
qCheckConv taskId (lCon0,t1,t2) = 
                fetchTotalCon taskId >>= \c ->
                getLContextDITRet c lCon0 >>= \lCon ->
                let cc = lCon `addLoc` c in
                getTermRet cc t1 >>= \(t1',_) ->
                getTermRet cc t2 >>= \(t2',_) ->
                return (RCheckIs (bdEqual cc t1' t2',lCon))

-- Extension: Subtyping:
qCheckSubtype :: TaskId -> (LContext,TermIT,TermIT) -> M Result
qCheckSubtype taskId (lCon0,t1,t2) = 
                fetchTotalCon taskId >>= \c ->
                getLContextDITRet c lCon0 >>= \lCon ->
                let cc = lCon `addLoc` c in
                getTermRet cc t1 >>= \(t1',_) ->
                getTermRet cc t2 >>= \(t2',_) ->
                fetchSyn >>= \si ->               
                return (RCheckIs (subtype si cc t1' t2', lCon))
-- End Extension: Subtyping

qZMatch :: TaskId -> (LContext,[Vari],TermIT,TermIT) -> M Result
qZMatch taskId (lCon0,exVars,p0,t0) =
             fetchTotalCon taskId >>= \c ->
             getLContextDITRet c lCon0 >>= \lCon ->
             let cc = lCon `addLoc` c in
             getTermRet cc p0 >>= \(p,_) ->
             getTermRet cc t0 >>= \(t,_) ->
             fetchSyn >>= \si ->
             return (RZMatchIs (match alwaysUnfold si (cc,exVars,p,t)))
                                      
---------------------
-- OTHER FUNCTIONS --
---------------------

getGoal1 :: TaskId -> M (Hnum,Goal)
getGoal1 taskId = getPath1 taskId >>= \tacPath ->
                  fetchTacticTree taskId >>= \tacTree ->
                  return (findGoal tacTree tacPath)

getPath1 :: TaskId -> M TacPath
getPath1 taskId = fetchTacPaths taskId >>= \tacPaths ->
                  if null tacPaths then
                     genErrS "There is no goal"
                  else   
                     return (head tacPaths)
                     
-- replaceTPath tree path u  replaces in tree at location path the tree
--                           by u                        
replaceTPath :: TacticTree -> TacPath -> TacticTree -> TacticTree
replaceTPath _ [] u = u
replaceTPath (TTTac tac p ts) (n:ns) u = 
    TTTac tac p (doInList n (\t -> replaceTPath t ns u) ts)

