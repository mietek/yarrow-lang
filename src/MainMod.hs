-- File: MainMod
-- Description: This module contains the code for the commands in the main
--              mode

module MainMod(doQuery, errNotInMainMode) where

import General
import Collect
import HaTuple
import HaMonSt
import Basic
import Paths(genErrS)
import SyntaxI
import Typing
import Matchin
import FancyTy(PseudoTermIT)
import GenComs
import Reduce
import PTSys
import ProvMod
import MainSta
import YarMsg
import TacSpec(qGiveUseFor,qUseFor)
import Modules

      
------------------------------------------------
-- S E L E C T I O N   O F   C O M M A N D S  --
------------------------------------------------

-- parsing and executing commands

doQuery :: Query -> M Result
doQuery query = 
          handleS (doQuery1 query)
          (\errMess -> return (RError errMess)) 
          return

-- First, we handle requests for information
doQuery1 QGiveSyntaxInfo = map RSyntaxInfoIs fetchSyn
doQuery1 QGiveGlobCon = map RGlobConIs fetchCon
doQuery1 QGiveModules = map RModulesAre fetchModulesInfo
doQuery1 (QGiveModuleContents m) = qGiveModuleContents m
doQuery1 QGiveUseFor = qGiveUseFor
-- Now commands that change the state
doQuery1 (QSetOptions opts) = setBoolOptions opts >> map RSyntaxInfoIs fetchSyn
-- Now commands that can be handled in both modes
doQuery1 QClearModule = qClearModule
doQuery1 (QGiveBDReductionPath taskNr ct)= giveNormalForm bdcom taskNr ct
doQuery1 (QGiveBReductionPath taskNr ct) = giveNormalForm bcom  taskNr ct
doQuery1 (QGiveDReductionPath taskNr ct) = giveNormalForm dcom  taskNr ct
doQuery1 (QGiveType taskNr ct) = giveType taskNr ct
doQuery1 (QCheckBDConv taskNr ctt) = qCheckConv taskNr ctt
doQuery1 (QCheckTyping taskNr ctt) = qCheckType taskNr ctt
-- Extension: Subtyping:
doQuery1 (QCheckSubtype taskNr ctt) = qCheckSubtype taskNr ctt
-- End Extension: Subtyping
doQuery1 (QZMatch taskNr cvtt) = qZMatch taskNr cvtt
doQuery1 (QGivePossibleImplArgs v) = map RPossibleImplArgsAre
                                         (givePossibleImplArgs v)
doQuery1 (QSetPrecAndAss via) = qSetPrecAndAss via
doQuery1 (QSetBinder vn) = qSetBinder vn
doQuery1 (QSetLaTeX v) = qSetLaTeX v
doQuery1 (QSetImplArgs vi) = qSetImplArgs vi
doQuery1 (QUseFor tacName v) = qUseFor tacName v
doQuery1 (QDeclareVars its) = addVar its
-- Extension: Subtyping:
doQuery1 (QDeclareVarsSub its) = addVarSub its
doQuery1 (QDeclareVarsSubW its) = addVarSubW its
-- End Extension: Subtyping
doQuery1 (QDefVar it) = addDef it
doQuery1 (QDefVarW it) = addDefW it
doQuery1 (QLoadModuleInput name contents) = qLoadModuleInput name contents
doQuery1 (QContinueLoad status) = qContinueLoad status
doQuery1 (QSaveModule name) = qSaveModule name
doQuery1 (QSaveCompleted status) = qSaveCompleted status
doQuery1 (QProveVar it) = callProver it
-- Now the commands that can only be performed in one of the two modes.
doQuery1 query = fetchTasks >>= \(_,tasks) ->
                 if null tasks then
                    doQueryM query
                 else
                    doQueryP query


doQueryM :: Query -> M Result
doQueryM (QDelFromVar v) = resetVar v
doQueryM (QSetTypingSystem sys) = changeSystem sys
doQueryM _ = errNotInMainMode

errNotInMainMode :: PreErrorMonad m => m a
errNotInMainMode = genErrS "This command is not available in main-mode"

 
       
---------------------
-- C O M M A N D S --
---------------------
     
-- commands for extending the context 

addVar :: ([Vari],TermIT) -> M Result
addVar (vars,(t0,it)) =
            checkVars vars >> 
            let oneDecl = mkDecl (head vars,t0,dummySort)
                allDecls = multDecl vars oneDecl in
            fetchCon >>= \c ->
            getLContextRet (globToTot c) allDecls it dummyIT >>= \allDecls' ->
            addConElems allDecls'


-- Extension: Subtyping:
addVarSub :: ([Vari],TermIT) -> M Result
addVarSub (vars,b) = addVarSubW (vars,b,dummyTermIT)

addVarSubW :: ([Vari],TermIT,TermIT) -> M Result
addVarSubW (vars,(bound0,itb),(t0,it)) =
            checkVars vars >>
            let oneDecl = mkSubDecl (head vars,bound0,t0,dummySort)
                allDecls = multDecl vars oneDecl in
            fetchCon >>= \c -> 
            getLContextRet (globToTot c) allDecls it itb >>= \allDecls' ->
            addConElems allDecls'
-- End Extension: Subtyping

addDef :: (Vari,TermIT) -> M Result
addDef (v,t) = addDefW (v,t,dummyTermIT)

addDefW :: (Vari,TermIT,TermIT) -> M Result
addDefW (v,(d0,itd),(t0,it)) =
            totallyFresh v >>
            let oneDecl = mkDef (v,d0,t0,dummySort)
                allDecls = listToLocCon [oneDecl] in
            fetchCon >>= \c ->
            getLContextRet (globToTot c) allDecls it itd >>= \allDecls' ->
            addConElems allDecls'
                          
totallyFresh :: Vari -> M ()
totallyFresh v = fetchSyn >>= \si ->
                 fetchCon >>= \c ->
                 handle (freshG si c v) err (\_ ->
                 domAllLocCon >>= \allLocVars ->
                 if v `elemC` allLocVars then
                    genErrS ("Variable "++printVarSt si v ++
                             " occurs already in some local context")
                 else
                 skip)

checkVars :: [Vari] -> M ()
checkVars vars = 
            maplComs totallyFresh vars >>
            let len = length vars
                conflicts = filter (\v -> v `elem` (vars\\[v])) vars in
            if not (null conflicts) then
               fetchSyn >>= \si ->
               genErrS ("Variable "++printVarSt si (head conflicts) ++ 
                        " declared twice")
            else                              
            skip

addConElems :: LContext -> M Result
addConElems lc = 
            fetchCon >>= \c ->
            let lc' = locConToList lc
                len = length lc'
                cc = lc' `addConElems'` c in
            setCon cc >>
            (if finalCheck then
                -- to depend only on inferType (and not on inferTypeRet),
                -- we have to check cc with function contnOk, as follows:
                fetchSyn >>= \si ->
                handleTypeErr (contnOk si len cc) >>= \_ ->
                skip
             else
                skip
             ) >>
             return (RGlobConExt (takeTWO len cc))
            
                 
-- if finalCheck  is true, every addition to the context (var,def) is also
-- checked by the ordinary type-checking routine, instead of just the
-- fancy type-checking routine.
finalCheck = True

addConElems' :: [ContextE] -> GContext -> GContext
addConElems' [] c = c
addConElems' (ce:ces) c = addConElems' ces (ce `addC` c)

multDecl :: [Vari] -> ContextE -> LContext
multDecl vs ce = listToLocCon (map (\v -> (v,snd ce)) vs)

-- throwing variables out of the context

resetVar :: Vari -> M Result
resetVar v =
         fetchCon >>= \c ->
         let (c1,c2) = breakTWO (==v) c in
         if isEmptyI c2 then
            genErrS ("Variable "++v++" is not declared")
         else                                       
         let (_,cKeep) = removeI c2 v
             cDelete = map fst c1 ++ [v] in
         fetchModulesInfo >>= \mi ->
         let lv = lastVarModuleDefined mi in
         if lv `elem` cDelete then
            genErrS ("Variable "++v++" occurs in a module")
         else
         maplComs removeInfo cDelete >>
         setCon cKeep >>
         return (RGlobConIs cKeep)

-- removeInfo v  removes all info about v from the state
-- currently, this is
--    * implicit-info
--    * lemmas present in the cache
removeInfo :: Vari -> M ()
removeInfo v = removeImplicit v >>
               removeLemmas v
  
                                  
-- changing and showing the PTS

changeSystem :: System -> M Result
changeSystem sys = 
      let ((sorts,axioms,rules,sortsSub,rulesSub),exs) = sys in
      if not (allDifferent sorts) then
         genErrS "Same sort occurs more than once in list of sorts"
      else
      let f1 a = [a]
          f2 (a,b) = [a,b]
          f3 (a,b,c) = [a,b,c]
          flat = concat (map f2 axioms) ++ concat (map f3 rules) ++
                 concat (map f1 sortsSub) ++ concat (map f3 rulesSub) in
      if not (all (`elem` sorts) flat) then
         genErrS "Sort mentioned in axioms or rules does not exist"
      else
      admitSystem sys >>
      let message = if nonNormalizing sys then
                       "Warning: System is not normalizing."
                    else
                    if normalizing sys then
                       "This system is normalizing."
                    else
                       "Warning: Don't know whether system is normalizing or not." in
      fetchSys >>= \oldSys ->
      fetchCon >>= \c ->
      if isEmptyI c || oldSys `partSystem` sys then
         setSys sys >>
         -- It may be the case that some of the definitions that didn't have
         -- a sort, do have a sort in the new system.
         fetchCon >>= \c ->
         (if not (isEmptyI c) then
              -- oldSys `partSystem` sys
              setCon (updateSortsOfDefsInContext oldSys sys c)
          else skip) >>
         return (RTypingSystemOk message)
      else
         genErrS ("System does not include old system. Delete entire "++
                  "context first.")



-- the prove command
callProver :: (Vari,TermIT) -> M Result
callProver (v,goal0) =
         totallyFresh v >> 
         fetchCon >>= \globCon -> 
         getSortRet (globToTot globCon) goal0 >>= \(goal,goalSrt) ->
         setUpProveMode (v,goal,goalSrt)
