-- File: ProvMod
-- Description: This module defines the prove-mode of the proof assistant.

module ProvMod(doQueryP, setUpProveMode) where

import HaTuple
import Collect(AssocList(..))
import General
import HaMonSt
import Basic
import Paths
import SyntaxI
import Typing
import Matchin
import FancyTy(PseudoTermIT)
import Reduce
import PTSys
import ProvDat
import MainSta
import YarMsg
import GenComs
import Tactics
import Tactals
import TacSpec


------------------------------------------------
-- S E L E C T I O N   O F   C O M M A N D S  --
------------------------------------------------

doQueryP :: Query -> M Result
doQueryP (QTactic taskId tac) = doTac taskId tac
doQueryP (QProverExit taskId Exit) = exitCom taskId
doQueryP (QProverExit taskId Abort) = abortCom taskId
doQueryP (QCommand taskId (PUndo n)) = doUndo taskId n
doQueryP (QCommand taskId PRestart) = restart taskId
doQueryP (QCommand taskId (PFocus n)) = focus taskId n
doQueryP (QGiveHistory taskId) = fetchTacPaths taskId >>= \tacPaths ->
                                 fetchTacticTree taskId >>= \tacTree ->
                                 return (RHistoryIs (tacPaths, tacTree))
doQueryP (QGiveTask taskId) = map RTaskIs (makeToProve taskId)
doQueryP _ = errNotInProveMode

errNotInProveMode :: M Result
errNotInProveMode = genErrS "This command is not available in prove-mode"



----------------------------------------------
-- S E L E C T I O N   O F   T A C T I C S  --
----------------------------------------------

nameToTactic :: TacticTerm -> Tactic
nameToTactic (TRepeat t) =           repeatFinTac (nameToTactic t)
nameToTactic (TTry t) =              tryTac (nameToTactic t)
nameToTactic (t `TThen` ts)=         nameToTactic t `thenTac`
                                     map nameToTactic ts
nameToTactic (t `TElse` u) =         nameToTactic t `elseTac`
                                     nameToTactic u
nameToTactic (TIntroVar v) =         introVar v
nameToTactic TIntro =                intro
nameToTactic TIntros =               introsTac
nameToTactic (TIntrosNum n) =        introsNumTac n
nameToTactic TAssumption =           assumption
nameToTactic (TLet v t) =            letTac v t
nameToTactic (TLetW v t u) =         letTypTac v t u
nameToTactic (TUnfold (occs,v)) =    \p -> makeAllSelect occs >>= \sel ->
                                           unfold v sel p
nameToTactic (TUnfoldIn (occs,v,h))= \p -> makeAllSelect occs >>= \sel ->
                                           unfoldHyp v h sel p
nameToTactic TSimplify =             simplify
nameToTactic (TConvert t) =          checkInputS convertTac t
nameToTactic (TCut t) =              checkInputS cut t
nameToTactic (TFirst t) =            checkInputS firstTac t
nameToTactic (TForward et) =         checkInputETS 
                                         (forwardTac alwaysUnfold) et
nameToTactic (TExact t) =            checkInputTS exact t
nameToTactic (TLewrite (occ,et)) =   checkInputETS 
                                         (rewriteRToL (makeOneSelect occ)) et
nameToTactic (TRewrite (occ,et)) =   checkInputETS
                                         (rewriteLToR (makeOneSelect occ)) et
nameToTactic (TLewriteIn (occ,et,h))=checkInputETS 
                                       (rewriteRToLin (makeOneSelect occ) h) et
nameToTactic (TRewriteIn (occ,et,h))=checkInputETS
                                       (rewriteLToRin (makeOneSelect occ) h) et
nameToTactic TRefl =                 reflTac
nameToTactic TAndI =                 andITac
nameToTactic (TAndEL et) =           checkInputETS andELTac et
nameToTactic (TAndER et) =           checkInputETS andERTac et
nameToTactic (TAndE et) =            checkInputETS andETac et
nameToTactic TOrIL =                 orILTac
nameToTactic TOrIR =                 orIRTac
nameToTactic (TOrE et) =             checkInputETS orETac et
nameToTactic TNotI =                 notITac
nameToTactic (TNotE et) =            checkInputETS notETac et
nameToTactic TFalseE =               falseETac
nameToTactic (TExistsI t) =          checkInputTS existsITac t
nameToTactic (TExistsE et) =         checkInputETS existsETac et
nameToTactic (TApply et) =           checkInputETS 
                                         (applyTac alwaysUnfold) et
nameToTactic (TPattern (occs,t)) =   \p -> makeAllSelect occs >>= \sel ->
                                           checkInputTS (pattern sel) t p
nameToTactic (THide vs) =            hideTac vs
nameToTactic (TUnhide vs) =          unhideTac vs
nameToTactic TUnhideAll =            unhideAllTac


-- checkInputTS tac term0  type-checks term0 and applies tac to 
-- the triple (term,type of term0,sort of term0)
checkInputTS :: ((Term,Term,Sort) -> Tactic) -> TermIT -> Tactic
checkInputTS tac term0 tr@(_,_,_,totCon) =
    getTypeRet totCon term0 >>= \tts ->
    tac tts tr
              
-- checkInputETS tac (term0,terms0)  type-checks term0 and terms0 and 
-- applies tac to the triple (term,type of term0,sort of term0)
checkInputETS :: (ExtTermTS -> Tactic) -> ExtTermIT -> Tactic
checkInputETS tac (term0,terms0) tr@(_,_,_,totCon) =
    getTypeRet totCon term0 >>= \tts ->
    mapL (getTypeRet totCon) terms0 >>= \ttss ->
    tac (tts,ttss) tr
              
-- checkInputS tac term0  type-checks term0 and applies tac to 
-- the triple (term,type of term0)
checkInputS :: ((Term,Sort)->Tactic) -> TermIT -> Tactic
checkInputS tac term0 tr@(_,_,_,totCon) =
    getSortRet totCon term0 >>= \ts ->
    tac ts tr
              


-- doTac handles all tactics
doTac :: TaskId -> TacticTerm -> M Result
doTac taskId tacTerm =                              
   let tactic = nameToTactic tacTerm in
   fetchTacticTree taskId >>= \tacTree ->
   getPath1 taskId >>= \tacPath ->
   fetchTacPaths taskId >>= \tacPaths ->
   setTaskId taskId >>  -- store this task number so we don't have to
                        -- give it as parameter to all tactics
   fetchCon >>= \globCon ->
   let TTHole (hn,(goal,locCon,gi)) = findSubtree tacTree tacPath 
       totCon = locCon `addLocG` globCon in
   tactic (goal,locCon,gi,totCon) >>= \(term, newGoals) ->
   let tacTree' = replaceTPath tacTree tacPath 
                  (TTTac tacTerm (hn,(goal,locCon,gi),term) 
                         (map TTHole newGoals)) in
   setTacticTree taskId tacTree' >>
   let newTacPaths = map (\n -> tacPath ++ [n]) 
                         (take (length newGoals) [0..]) in
   setTacPaths taskId (newTacPaths ++ tail tacPaths) >>
   map (RTactic (hn,term)) (makeToProve taskId)


-- routine for making a selector
makeAllSelect :: [Occurrence] -> M (TermPath,Selector)
makeAllSelect [PathOccurrence path] = return (path, const True)
makeAllSelect occs = let unNum (NumOccurrence occ) = return occ
                         unNum _ = genErrS "Incorrect path" in
                     mapL unNum occs >>= \occs' ->
                     let sel n = null occs || n `elem` occs' in
                     return (emptyTermPath, sel)

{- tentative new code
makeAllSelect :: [Occurrence] -> [(TermPath,Selector)]
makeAllSelect [] = [(emptyTermPath, const True)]
makeAllSelect occs = map makeSelect occs

makeSelect (PathOccurrence path) = (path, const True)
makeSelect (NumOccurrence occ) = occs = let unNum (NumOccurrence occ) = occ
                         occs' = map unNum occs
                         sel n = null occs || n `elem` occs' in
                                    (emptyTermPath, sel)
-}

makeOneSelect :: Occurrence -> (TermPath,Int)
makeOneSelect (PathOccurrence path) = (path,1)
makeOneSelect (NumOccurrence num) = (emptyTermPath,num)


-------------------------------------------------------
-- S E T T I N G   U P   T H E   P R O O F   L O O P --
-------------------------------------------------------

initProver :: Item -> Task
initProver it@(_,t,_) = let nextHole = nextHnum initHnum in
                        (it,TTHole (initHnum,(t,emptyLCon,initGoalInfo)),
                         [[]], nextHole)

initGoalInfo :: GoalInfo
initGoalInfo = []

setUpProveMode :: Item -> M Result
setUpProveMode it@(v,_,_) = 
           fetchTasks >>= \(_,tasks) ->
           let taskId = v in
           setTasks (undefined,tasks ++ [initProver it]) >>
           makeToProve taskId >>= \toProve ->
           return (RProofTaskId taskId toProve)


----------------------------------------------------------------------
--  C O M M A N D S   S P E C I F I C   F O R   T H E   P R O V E R --
----------------------------------------------------------------------
  
-- Exiting prove mode

abortCom :: TaskId -> M Result
abortCom taskId =
             fetchTaskItem taskId >>= \(v,t,_) ->
             fetchTacticTree taskId >>= \history ->
             removeTask taskId >>
             fetchCon >>= \con ->
             return (RExit [] (v,t,history,Abort)) 

exitCom :: TaskId -> M Result
exitCom taskId = 
            fetchTaskItem taskId >>= \(v,t,_) ->
            makeToProve taskId >>= \(proofterm,goals) -> 
            if null goals then
               fetchTacticTree taskId >>= \history ->
               addLemma taskId proofterm >>
               fetchCon >>= \con ->
               return (RExit [headI con] (v,t,history,Exit))
            else
               genErrS "Proof is not finished"

removeTask :: TaskId -> M ()
removeTask taskId = 
     fetchTasks >>= \(_,tasks) ->
     let (task1,rest) = break (taskHasId taskId) tasks in
     setTasks (undefined, task1 ++ tail rest)
 

addLemma :: TaskId -> Term -> M ()
addLemma taskId proofterm = 
         fetchTaskItem taskId >>= \(v,t,s) ->
         removeTask taskId >>
         fetchCon >>= \globCon ->
         fetchSyn >>= \si ->
         let newCon = mkDef (v,proofterm,t,s) `addI` globCon 
             errText = "Prover gave UNCORRECT PROOF TERM!!!" in
         handle (contnOk si 1 newCon) 
         (\_ -> internalErr errText)
         (\_ -> setCon newCon)


-- Some commands for handling the history

doUndo :: TaskId -> Int -> M Result
doUndo taskId n = 
    fetchTacticTree taskId >>= \tacTree ->
    fetchTacPaths taskId >>= \tacPaths ->
    if null tacPaths then
       genErrS "No goal to undo a tactic in"
    else
    let tacPath = head tacPaths in
    if n<0 || n > length tacPath then
       genErrS "Cannot go back that far"
    else 
    (if n == 0 then 
        skip
     else      
        let tacPath' = take (length tacPath - n) tacPath
            TTTac _ (hnum,goal,_) _ = findSubtree tacTree tacPath'
            tacTree' = replaceTPath tacTree tacPath' (TTHole (hnum,goal)) 
            tacPaths' = filter (not . (flip beginsWith tacPath')) tacPaths in
        setTacticTree taskId tacTree' >>
        setTacPaths taskId (tacPath':tacPaths')
    ) >>
    makeToProve taskId >>= \toProve ->
    return (RTaskIs toProve)
       
restart :: TaskId -> M Result
restart taskId = fetchTaskItem taskId >>= \it ->
                 setTask taskId (initProver it) >>
                 map RTaskIs (makeToProve taskId)


focus :: TaskId -> Int -> M Result
focus taskId n = 
    fetchTacPaths taskId >>= \tacPaths ->
    if n > length tacPaths then
       genErrS ("Goal " ++ show n ++ " doesn't exist")
    else
       setTacPaths taskId ([tacPaths!!(n-1)] ++
                           take (n-1) tacPaths ++ drop n tacPaths) >>
       map RTaskIs (makeToProve taskId)
