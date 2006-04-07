-- File: MainSta
-- Description: This module contains the state we use in yarrow

module MainSta(OptList,ModuleName,Checksum, ModuleInfo, 
               StatusLoad(..), StatusSave,
               SpecialLemmas, emptyLemmas,
               MainS, Tasks, M, 
               PartContext(..), HasContext(..),
               fetchModulesInfo, setModulesInfo, 
               fetchTasks, updateTasks', setTasks,
               fetchLemmas, updateLemmas', removeLemmas, setLemma,
               extractTaskId, taskHasId, updateTask', fetchTask, setTask,
               fetchTaskItem, fetchTacticTree, setTacticTree,
               fetchTacPaths, setTacPaths, fetchTaskId, setTaskId,
               setHnumS, fetchHnumS,
               makeToProve, makeProofTerm, replace, domAllLocCon,
               findGoal, findSubtree,
               initState) where

import HaTuple
import Collect
import General
import HaMonSt
import SyntaxI
import Basic
import ProvDat



--------------------
-- Handling State --
--------------------                                        

-- the type of options for the 'option' command.
type OptList = (String,Bool)

type ModuleName = String

type Checksum = Int                      

type ModuleInfo = (ModuleName, (Vari, Vari), Checksum)
--                 name        first  last
--                  of         ident  ident
--                module        of     of
--                             module module
-- if the piece of context associated with a module is empty, we will
-- use dummyVar for both first and last ident of the module.

-- The following two types are used only in the module "Modules.hs" and
-- some queries concerning loading and saving of modules.

data StatusLoad = 
    StartLoading ModuleName System (String,Checksum) [(String,Checksum)] |
    StartChecking ModuleName 
                      ([(Vari,(Int,Assoc))],[Vari],[(Vari,Int)],[(Vari,Int)],
                          [((Vari,Int),(Vari,String,[Sort]))],[Vari],Checksum)
                      [ContextE] GContext

type StatusSave = [ModuleInfo]

                                           
-- The type SpecialLemmas is used for remembering the lemmas used in the 
-- special tactics. They are characterized by
--   1. the connective
--   2. the name of the special tactic 
--   3. a list of sorts.
-- As additional info the number of arguments for polymorphism is stored
-- (which is only used for refl, existsi, existse, rewrite, lewrite)
type SpecialLemmas = IL (Vari,String,[Sort]) (Vari,Int)          
-- Naming convention: lemmas

emptyLemmas :: SpecialLemmas
emptyLemmas = emptyI


data MainS= MAINS (SyntaxInfo,GContext,[ModuleInfo],Tasks,SpecialLemmas)
                                 
-- The integer in the tasks-type is only used for tactics, i.e.
-- indicate on what task a tactic is acting
type Tasks = (TaskId,[Task])

initTasks = (undefined,[])

type M a = State MainS a


--------------------
-- Handling State --
--------------------

-- for the 'global state' in the prover and main loops

class PartContext s where
     extractCon :: s -> GContext
     insertCon :: (GContext->GContext)->(s->s)

class (Functor m, Monad m) => HasContext m where
     fetchCon   :: m GContext
     updateCon  :: (GContext->GContext)-> m GContext
     setCon     :: GContext -> m ()
     fetchCon    = updateCon id
     setCon new  = fmap (const ()) (updateCon (\old -> new))


    
instance PartContext s => HasContext (State s) where
     updateCon f = fmap extractCon (updateS2 (insertCon f))
     -- hbc 0.9999.4 will complain if we replace updateS2 above by update,
     -- so we need a updateS2 function with a more restricted type.

updateS2 :: (s->s) -> State s s
updateS2 = update

    
               
instance PartSyntax MainS where
     extractSyn (MAINS ps) = fst5 ps
     insertSyn f (MAINS ps) = MAINS (doFst5 f ps)

instance PartContext MainS where
     extractCon (MAINS ps) = snd5 ps
     insertCon f (MAINS ps) = MAINS (doSnd5 f ps)

fetchModulesInfo :: M [ModuleInfo]
fetchModulesInfo = fmap (\(MAINS (_,_,mi,_,_)) -> mi) fetchS
     -- hbc 0.9999.4 will complain if we replace fetchS above by update,
     -- so we need a fetchS function with a more restricted type.

fetchS :: State s s
fetchS = fetch

setModulesInfo :: [ModuleInfo] -> M ()                                
setModulesInfo mi = update' (\(MAINS (si,con,_ ,mode, lemmas)) ->
                                MAINS (si,con,mi,mode, lemmas))


fetchTasks :: M Tasks
fetchTasks = fmap (\(MAINS (_,_,_,mode,_)) -> mode) fetchS

updateTasks' :: (Tasks -> Tasks) -> M ()
updateTasks' fmode = update' (\(MAINS (si,con,mi,mode,lemmas)) ->
                                     MAINS (si,con,mi,fmode mode,lemmas))


setTasks :: Tasks -> M ()
setTasks mode = updateTasks' (const mode)


fetchLemmas :: M SpecialLemmas
fetchLemmas = fmap (\(MAINS (_,_,_,_,lemmas)) -> lemmas) fetchS

updateLemmas' :: (SpecialLemmas -> SpecialLemmas) -> M ()
updateLemmas' fLemmas = update' (\(MAINS (si,con,mi,mode,lemmas)) ->
                                    MAINS (si,con,mi,mode,fLemmas lemmas))

removeLemmas :: Vari -> M ()
removeLemmas v = 
    let f = listToIndexedIL . filter ((/=v).fst.snd) . indexedToListIL in
    updateLemmas' f

setLemma :: (Vari,String,[Sort]) -> (Vari,Int) -> M ()
setLemma key v = fetchLemmas >>= \lemmas ->
                 let (found,lemmas') = removeI lemmas key
                     lemmas'' = if found then lemmas'
                                else addI (key,v) lemmas in
                 updateLemmas' (const lemmas'')

-----------------------------------------------------------------------
--  H A N D L I N G   S T A T E   I N   T H E   P R O O F - M O D E  --
-----------------------------------------------------------------------
              
extractTaskId :: Task -> TaskId
extractTaskId = fst3 . fst4

taskHasId :: TaskId -> Task -> Bool
taskHasId taskId= (==taskId) . extractTaskId

updateTask' :: TaskId -> (Task->Task) -> M ()                   
updateTask' taskId f = 
       let f' task = if extractTaskId task == taskId then
                           f task
                        else
                           task in
       updateTasks' (doSnd (fmap f'))

fetchTask :: TaskId -> M Task
fetchTask taskId = fmap (head.(filter (taskHasId taskId)).snd) 
                         fetchTasks
    
setTask :: TaskId -> Task -> M ()
setTask taskId task = let f t | taskHasId taskId t = task
                          f t | otherwise = t in
                      updateTasks' (doSnd (fmap f))
                                                     
fetchTaskItem :: TaskId -> M Item
fetchTaskItem taskId = fmap fst4 (fetchTask taskId)

fetchTacticTree :: TaskId -> M TacticTree
fetchTacticTree taskId = fmap snd4 (fetchTask taskId)

setTacticTree :: TaskId -> TacticTree -> M ()
setTacticTree taskId tacTree = updateTask' taskId (doSnd4 (const tacTree))

fetchTacPaths :: TaskId -> M [TacPath]
fetchTacPaths taskId = fmap thd4 (fetchTask taskId)

setTacPaths :: TaskId -> [TacPath] -> M ()
setTacPaths taskId tacPaths = updateTask' taskId (doThd4 (const tacPaths))

fetchTaskId :: M TaskId
fetchTaskId = fmap fst fetchTasks

setTaskId :: TaskId -> M ()
setTaskId taskId = fetchTasks >>= \(_,tasks) ->
                     --if taskId >= length tasks then
                     --   internalErr "Selection of task"
                     --else 
                     updateTasks' (doFst (const taskId))

-- The following two commands are the only ones that use the
-- taskNr field in the type Tasks
setHnumS :: Hnum -> M ()
setHnumS gn = fetchTaskId >>= \taskId ->
              updateTask' taskId (doFth4 (const gn))

fetchHnumS :: M Hnum
fetchHnumS = fetchTaskId >>= \taskId ->
             fmap fth4 (fetchTask taskId)

makeToProve :: TaskId -> M ToProve
makeToProve taskId = 
    fetchTacticTree taskId >>= \tacTree ->
    fetchTacPaths taskId >>= \tacPaths ->
    return (snd (makeProofTerm tacTree),
            fmap (findGoal tacTree) tacPaths)

makeProofTerm :: TacticTree -> (Hnum, Term)
makeProofTerm (TTHole (hnum,_)) = (hnum, mkHole hnum)
makeProofTerm (TTTac _ (hnum,_,term) tacTrees) =
       (hnum,foldl replace term (fmap makeProofTerm tacTrees))


-- replace n t u  replaces in term t all occurrences of Hole n by u 
replace :: Term -> (Hnum, Term) -> Term  
replace (Basic (Hole m)) (n,u) | n==m = u
-- rest: distribute
replace (Basic cat) s = mkBasic cat
replace (Nonb cat ts) s = mkNonb cat (fmap (\a -> replace a s) ts)
replace (Bind cat ts (v,t,s) b) sig = mkBind cat
                                                (fmap (\a-> replace a sig) ts)
                                                (v, replace t sig, s)
                                                (replace b sig)


-- Delivers all variables occuring in local contexts
domAllLocCon :: M [Vari]
domAllLocCon = 
    fetchCon >>= \globCon ->                   
    fetchTasks >>= \(_,tasks) ->
    let varsTask :: TaskId -> M [Vari]
        varsTask taskId =
         fetchTaskItem taskId >>= \(nameProof,_,_) ->
         makeToProve taskId >>= \(_,goals) ->
         return (nameProof : concat (fmap domLCon (fmap (snd3.snd) goals))) in
    mapL varsTask (fmap extractTaskId tasks) >>= \varLists ->
    return (removeDoubles (concat varLists))

-- findGoal tree path finds the goal corresponding to path in tree
findGoal :: TacticTree -> TacPath -> (Hnum,Goal)
findGoal tacTree tacPath = 
    let TTHole p = (findSubtree tacTree tacPath) in
    p

findSubtree :: TacticTree -> TacPath -> TacticTree
findSubtree t [] = t
findSubtree (TTTac _ _ ts) (n:ns) = findSubtree (ts!!n) ns

-------------------------------
-- I N I T I A L   S T A T E --
-------------------------------
                         
-- initial state

-- initial context
initCon = emptyGCon

-- Initial syntax
initSyntax :: System -> SyntaxInfo
initSyntax sys = (sys,(False,True,False,False),emptyI,[],emptyI,emptyI) 
                                            

initState sys = MAINS (initSyntax sys,initCon,[],initTasks,emptyLemmas)

             
