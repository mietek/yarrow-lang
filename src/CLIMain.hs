-- File: Main
-- Description: This module implements a command-line interface for Yarrow
--              A window interface is on the way :-)

-- This interface communicates with the kernel of Yarrow by asking Queries and
-- getting Results as answer (see module YarMsg.hs). However, the interface
-- also reads parts of the state directly, instead of by asking.

module Main(main) where

import GenComs(getType) -- Just for FrankContext
import Char(toUpper)
import General
import Display
import HaTuple
import Collect(findAll3,AssocList(..),findAL,notElemC)
import HaMonSt
import HaMonIO

import Platfor

import Engine
import Service
-- temporary solution
import Deduct
import LatexPr

----------------------------
-- STATE IN THE INTERFACE --
----------------------------

-- FileInput holds the lines of the input file(s) that yet have to be
-- processed.
type FileInput = [String]

-- Inital file input is empty
initFileInput :: FileInput
initFileInput = []

-- EnvVars holds the value of the used environmental variables
-- Currently, only the variable YARROW
type EnvVars = String

-- Inital environmental vars; will be reset when program really starts
initEnvVars :: EnvVars
initEnvVars = ""

-- Paths contains paths containing names of directories to be searched
-- when loading modules or reading script-files.
type Paths = [String]

initPaths :: Paths
initPaths = [currentDir]

initTaskId :: TaskId
initTaskId = noTask

data CLIS = CLIS (MainS, FileInput, EnvVars, Paths, TaskId)
type CLI a = Imp CLIS a

initCLIState :: CLIS
initCLIState = CLIS (initState systemC, initFileInput, initEnvVars, initPaths,
                     initTaskId)

-- unClis removes type constructor
unClis (CLIS t) = t

-- Make syntactic info and global context also accessible to the interface.
instance PartSyntax CLIS where
         extractSyn (CLIS clis) = extractSyn (fst5 clis)
         insertSyn f (CLIS clis) = CLIS (doFst5 (const (insertSyn f (fst5 clis))) clis)

instance PartContext CLIS where
         extractCon (CLIS clis) = extractCon (fst5 clis)
         insertCon f (CLIS clis) = CLIS (doFst5 (const (insertCon f (fst5 clis))) clis)

instance PartSyntax s => HasSyntax (Imp s) where
     updateSyn f = fmap extractSyn (updateS3 (insertSyn f))
     -- hbc 0.9999.4 will complain if we replace updateS3 above by update,
     -- so we need a updateS3 function with a more restricted type.

updateS3 :: (s->s) -> Imp s s
updateS3 = update

instance PartContext s => HasContext (Imp s) where
     updateCon f = fmap extractCon (updateS3 (insertCon f))

-- Input files
fetchInputFile :: CLI FileInput
fetchInputFile = fmap (snd5.unClis) fetchS5

fetchS5 :: Imp s s
fetchS5 = fetch

updateInputFile :: (FileInput -> FileInput) -> CLI ()
updateInputFile f = update' (CLIS . doSnd5 f . unClis)

-- Environment variables
fetchEnvVars :: CLI EnvVars
fetchEnvVars = fmap (thd5.unClis) fetchS5

fetchYarrowDir :: CLI String
fetchYarrowDir = fetchEnvVars

setEnvVars :: EnvVars -> CLI ()
setEnvVars envVars = update' (CLIS . doThd5 (const envVars) . unClis)

-- path stuff
fetchPaths :: CLI Paths
fetchPaths = fmap (fth5.unClis) fetchS5

setNewPath :: String -> CLI ()
setNewPath path = update' (CLIS . doFth5 (path :) . unClis)

-- current task
fetchCurTaskId :: CLI TaskId
fetchCurTaskId = fmap (ffh5.unClis) fetchS5

setCurTaskId :: TaskId -> CLI ()
setCurTaskId taskId = update' (CLIS. doFfh5 (const taskId) . unClis)


-- Interface to the Yarrow engine
mToCLI :: M a -> CLI a
mToCLI mProg = fetchS5 >>= \state ->
               let mainS = fst5 (unClis state) in
               performS mainS mProg >>= \(res,mainS') ->
               updateS4' (CLIS . doFst5 (const mainS') . unClis) >>
               return res
     -- hbc 0.9999.4 will complain if we replace updateS4' above by update',
     -- so we need a updateS4' function with a more restricted type.

updateS4' :: (s->s) -> Imp s ()
updateS4' = update'

---------------
-- MAIN LOOP --
---------------

finalHandleError err = updateInputFile (const []) >>  -- flush file input
                       fetchSyn >>= \si ->
                       putLines (errorToStrings si err)


loop :: CLI ()
loop = mToCLI fetchTasks >>= \(_,tasks) ->
       (if null tasks then
           putSt "> "
        else
           putSt "$ ") >>
       handleS readCommand
       -- error
       (\err -> finalHandleError err >> loop)
       -- OK
       (\comm ->
        -- putLine (commandToString comm) >>
        case comm of
        CQuit -> doQuit
        otherwise -> -- doCommand can give an error
                     handleS (doCommand comm) finalHandleError (\_ -> skip) >>
                     loop
       )

doQuit :: CLI ()
doQuit = putLine "Bye bye"
      {- mToCLI fetchTasks >>= \(_,tasks) ->
         if null tasks then
            putLine "Bye bye"
         else
            putLine ("Not allowed to quit in prove-mode" ++ genErrSuffix) >>
            loop -}

doCommand :: Command -> CLI ()
doCommand CSkip = skip
doCommand (CShow taskId goalNr) = cShow taskId goalNr
doCommand (CHistory taskId) = cHistory taskId
doCommand CGiveOptions = cGiveOptions
doCommand CGiveTypingSystem = cGiveTypingSystem
doCommand (CRead f) = cRead f
doCommand CHelp = cHelp
doCommand (CHelpOn s) = cHelpOn s
doCommand (CPrintVar taskId v) = cPrintVar taskId v
doCommand (CDeduction latex taskId v n toF) = cDeduction latex taskId v n toF
doCommand (CLoadModule modName) = cLoadModule modName
doCommand (CSaveModule modName) = cSaveModule modName
doCommand (CAddPath path) = addPath path
doCommand CShowPath = putPaths
doCommand (CSetTask v) = cSetTask v
doCommand CGiveTasks = cGiveTasks
doCommand (CGiveContext latex r sl toFile) = cGiveContext latex r sl toFile
doCommand CSize = cSize
-- next one only for testing!
doCommand (CZwerver z) = cZwerver z
doCommand comm = commandToQuery comm >>= \query ->
                 -- putLine (queryToString query) >>
                 fetchSyn >>= \si ->
                 doQueryC query >>=
                 handleResult si

doQueryC :: Query -> CLI Result
doQueryC = mToCLI . doQuery

-- commands that ask a Query to Yarrow
commandToQuery :: Command -> CLI Query
commandToQuery (CSetOptions optList) = cSetOptions optList
commandToQuery query = return (commandToQuery' query)

commandToQuery' :: Command -> Query
commandToQuery' (CDeclareVars its) = QDeclareVars its
-- Extension: Subtyping:
commandToQuery' (CDeclareVarsSub its) = QDeclareVarsSub its
commandToQuery' (CDeclareVarsSubW its) = QDeclareVarsSubW its
-- End Extension: Subtyping
commandToQuery' (CDefVar it) = QDefVar it
commandToQuery' (CDefVarW it) = QDefVarW it
commandToQuery' (CDelFromVar v) = QDelFromVar v
commandToQuery' (CTactic taskId tac) = QTactic taskId tac
commandToQuery' (CProverExit taskId exitMode) = QProverExit taskId exitMode
commandToQuery' (CProverCommand taskId provCom) = QCommand taskId provCom
commandToQuery' (CProveVar it) = QProveVar it
commandToQuery' (CGiveBDReductionPath taskId t) = QGiveBDReductionPath taskId t
commandToQuery' (CGiveBReductionPath taskId t)  = QGiveBReductionPath taskId t
commandToQuery' (CGiveDReductionPath taskId t)  = QGiveDReductionPath taskId t
commandToQuery' (CGiveType taskId t) = QGiveType taskId t
commandToQuery' (CCheckBDConv taskId ctt) = QCheckBDConv taskId ctt
commandToQuery' (CCheckTyping taskId ctt) = QCheckTyping taskId ctt
-- Extension: Subtyping:
commandToQuery' (CCheckSubtype taskId ctt) = QCheckSubtype taskId ctt
-- End Extension: Subtyping
commandToQuery' (CZMatch taskId cvtt) = QZMatch taskId cvtt
commandToQuery' (CSetPrecAndAss via) = QSetPrecAndAss via
commandToQuery' (CSetBinder vn) = QSetBinder vn
commandToQuery' (CSetLaTeX v) = QSetLaTeX v
commandToQuery' (CSetImplArgs vi) = QSetImplArgs vi
commandToQuery' CGiveUseFor = QGiveUseFor
commandToQuery' (CSetTypingSystem sys) = QSetTypingSystem sys
commandToQuery' (CUseFor tacName v) = QUseFor tacName v
commandToQuery' CClearModule = QClearModule
commandToQuery' CGiveModules = QGiveModules
commandToQuery' _ = error "Unknown command to query"

yesNoQuestion :: CLI Bool
yesNoQuestion = getLin >>= \answer ->
                let yn = fmap toUpper answer in
                return (take 1 yn == "Y")



main = goSte (initYarrow >> loop) initCLIState

initYarrow :: CLI ()
initYarrow =
  -- When changing version, also adapt helpdir/about !
  putSt "Welcome to Yarrow v1.20\n" >>
  handleS getYarrowDir
  (\[ES errmess] -> putLine ("No specific help available, since "
                               ++errmess))
  (\yarrowDir -> setEnvVars yarrowDir >>
                 putSt "Type 'Help introduction' for an introduction.\n")

readCommand :: CLI Command
readCommand = fetchCurTaskId >>= \taskId ->
              doFullParse getLineI (stop (parseCommand taskId))

getLineI :: CLI String
getLineI = fetchInputFile >>= \ils ->
           case ils of
           [] -> getLin
           (l:ls) -> updateInputFile tail >>
                     putSt (l++"\n") >>
                     return l


-- doFullParse scans and parses a string, given a parser
-- the input string is also returned
-- doFullParse :: Parse a -> CLI a
doFullParse getLine pars =
  scanLines [] 1 >>= \ts ->
  fetchSyn >>= \si ->
  fmap fst (performS (PARSES (si,ts)) pars)

-- scanLines ln  scans lines, starting with line number ln
scanLines :: Tokens -> Int -> CLI Tokens
scanLines oldToks ln=
      getLineI >>= \s->
      scanLine s ln >>= \toks ->
      let allToks = oldToks ++ toks in
      if length toks == 1 || isInputComplete allToks then
         return allToks
      else
         -- read another line
         putSt ". " >>
         -- init is necessary to cut off the Eoln token
         scanLines (init allToks) (ln+1)

{- For testing purposes
queryToString (QGiveBReductionPath _ _) = "Q: Give normal form"
queryToString (QTactic _ _) = "Q: Some tactic"
queryToString _ = "Q: Other query"

commandToString (CTactic _ _) = "C: Some tactic"
commandToString _ = "C: Other command"
-}

--------------------------
-- INFORMATION COMMANDS --
--------------------------

-- These functions print some requested information on the screen

cShow  :: TaskId -> GoalNr -> CLI ()
cShow taskId n =
          if taskId == noTask then
             errNotInMainMode
          else
          fetchSyn >>= \si ->
          mToCLI (makeToProve taskId) >>= \toProve@(prftrm,goals) ->
          if n<1 || (n > 1 && n > length goals)  -- when 0 goals, n=1 is OK
          then
             genErrS "Goal doesn't exist"       -- checks whether or not n OK
          else
          putLines (printGoalsSt si n toProve) >>
          putLn

cHistory taskId = if taskId == noTask then
                    errNotInMainMode
                 else
                 mToCLI (fetchTacPaths taskId) >>= \tacPaths ->
                 mToCLI (fetchTacticTree taskId) >>= \tacTree ->
                 fetchSyn >>= \si ->
                 putLines (showNumHistory si (tacPaths,tacTree))


cGiveTasks :: CLI ()
cGiveTasks =
           mToCLI fetchTasks >>= \(_,tasks) ->
           if null tasks then
              putLine "No tasks active"
           else
           fetchCurTaskId >>= \curTaskId ->
           let print taskId = if taskId == curTaskId then
                                taskId ++ " (current task)"
                             else
                                taskId in
           putLines (fmap (print.fst3.fst4) tasks)

cGiveOptions :: CLI ()
cGiveOptions = fetchSyn >>= \si ->
               let opts = extractBoolOptions si
                   sign False = "-"
                   sign True  = "+"
                   printOpt (s,(read,_)) = sign (read opts) ++ s in
               putLine ("Current options are: " ++
                        commas (fmap printOpt listOptions))

cGiveContext :: OutputMode -> ConPart -> [Sort] -> ConToFile -> CLI ()
cGiveContext OutFrank part sl toFile =
    makeFrankPart part >>= \lines ->
    putStream toFile lines
-- entire module then never write to screen, but use module name instead
cGiveContext OutJava part@(ConModule m) sl ConToScreen =
    makeJavaPart part sl >>= \lines ->
    putStream (ConToFile (m++".yct")) lines
cGiveContext OutJava part sl toFile =
    makeJavaPart part sl >>= \lines ->
    putStream toFile lines
cGiveContext outputMode part sl toFile =
    let latex = case outputMode of
                OutLatex -> True
                otherwise -> False in
    makePart latex part sl >>= \lines ->
    putStream toFile lines

putStream :: ConToFile -> [String] -> CLI ()
putStream toFile lines =
    case toFile of
    ConToScreen -> putLines lines
    (ConToFile f) -> writeFil f (concat (fmap (++"\n") lines))

cSize :: CLI ()
cSize = fetchCon >>= \c ->
        let l = globConToList c
            sizeCE (_,((t,_),_,ts)) = sum (fmap size' (t:ts))
            size' t = let s = size t in
                      if s>=0 then s else s
            size (Basic _) = 1
            size (Nonb _ ts) = sum (fmap size' ts)
            size (Bind _ ts (_,t,_) b) = sum (fmap size' (t:b:ts)) in
        putLine ("Number of items: " ++ show (length l)) >>
        putLine ("Total size (number of variables and sorts in all terms): " ++
                 show (sum (fmap sizeCE l)))


-- cPrintVar  prints the declaration/definition of var
cPrintVar :: TaskId -> Vari -> CLI ()
cPrintVar taskId v =
             mToCLI (fetchTotalCon taskId) >>= \con ->
             fetchSyn >>= \si ->
             let (found,cer) = findDeclDef con v in
             if not found then
                 genErrS ("No declaration or definition of "++v++
                          " in the context")
             else
             putLine (printContextE displayString si (const True) (v,cer))

-- cDeduction  prints the definition of var as a proof with flags
cDeduction :: OutputMode -> TaskId -> Vari -> Int -> ConToFile -> CLI ()
cDeduction latex taskId v n toFile =
             mToCLI (fetchTotalCon taskId) >>= \con ->
             fetchSyn >>= \si ->
             let (found,tts) = findDefTypeSort con v in
             if not found then
                 genErrS ("No definition of "++v++
                          " in the context")
             else
             mToCLI fetchLemmas >>= \sl ->
             handle (printDeduct si sl con v tts n latex)
             (\e -> err e)
             (\lines -> putStream toFile lines)

cGiveTypingSystem :: CLI ()
cGiveTypingSystem = fetchSyn >>= \si ->
                    fetchSys >>= \sys ->
                    let (l1,l2,l3,l4,l5) = printSystemSt si sys in
                    putLines (["Current type system is:",
                               "  Sorts:  " ++ l1,
                               "  Axioms: " ++ l2,
                               "  Rules:  " ++ l3] ++
                              if not (null l4) then
                              ["  Subtyping sorts:  " ++ l4,
                               "  Subtyping rules:  " ++ l5]
                              else [])

-- handling the path
putPaths :: CLI ()
putPaths = fetchPaths >>= \path ->
           putLines ("Current paths:" :
                     fmap (\n -> "\""++n++"\"") path)

addPath :: String -> CLI ()
addPath path = fetchPaths >>= \paths ->
               let stPath = standardPathName path in
               if stPath `elem` paths then
                  skip
               else
                  setNewPath stPath

cSetTask :: Vari -> CLI ()
cSetTask v =
           mToCLI fetchTasks >>= \(_,tasks) ->
           let nameTasks = fmap (fst3.fst4) tasks in
           if v `notElemC` nameTasks then
              genErrS ("There is no task "++v)
           else
           setCurTaskId v >>
           mToCLI (makeToProve v) >>= \toProve ->
           mToCLI fetchSyn >>= \si ->
           putLines (printGoalsSt si 1 toProve) >>
           putLn

----------
-- Help --
----------

-- Help is offered in two forms.
-- 1. If help for a specific command is asked, genHelpOn is invoked.
--    It reads the help-text for that command from file.
--
-- 2. If 'help' without parameters is entered, genHelpOn is invoked
--    with topic "main-mode" or "prove-mode", depending on the current mode.


-- genHelp  gives a list of often used commands, depending on the current
--          mode.
cHelp :: CLI ()
cHelp = mToCLI fetchTasks >>= \(_,tasks) ->
        cHelpOn (if null tasks then "main-mode" else "prove-mode")

cHelpOn :: String -> CLI ()
cHelpOn key =
    fetchYarrowDir >>= \yarrowDir ->
    handleS (readFil (fileHelp yarrowDir (toLowers key)))
    (\e -> putLine ("No help on "++key))
    (\contents -> putSt (format displayString lineLength
                                (parseFancy contents)))

lineLength :: Int
lineLength = 70

--------------------
-- OTHER COMMANDS --
--------------------

cSetOptions :: OptList -> CLI Query
cSetOptions (s,b) = findOption s >>= \d ->
                    fetchSyn >>= \si ->
                    return (setOptGen si d b)


findOption :: String -> CLI CodeOption
findOption s = let (found,res) = findAL listOptions s in
               if not found then
                  genErrS "Unknown option"
               else
                  return res

setOptGen :: SyntaxInfo -> CodeOption -> Bool -> Query
setOptGen si codeOpt b = QSetOptions (snd codeOpt b (extractBoolOptions si))



cRead :: String -> CLI ()
cRead f = readFilFromPath (addExtension f "ys") >>= \cont ->
          insertInput (lines cont)

insertInput :: [String] -> CLI ()
insertInput ils = updateInputFile (ils++)

readFilFromPath :: String -> CLI String
readFilFromPath f = fetchSyn >>= \si ->
                    fetchPaths >>= \paths ->
                    let read :: Paths -> CLI String
                        read [] = genErrS ("Can't find \""++f++"\" on path")
                        read (path:paths) = handleS (readFil (path++dirSep++f))
                                            -- on error, try next path
                                            (\e -> read paths)
                                            -- OK! Then return result
                                            return in
                    read paths

cSaveModule :: ModuleName -> CLI ()
cSaveModule modName =
  let modName' = removeExt modName yarrowCodeExt in
  doQueryC (QSaveModule modName') >>= \res ->
  case res of
  RTrySaveThis contents status ->
                   writeFil (makeModuleName modName') contents >>
                   doQueryC (QSaveCompleted status) >>= \res ->
                   fetchSyn >>= \si ->
                   handleResult si res
  RError s -> genErr s

cLoadModule :: ModuleName -> CLI ()
cLoadModule modName =
  let modName' = removeExt modName yarrowCodeExt in
  handleS (cLoadModuleRec modName')
  (\e -> putModules >> err e)
  (\_ -> putModules)

cLoadModuleRec :: ModuleName -> CLI ()
cLoadModuleRec modName =
  readFilFromPath (makeModuleName modName) >>= \contents ->
  cLoadModuleRec2 (QLoadModuleInput modName contents)

cLoadModuleRec2 :: Query -> CLI ()
cLoadModuleRec2 query =
  doQueryC query >>= \res ->
  case res of
  RDone -> skip
  RLoadMessage mess status -> putLine ("["++mess++"]") >>
                              cLoadModuleRec2 (QContinueLoad status)
  RModulesAre _ -> skip
  RLoadList modNameList -> maplComs cLoadModuleRec modNameList
  RError s -> err s

makeModuleName :: ModuleName -> String
makeModuleName modName = modName ++ extensSep ++ yarrowCodeExt

yarrowCodeExt :: String
yarrowCodeExt = "yc"

addExtension :: String -> String -> String
addExtension f ext = removeExt f ext ++ extensSep ++ ext

removeExt :: String -> String -> String
removeExt f ext = let sepExt = extensSep ++ ext in
                  if f `endsWith` sepExt then
                     take (length f - length sepExt) f
                  else
                     f



----------------------
-- HANDLING RESULTS --
----------------------

handleResult :: SyntaxInfo -> Result -> CLI ()
handleResult si RDone = skip
handleResult si (RError s) = finalHandleError s
handleResult si (RGlobConIs con) = makePart False ConAll [] >>=
                                   putLines
                                   -- we read the context directly from state
handleResult si (RGlobConExt con) = putContext si con
handleResult si (RModuleContentsIs con) = putContext si con
handleResult si (RTactic subst toProve) =
                                    putMaybeSubst subst >>
                                    putLines (printGoalsSt si 1 toProve) >>
                                    putLn
handleResult si (RTaskIs toProve)= putLines (printGoalsSt si 1 toProve) >>
                                      putLn
handleResult si (RProofTaskId taskId toProve) =
                                    setCurTaskId taskId >>
                                    putLines (printGoalsSt si 1 toProve) >>
                                    putLn
handleResult si (RExit con his) = rExit con his
handleResult si (RReductionPathIs (ts,_)) = putReductionPath si ts
handleResult si (RTypeIs (t,_)) = putTermTypeSort si t
handleResult si (RCheckIs (b,_)) = putBool b
handleResult si (RZMatchIs substs) = putLine (showSubsts si substs)
handleResult si (RTypingSystemOk properties) = putLine properties
handleResult si (RModulesAre modInfos) = putModules
                                 -- we read the modules directly from state
handleResult si (RSyntaxInfoIs _) = skip
handleResult si (RUseForIs lemmas) = rUseForIs lemmas
handleResult _ _ = putSt "Can't handle this Result\n"

rExit con (v,t,his,exitMode) =
                   fetchSyn >>= \si ->
                   putLine ("Prove " ++ printVarSt si v ++ " : " ++
                            printTermSt si t) >>
                   putLines (showHistory si (showExitMode exitMode) his) >>
                   mToCLI fetchTasks >>= \(_,tasks) ->
                   let nameTasks = fmap extractTaskId tasks
                       newTaskId = last (noTask : nameTasks) in
                   setCurTaskId newTaskId >>
                   case exitMode of
                   Exit -> putLn >>
                           putContext si con
                   Abort -> putLine "\nProof discarded"

putModules :: CLI ()
putModules = mToCLI showModules >>= putLines

makePart :: Bool -> ConPart -> [Sort] -> CLI [String]
makePart latex ConAll sl =
             fetchCon >>= \c ->
             fetchSyn >>= \si ->
             mToCLI showListModules >>= \modsText ->
             mToCLI fetchModulesInfo >>= \mi ->
             let lv = lastVarModuleDefined mi
                 partC = takeWhile (\it-> lv /= domConE it)
                                   (globConToList c) in
             putCon si latex sl partC >>= \conText ->
             return (modsText ++ conText)
makePart latex (ConModule m) sl =
             fetchSyn >>= \si ->
             doQueryC (QGiveModuleContents m) >>= \r ->
             case r of
             RModuleContentsIs con -> putCon si latex sl con
             RError mess -> err mess
makePart latex (ConRange (v1,v2)) sl =
             fetchCon >>= \c ->
             fetchSyn >>= \si ->
             let partC = takeUntil (\it-> v1 == domConE it)
                         (dropWhile (\it -> v2 /= domConE it)
                                    (globConToList c)) in
             if null partC ||
                domConE (head partC) /= v2 || domConE (last partC) /= v1 then
                genErrS "Invalid range"
             else
             putCon si latex sl partC >>= \conText ->
             return conText

makeJavaPart (ConRange (v1,v2)) sl =
             fetchCon >>= \c ->
             fetchSyn >>= \si ->
             let partC = takeUntil (\it-> v1 == domConE it)
                         (dropWhile (\it -> v2 /= domConE it)
                                    (globConToList c)) in
             if null partC ||
                domConE (head partC) /= v2 || domConE (last partC) /= v1 then
                genErrS "Invalid range"
             else
             putJavaContext "" si (globToTot c) (`elem` sl) (reverse partC)

makeJavaPart (ConModule m) sl =
             fetchCon >>= \c ->
             fetchSyn >>= \si ->
             doQueryC (QGiveModuleContents m) >>= \r ->
             case r of
             RError mess -> err mess
             RModuleContentsIs con ->
                 putJavaContext (m++dirSep) si (globToTot c) (`elem` sl) (reverse con)

makeJavaPart ConAll sl =
             fetchCon >>= \c ->
             fetchSyn >>= \si ->
             mToCLI fetchModulesInfo >>= \mi ->
             let doModule m =
                   makeJavaPart (ConModule m) sl >>= \lines ->
                   putStream (ConToFile (m++".yct")) lines >>
                   return (", M \"" ++ m ++ "\" \"" ++ m ++ ".yct\"") in
             mapL doModule (reverse (fmap fst3 mi)) >>= \sms ->
             let lv = lastVarModuleDefined mi
                 partC = takeWhile (\it-> lv /= domConE it)
                                   (globConToList c) in
             mapL (putJavaContextE "" si (globToTot c) (`elem` sl))
                  (reverse partC) >>= \its ->
             return (["("] ++ sms ++ its ++ [")"])

putJavaContextE :: String -> SyntaxInfo -> Context -> (Sort -> Bool) ->
                   ContextE -> CLI String
putJavaContextE dir si con _ ce | isGenDecl ce =
            let (_,(v,t,s),constrs,cts) = deconstructGenDecl ce in
            return (
            ",O \"" ++ latexPrintVar si con v ++ "\"" ++
            (case constrs of
             CNone -> " 1"
             -- Extension: Subtyping:
             CSub ->  " 2 \"\\sub\" " ++
                       latexPrintTerm si con (head cts)
             -- End Extension: Subtyping
            ) ++
            " \":\" \"" ++ latexPrintTermS si con v (t,s) ++ "\"")
putJavaContextE dir si con pDef ce | isDef ce =
    let (_,(v,d,t,s)) = deconstructDef ce in
    if pDef s then
       return (
       ",O \"" ++
       latexPrintVar si con v ++ "\" 2 \"\\isd\" \"" ++
       latexPrintTerm' si con d ++ "\" \"\\has\" \"" ++
       latexPrintTermS si con v (t,s) ++ "\"")
    else
       let filename = dir ++ v ++ ".yct" in
       cDeduction OutJava noTask v 0 (ConToFile filename) >>
       return (
       ",L \"" ++
       latexPrintVar si con v ++ "\" \"" ++ filename ++ "\" \"" ++
       latexPrintTermS si con v (t,s) ++ "\"")

--cDeduction :: OutputMode -> TaskId -> Vari -> Int -> ConToFile -> CLI ()


putJavaContext :: String -> SyntaxInfo -> Context -> (Sort -> Bool) ->
                     [ContextE] -> CLI [String]
putJavaContext dir si con pDef c = mapL (putJavaContextE dir si con pDef)
                                       c >>= \ss ->
                                  return (["("] ++ ss ++ [")"])
{-
system (*p,#p),(*p:#p),((*p,*p))
 var A:*p
def B := A
Prove bla : B->A
Intro
Assumption
Exit

javacontext A .. bla : #p On "test.yct"
-}

makeFrankPart (ConRange (v1,v2)) =
             fetchCon >>= \c ->
             fetchSyn >>= \si ->
             let partC = takeUntil (\it-> v1 == domConE it)
                         (dropWhile (\it -> v2 /= domConE it)
                                    (globConToList c)) in
             if null partC ||
                domConE (head partC) /= v2 || domConE (last partC) /= v1 then
                genErrS "Invalid range"
             else
             putFrankCon si (globToTot c) (reverse partC) >>= \conText ->
             return conText

makeFrankPart _ = genErrS "Wrong syntax, Frank!"
{-
main
var N:*
var O:N
var S:N->N
def uno := S O
def (=) :=\A:*.\x,y:A. @P:A->*. P x -> P y

frankcontext N..(=)
(decl N,(sort *),#)
(decl O,(var N),*)
(decl S,(arrow (var N) (var N)),*)
(def uno,(type (app (type (var S) (arrow (var N) (var N)) *) (type (var O) (var N) *)) (var N) *),(var N),*)
(def =,(type (lambda A,(sort *),#,(type (lambda x,(var A),*,(type (lambda y,(var A),*,(type (pi P,(arrow (var A) (sort *)),#,(type (arrow (type (app (type (var P) (arrow (var A) (sort *)) #) (type (var x) (var A) *)) (sort *) #) (type (app (type (var P) (arrow (var A) (sort *)) #) (type (var y) (var A) *)) (sort *) #)) (sort *) #)) (sort *) #)) (arrow (var A) (sort *)) #)) (arrow (var A) (arrow (var A) (sort *))) #)) (pi A,(sort *),#,(arrow (var A) (arrow (var A) (sort *)))) #),(pi A,(sort *),#,(arrow (var A) (arrow (var A) (sort *)))),#)
-}


putFrankCon :: SyntaxInfo -> Context -> [ContextE] -> CLI [String]
putFrankCon si c ces = mapL (putFrankCE si c) ces

putFrankCE si c ce | isDef ce =
     let (_,(v,d,t,s)) = deconstructDef ce in
     putFrankTerm si (True,True) c d >>= \sd ->
     putFrankTerm si (False,False) c t >>= \st ->
     return ("(def "++v++","++ sd ++"," ++ st ++ "," ++ sortToIdent s ++ ")")
putFrankCE si c ce | isDecl ce =
        let (_,(v,t,s)) = deconstructDecl ce in
        putFrankTerm si (False,False) c t >>= \st ->
        return ("(decl "++v++","++st ++ "," ++ sortToIdent s ++ ")")

--putFrankTerm si (printEverType,printNowType) c t
putFrankTerm si (_,True) c t =
      putFrankTerm si (True,False) c t >>= \st ->
      getType c t >>= \(typ,s) ->
      putFrankTerm si (False,False) c typ >>= \styp ->
      return ("(type " ++ st ++ " " ++ styp ++ " " ++ sortToIdent s ++ ")")
putFrankTerm si (pET,False) c t | isVar t =
      let (_,v) = deconstructVar t in
      return ("(var "++v++")")
putFrankTerm si (pET,False) c t | isSort t =
      let (_,s) = deconstructSort t in
      return ("(sort "++sortToIdent s++")")
putFrankTerm si (pET,False) c t | isApp t =
      let (_,t1,t2) = deconstructApp t in
      putFrankTerm si (pET,pET) c t1 >>= \st1->
      putFrankTerm si (pET,pET) c t2 >>= \st2->
      return ("(app "++ st1 ++ " " ++ st2 ++ ")")
putFrankTerm si (pET,False) c t | isArrow t =
      let (_,t1,t2) = deconstructArrow t in
      putFrankTerm si (pET,pET) c t1 >>= \st1->
      putFrankTerm si (pET,pET) c t2 >>= \st2->
      return ("(arrow "++ st1 ++ " " ++ st2 ++ ")")
putFrankTerm si (pET,False) c t | isAbs t =
      let (_,(v,t1,s),t2) = deconstructAbs t
          c' = addC (mkDecl (v,t1,s)) c in
      putFrankTerm si (False,False) c t1 >>= \st1 ->
      putFrankTerm si (pET,pET) c' t2 >>= \st2 ->
      return ("(lambda "++ v ++ "," ++ st1 ++ "," ++ sortToIdent s ++
              "," ++ st2 ++ ")")
putFrankTerm si (pET,False) c t | isAll t =
      let (_,(v,t1,s),t2) = deconstructAll t
          c' = addC (mkDecl (v,t1,s)) c in
      putFrankTerm si (False,False) c t1 >>= \st1 ->
      putFrankTerm si (pET,pET) c' t2 >>= \st2 ->
      return ("(pi "++ v ++ "," ++ st1 ++ "," ++ sortToIdent s ++
              "," ++ st2 ++ ")")
putFrankTerm si (pET,False) c t | isDelta t =
      let (_,(v,d1,t1,s),t2) = deconstructDelta t
          c' = addC (mkDef (v,d1,t1,s)) c in
      putFrankTerm si (pET,pET) c d1 >>= \sd1 ->
      putFrankTerm si (False,False) c t1 >>= \st1 ->
      putFrankTerm si (pET,pET) c' t2 >>= \st2 ->
      return ("(let "++ v ++ "," ++ sd1 ++ "," ++ st1 ++ "," ++
              sortToIdent s ++ "," ++ st2 ++ ")")
putFrankTerm si _ _ _ = genErrS "Unexpected term construct in putFrankTerm"




--finalHandleError mess


putContext :: SyntaxInfo -> [ContextE] -> CLI ()
putContext si con =
    putCon si False [] con >>=
    putLines

putCon :: SyntaxInfo -> Bool -> [Sort] -> [ContextE] -> CLI [String]
putCon si latex whichSorts con =
    let sortsSel = (`elem` whichSorts) in
    if latex then
       fetchCon >>= \c ->
       return (latexPrintContextSt si (globToTot c) sortsSel con)
    else
       return (printContextSt si sortsSel con)

putReductionPath :: SyntaxInfo -> [Term] -> CLI ()
putReductionPath si redSeq =
            fetchOptShowRedPath >>= \showPath ->
            if showPath then
               putLines (fmap (printTermSt si) redSeq)
            else
               let (count,nf) = lengthLast redSeq in
               putSt (printTermSt si nf ++"\n"++
                                    show (count-1) ++ " reductions.\n")

-- lengthLast xs = (length xs, last xs)
-- but lengthLast has optimal space behaviour.
lengthLast = lengthLast' 0
lengthLast' n [x] = (n+1,x)
lengthLast' n (x:xs) = if n==n then lengthLast' (1+n) xs else undefined

putTermTypeSort :: SyntaxInfo -> (Term,Term,Sort) -> CLI ()
putTermTypeSort si tts = putLine (printTermESSt si tts)

putBool :: Bool -> CLI ()
putBool = putLine . boolToEnglish

boolToEnglish :: Bool -> String
boolToEnglish False = "No."
boolToEnglish True  = "Yes."

putMaybeSubst :: (Hnum,Term) -> CLI ()
putMaybeSubst subst = fetchOptShowProofterm >>= \spt ->
                      if spt then
                         putSubst subst
                      else
                         skip


putSubst :: (Hnum,Term) -> CLI ()
putSubst subst = fetchSyn >>= \si ->
                 putLine (printHoleSubstSt si subst)


rUseForIs :: [(String,Vari,Vari)] -> CLI ()
rUseForIs lemmas =
   putTable3 "  " "  " (LeftAl,CentreAl,LeftAl)
             (("tactic","connective","lemma") : niceTable3 lemmas)

niceTable3 :: [(String,String,String)] -> [(String,String,String)]
niceTable3 table =
       let display (a,b,c) (olda,oldb,oldc) = if a == olda then
                                                 if b == oldb then
                                                    ("","",c)
                                                 else
                                                    ("",b,c)
                                              else
                                                 (a,b,c) in
       zipWith display table (("","","") : table)

putTable3 :: String -> String -> (Align,Align,Align) ->
             [(String,String,String)] -> CLI ()
putTable3 sep1 sep2 als table = putLines (showTable3 sep1 sep2 als table)


---------------------------------------
-- P R I N T I N G   R O U T I N E S --
---------------------------------------

printContextSt :: SyntaxInfo -> (Sort->Bool) -> [ContextE] -> [String]
printContextSt = printContext displayString

-- printFullGoalSt print a goal with its local context
printFullGoalSt :: SyntaxInfo -> (Hnum,Goal) -> [String]
printFullGoalSt si (n,(term,locCon,gi)) =
    let locConL = locConToList locCon
        shownLocCon = fmap fst (filter (((==) True).snd) (zip locConL gi)) in
    -- const True means "print all definitions in full"
    printContextSt si (const True) shownLocCon ++
    [take 50 (repeat '-')] ++
    [printGoalSt si goalPath (n,(term,locCon,gi))]

goalPath = ("",[])


printGoalSt = printGoal displayString

-- printGoals prints goal n fully, and the rest in short form
printGoalsSt :: SyntaxInfo -> GoalNr -> ToProve -> [String]
printGoalsSt si n (prftrm,gs) =
        let pretext = if extractOptShowProofterm si then
                         ["Proofterm = " ++ printTermSt si prftrm,""]
                      else
                         [] in
        pretext ++ printGoalsSt0 si n gs


printGoalsSt0 :: SyntaxInfo -> GoalNr -> Goals -> [String]
printGoalsSt0 si _ [] = ["Goal proved!"]
printGoalsSt0 si _ [g] = printFullGoalSt si g
printGoalsSt0 si n gs = let len = length gs in
                        [show len ++ " goals",""] ++
                        printFullGoalSt si (gs!!(n-1)) ++ [""] ++
                        let restGs = filter ((n/=) . snd) (zip gs [1..]) in
                        fmap (\(g,m) -> show m ++ ") " ++
                                       printGoalSt si goalPath g)
                            restGs

printHoleSubstSt :: SyntaxInfo -> (Hnum,Term) -> String
printHoleSubstSt si (hnum,term) =
         printHnumSt si hnum ++ " := " ++ printTermSt si term


-- print two terms and a sort (see above)
printTermESSt :: SyntaxInfo -> (Term,Term,Sort) -> String
printTermESSt si (t,u,v) = printTermSt si t ++ " : " ++
                           printTermSSt si (u,v)

printTermSSt si =  printTermS displayString si dummyVar

showSubsts :: SyntaxInfo -> [Subst] -> String
showSubsts si [] = "No substitutions found"
showSubsts si [s] = showSubst si s

showSubst :: SyntaxInfo -> Subst -> String
showSubst si s =
         "<"++ commas (fmap (\(v,t) -> v++":="++printTermSt si t) s) ++">"

------------------
-- For Jan only --
------------------


cZwerver :: (TermIT,TermIT) -> CLI ()
cZwerver (t1',t2') = genErrS "Not implemented"
{-
    fmap globToTot fetchCon >>= \con ->
    getTypeRet con t1' >>= \(t1,type1,_) ->
    getTypeRet con t2' >>= \(t2,type2,sort2) ->
    fetchSyn >>= \si ->
    maplComs (putRes si) (combine si con type1 (t2,type2))

putRes :: SyntaxInfo -> (LContext,Term,Subst) -> CLI ()
putRes si (lCon,term,sigma) =
      putLine "Exis. context" >>
      putLines (printContext displayString si True (indexedToList lCon)) >>
      putLine "Rest" >>
      putLine (printTermSt si term) >>
      putLine "Substitutie" >>
      putLine (showSubst si sigma) >>
      putLine ""
-}


{-
cZwerver t = let ts = unwindAppITs t in
             fmap globToTot fetchCon >>= \c ->
             mapL (getTypeRet c) ts >>= \tTss ->
             handle (zetHaakjes (fmap (\(a,b,c) -> (a,b)) tTss))
             (\e -> err e)
             (\(t,typ) -> fetchSyn >>= \si ->
                          putLine (printTermSt si t) >>
                          putLine "with type" >>
                          putLine (printTermSt si typ))

unwindAppITs :: TermIT -> [TermIT]
unwindAppITs t = unwindAppITs' t []

unwindAppITs' :: TermIT -> [TermIT] -> [TermIT]
unwindAppITs' t l = let (isApp,t1,t2) = deconstructAppIT t in
                    if isApp then
                       unwindAppITs' t1 (t2:l)
                    else
                       t:l

deconstructAppIT (t,IT _ its) | isApp t =
                let (_,t1,t2) = deconstructApp t
                    [it1,it2] = its in
                (True,(t1,it1),(t2,it2))
deconstructAppIT _ = (False,dummyTermIT,dummyTermIT)

-- Pre: argument not empty list
zetHaakjes :: [(Term,Term)] -> E (Term,Term)
zetHaakjes [(t,typ)] = return (t,typ)
zetHaakjes ((t,typ):l) | isArrow typ =
            let (_,dom,cod) = deconstructArrow typ in
            zetHaakjes' l dom >>= \(u,l') ->
            zetHaakjes ((t `mkApp` u,cod):l')
zetHaakjes _ = genErrS "Lukt niet 1"

-- Pre: argument not empty list
zetHaakjes' :: [(Term,Term)] -> Term -> E (Term,[(Term,Term)])
zetHaakjes' [] goal = genErrS "Lukt niet 2"
zetHaakjes' ((t,typ):l) goal | typ==goal = return (t,l)
zetHaakjes' ((t,typ):l) goal | isArrow typ =
            let (_,dom,cod) = deconstructArrow typ in
            zetHaakjes' l dom >>= \(u,l') ->
            zetHaakjes' ((t `mkApp` u,cod):l') goal
zetHaakjes' _ _ = genErrS "Lukt niet 3"

{- OLD:
cZwerver :: Path -> CLI ()
cZwerver p = mToCLI fetchSyn >>= \si ->
             mToCLI fetchCon >>= \con ->
             findCon si con p >>=
             putLine


findConE :: SyntaxInfo -> GContext -> ContextE -> TermPath -> CLI String
findConE si con _ [] = pathError
findConE si con (v,((t,s),_,ts)) (p:ps) | isPathConVar p =
                    return ("Variabele decl. / def. " ++ v)
findConE si con (v,((t,s),_,ts)) (p:ps) | isPathConTyp p =
                    findSubterm (domGCon con) t ps >>= \(t',subCon) ->
                    return ("In typ van " ++ v ++ " " ++ printTermSt si t')
findConE si con (v,((t,s),_,ts)) (p:ps) | isPathConSort p =
                    return ("Soort van " ++ v ++ " "++ printSortSt si s)
findConE si con (v,((t,s),_,ts)) (p:ps) | isPathConOther p =
                    let (_,idx) = deconPathConOther p in
                    if idx >= length ts then
                       pathError
                    else
                    findSubterm (domGCon con) (ts!!idx) ps >>= \(t',subCon)->
                    return ("In def. of zo van "++v++" "++ printTermSt si t')


findCon :: SyntaxInfo -> GContext -> Path -> CLI String
findCon si con (v,tpath) = let (found,cer) = findI con v in
                           if not found then
                              pathError
                           else
                           findConE si con (v,cer) tpath

pathError :: CLI a
pathError = genErrS "Path does not exist"
-}
-}
