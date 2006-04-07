-- File: Modules
-- Description: This module contains all functions needed for the management
-- of modules

module Modules(lastVarModuleDefined,
               qLoadModuleInput,qContinueLoad,
               qSaveModule,qSaveCompleted,qClearModule,
               qGiveModuleContents) where

import HaTuple
import Collect
import HaMonSt
import General
import Basic
import Paths(internalErr,genErrS,genErrSuffix)
import SyntaxI
import MainSta
import Char(isDigit)
import PTSys(partSystem,updateSortsOfDefsInContextEList)
import GenComs
import Typing(contnOk)
import YarMsg

-- Read the part of the documentation on modules first!
-- Yarrow detects changes of modules by including for every module in the
-- import-list a checksum.
-- When a module is loaded, the checksum is calculated and stored.
-- When this module is in the import-list of another module, the checksum
-- in the import list and the stored checksum are compared.
-- If they are equal, we assume this module hasn't changed (statistically
-- this is justified). If they are not equal, the new module is type-
-- checked again.

{-
EBNF Syntax for terms and contexts in code files

Term ::= 'B' Basic |
         'N' Nonb |
         'L' Bind Terms Item Term          -- L for Lambda-ish
Terms ::= '(' Terms0 ')'
Terms0 ::= empty | ',' Term Terms0
Basic ::= 'S' Sort |     -- Sort
          'V' Var        -- Var
Nonb ::= 'A'             -- App
Bind ::= '\' |           -- Abs
         '@' |           -- All
         '='             -- Delta
Item ::= Var ':' Term ':' Sort '.'
Var ::= every char except from ":).,"
Sort ::= Var

Context ::= '}' |                  -- empty
            ContextE '\n' Context 
ContextE ::= ContCat Terms Item
ContCat ::= '=' |    -- Def
            ':'      -- Decl
-}

{- Implementation detail:
   At one point I tried to use classes to simplify saving and loading of
   modules, e.g.
     class Saveable a where save :: a -> ModulesO ()
   The problem is that Haskell doesn't accept
     instance Saveable Vari
   because Vari is not declared as a 'datatype'. This severely limits the
   use of classes.
-}
   

-------------------------------------
--  S A V I N G   C O N T E X T S  --
-------------------------------------

-- we use simple state monads for loading and saving to limit the overhead.
                   
type MOState = (String->String,Checksum)
type ModulesO a = State MOState a

-- we store terms in a very simple way, since the contents of modules are
-- not intended for the user

mWriteC :: Char -> ModulesO ()
mWriteC c = fetchS2 >>= \(f,checksum) ->
            -- hbc 0.9999.4 will complain if we replace fetchS2 above by fetch,
            -- so we need a fetchS2 function with a more restricted type.
            let checksum' = computeChecksum checksum c
                f' = f . (c:) in
            if checksum' /= checksum' + 1 then
               setS (f',checksum')
               -- hbc 0.9999.4 will complain if we replace setS above by set,
               -- so we need a setS function with a more restricted type.
            else
               internalErr "mWriteC"

fetchS2 :: State s s
fetchS2 = fetch

setS :: s -> State s ()
setS = set

                
mWriteS :: String -> ModulesO ()
mWriteS s = fetchS2 >>= \(f,checksum) ->
            let checksum' = foldl computeChecksum checksum s
                f' = f . (s++) in
            if checksum' /= checksum' + 1 then
               setS (f',checksum')
            else
               internalErr "mWriteS"

-- TERMS

saveTerm :: Term -> ModulesO ()
saveTerm term | isBasic term = let (_,cat) = deconstructBasic term in
                               mWriteC 'B' >>
                               saveBasic cat
saveTerm term | isNonb term = let (_,cat,ts) = deconstructNonb term in
                              mWriteC 'N' >>
                              saveNonb cat >>
                              saveTerms ts
saveTerm term | isBind term = let (_,cat,ts,it,u) = deconstructBind term in
                              mWriteC 'L' >>
                              saveBind cat >>
                              saveTerms ts >>
                              saveItem it >>
                              saveTerm u
                               
saveTerms :: [Term] -> ModulesO ()
saveTerms = saveList saveTerm

saveBasic :: BasicCat -> ModulesO ()
saveBasic (Srt s) = mWriteC 'S' >>
                    saveSort s
saveBasic (Vr v) = mWriteC 'V' >>
                   saveVar v

saveNonb :: NonbCat -> ModulesO ()
saveNonb App = mWriteC 'A'
-- Extension: Records:
saveNonb (RecType ls)= mWriteC 'R' >> saveLabels ls
saveNonb (RecValue ls)= mWriteC 'r' >> saveLabels ls
saveNonb (RecSelect l)= mWriteC 'S' >> saveLabel l

saveLabels :: [RecLabel] -> ModulesO ()
saveLabels = saveList saveLabel

saveLabel :: RecLabel -> ModulesO ()
saveLabel = saveVar
-- End Extension: Records:

saveBind :: BindCat -> ModulesO ()
saveBind (Abs constrs) = mWriteC '\\' >>
                         saveConstraints constrs
saveBind (All constrs) = mWriteC '@' >>
                         saveConstraints constrs
saveBind Delta = mWriteC '='

saveConstraints :: Constraints -> ModulesO ()
saveConstraints CNone = mWriteC 'N'
-- Extension: Subtyping:
saveConstraints CSub = mWriteC 'S'
-- End Extension: Subtyping

                                  
saveItem :: Item -> ModulesO ()
saveItem (v,t,s) = saveVar v >>
                   mWriteC ':' >> 
                   saveTerm t >> 
                   mWriteC ':' >>
                   saveSort s >>
                   mWriteC '.'



saveVar :: Vari -> ModulesO ()
saveVar v = mWriteS v

saveSort (SORT s) = mWriteS s
                    
-- CONTEXTS
         
saveContextE :: ContextE -> ModulesO ()
saveContextE (v,((t,s),cat,ts)) = saveContCat cat >>
                                  saveTerms ts >>
                                  saveItem (v,t,s)   

saveContCat :: ContCat -> ModulesO ()
saveContCat Def = mWriteC '='
saveContCat (Decl constrs) = mWriteC ':' >>
                             saveConstraints constrs

saveContext :: [ContextE] -> ModulesO ()
saveContext con = maplComs (\it -> saveContextE it >> mWriteC '\n') con

saveSystem :: System -> ModulesO ()
saveSystem (pts,exs) = savePTSystem pts >>
                       saveExSystem exs

savePTSystem :: PTSystem -> ModulesO ()
savePTSystem (sorts,axioms,rules,sortsSub,rulesSub) = 
    saveList save1Sort sorts >>
    saveList save2Sort axioms >> 
    saveList save3Sort rules >> 
    saveList save1Sort sortsSub >>
    saveList save3Sort rulesSub >> 
    mWriteC '\n'

saveExSystem :: ExSystem -> ModulesO ()
saveExSystem exS = let saveSortExt (s,ext) = saveSort s >>
                                             mWriteC ':' >>
                                             saveExtension ext in
                   mWriteC 's' >>
                   saveList saveSortExt exS >>
                   mWriteC '\n'


saveExtension :: Extension -> ModulesO ()
-- Extension: Records:
saveExtension Records = mWriteC 'R'
-- End Extension: Records:
                                  
save1Sort s = saveSort s
save2Sort (s1,s2) = saveSort s1 >> 
                    mWriteC ':' >> 
                    saveSort s2
save3Sort (s1,s2,s3) = saveSort s1 >> 
                       mWriteC ':' >> 
                       saveSort s2 >> 
                       mWriteC ':' >> 
                       saveSort s3

saveImport :: (String,Checksum) -> ModulesO ()
saveImport (s,c) = mWriteC '\"' >> 
                   mWriteS s >> 
                   mWriteC '\"' >> 
                   saveChecksum c

saveImports :: [(String,Checksum)] -> ModulesO ()
saveImports ms = saveList saveImport (reverse ms) >>
                 mWriteC '\n'
                         
savePrec :: (Vari,(Int,Assoc)) -> ModulesO ()
savePrec (v,(n,a)) = mWriteS v >> 
                     mWriteC ':' >> 
                     mWriteS (show n) >> 
                     mWriteC (showA a)
                      where showA NoAssoc = 'n'
                            showA LeftAssoc = 'l'
                            showA RightAssoc = 'r'

savePrecs :: [(Vari,(Int,Assoc))] -> ModulesO ()
savePrecs precs = mWriteC 'p' >>
                  saveList savePrec precs  >> 
                  mWriteC '\n'

saveBinds :: [Vari] -> ModulesO ()
saveBinds binds = mWriteC 'b' >>
                  saveList saveVar binds  >> 
                  mWriteC '\n'

saveLatexs :: [(Vari,Int)] -> ModulesO ()
saveLatexs latexs = mWriteC 'l' >>
                    saveList saveImpl latexs  >> 
                    mWriteC '\n'

                     

saveImpl :: (Vari,Int) -> ModulesO ()
saveImpl (v,n) = mWriteS v >> 
                 mWriteC ':' >> 
                 mWriteS (show n)

saveImpls :: [(Vari,Int)] -> ModulesO ()
saveImpls impls = mWriteC 'i' >>
                  saveList saveImpl impls >> 
                  mWriteC '\n'

saveLemma :: ((Vari,String,[Sort]),(Vari,Int)) -> ModulesO ()
saveLemma ((w,s,sorts),(v,i)) = 
    mWriteS v >> 
    mWriteC ':' >> 
    mWriteS (show i) >> 
    mWriteC ':' >> 
    mWriteS w >>
    mWriteC ':' >>
    mWriteS s >>
    mWriteC ':' >>
    saveList saveSort sorts

saveLemmas :: [((Vari,String,[Sort]),(Vari,Int))] -> ModulesO ()
saveLemmas lemmas = mWriteC 'l' >>
                    saveList saveLemma lemmas >> 
                    mWriteC '\n'


                  
saveModule :: (System,[(String,Checksum)],[(Vari,(Int,Assoc))],[Vari],
                      [(Vari,Int)],
                      [(Vari,Int)],[((Vari,String,[Sort]),(Vari,Int))],
                      [ContextE]) ->
              ModulesO ()
saveModule (sys,ms,prec,binds,latexs,impl,lemmas,con) = 
        saveSystem sys >> saveImports ms >> savePrecs prec >>
        saveBinds binds >> saveLatexs latexs >>
        saveImpls impl >> saveLemmas lemmas >> saveContext con

performSaveModule :: 
              (System,[(String,Checksum)],[(Vari,(Int,Assoc))],[Vari],
                      [(Vari,Int)],
                      [(Vari,Int)],[((Vari,String,[Sort]),(Vari,Int))],
                      [ContextE]) ->
              M (String,Checksum)
performSaveModule all = fmap (\(_,(f,c)) -> (f [],c))
                        (perform (id,startChecksum) (saveModule all))



saveList :: (a -> ModulesO ()) -> [a] -> ModulesO ()
saveList sa as = mWriteC '(' >>
                 maplComs (\a -> mWriteC ',' >> sa a) as >>
                 mWriteC ')'

---------------------------------------
--  L O A D I N G   C O N T E X T S  --
---------------------------------------
                       
-- we use simple state monads for loading to limit the overhead.

type MState = (String,Checksum)
type ModulesI a = State MState a

makeErrorMP :: PreErrorMonad m => String -> m a
makeErrorMP s = genErrS ("Not a module at "++ take 10 s)

loadErr :: ModulesI a      
loadErr = fetchS2 >>= \(s,_) ->
          makeErrorMP s

mReadChar :: ModulesI Char
mReadChar = fetchS2 >>= \((c:_),_) ->
            return c

mNextChar :: ModulesI ()
mNextChar = fetchS2 >>= \(c:s,checksum) -> 
            if checksum/=checksum+1 then -- force strictness!
               set (s,computeChecksum checksum c)
            else
               loadErr
  
mTakeUntil :: (Char -> Bool) -> ModulesI String
mTakeUntil p = mReadChar >>= \c ->
               if p c then
                  return ""
               else
               mNextChar >>
               fmap (c:) (mTakeUntil p)

mReadIdent :: ModulesI String
mReadIdent = mTakeUntil (`elem` ":().,")  -- " \n:{}().,")

mEat :: Char -> ModulesI ()
mEat t = mReadChar >>= \u ->
         if t==u then mNextChar
         else loadErr

loadTerm :: ModulesI Term
loadTerm  = 
    mReadChar >>= \t ->
    case t of
    'B' -> mNextChar >>
           loadBasic >>= \cat ->
           return (mkBasic cat)
    'N' -> mNextChar >>
           loadNonb >>= \cat ->
           loadTerms >>= \ts ->
           return (mkNonb cat ts)
    'L' -> mNextChar >>
           loadBind >>= \cat ->
           loadTerms >>= \ts ->
           loadItem >>= \it ->
           loadTerm >>= \u ->
           return (mkBind cat ts it u)
    otherwise -> loadErr

loadTerms :: ModulesI [Term]
loadTerms = loadList loadTerm
                        
loadBasic :: ModulesI BasicCat
loadBasic = 
    mReadChar >>= \c ->
    case c of
    'S' -> mNextChar >>  
           loadSort >>= \s ->
           return (Srt s) 
    'V' -> mNextChar >>
           loadVar >>= \v->
           return (Vr v)
    otherwise -> loadErr

loadNonb :: ModulesI NonbCat
loadNonb =
    mReadChar >>= \c ->
    case c of
    'A' -> mNextChar >>
           return App
    -- Extension: Records:
    'R' -> mNextChar >>
           loadLabels >>= \ls ->
           return (RecType ls)
    'r' -> mNextChar >>
           loadLabels >>= \ls ->
           return (RecValue ls)
    'S' -> mNextChar >>
           loadLabel >>= \l ->
           return (RecSelect l)
    -- End Extension: Records:
    otherwise -> loadErr      

-- Extension: Records:
loadLabels :: ModulesI [RecLabel]
loadLabels = loadList loadVar

loadLabel :: ModulesI RecLabel
loadLabel = loadVar
-- End Extension: Records:


loadBind :: ModulesI BindCat
loadBind =
    mReadChar >>= \c ->
    case c of
    '\\' -> mNextChar >>
            loadConstraints >>= \constrs ->
            return (Abs constrs)
    '@' -> mNextChar >>
           loadConstraints >>= \constrs ->
           return (All constrs)
    '=' -> mNextChar >>
           return Delta
    otherwise -> loadErr
                              
loadConstraints :: ModulesI Constraints
loadConstraints =
    mReadChar >>= \c ->
    case c of
    'N' -> mNextChar >>
           return CNone
    -- Extension: Subtyping:
    'S' -> mNextChar >>
           return CSub
    -- End Extension: Subtyping
    otherwise -> loadErr


loadItem :: ModulesI Item
loadItem = loadVar >>= \v ->
           mEat ':' >>
           loadTerm >>= \t ->
           mEat ':' >>
           loadSort >>= \s ->
           mEat '.' >>
           return (v,t,s)


loadVar :: ModulesI Vari
loadVar =  mReadIdent

loadSort :: ModulesI Sort
loadSort = fmap SORT mReadIdent

loadContextE :: ModulesI ContextE
loadContextE = loadContCat >>= \cat ->
               loadTerms >>= \ts ->
               loadItem >>= \(v,t,s) ->
               return (v,((t,s),cat,ts))

loadContCat :: ModulesI ContCat
loadContCat =  mReadChar >>= \t ->
               case t of
               '=' -> mNextChar >>
                      return Def
               ':' -> mNextChar >>
                      loadConstraints >>= \constrs ->
                      return (Decl constrs)
               otherwise -> loadErr

loadContext :: ModulesI [ContextE]
loadContext = mReadChar >>= \t ->
              case t of
              '}' -> return []
              otherwise -> loadContextE >>= \ce ->
                           mEat '\n' >>
                           fmap (ce :) loadContext
                                      
loadSystem :: ModulesI System
loadSystem = loadPTSystem >>= \pts ->
             loadExSystem >>= \exs ->
             return (pts,exs)

loadPTSystem :: ModulesI PTSystem
loadPTSystem = loadList load1Sort >>= \sorts ->
               loadList load2Sort >>= \axioms ->
               loadList load3Sort >>= \rules ->
               mReadChar >>= \t ->
               (case t of
                '(' -> loadList load1Sort >>= \sortsSub ->
                       loadList load3Sort >>= \rulesSub ->
                       return (sortsSub,rulesSub)
                -- backwards compatibility
                otherise -> return ([],[])
               ) >>= \(sortsSub,rulesSub) ->
               mEat '\n' >>
               return (sorts,axioms,rules,sortsSub,rulesSub)

loadExSystem :: ModulesI ExSystem
loadExSystem = mReadChar >>= \c ->
               if c/='s' then -- backwards compatibility
                  return []
               else
                  mEat 's' >>
                  let loadSortExt = loadSort >>= \s ->
                                    mEat ':' >>
                                    loadExtension >>= \ext ->
                                    return (s,ext) in
                  loadList loadSortExt >>= \exs ->
                  mEat '\n' >>
                  return exs

loadExtension :: ModulesI Extension
loadExtension = mReadChar >>= \c ->
                case c of
                -- Extension: Records:
                'R' -> mNextChar >> return Records
                -- End Extension: Records:
                otherwise -> loadErr


load1Sort = loadSort

load2Sort = loadSort >>= \s1 ->
            mEat ':' >>                                 
            loadSort >>= \s2 ->
            return (s1,s2)

load3Sort = loadSort >>= \s1 ->
            mEat ':' >>                                 
            loadSort >>= \s2 ->
            mEat ':' >>                                 
            loadSort >>= \s3 ->
            return (s1,s2,s3)


            
loadFilename :: ModulesI String      
loadFilename = mTakeUntil (=='"')

loadInt :: ModulesI Int
loadInt = mTakeUntil (not . isDigit) >>= \s ->
                return (fst (readNum s))

loadImport :: ModulesI (String,Checksum)
loadImport = mEat '"' >>
             loadFilename >>= \f ->
             mEat '"' >>
             loadChecksum >>= \c ->
             return (f,c)

loadImports :: ModulesI [(String,Checksum)]
loadImports = loadList loadImport >>= \imps ->
              mEat '\n' >>
              return imps

loadPrec :: ModulesI (Vari,(Int,Assoc))
loadPrec = loadVar >>= \v ->
           mEat ':' >>
           loadInt >>= \i ->
           mReadChar >>= \c ->
           mNextChar >>
           let conv 'l' = LeftAssoc
               conv 'r' = RightAssoc
               conv _ = NoAssoc in
           return (v,(i,conv c))
                  
loadPrecs = mEat 'p' >>
            loadList loadPrec >>= \precs ->
            mEat '\n' >>
            return precs

loadBinds :: ModulesI Binder
loadBinds = mEat 'b' >>
            loadList loadVar >>= \binds ->
            mEat '\n' >>
            return binds

loadLatexs = mReadChar >>= \c ->
             if c/='l' then -- backwards compatibility
                return []
             else
             mEat 'l' >>
             loadList loadImpl >>= \latexs ->
             mEat '\n' >>
             return latexs

loadImpl :: ModulesI (Vari,Int)
loadImpl = loadVar >>= \v ->
           mEat ':' >>
           loadInt >>= \i ->
           return (v,i)
                  
loadImpls = mEat 'i' >>
            loadList loadImpl >>= \impls ->
            mEat '\n' >>                          
            return impls

loadLemma :: ModulesI ((Vari,Int),(Vari,String,[Sort]))
loadLemma = loadVar >>= \v ->
            mEat ':' >>
            loadInt >>= \i ->
            mEat ':' >>
            loadVar >>= \w ->
            mEat ':' >>
            loadVar >>= \s ->
            mEat ':' >>
            loadList loadSort >>= \sorts ->
            return ((v,i),(w,s,sorts))
                  
loadLemmas = mEat 'l' >>
             loadList loadLemma >>= \lemmas ->
             mEat '\n' >>                          
             return lemmas



loadModule1 :: ModulesI (System,[(String,Checksum)])
loadModule1 = loadSystem >>= \sys ->
              loadImports >>= \imports ->
              return (sys,imports)

loadModule2 :: ModulesI ([(Vari,(Int,Assoc))],[Vari],[(Vari,Int)],[(Vari,Int)],
                         [((Vari,Int),(Vari,String,[Sort]))],[ContextE])
loadModule2 = loadPrecs >>= \precs ->
              loadBinds >>= \binds ->
              loadLatexs >>= \latexs ->
              loadImpls >>= \impls ->                  
              loadLemmas >>= \lemmas ->
              loadContext >>= \con ->
              return (precs,binds,latexs,impls,lemmas,con)

performLoadMod1 :: String -> M (System,[(String,Checksum)],(String,Checksum))
performLoadMod1 s = 
  perform (s++"}",startChecksum) loadModule1 >>= 
                                    \((sys,imp),st) ->
  return (sys,imp,st)

performLoadMod2 :: (String,Checksum) -> 
                   M ([(Vari,(Int,Assoc))],[Vari],[(Vari,Int)],[(Vari,Int)],
                      [((Vari,Int),(Vari,String,[Sort]))],[ContextE],Checksum) 
performLoadMod2 st = 
 perform st loadModule2 >>= \((precs,binds,latexs,impls,lemmas,con),(s',cs)) ->
 if s'/="}" then makeErrorMP s' 
 else 
 return (precs,binds,latexs,impls,lemmas,con,cs)


           
loadList :: ModulesI a -> ModulesI [a]
loadList la =                         
    mEat '(' >>
    loadList' >>= \ts ->
    mEat ')' >>
    return ts
       where loadList' = mReadChar >>= \c ->
                         case c of
                         ',' -> mNextChar >>
                                la >>= \t ->
                                fmap (t:) loadList'
                         otherwise -> return []

---------------
-- CHECKSUMS --
---------------

-- the type Checksum is defined in MainSta.hs

computeChecksum :: Checksum -> Char -> Checksum
computeChecksum n c = (3*n) `mod` 1073741824 + ord c

startChecksum :: Checksum
startChecksum = 17

loadChecksum :: ModulesI Checksum
loadChecksum = loadInt

saveChecksum :: Checksum -> ModulesO ()
saveChecksum = mWriteS . show

-------------------------------------------
--  A U X I L A R Y   F U N C T I O N S  --
------------------------------------------- 

-- splitContext splits the current context into two pieces.
-- The second piece is the part of the context corresponding to modules,
-- the first piece is the rest
splitContext :: [ModuleInfo] -> M ([ContextE],GContext)
splitContext mi = fetchCon >>= \con ->
                  let lastVar = lastVarModuleDefined mi in
                  return (breakTWO (==lastVar) con)


-- checkConflicts checks that the all new names are fresh. The names of
-- sorts are not forgotten.
checkConflicts :: [Vari] -> M ()
checkConflicts ids =
    fetchSyn >>= \si ->
    let sorts = extractSorts si in
    fetchCon >>= \con ->
    domAllLocCon >>= \locVars ->
    let unsort (SORT s) = s
        sortsAsIds = fmap unsort sorts
        globVars = domGCon con
        allIds = sortsAsIds +++ (locVars +++ globVars)
        conflicts = filter (`elemC` allIds) ids
        (conflict1:conflicts') = conflicts in
    if null conflicts then
       skip
    else
    fetchSyn >>= \si ->
    let nameName = if null conflicts' then "name: " else "names, e.g.: " in
    loadMainErr [ES ("Conflicting " ++ nameName ++
                          printVarSt si conflict1), ES genErrSuffix]
                    
                     

                        
headOrDummy :: [Vari] -> Vari
headOrDummy [] = dummyVar
headOrDummy (v:_) = v
                        
------------------------------
--  L O A D  C O M M A N D  --
------------------------------
                      
loadMainErr :: PreErrorMonad m => Error -> m a                   
loadMainErr er = err (er `errConc` loadMainErrMess)
loadMainErrMess = "\nLoading aborted"

-- checkChecksums returns True iff for all imported modules have the same
-- checksum in the import list and the list of loaded modules
checkChecksums :: [(String,Checksum)] -> M Bool
checkChecksums [] = return True
checkChecksums ((name,checksum):ms) =
            fetchModulesInfo >>= \mi ->
            let found = findAll3 mi name
                ((_,presentChecksum):_) = found in
            if null found then
               internalErr ("Module required and not loaded")
            else if presentChecksum /= checksum then
               return False
            else
               checkChecksums ms    


setPrecs :: [(Vari,(Int,Assoc))] -> M ()
setPrecs [] = skip
setPrecs ((v,i):l) = setPrec v i >>
                     setPrecs l

setBinds :: [Vari] -> M ()
setBinds [] = skip
setBinds (v:l) = setBind v >>
                 setBinds l

setLatexs :: [(Vari,Int)] -> M ()
setLatexs [] = skip
setLatexs ((v,n):l) = setLatex v n >>
                      setLatexs l

setImpls :: [(Vari,Int)] -> M ()
setImpls [] = skip
setImpls ((v,i):l) = setImplicit v i >>
                     setImpls l
      
setLemmas :: [((Vari,Int),(Vari,String,[Sort]))] -> M ()
setLemmas [] = skip
setLemmas ((v,key):l) = setLemma key v >>
                        setLemmas l
      


-- qLoadModuleInput loads a module.
-- More specifically, it does the following things:
-- 1. Check that the PTS of the module is a part of the current PTS.
-- 2. Check the modules of the import-list; if some are not loaded yet
--    it returns RLoadList <modules-to-be-loaded-inclusing-this-one>
-- 3. Check that no name conflicts arise.
-- 4. Check module is consistent with the loaded modules
-- 5. Update the context, implicit and infix info, and the modules.

qLoadModuleInput :: ModuleName -> String -> M Result
qLoadModuleInput modName contents =
        fetchModulesInfo >>= \mi ->
        if modName `elem` fmap fst3 mi then -- module already loaded
           return RDone -- of (RModulesAre mi)  -- nothing 
        else
        performLoadMod1 contents >>= \(sys,imports,st)->
        fetchSys >>= \curSys ->
        (if not (sys `partSystem` curSys) then
            fetchCon >>= \curCon ->
            if isEmptyI curCon then
               setSys sys
            else
               genErrS "Module not valid in current PTS"
         else
            skip) >>
        let loadList = fmap fst imports \\ fmap fst3 mi in
        if not (null loadList) then
           -- load imported modules first, then try again.
           return (RLoadList (loadList ++ [modName]))
        else
           return (RLoadMessage ("Loading module \"" ++ modName ++ "\"")
                                (StartLoading modName sys st imports))

qContinueLoad :: StatusLoad -> M Result
qContinueLoad (StartLoading modName sys st imports) =
     -- Precondition: modName is not yet loaded
     performLoadMod2 st >>= \(t1,t2,t3,t4,t5,fileCon,t7)->
     let varsOfFile = toC (fmap fst fileCon) in
     checkConflicts varsOfFile >>
     fetchModulesInfo >>= \mi ->
     splitContext mi >>= \(userCon,modCon) ->
     checkChecksums imports >>= \b ->
     fetchSys >>= \curSys ->
     let fileCon' = updateSortsOfDefsInContextEList sys curSys fileCon
         newModCon = fileCon' `addListI` modCon
         tup' = (t1,t2,t3,t4,t5,varsOfFile,t7) in
     if b then 
        let newCon = userCon `addListI` newModCon in
        continueLoad modName tup' newCon
     else
        return (RLoadMessage ("Rechecking module \"" ++ modName ++ "\"")
                             (StartChecking modName tup' userCon newModCon))
             
qContinueLoad (StartChecking modName tup@(_,_,_,_,_,vars,_) 
              userCon newModCon) =
        fetchSyn >>= \si ->
        handle (contnOk si (length vars) newModCon)
        (\e -> loadMainErr e)
        (\_ -> let newCon = userCon `addListI` newModCon in
               continueLoad modName tup newCon)


continueLoad modName (precs,binds,latexs,impls,lemmas,varsOfFile,checksum)
             newCon =
        setCon newCon >>
        setPrecs precs >>
        setBinds binds >>
        setLatexs latexs >>
        setImpls impls >>
        setLemmas lemmas >>
        fetchModulesInfo >>= \mi ->
        let firstOfFile = headOrDummy (reverse varsOfFile)
            lastOfFile = headOrDummy varsOfFile 
            mi' = (modName,(firstOfFile,lastOfFile),checksum) : mi in
        setModulesInfo mi' >>
        return (RModulesAre mi')



-- type StatusLoad = defined in MainSta.hs
                              


-------------------------------
--  S A V E   C O M M A N D  --
-------------------------------

-- saveMod corresponds to the command 'save'.
-- It distinguishes three situations:
-- 1. The name is new, then the new part of the context is saved.
-- 2. The name is the most recent module name. Then definitions of this
--    module are also saved in the new version.
-- 3. The name is a loaded module, but not the most recent. An error
--    message is issued.
qSaveModule :: ModuleName -> M Result
qSaveModule modName = 
            fetchModulesInfo >>= \mi ->
            let miModNames = fmap fst3 mi in
            if take 1 miModNames == [modName] then
               saveMod1 modName (tail mi)
               --("Module \"" ++ modName ++ "\" updated\n")
            else
            if modName `elem` miModNames then
               genErrS ("Module \"" ++modName++ " is not the most recent, "++
                       "so can't be updated")
            else
               saveMod1 modName mi --("Module \"" ++ modName ++ "\" saved\n")

-- saveMod1 saves the new part of the context in the file, and registers
-- the new module in the module list.
saveMod1 :: String -> [ModuleInfo] -> M Result
saveMod1 modName mi = 
     fetchSys >>= \sys ->
     splitContext mi >>= \(newCon,_) ->
     fetchPrecedence >>= \allPrec ->
     fetchBinder >>= \allBind ->
     fetchLatexVar >>= \allLatex ->
     fetchImplicits >>= \allImplicits ->
     fetchLemmas >>= \allLemmas ->
     let varsOfF = toC (fmap fst newCon) in
     let imports = fmap (\(name,_,checksum) -> (name,checksum)) mi
         precInfo = partA (indexedToListIL allPrec) varsOfF
         bindInfo = filter (`elem` varsOfF) allBind
         latexInfo = partA (indexedToListIL allLatex) varsOfF
         implicitInfo = partA (indexedToListIL allImplicits) varsOfF
         lemmasInfo = filter (\(_,(v,_)) -> v `elem` varsOfF) 
                                 (indexedToListIL allLemmas)  in
     performSaveModule (sys,imports,precInfo,bindInfo,latexInfo,implicitInfo,
                        lemmasInfo,newCon)       >>= \(contents,checksum) ->
     let firstOfF = headOrDummy (reverse varsOfF)
         lastOfF = headOrDummy varsOfF
         mi' = ((modName,(firstOfF,lastOfF),checksum) : mi) in
     return (RTrySaveThis contents mi')
              
-- Only when the data is really saved to disk, update the ModulesInfo-part
-- of the state
qSaveCompleted :: StatusSave -> M Result
qSaveCompleted mi = setModulesInfo mi >>
                    return (RModulesAre mi)


-----------------------------------
--  O T H E R   C O M M A N D S  --
-----------------------------------

qClearModule :: M Result
qClearModule = fetchModulesInfo >>= \mi ->
              if null mi then
                 genErrS "No modules loaded"
              else
              let mi' = tail mi in
              setModulesInfo mi' >>
              return (RModulesAre mi')


-- lastVarModuleDefined gives the last variable that is defined in a
-- module, and dummyVar if no variable is defined in a module.
lastVarModuleDefined :: [ModuleInfo] -> Vari
lastVarModuleDefined [] = dummyVar
lastVarModuleDefined ((_,(_,id),_):mi) = if id == dummyVar then
                                             lastVarModuleDefined mi
                                         else id                           

qGiveModuleContents :: String -> M Result
qGiveModuleContents m = 
                    fetchCon >>= \c ->
                    fetchModulesInfo >>= \mi ->
                    let mfs = findAll3 mi m  
                        (first,last) = fst (head mfs) in
                    if null mfs then
                       genErrS ("No module \""++m++"\" loaded")
                    else
                    -- Note that the order in a context is reversed w.r.t.
                    -- the usual notation on paper!
                    let partC = takeUntil (\it -> domConE it == first)
                                (dropWhile (\it -> domConE it /= last)
                                 (globConToList c)) in
                    return (RModuleContentsIs partC)

