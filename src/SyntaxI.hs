-- File: SyntaxI
-- Description: This module defines the type SyntaxInfo, which holds 
--   information about the type system used and syntactic information,
--   e.g. the associativity of operators.

module SyntaxI(Assoc(..), Precedence, Binder, LatexVar, Implicit, AllOptions,
               BoolOptions,
               SyntaxInfo, dummySyntax, PartSyntax(..), HasSyntax(..),
               updateSyn',
               -- TYPE SYSTEM
               extractSys, insertSys, extractPTSys, insertPTSys,
               hasSubtyping,
               extractExSys, insertExSys, extractSorts, extractAxioms,
               extractRules, extractSortsSub, extractRulesSub,
               fetchSys, setSys, isIdentSort,
               -- PRECEDENCE
               extractPrecedence, insertPrecedence, extractPrec, 
               {- defaultAssoc -} fetchPrecedence, fetchPrec, setPrec,
               -- BINDER
               extractBinder, insertBinder, extractBind, fetchBinder,
               fetchBind, setBind,
               -- LaTeX
               extractLatexVar, insertLatexVar, extractLatex, fetchLatexVar,
               fetchLatex, setLatex,
               -- IMPLICIT
               extractImplicit, insertImplicit, getImplicit, {-defaultImplic -}
               fetchImplicits, fetchImplicit, setImplicit, removeImplicit,
               -- OPTIONS
               extractAllOptions, insertAllOptions, extractBoolOptions,
               insertBoolOptions, CodeOption, fetchOptGen, setBoolOptions,
               optShowSort, optImplicit, optShowProofterm, optShowRedPath,
               fetchOptShowSort, extractOptShowSort, fetchOptImplicit,
               extractOptImplicit, fetchOptShowProofterm,
               extractOptShowProofterm, fetchOptShowRedPath,
               -- SIMPLE PRINTING ROUTINES
               isO1, isO, isOper,
               printHnumSt, printVarSt, printVarListSt, 
               printSortSt, printRule12St
               ) where
               
import Char(isDigit)
import General
import HaTuple
import HaMonSt
import Basic
import Collect



-- associativity of operators 
data Assoc = NoAssoc | LeftAssoc | RightAssoc

instance Eq Assoc where
         NoAssoc == NoAssoc = True
         LeftAssoc == LeftAssoc = True
         RightAssoc == RightAssoc = True
         _ == _ = False


-- Precedence is an association list, holding operators with their precedence
-- and associativity.
type Precedence = IL Vari (Int,Assoc)              

-- Binder is a list of variables that are treated as a binder.
type Binder = [Vari]

-- Latexvar is an association list, holding variables with a number of
-- arguments that are printed using a macro in LaTeX-mode
type LatexVar = IL Vari Int

-- Implicit is an association list, holding operators with
-- information of how may implicit arguments it can have.
type Implicit =  IL Vari Int

                                                     
-- AllOptions contains the values of a number of options
type AllOptions = BoolOptions

-- Options contains the values of a number of options
type BoolOptions = (Bool,Bool,Bool,Bool)
-- option 1: printing of the sorts of terms
-- option 2: implicit paramaters are possible
-- option 3: show proof term
-- option 4: show reduction path
                    

-- SyntaxInfo holds also the type system used, so the name is a little
-- misleading
type SyntaxInfo = (System,AllOptions,Precedence,Binder,LatexVar,Implicit)


-- only for testing
dummySyntax :: SyntaxInfo
dummySyntax = ((([],[],[],[],[]),[]),(True,False,True,False),
               emptyI,[],emptyI,emptyI) 


-------------------------------------------------
-- SETTING AND READING VARIABLES IN SYNTAXINFO --
-------------------------------------------------

-- We adopt the following naming-conventions:
-- + For FUNCTIONAL use we have
--   - extract  to extract some state component from syntaxinfo
--   - insert   to change some state component in syntaxinfo
-- + For MONADIC use we have
--   - fetch     to read some state component
--   - update    to change some state component (i.e. with a function)
--   - set       to set some state component (i.e. with a value)

class PartSyntax s where
     extractSyn :: s -> SyntaxInfo
     insertSyn :: (SyntaxInfo->SyntaxInfo)->(s->s)

class (Functor m,Monad m) => HasSyntax m where
     fetchSyn   :: m SyntaxInfo
     updateSyn  :: (SyntaxInfo->SyntaxInfo)-> m SyntaxInfo
     setSyn     :: SyntaxInfo -> m ()
     fetchSyn    = updateSyn id
     setSyn new  = map (const ()) (updateSyn (\old -> new))
   
updateSyn' :: HasSyntax m => (SyntaxInfo->SyntaxInfo)-> m ()
updateSyn' f = map (const ()) (updateSyn f)

instance PartSyntax s => HasSyntax (State s) where
     updateSyn f = map extractSyn (updateS (insertSyn f))
     -- hbc 0.9999.4 will complain if we replace updateS above by update,
     -- so we need a updateS function with a more restricted type.

updateS :: (s->s) -> State s s
updateS = update
   


-- Now all variables for reading and writing syntaxinfo will follow,
-- in the following order:
--          1. Type System
--          2. Options
--          3. Precedence
--          4. Binder
--          5. Implicit

-- 1. TYPE SYSTEM

extractSys :: SyntaxInfo -> System
extractSys = fst6

insertSys :: (System -> System) -> SyntaxInfo -> SyntaxInfo
insertSys = doFst6

extractPTSys :: SyntaxInfo -> PTSystem
extractPTSys = fst . extractSys

insertPTSys :: (PTSystem -> PTSystem) -> SyntaxInfo -> SyntaxInfo
insertPTSys = insertSys . doFst

hasSubtyping :: SyntaxInfo -> Bool
hasSubtyping = not . null . fth5 . extractPTSys

extractExSys :: SyntaxInfo -> ExSystem
extractExSys = snd . extractSys

insertExSys :: (ExSystem -> ExSystem) -> SyntaxInfo -> SyntaxInfo
insertExSys = insertSys . doSnd


extractSorts :: SyntaxInfo -> [Sort]
extractSorts = fst5 . extractPTSys

extractAxioms :: SyntaxInfo -> [(Sort,Sort)]
extractAxioms = snd5 . extractPTSys

extractRules :: SyntaxInfo -> [(Sort,Sort,Sort)]
extractRules = thd5 . extractPTSys

extractSortsSub :: SyntaxInfo -> [Sort]
extractSortsSub = fth5 . extractPTSys

extractRulesSub :: SyntaxInfo -> [(Sort,Sort,Sort)]
extractRulesSub = ffh5 . extractPTSys

fetchSys :: HasSyntax m => m System
fetchSys = map extractSys fetchSyn

setSys :: HasSyntax m => System -> m ()
setSys sys = updateSyn' (insertSys (const sys))


-- representation of the sorts
isIdentSort :: SyntaxInfo -> String -> Bool
isIdentSort si s = SORT s `elem` extractSorts si


-- 2. OPTIONS

-- general stuff

extractAllOptions :: SyntaxInfo -> AllOptions
extractAllOptions = snd6

insertAllOptions :: (AllOptions -> AllOptions) -> SyntaxInfo -> SyntaxInfo
insertAllOptions = doSnd6

extractBoolOptions :: SyntaxInfo -> BoolOptions
extractBoolOptions = extractAllOptions

insertBoolOptions :: (BoolOptions -> BoolOptions) -> SyntaxInfo -> SyntaxInfo
insertBoolOptions = insertAllOptions

type CodeOption = (BoolOptions->Bool,Bool->BoolOptions->BoolOptions)

fetchOptGen :: HasSyntax m => CodeOption -> m Bool
fetchOptGen opt = map ((fst opt) . extractBoolOptions) fetchSyn 

setBoolOptions :: HasSyntax m => BoolOptions -> m ()
setBoolOptions opts = updateSyn' (insertBoolOptions (const opts))

-- specific stuff       

optShowSort      :: CodeOption
optShowSort      = (fst4, doFst4 . const)

optImplicit      :: CodeOption
optImplicit      = (snd4, doSnd4 . const)

optShowProofterm :: CodeOption
optShowProofterm = (thd4, doThd4 . const)

optShowRedPath   :: CodeOption
optShowRedPath   = (fth4, doFth4 . const)


fetchOptShowSort :: HasSyntax m => m Bool
fetchOptShowSort = fetchOptGen optShowSort

extractOptShowSort :: SyntaxInfo -> Bool
extractOptShowSort = fst optShowSort . extractBoolOptions

fetchOptImplicit :: HasSyntax m => m Bool
fetchOptImplicit = fetchOptGen optImplicit

extractOptImplicit :: SyntaxInfo -> Bool
extractOptImplicit = fst optImplicit . extractBoolOptions

fetchOptShowProofterm :: HasSyntax m => m Bool
fetchOptShowProofterm = fetchOptGen optShowProofterm

extractOptShowProofterm :: SyntaxInfo -> Bool
extractOptShowProofterm = fst optShowProofterm . extractBoolOptions

fetchOptShowRedPath :: HasSyntax m => m Bool
fetchOptShowRedPath = fetchOptGen optShowRedPath

-- 3. PRECEDENCE

extractPrecedence :: SyntaxInfo -> Precedence
extractPrecedence = thd6

insertPrecedence :: (Precedence -> Precedence) -> SyntaxInfo -> SyntaxInfo
insertPrecedence = doThd6

extractPrec :: SyntaxInfo -> Vari -> (Int,Assoc)
extractPrec si v = snd (foundI (extractPrecedence si) defaultAssoc v)


defaultAssoc :: (Int,Assoc)
defaultAssoc = (6,NoAssoc)

fetchPrecedence :: HasSyntax m => m Precedence
fetchPrecedence = map extractPrecedence fetchSyn 

fetchPrec :: HasSyntax m => Vari -> m (Int,Assoc)
fetchPrec v = fetchSyn >>= \si -> 
              return (extractPrec si v)

setPrec :: HasSyntax m => Vari -> (Int,Assoc) -> m ()
setPrec v ia = updateSyn' (insertPrecedence upd)
                      where upd p = setI p v ia

-- 4. BINDER

extractBinder :: SyntaxInfo -> Binder
extractBinder = fth6

insertBinder :: (Binder->Binder) -> SyntaxInfo -> SyntaxInfo
insertBinder = doFth6

extractBind :: SyntaxInfo -> Vari -> Bool
extractBind si v = v `elem` extractBinder si

fetchBinder :: HasSyntax m => m Binder
fetchBinder = map extractBinder fetchSyn

fetchBind :: HasSyntax m => Vari -> m Bool
fetchBind v = fetchSyn >>= \si ->
              return (extractBind si v)

setBind :: HasSyntax m => Vari -> m ()
setBind v = updateSyn' (insertBinder upd)
               where upd l | v `elem` l = l \\ [v]
                           | otherwise = v : l

-- 5. Latex

extractLatexVar :: SyntaxInfo -> LatexVar
extractLatexVar = ffh6

insertLatexVar :: (LatexVar->LatexVar) -> SyntaxInfo -> SyntaxInfo
insertLatexVar = doFfh6

extractLatex :: SyntaxInfo -> Vari -> (Bool,Int)
extractLatex si = findI (extractLatexVar si)

fetchLatexVar :: HasSyntax m => m LatexVar
fetchLatexVar = map extractLatexVar fetchSyn

fetchLatex :: HasSyntax m => Vari -> m (Bool,Int)
fetchLatex v = fetchSyn >>= \si ->
               return (extractLatex si v)

setLatex :: HasSyntax m => Vari -> Int -> m ()
setLatex v i = updateSyn' (insertLatexVar (\il -> setI il v i))

-- 6. IMPLICIT PARAMETERS

extractImplicit :: SyntaxInfo -> Implicit
extractImplicit = sxh6

insertImplicit :: (Implicit -> Implicit) -> SyntaxInfo -> SyntaxInfo
insertImplicit = doSxh6

-- implicit

getImplicit :: SyntaxInfo -> Vari -> Int
getImplicit si v = snd (foundI (extractImplicit si) defaultImplic v)

defaultImplic :: Int
defaultImplic = 0

fetchImplicits :: HasSyntax m => m Implicit
fetchImplicits = map extractImplicit fetchSyn 

fetchImplicit :: HasSyntax m => Vari -> m Int
fetchImplicit v = fetchSyn >>= \si -> 
                  return (getImplicit si v)

setImplicit :: HasSyntax m => Vari -> Int -> m ()
setImplicit v n = updateSyn' (insertImplicit d)
                         where d ii = setI ii v n

removeImplicit :: HasSyntax m => Vari -> m ()
removeImplicit v = updateSyn' (insertImplicit (snd . flip removeI v))



------------------------------
-- SIMPLE PRINTING ROUTINES --
------------------------------

-- These printing routines are not included in module Printer, because
--        1) They are needed everywhere in the yarrow (not just in the
--           user interface), to produce error messages.
--        2) They are not polymorphic, but just deliver a string.

           
-- All these routines return a character string.
-- Their name ends in St (for String), and they get as parameter the
-- syntactic info.                                    

-- isO1 checks this character can be the start of an operator
isO1 :: Char -> Bool
isO1 c = c `elem` "+<>/\\&!$%^~|@;=[]-"

-- isO  checks this character can occur after the first character of
-- an operator     
isO :: Char -> Bool
isO '\'' = True
isO '_' = True
isO c | isDigit c = True
isO c = isO1 c

-- isOper checks if this variable is an operator
isOper :: Vari -> Bool
isOper = isO1 . head

printHnumSt si (N n) =  "?"++show n
                       
printVarSt :: SyntaxInfo -> Vari -> String
printVarSt si v | isOper v || extractBind si v = "("++v++")"
printVarSt si v  = v

printVarListSt :: SyntaxInfo -> [Vari] -> String
printVarListSt si = prList (printVarSt si) ","

printVarListSpaceSt :: SyntaxInfo -> [Vari] -> String
printVarListSpaceSt si = prList (printVarSt si) " "              

printSortSt :: SyntaxInfo -> Sort -> String
printSortSt si s = sortToIdent s

printRule12St :: SyntaxInfo -> Sort -> Sort -> String
printRule12St si s1 s2 = "("++ printSortSt si s1 ++","++ 
                         printSortSt si s2 ++ ",?)"


