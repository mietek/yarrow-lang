-- File: Basic
-- Description: This module defines the term structure

module Basic(-- TERMS
             Sort(SORT),topSort,isProperSort,dummySort,
             identToSort, sortToIdent, 
             Hnum(N),
             Vari,dummyVar,
             RecLabel, dummyRecLabel,
             Item,ItemD, 
             Term(..),
             BasicCat(..),NonbCat(..),BindCat(..), Constraints(..),
             dummyTerm, dummyItem, 
             {- dummyItemD, dummyTermL, dummyBasicCat, dummyNonbCat,
                dummyBindCat -}

             -- CONSTRUCTOR FUNCTIONS
             mkBasic,mkNonb,mkBind,mkApp,mkAbs,mkGenAbs,mkSubAbs,
             mkAll,mkGenAll,mkSubAll,
             mkDelta,mkVr,mkSrt,mkHole,mkArrow,
             mkRecValue, mkRecType, mkRecSelect,

             -- FREE VARIABLES & SUBSTITUTION
             fv, subst, alpha, findFree,
             changeVar, equateVarsBinders, changeVar2, occurVar, 
             isDummyVar, findNiceFree, changeNiceVar,

             -- CONTEXTS
             infinity, ContextE, ContextERest, ContCat(..), 
             GContext, emptyGCon, addC,
             LContext, emptyLCon, dummyLContext, filterLCon, concLCon,
             Context, dummyContext, emptyCon, globToTot, addLoc, addLocG,
             locConToList, listToLocCon, globConToList,
             convBindToCont, isGenDecl,isDecl,isSubDecl,isDef,
             deconstructGenDecl,deconstructDecl,deconstructSubDecl,
             deconstructDef,mkDecl,mkGenDecl,mkSubDecl,
             mkDef,mkContextE,
             lConToType, domConE, domLCon, domGCon, domCon, fvLCon,
             domDeclLCon, findDeclDef, findTypeSort, findType, findGenDecl,
             findDef, findDefTypeSort, findSubBound,

             -- DECONSTRUCTOR FUNCTIONS
             isBasic, isNonb, isBind, isCatVar, isCatRecSelect,
             isVar, isSort, isHole, isGenAbs, isAbs, isSubAbs, isApp,
             isGenAll, isAll, isSubAll, isDelta, isArrow, isRealAll,
             isRecValue, isRecType, isRecSelect, isGenAllN,
             deconstructBasic, deconstructNonb, deconstructBind, 
             deconstructVar, deconstructSort, deconstructHole,
             deconstructAbs, deconstructGenAbs, deconstructSubAbs,
             deconstructApp, 
             deconstructAll, deconstructGenAll, deconstructSubAll, 
             deconstructDelta, 
             deconstructAbsMax,
             deconstructArrow, deconstructSpecVar, deconstructApp2,
             deconstructApp3, deconstructAppN, deconstructAppMax, 
             deconstructGenAllMax, deconstructArrowN,
             deconstructRecValue, deconstructRecType, deconstructRecSelect,

             -- HANDLING PLACE INFORMATION
             Place,PlaceInfo, dummyPlace, dummyPI, InfoTree(..), dummyIT,
             TermIT, dummyTermIT, forgetIT, changeStart, changeEnd,
             changeStartEnd, combinePlace, combineIT, termToTermIT,

             -- MISCELLANEOUS 
             ErrorElem(..), Error, errConc,
             maxPrec,
             PTSystem, Extension(..), SortEx, ExSystem, System
             ) where

import Char(isDigit)
import General
import HaTuple
import Collect
         
infixl 7 `mkApp`

-- I introduce here a number of naming conventions. All names may be suffixed
-- with a number or with primes.
-- There is no strict adherence to this convention! Often a more descriptive
-- name will be used :-), and sometimes a more confusing name is used :-(

-- SORTS
                            
data Sort = SORT String 
-- Naming convention: s

identToSort :: String -> Sort
identToSort = SORT

sortToIdent :: Sort -> String
sortToIdent (SORT s) = s
                            
instance Eq Sort where SORT s1 == SORT s2 = s1 == s2

-- for type-technical reasons also neeeded:
instance Ord Sort where SORT s1 < SORT s2 = s1 < s2

-- topSort is used for terms that have no proper sort.
-- For a more extensive discussion, see the typing module.
topSort =  SORT "0" 

-- contains the sorts of the system
isProperSort :: Sort -> Bool
isProperSort = (/= topSort)


dummySort = SORT "1"               -- may be anything that cannot be confused
                                   -- with real sorts.



-- HOLES

-- Holes are solely for the interactiver prover.
-- They are included in the term structure because for ease.
data Hnum = N Int 
-- Naming convention: hn

instance Eq Hnum where (N a) == (N b) = a ==b

dummyHole = N 0                
      

-- VARIABLES

type Vari = String     
-- Naming convention: v,w

dummyVar :: Vari
dummyVar = "_"

  
-- Extensions: Records:
type RecLabel = String             

dummyRecLabel :: RecLabel
dummyRecLabel = "_"
-- End Extension: Records

---------------
-- T E R M S --
---------------

-- Terms are represented by trees in a straightforward way. The special thing-- is that for every variable also the sort of the variable in the binder
-- is recorded.
-- Since the sort is needed often, this will improve efficiency.
-- For definitions this may not be a proper sort. We call pi-terms
-- all-terms.

type Item = (Vari,Term,Sort)          -- var with type and sort
type ItemD = (Vari,Term,Term,Sort)    -- var with definiens, type and sort
-- Naming convention for both of these: it

data Term = Basic BasicCat |                  -- Categories with no subterms
            Nonb NonbCat [Term] |             -- Non-binders with subterms
            Bind BindCat [Term] Item Term     -- Binders

-- We assume that given a category, there is a fixed number of arguments.
data BasicCat = Vr Vari |
                Srt Sort |
                Hole Hnum

data NonbCat = App |          -- Two arguments
               -- Extensions: Records:
               RecValue [RecLabel] |    -- Zero or more arguments
                                        -- (as many as labels)
               RecType [RecLabel] |     -- Zero or more arguments
               RecSelect RecLabel       -- One argument
               -- End Extension: Records

data BindCat = Abs Constraints |         -- For other non-bound arguments,
               All Constraints |         -- see Constraints
               Delta                     -- One other non-bound arguments
-- Naming convention for terms: t,u, and d (intending a definiens)

data Constraints = CNone |         -- No other non-bound arguments
                   -- Extension: Subtyping:
                   CSub            -- One other non-bound argument
                   -- End Extension: Subtyping

-- Sometimes we compare to dummyTerm
dummyTerm :: Term
dummyTerm = Basic (Srt dummySort)

dummyItem :: Item
dummyItem = (dummyVar,dummyTerm,dummySort)

dummyItemD :: ItemD
dummyItemD = (dummyVar,dummyTerm,dummyTerm,dummySort)

dummyTermL :: [Term]
dummyTermL = []

dummyBasicCat = Srt dummySort
dummyNonbCat = undefined
dummyBindCat = undefined

dummyConstr :: Constraints
dummyConstr = undefined



---------------------------
-- CONSTRUCTOR FUNCTIONS --
---------------------------

-- these function are the basic constructors
-- no information

mkBasic :: BasicCat -> Term
mkNonb :: NonbCat -> [Term] -> Term
mkBind :: BindCat -> [Term] -> Item -> Term -> Term

mkApp :: Term -> Term -> Term
mkAbs :: Item -> Term -> Term
-- Extension: Subtyping:
mkGenAbs :: (Item,Constraints,[Term]) -> Term -> Term
mkSubAbs :: ItemD -> Term -> Term
-- End Extension: Subtyping
mkAll :: Item -> Term -> Term
-- Extension: Subtyping:
mkGenAll :: (Item,Constraints,[Term]) -> Term -> Term
mkSubAll :: ItemD -> Term -> Term
-- End Extension: Subtyping
mkDelta :: ItemD -> Term -> Term
mkVr :: Vari -> Term
mkSrt :: Sort -> Term
mkHole :: Hnum -> Term
mkArrow :: (Term,Sort) -> Term -> Term
               
-- Extensions: Records:
mkRecValue :: [(RecLabel,Term)] -> Term
mkRecType :: [(RecLabel,Term)] -> Term
mkRecSelect :: Term -> RecLabel -> Term
-- End Extension: Records

mkBasic cat = Basic cat
mkNonb cat ts = Nonb cat ts
mkBind cat ts it u = Bind cat ts it u

mkApp t u = Nonb App [t,u]
mkAbs it u = mkGenAbs (it,CNone,[]) u
-- Extension: Subtyping:
mkGenAbs (it,constrs,cts) u = Bind (Abs constrs) cts it u
mkSubAbs (v,b,t,s) u = mkGenAbs ((v,t,s),CSub,[b]) u
-- End Extension: Subtyping
mkAll it u = mkGenAll (it,CNone,[]) u
-- Extension: Subtyping:
mkGenAll (it,constrs,cts) u = Bind (All constrs) cts it u
mkSubAll (v,b,t,s) u = mkGenAll ((v,t,s),CSub,[b]) u
-- End Extension: Subtyping
mkDelta (v,d,t,s) u = Bind Delta [d] (v,t,s) u
mkVr v = Basic (Vr v)
mkSrt s = Basic (Srt s)
mkHole hn = Basic (Hole hn)
mkArrow (t,s) u = mkAll (dummyVar,t,s) u
               
-- Extensions: Records:
mkRecValue fs = let (labels,ts) = unzip fs in
                Nonb (RecValue labels) ts
mkRecType fs = let (labels,ts) = unzip fs in
               Nonb (RecType labels) ts
mkRecSelect t l = Nonb (RecSelect l) [t]
-- End Extension: Records
  

-------------------------------------
-- FREE VARIABLES & ALPHA EQUALITY --
-------------------------------------

-- fv finds the free variables of a term
fv :: Term -> [Vari]
fv (Basic (Vr v)) = single v
fv (Basic _) = empty
fv (Nonb _ ts) = union (map fv ts)
fv (Bind _ ts (v,t,s) u) = union (map fv ts) +++ fv t +++ 
                           (removeC (fv u) v)
                                 

instance Eq BasicCat where
          (Vr v) == (Vr w) = v==w
          (Srt s) == (Srt t) = s==t
          _ == _ = False

instance Eq NonbCat where
          App == App = True
          -- Extensions: Records:
          RecValue ls == RecValue ms = ls == ms
          RecType ls == RecType ms = ls == ms
          RecSelect l == RecSelect m = l == m
          -- End Extension: Records
          _ == _ = False

instance Eq BindCat where
          (Abs constr1) == (Abs constr2) = constr1 == constr2
          (All constr1) == (All constr2) = constr1 == constr2
          Delta == Delta = True
          _ == _ = False


instance Eq Constraints where
         CNone == CNone = True
         -- Extension: Subtyping:
         CSub == CSub = True
         -- End Extension: Subtyping
         _ == _ = False

-- alpha-equality
instance Eq Term where
  Basic cat1 == Basic cat2 = cat1 == cat2
  Nonb cat1 ts1 == Nonb cat2 ts2 = cat1 == cat2 && and (zipWith (==) ts1 ts2)
  Bind cat1 ts1 (v1,t1,s1) u1 == Bind cat2 ts2 (v2,t2,s2) u2 =
                      cat1 == cat2 &&
                      s1 == s2 && 
                      t1 == t2 && 
                      and (zipWith (==) ts1 ts2) && (
                      if v1 == v2 then
                         u1 == u2
                      else 
                         if v1 `elemC` fv u2 then False
                         else
                            u1 == subst u2 v2 (mkVr v1)
                      )
  _ == _ = False


-----------------------------
-- S U B S T I T U T I O N --
-----------------------------


-- substitution, including alpha-conversion
-- subst t v u  substitutes in t all occurrences of v for u
subst :: Term -> Vari -> Term -> Term
subst t v u = substFvL t v u (add v (fv u))
                     

                                                 
-- substFv  does the same, but assumes fvu = add v (fv u)
-- this efficiency measure makes the whole prover about 4% faster.
substFv :: Collection c => Term -> Vari -> Term -> c Vari -> Term
substFv b@(Basic (Vr w)) v u _ | w==v = u 
                               | otherwise = b
substFv b@(Basic cat) _ _ _ = b
substFv (Nonb cat ts) v u fvu = Nonb cat (map (\a -> substFv a v u fvu) ts)
substFv (Bind cat ts (w,t1,s1) t2) v u fvu = 
                     let ts' = map (\a -> substFv a v u fvu) ts
                         t1' = substFv t1 v u fvu in
                     if w==v then Bind cat ts' (w,t1',s1) t2
                     else
                     let (w',t2') = alpha (w,t2) fvu in
                     Bind cat ts' (w',t1',s1) (substFv t2' v u fvu)
 
  
      
-- alpha v t fvl  renames the variable v in t in such a way that it
-- doesn't occur in fvl (it doesn't rename to a free variable of t).
-- It also returns the new name of the variable
alpha :: Collection c => (Vari,Term) -> c Vari -> (Vari,Term)
alpha (v,t) fvl = if v `notElemC` fvl then
                     (v,t)
                  else
                     let w = findFree (fv t +++ fvl) v in
                     (w,subst t v (mkVr w))

-- find a variable (looking like v) not already occuring in set freev
-- by appending it with a number         
findFree :: Collection c => c Vari -> Vari -> Vari
findFree freev v = let suffixes = "":(map show [1..])
                       -- drop everything after the first digit
                       -- so x1 is renamed to x2 (if x already occurs)
                       -- x1a may be renamed to x2, but we do not consider
                       -- this to be a problem
                       v' = takeWhile (not . isDigit) v
                       altern = v : map (v'++) suffixes in
                   head (filter (flip notElemC freev) altern)

                                           
-- For some *STUPID* bug in Gofer, we have to specialize these functions
-- to lists, for use in subst.

substFvL :: Term -> Vari -> Term -> [Vari] -> Term
substFvL b@(Basic (Vr w)) v t _ | w==v = t 
                                | otherwise = b
substFvL b@(Basic cat) _ _ _ = b
substFvL (Nonb cat ts) v t fvt = Nonb cat (map (\a -> substFvL a v t fvt) ts)
substFvL (Bind cat ts (w,t1,s1) t2) v t fvt = 
                      let ts' = map (\a -> substFvL a v t fvt) ts
                          t1' = substFvL t1 v t fvt in
                      if w==v then Bind cat ts' (w,t1',s1) t2
                      else
                      let (w',t2') = alphaL (w,t2) fvt in
                      Bind cat ts' (w',t1',s1) (substFvL t2' v t fvt)
 
alphaL :: (Vari,Term) -> [Vari] -> (Vari,Term)
alphaL (v,t) fvl = if v `notElemC` fvl then
                      (v,t)
                   else
                      let w = findFree (fv t +++ fvl) v in
                      (w,subst t v (mkVr w))

-- End stupid bug workaround.

---------------------------------------
-- HELP ROUTINES FOR NAME CONVERSION --
---------------------------------------


-- changeVar t fv changes the name of a variable in a binder
-- so that it doesn't occur in fv 
-- doesn't change the information !
changeVar :: Collection c => Term -> c Vari -> Term
changeVar (Bind cat ts (v,t,s) u) fvl = let (v',u') = alpha (v,u) fvl in
                                        Bind cat ts (v',t,s) u'

-- equateVarsBinders fvl it1 it2 renames the variables in the binders so
-- that they are equal (and do not occur in fvl)
equateVarsBinders ::  Collection c => c Vari -> (Vari,Term) -> (Vari,Term) ->
                     (Vari,Term,Term)
equateVarsBinders fvl (v1,u1) (v2,u2) =
           if v1 `notElemC` fvl then
              if v1 == v2 then
                 (v1,u1,u2)
              else
                 if v1 `notElem` fv u2 then
                    (v1,u1, subst u2 v2 (mkVr v1))
                 else
                    renameBoth
           else
              renameBoth
           where renameBoth = 
                    let v3 = findFree (fv u1 +++ fv u2 +++ fvl) v1 in
                    (v3, subst u1 v1 (mkVr v3), subst u2 v2 (mkVr v3))

changeVar2 :: Collection c => (Term,Term) -> c Vari -> (Term,Term)
changeVar2 (Bind cat1 ts1 (v1,t1,s1) u1, Bind cat2 ts2 (v2,t2,s2) u2) fvl =
           let (v, u1', u2') = equateVarsBinders fvl (v1,u1) (v2,u2) in
           (Bind cat1 ts1 (v,t1,s1) u1', Bind cat2 ts2 (v,t2,s2) u2')

-- occurVar t gives all variables that are bound by t somewhere
occurVar :: Term -> [Vari]
occurVar (Basic _) = empty
occurVar (Nonb _ ts) = union (map occurVar ts)
occurVar (Bind _ ts (v,t,s) u) = union (map occurVar ts) +++ single v +++
                                 occurVar t +++ occurVar u


-------------------------
-- NICE VARIABLE NAMES --
-------------------------

-- The following routines are alternatives of the routines above
-- that give nicer names to variables.

isDummyVar :: Vari -> Bool
isDummyVar v = head v == head dummyVar

-- findNiceFree' is a variant of findFree.
-- It finds a name like vr not occurring in oldNames
-- if vr is equal to dummyVar, it can use its sort to get a nice name.
findNiceFree :: Collection c => Sort -> c Vari -> Vari -> Vari
findNiceFree sort oldNames vr = let vr' = if isDummyVar vr then
                                             "H"
                                          else
                                             vr in
                                findFree oldNames vr'
  
-- alphaNice is a variant of the functions alpha (in the basic module)
-- that gives a nice name to dummy variables
-- This could be made more efficient in the case the variable is
-- already fresh
alphaNice :: Collection c => Sort -> (Vari,Term) -> c Vari -> (Vari,Term)
alphaNice s (v,t) fv = let w = findNiceFree s fv v in
                       (w,subst t v (mkVr w))

-- changeNiceVar is a variant of the functions changeVar (in the basic
-- module), that gives a nice name to dummy variables
-- changeNiceVar si t s fv changes the name of a variable in a binder
-- so that it doesn't occur in con.
-- It chooses a name according to findNiceFree and context con.
-- It doesn't change the annotation !
changeNiceVar :: Collection c => Term -> c Vari -> Term
changeNiceVar (Bind cat ts (v,t,s) u) fvl =
                            let (v',u') = alphaNice s (v,u) fvl in
                            Bind cat ts (v',t,s) u'


---------------------
-- C O N T E X T S --
---------------------                                  
                    

-- infinity is used for the maximum length of a context
infinity :: Int
infinity = 10000000

-- we can have declarations and definitions in the context
-- (in a PTS, the context consists solely of declarations,
--  we implement a DPTS that can also have definitions)
type ContextERest = ((Term,Sort),ContCat,[Term])
                                                       
-- ContextE stands for context element
type ContextE = (Vari,ContextERest)

data ContCat = Decl Constraints |     -- For other arguments, see Constraints
               Def                    -- One other argument
                                              
                                      

-- For efficiency reasons (quick lookup of a name), we implement three sorts
-- of contexts:
--   * GContext: for the global context. This is implemented by trees with
--     an order. A GContext can become quite big (hundreds of elements), and
--     doesn't change frequently
--   * LContext: for the local context, which is the additional context
--     created in a proof session or in the typing algorithm.
--     This is implemented by lists, because it stays small (in practice
--     at most 20 elements), and changes frequently.
--   * Context: for the total context, the combination of a (number of) 
--     LContext's and the GContext.
-- The order in contexts is opposite to the order in which contexts normally
-- are written on paper. E.g. the local context
--     [mkDecl x A *, mkDecl A * #]
-- stands for 
--     A:*:#, x:A:*
-- In a total context, the local context always has the more recent items.


type GContext = TreeWithOrder Vari ContextERest

emptyGCon :: GContext                 
emptyGCon = emptyI

-- addC :: ContextE -> {G,L, }Context -> {G,L, }Context
addC :: AssocList c => ContextE -> c Vari ContextERest -> c Vari ContextERest
addC = addI


type LContext = IL Vari ContextERest

-- Functions for local contexts

emptyLCon :: LContext                 
emptyLCon = emptyI

dummyLContext :: LContext
dummyLContext = undefined

filterLCon :: (ContextERest->Bool) -> LContext -> LContext
filterLCon = filterIL

-- Precondition for concLCon l1 l2:
--   No key of l1 occurs in l2
concLCon :: LContext -> LContext -> LContext
concLCon = concIL


-- Naming convention for all sorts of contexts: c,con
type Context = ListsAndOTree Vari ContextERest

-- Functions for total contexts

dummyContext :: Context
dummyContext = undefined    
 
emptyCon :: Context
emptyCon = emptyI


-- Other functions for contexts                  

globToTot :: GContext -> Context
globToTot = makeLAOT
                 
addLoc :: LContext -> Context -> Context
addLoc = addLAOT

addLocG :: LContext -> GContext -> Context
addLocG = addMakeLAOT

locConToList :: LContext -> [ContextE]
locConToList = indexedToListIL

listToLocCon :: [ContextE] -> LContext
listToLocCon = listToIndexedIL

globConToList :: GContext -> [ContextE]
globConToList = indexedToListTWO



-- convBindToCont cat  calculates the context category associated with cat
convBindToCont :: BindCat -> ContCat
convBindToCont (Abs constr) = Decl constr
convBindToCont (All constr) = Decl constr
convBindToCont Delta = Def

                
isGenDeclRest :: ContextERest -> Bool
isGenDeclRest (_,Decl _,_) = True
isGenDeclRest _ = False

isGenDecl :: ContextE -> Bool
isGenDecl (_,cer) = isGenDeclRest cer

isDecl :: ContextE -> Bool
isDecl (_,(_,Decl CNone,_)) = True
isDecl _ = False

-- Extension: Subtyping:
isSubDecl :: ContextE -> Bool
isSubDecl (_,(_,Decl CSub,_)) = True
isSubDecl _ = False
-- End Extension: Subtyping

isDefRest :: ContextERest -> Bool
isDefRest (_,Def,_) = True
isDefRest _ = False

isDef :: ContextE -> Bool
isDef (_,cer) = isDefRest cer

deconstructGenDecl :: ContextE -> (Bool,Item,Constraints,[Term])
deconstructGenDecl (v,((t,s),Decl constrs,cts)) = (True,(v,t,s),constrs,cts)
deconstructGenDecl _ = (False,dummyItem,undefined,undefined)

deconstructDecl :: ContextE -> (Bool,Item)
deconstructDecl (v,((t,s),Decl CNone,_)) = (True,(v,t,s))
deconstructDecl _ = (False,dummyItem)

-- Extension: Subtyping:
deconstructSubDecl :: ContextE -> (Bool,(Vari,Term,Term,Sort))
deconstructSubDecl (v,((t,s),Decl CSub,[bound])) = (True,(v,bound,t,s))
deconstructSubDecl _ = (False,dummyItemD)
-- End Extension: Subtyping

deconstructDef :: ContextE -> (Bool,ItemD)
deconstructDef (v,((t,s),Def,[d])) = (True,(v,d,t,s))
deconstructDef _ = (False,dummyItemD)

mkDecl :: Item -> ContextE
mkDecl (v,t,s) = (v,((t,s),Decl CNone,[]))

-- Extension: Subtyping:
mkGenDecl :: (Item,Constraints,[Term]) -> ContextE
mkGenDecl ((v,t,s),cts,ts) = (v,((t,s),Decl cts,ts))

mkSubDecl :: (Vari,Term,Term,Sort) -> ContextE
mkSubDecl (v,bound,t,s) = (v,((t,s),Decl CSub,[bound]))
-- End Extension: Subtyping

mkDef :: ItemD -> ContextE
mkDef (v,d,t,s) = (v,((t,s),Def,[d]))

mkContextE :: ContCat -> [Term] -> Item -> ContextE
mkContextE cat ts (v,t,s) = (v,((t,s),cat,ts))

-- ALL VARIABLES
  

lConToType :: LContext -> IL Vari Term
lConToType = mapI (fst . fst3)
                      
-- domConE  gives the variable declared in a context-item
domConE :: ContextE -> Vari
domConE = fst               

-- domLCon  gives the domain of a local context 
--          (all variables declared/defined in a local context)
domLCon :: LContext -> [Vari]
domLCon = keysIL
 
-- domGCon finds all variables in a global context
domGCon :: GContext -> Tree Vari
domGCon = keysTWO
 
-- domCon finds all variables in a context
domCon :: Context -> ListsAndTree Vari
domCon = keysLAOT
  
-- fvLCon gives the free variables in a local context
fvLCon :: LContext -> [Vari]
fvLCon = union . map fvContextE . locConToList

-- fvContextE gives the free variables in a context element
fvContextE :: ContextE -> [Vari]
fvContextE (_,((typ,_),_,terms)) = concat (map fv (typ:terms))
        

-- FOR DECLARATIONS
        
-- domDeclLCon finds all variables that are declared (not defined) in a
-- local context
domDeclLCon :: LContext -> [Vari]
domDeclLCon = domLCon . filterLCon isGenDeclRest


-- findDeclDef  finds declaration / definition                               findDeclDef :: Context -> Vari -> (Bool,ContextERest)
findDeclDef c v = findI c v                 


-- findTypeSort  finds the occurence of the variable and delivers the type
--               and sort
findTypeSort :: AssocList a => 
                a Vari ContextERest -> Vari -> (Bool,(Term,Sort))
findTypeSort c v = doSnd fst3 (findI c v)
  

-- findType finds the occurences of the variable and delivers the type
findType :: AssocList a => a Vari ContextERest -> Vari -> (Bool,Term)
findType c v = doSnd fst (findTypeSort c v) 

findGenDecl :: AssocList a =>
               a Vari ContextERest -> Vari -> 
               (Bool,(Term,Sort),Constraints,[Term])
findGenDecl c v = let (b,cer) = findI c v in
                  if not b then
                     (False,undefined,undefined,undefined)
                  else
                     case cer of
                     ((t,s), Decl constr, cts) -> (True, (t,s), constr, cts)
                     otherwise -> (False,undefined,undefined,undefined)

-- FOR DEFINITIONS

-- findDefTypeSort  finds the definition (with its type and sort) of
--                  a variable
findDefTypeSort :: Context -> Vari -> (Bool,(Term,Term,Sort))
findDefTypeSort c v = let (b,ce) = findI c v in
                      if b then
                         case ce of
                         ((t,s),Def,[d]) -> (True,(d,t,s))
                         _ -> (False,undefined)
                      else
                         (False,undefined)
 
-- findDef  finds the definition of a variable
findDef :: Context -> Vari -> (Bool,Term)
findDef c v = doSnd fst3 (findDefTypeSort c v)

-- Extension: Subtyping:
-- findSubBound  finds the subtyping-bound of a variable
findSubBound :: Context -> Vari -> (Bool,Term)
findSubBound c v = let (b,ce) = findI c v in
                   if b then
                      case ce of
                      ((t,s),Decl CSub ,[bound]) -> (True,bound)
                      _ -> (False,undefined)
                   else
                      (False,undefined)
-- End Extension: Subtyping





-----------------------------
-- DECONSTRUCTOR FUNCTIONS --
-----------------------------

isBasic :: Term -> Bool
isBasic (Basic _) = True
isBasic _ = False

isNonb :: Term -> Bool
isNonb (Nonb _ _) = True
isNonb _ = False

isBind :: Term -> Bool
isBind (Bind _ _ _ _) = True
isBind _ = False

isCatVar :: BasicCat -> Bool
isCatVar (Vr _) = True
isCatVar _ = False
 
isCatRecSelect :: NonbCat -> Bool
isCatRecSelect (RecSelect _) = True
isCatRecSelect _ = False
 
isVar :: Term -> Bool
isVar (Basic (Vr _)) = True
isVar _ = False

isSort :: Term -> Bool
isSort (Basic (Srt _)) = True
isSort _ = False

isHole :: Term -> Bool
isHole (Basic (Hole _)) = True
isHole _ = False

isGenAbs :: Term -> Bool
isGenAbs (Bind (Abs _) _ _ _) = True
isGenAbs _ = False

isAbs :: Term -> Bool
isAbs (Bind (Abs CNone) _ _ _) = True
isAbs _ = False

-- Extension: Subtyping:              
isSubAbs :: Term -> Bool
isSubAbs (Bind (Abs CSub) _ _ _) = True
isSubAbs _ = False
-- End Extension: Subtyping

isApp :: Term -> Bool
isApp (Nonb App _) = True
isApp _ = False

isGenAll :: Term -> Bool
isGenAll (Bind (All _) _ _ _) = True
isGenAll _ = False

isAll :: Term -> Bool
isAll (Bind (All CNone) _ _ _) = True
isAll _ = False

-- Extension: Subtyping:              
isSubAll :: Term -> Bool
isSubAll (Bind (All CSub) _ _ _) = True
isSubAll _ = False
-- End Extension: Subtyping

isDelta :: Term -> Bool
isDelta (Bind Delta _ _ _) = True
isDelta _ = False

-- the following two routines are only used for printing
isArrow :: Term -> Bool
isArrow (Bind (All CNone) _ (v,_,_) u) | v `notElemC` fv u = True
isArrow _ = False

isRealAll :: Term -> Bool
isRealAll (Bind (All CNone) _ (v,_,_) u) | v `elemC` fv u = True
isRealAll _ = False

-- Extensions: Records:
isRecValue :: Term -> Bool
isRecValue (Nonb (RecValue _) _) = True
isRecValue _ = False

isRecType :: Term -> Bool
isRecType (Nonb (RecType _) _) = True
isRecType _ = False

isRecSelect :: Term -> Bool
isRecSelect (Nonb (RecSelect _) _) = True
isRecSelect _ = False
-- End Extension: Records
                 
isGenAllN :: Term -> Int -> Bool
isGenAllN t 0 = True
isGenAllN t n | isGenAll t = let (_,_,_,_,t') = deconstructGenAll t in
                             isGenAllN t' (n-1)
isGenAllN _ _ = False


deconstructBasic :: Term -> (Bool,BasicCat)
deconstructBasic (Basic cat) = (True,cat)
deconstructBasic _ = (False,dummyBasicCat)

deconstructNonb :: Term -> (Bool,NonbCat,[Term])
deconstructNonb (Nonb cat ts) = (True,cat,ts)
deconstructNonb _ = (False,dummyNonbCat,dummyTermL)

deconstructBind :: Term -> (Bool,BindCat,[Term],Item,Term)
deconstructBind (Bind cat ts it u) = (True,cat,ts,it,u)
deconstructBind _ = (False,dummyBindCat,dummyTermL,dummyItem,dummyTerm)


deconstructSort :: Term -> (Bool,Sort)
deconstructSort (Basic (Srt s)) = (True,s)
deconstructSort _ = (False,dummySort)
                                     
deconstructVar :: Term -> (Bool,Vari)
deconstructVar (Basic (Vr v)) = (True,v)
deconstructVar _ = (False,dummyVar)
                                     
deconstructHole :: Term -> (Bool,Hnum)
deconstructHole (Basic (Hole hn)) = (True,hn)
deconstructHole _ = (False,dummyHole)

deconstructApp :: Term -> (Bool,Term,Term)
deconstructApp (Nonb App [t1,t2]) = (True,t1,t2)
deconstructApp _ = (False,dummyTerm,dummyTerm)

deconstructAll :: Term -> (Bool,Item,Term)
deconstructAll (Bind (All CNone) _ it u) = (True,it,u)
deconstructAll _ = (False,dummyItem,dummyTerm)

-- Extension: Subtyping:    
deconstructGenAll :: Term -> (Bool,Item,Constraints,[Term],Term)
deconstructGenAll (Bind (All constr) cts it u) = (True,it,constr,cts,u)
deconstructGenAll _ = (False,dummyItem,dummyConstr,dummyTermL,dummyTerm)
          
deconstructSubAll :: Term -> (Bool,ItemD,Term)
deconstructSubAll (Bind (All CSub) [b] (v,t,s) u) = (True,(v,b,t,s),u)
deconstructSubAll _ = (False,dummyItemD,dummyTerm)
-- End Extension: Subtyping

deconstructAbs :: Term -> (Bool,Item,Term)
deconstructAbs (Bind (Abs CNone) _ it u) = (True,it,u)
deconstructAbs _ = (False,dummyItem,dummyTerm)

-- Extension: Subtyping:              
deconstructGenAbs :: Term -> (Bool,Item,Constraints,[Term],Term)
deconstructGenAbs (Bind (Abs constr) cts it u) = (True,it,constr,cts,u)
deconstructGenAbs _ = (False,dummyItem,dummyConstr,dummyTermL,dummyTerm)
          
deconstructSubAbs :: Term -> (Bool,ItemD,Term)
deconstructSubAbs (Bind (Abs CSub) [b] (v,t,s) u) = (True,(v,b,t,s),u)
deconstructSubAbs _ = (False,dummyItemD,dummyTerm)
-- End Extension: Subtyping

deconstructDelta :: Term -> (Bool,ItemD,Term)
deconstructDelta (Bind Delta [d] (v,t,s) u) = (True,(v,d,t,s),u)
deconstructDelta _ = (False,dummyItemD,dummyTerm)

                        
deconstructAbsMax :: Term -> ([Item],Term)
deconstructAbsMax t | isAbs t = 
                      let (_,it,u) = deconstructAbs t
                          (its,v) = deconstructAbsMax u in
                      (its ++ [it], v)
deconstructAbsMax t = ([],t)

deconstructArrow :: Term -> (Bool,Term,Term)
deconstructArrow (Bind (All CNone) _ (v,t,_) u) | v `notElemC` fv u =
                                                                 (True,t,u)
deconstructArrow t = (False,dummyTerm,dummyTerm)

-- deconstructSpecVar t v  checks t is the variable v
deconstructSpecVar :: Term -> Vari -> Bool
deconstructSpecVar t v = let (vr,varName) = deconstructVar t in
                         vr && v == varName

-- deconstructApp2 "(t1 t2) t3" = (True,t1,t2,t3)
deconstructApp2 :: Term -> (Bool,Term,Term,Term)
deconstructApp2 t = let (ap1,t',t3) = deconstructApp t
                        (ap2,t1,t2) = deconstructApp t' in
                    (ap1 && ap2,t1,t2,t3)

-- deconstructApp3 "((t1 t2) t3) t4" = (True,t1,t2,t3,t4)
deconstructApp3 :: Term -> (Bool,Term,Term,Term,Term)
deconstructApp3 t = let (ap1,t',t4) = deconstructApp t
                        (ap2,t1,t2,t3) = deconstructApp2 t' in
                    (ap1 && ap2,t1,t2,t3,t4)

deconstructAppN :: Term -> Int -> (Bool,Term,[Term])
deconstructAppN t 0 = (True,t,[])
deconstructAppN t n = let (ap1,t1,t2) = deconstructApp t
                          (ap2,t0,ts) = deconstructAppN t1 (n-1) in
                      (ap1 && ap2, t0, ts ++ [t2])

deconstructAppMax :: Term -> (Term,[Term])
deconstructAppMax t | isApp t = 
                      let (_,t1,t2) = deconstructApp t
                          (t0,ts) = deconstructAppMax t1 in
                      (t0, ts ++ [t2])
deconstructAppMax t = (t,[])

                        
deconstructGenAllMax :: Term -> ([ContextE],Term)
deconstructGenAllMax t | isGenAll t = 
                      let (_,it,cts,ts,u) = deconstructGenAll t
                          (its,v) = deconstructGenAllMax u in
                      (its ++ [mkGenDecl (it,cts,ts)], v)
deconstructGenAllMax t = ([],t)

deconstructArrowN :: Term -> Int -> (Bool,[Term],Term)
deconstructArrowN t 0 = (True, [], t)
deconstructArrowN t n = let (ok, t1, t2) = deconstructArrow t in
                        if ok then
                           doSnd3 (t1:) (deconstructArrowN t2 (n-1))
                        else
                           (False,[],t)

-- Extensions: Records:
deconstructRecValue :: Term -> (Bool,[(RecLabel,Term)])
deconstructRecValue (Nonb (RecValue ls) ts) = (True,zip ls ts)
deconstructRecValue _ = (False,[])

deconstructRecType :: Term -> (Bool,[(RecLabel,Term)])
deconstructRecType (Nonb (RecType ls) ts) = (True,zip ls ts)
deconstructRecType _ = (False,[])

deconstructRecSelect :: Term -> (Bool,Term,RecLabel)
deconstructRecSelect (Nonb (RecSelect l) [t]) = (True,t,l)
deconstructRecSelect _ = (False,dummyTerm,dummyRecLabel)
-- End Extension: Records


--------------------------------
-- HANDLING PLACE INFORMATION --
--------------------------------

-- There is a separate type for recording the place (in a line of text)
-- of subterms, i.e. where the term started and where it ends.
-- This is purely for giving nice error messages.
-- A place is a line number and place in line.

type Place = (Int,Int)
type PlaceInfo = (Place,Place)
-- Naming convention: pi

dummyPlace :: Place
dummyPlace = (0,0)
dummyPI :: PlaceInfo
dummyPI = (dummyPlace,dummyPlace)
                    

-- An InfoTree follows the structure of the term
data InfoTree = IT PlaceInfo [InfoTree]

instance Eq InfoTree where
      IT pi1 its1 == IT pi2 its2 = pi1 == pi2 && and (zipWith (==) its1 its2)

dummyIT :: InfoTree
dummyIT = IT dummyPI []

-- A term together with a tree of place-information
type TermIT = (Term,InfoTree)
                                 
dummyTermIT :: TermIT
dummyTermIT = (dummyTerm,dummyIT)
                         
forgetIT :: TermIT -> Term
forgetIT = fst

changeStart :: PlaceInfo -> TermIT -> TermIT         
changeStart (start,_) (t, IT (_,end) its) = (t, IT (start,end) its)
                                      
changeEnd :: PlaceInfo -> TermIT -> TermIT         
changeEnd (_,end) (t, IT (start,_) its) = (t, IT (start,end) its)
                                      
changeStartEnd :: PlaceInfo -> TermIT -> TermIT
changeStartEnd pi (t, IT _ its) = (t, IT pi its)
                                      
combinePlace :: PlaceInfo -> PlaceInfo -> PlaceInfo
combinePlace (start1,end1) (start2,end2) = (start1,end2)

combineIT :: InfoTree -> InfoTree -> PlaceInfo
combineIT (IT pi1 _) (IT pi2 _) = combinePlace pi1 pi2

-- termToTermIT makes an information tree for a term, with dummy place-info.
termToTermIT :: Term -> TermIT
termToTermIT t = (t,termToIT t)

termToIT :: Term -> InfoTree
termToIT (Basic bas) = dummyIT
termToIT (Nonb _ ts) = IT dummyPI (map termToIT ts)
termToIT (Bind _ ts (v,t,s) b) = 
     --            v           t        s           b         other
     IT dummyPI ([dummyIT, termToIT t, dummyIT, termToIT b]++map termToIT ts)

-------------------------------
-- M I S C E L L A N E O U S --
-------------------------------

data ErrorElem = ES String |           -- Just a string
                 EP PlaceInfo |        -- An indicated place
                 ET Term |             -- A term
                 ETP (Term,PlaceInfo)  -- A term with its place, can be used
                                       -- to give a nicer error message

type Error = [ErrorElem]

errConc :: Error -> String -> Error
errConc e s = e ++ [ES s]



-- user defined operators have a precedence of 1 .. maxPrec      
maxPrec :: Int
maxPrec = 9                                                


--               Sorts  Axioms        Rules              
type PTSystem = ([Sort],[(Sort,Sort)],[(Sort,Sort,Sort)],
                 -- Extension: Subtyping:
                 [Sort],[(Sort,Sort,Sort)])
--              SortsSub, RulesSub 
                 -- End Extension: Subtyping
                           
data Extension = -- Extension: Records:
                 Records
                 -- End Extension: Records

instance Eq Extension where
            -- Extension: Records:
            Records == Records = True
            -- End Extension: Records
            _ == _ = False
             
type SortEx = (Sort,Extension)

type ExSystem = [SortEx]

type System = (PTSystem,ExSystem)

