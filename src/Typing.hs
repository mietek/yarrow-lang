-- File: Typing
-- Description: This module contains the type-checking routine.

module Typing(PseudoTerm, PseudoSort, admitSystem, freshG, fresh, contnOk,
              inferTerm, inferType, findSortOfRecords,
              inferTypeSort, inferSort,
              errorRule12, errorSubRule12, deconstructWhnfAll, 
              redToSort, redToSort', subtype,
              typeErr, typeErrTI
              ) where

import HaTuple
import General
import Collect
import HaMonSt
import Basic
import Paths
import PTSys
import Reduce
import SyntaxI

-- type checking for bijective and functional PTS's with subtyping,
-- as given by 
-- Section !!!.!!! of my thesis
-- here the |-sd relation is implemented, and extended with definitions
-- and implicit arguments. This type-checker is complete for bijective
-- PTS's with subtyping                                 
--
-- NOTE: The algorithm for functional PTS's is not proved complete. So there
--       could be terms that are typable but are not recognized as such by
--       this typing algorithm.

-- Important features of the type-checking algorithm are:
-- 1) The algorithm doesn't only deliver the type of a term, but also the
--    sort of the term. Since some terms don't have a sort, the set of sorts
--    is extended with a so-called top-sort, which can be assigned to those
--    terms which don't have a proper sort.
-- 2) It is most efficient when handling bijective type-systems.
--    A type-system is bijective
--    iff the following properties hold:
--      a) (s1,s2) in A, (s1,s3) in A => s2 = s3
--      b) (s1,s2,s3) in R, (s1,s2,s3) in R => s3 = s3'
--      c) (s1,s2,s3) in R, (s1,s2',s3) in R => s2 = s2'
--      d) (s1,s2,s3) in Rsub, (s1,s2,s3) in Rsub => s3 = s3'
--      e) (s1,s2,s3) in Rsub, (s1,s2',s3) in Rsub => s2 = s2'
--    The properties c and e distinguish bijective from functional
--    (or single-sorted, which is the same).


-- In the rest of this program, PseudoTerm stands for any term, whereas 
-- Term stands for typed (or inhabited) terms, that are completely
-- annotated with the sorts of variables in binders, and for which all 
-- implicit arguments are inserted.
-- So the parser delivers PseudoTerms, and the typing routine makes from
-- a PseudoTerm a Term.
-- This distinction is purely for the programmer; the Gofer type-checker
-- doesn't distinguish between the two!
type PseudoTerm = Term

-- Likewise for contexts, PseudoContext stands for any context,
-- and Context for well-formed contexts.
type PseudoContext = GContext

-- 
-- Likewise, in the rest of this program, PseudoSort stands for any
-- syntactic sort (including the top-sort), and Sort stands for any proper
-- sort (in the definition of the type-system, so excluding the top-sort)
type PseudoSort = Sort

{-
-- The most important EXPORTS are:

-- A set of typing routines (where s is a Sort)
inferTerm            |- t : T         t is a term (because T may be top-sort)
inferType            |- t : T         t is typable 
inferTypeSort        |- t : T : s     t is typable and has a sort
inferSort            |- t : s         t is typable with a sort

-}

-----------------------------------------------
-- A D M I T T E D   T Y P E - S Y S T E M S --
-----------------------------------------------

admitSystem :: PreErrorMonad m => System -> m ()
admitSystem (pts,exS) =
  if not (functional pts) then
     genErrS "I can handle only functional type systems"
  else   
  -- Extension: Records:
  if exS `hasMultiple` Records then
     genErrS "Records may be used for only one sort"
  else
  -- End Extension: Records:
  if not (fmap fst3 (ffh5 pts) `sublist` fth5 pts) then
     genErrS "Bounded quantifications only admitted for subtyping sorts"
  else
  -- End Extension: Records:
     skip

functional :: PTSystem -> Bool
functional (_,axioms,rules,_,rulesSub) = 
        let axiomOk s = length (findAll axioms s) == 1
            rules1 = fmap (\(s1,s2,s3) -> ((s1,s2),s3)) rules 
            rulesSub1 = fmap (\(s1,s2,s3) -> ((s1,s2),s3)) rulesSub 
            ruleOk rs ss = length (findAll rs ss) == 1 
            rulesOk rs = all (ruleOk rs . fst) rs in
        all (axiomOk . fst) axioms && 
        rulesOk rules1 &&
        rulesOk rulesSub1                             

hasMultiple :: ExSystem -> Extension -> Bool
hasMultiple exs ext = length (filter ((ext==).snd) exs) > 1
        

selectEx :: Extension -> [(sr,Extension)] -> [sr]
selectEx ext = fmap fst . filter ((ext==).snd)

----------------------------------------------------
-- T Y P E  C H E C K I N G  &  I N F E R E N C E --
----------------------------------------------------

-- Type checking is divided in two main routines.
-- One for checking that a context is well-formed (contOk), and one for 
-- infering the type of a term in a well-formed context (inferType)
           
--------------
-- CONTEXTS --
--------------
   
  
-- freshG checks whether a variable is fresh in a global context
freshG :: SyntaxInfo -> GContext -> Vari -> E ()
freshG si c v = if v `elemC` domGCon c then
                   genErrS ("Ident "++printVarSt si v++" already declared")
                else
                   skip
       
-- fresh checks whether a variable is fresh in a context
-- unfortunately, we can't make this function more polymorphic
fresh :: SyntaxInfo -> Context -> Vari -> E ()
fresh si c v = if v `elemC` domCon c then
                  genErrS ("Ident "++printVarSt si v++" already declared")
               else
                  skip
       
-- contnOk checks whether the first n items of the context are OK
contnOk :: SyntaxInfo -> Int -> PseudoContext -> E ()
contnOk si 0 c = skip
contnOk si n c | isEmptyI c = skip
contnOk si n c = 
              let ce = headI c
                  c' = tailI c
                  tc' = globToTot c' in
              contnOk si (n-1) c' >>
              declOk si tc' ce

declOk :: SyntaxInfo -> Context -> ContextE -> E ()
declOk si c ce | isDecl ce =  
              let (_,(v,t,s)) = deconstructDecl ce in
              fresh si c v >>
              inferSort si c t >>= \tS ->
              checkSortsEqual s tS
declOk si c ce | isSubDecl ce =
              let (_,(v,bound,t,s)) = deconstructSubDecl ce in
              fresh si c v >>
              inferType si c bound >>= \(boundT,boundS) ->
              inferType si c t >>= \_ ->
              checkSubtypingSort si bound s >>
              checkSubtype si c boundT t
declOk si c ce | isDef ce =
              let (_,(v,d,t,s)) = deconstructDef ce in
              fresh si c v >>
              inferType si c d >>= \(dT,dS) ->
              inferTerm si c t >>= \tS ->
              checkSortsEqual s dS >>
              checkSubtype si c dT t

checkSubtypingSort :: SyntaxInfo -> Term -> Sort -> E ()
checkSubtypingSort si t s = if s `elem` extractSortsSub si then
                                skip
                            else
                                typeErrT "" t (" does not live in a " ++
                                               "subtyping sort")


-----------------------
-- I N F E R T Y P E --
-----------------------

-- inferType si c t  checks whether the term t is typable in
-- context c, that must be well-formed. It returns its type and its
-- sort (which may be the top-sort). We assume that t is fully
-- annnotated and has no implicit arguments.

-- inferType is intended to be used internally; use inferRetType in
-- module FancyTy to type terms fresh from the keyboard.
                 

     
-- inferType          |- t : T? : s?      t is typable, s may be top-sort
inferType :: SyntaxInfo -> Context -> PseudoTerm -> E (Term,PseudoSort) 

inferType si c srt | isSort srt =
                    let (_,s) = deconstructSort srt
                        (hasT,typeS) = axiom si s in
                    if not hasT then
                       typeErrT "" srt " has no type"
                    else
                    return (mkSrt typeS,typeSort si typeS)

inferType si c vr | isVar vr = 
                     let (_,v) = deconstructVar vr
                         (found,ts) = findTypeSort c v in
                     if not found then
                        typeErrT "Undeclared variable " vr ""
                     else
                     return ts

inferType si c app | isApp app = 
    let (_,t,u) = deconstructApp app in
    inferTypeSort si c u >>= \(typeU,sortU) ->
    inferTypeSort si c t >>= \(typeT,sortT) ->
    let typeT' = bdswhnf c typeT
        (isGenAll,(vr,typeU2,sortU2),constrs,cts,typeApp) = 
                                                 deconstructGenAll typeT' in
    if not isGenAll then
        typeErrT "Term " t " has no function type"
    else
    if not (subtype si c typeU typeU2) then
        typeErr [ET t, ES " expects a ", ET typeU2, ES " but is applied to ",
                 ET u, ES " with type ", ET typeU]
    else         
    (case constrs of
          CNone -> return (rules13 si sortU sortT)
          CSub -> let [bound] = cts in
                  -- u has the proper type, and t sits in the proper sort
                  -- (otherwise the bounded quantification couldn't have
                  -- been made), so we can just check the subtyping.
                  if not (subtype si c u bound)
                  then typeErrTT "" u " is not <: " bound ""
                  else return (rulesSub13 si sortU sortT)
    ) >>= \(resultSort:moreSorts) ->
    let resultType = subst typeApp vr u in
    (if null moreSorts then
          -- the sort of the application must be resultSort
         return resultSort
     else -- the sort of the application can also be an element of
          -- moreSorts, so type 'resultType' to get the correct sort.
         inferSort si c resultType
    ) >>= \resultSort ->
    return (resultType,resultSort)

inferType si c abs | isAbs abs =                     
         let (_,(oldv,_,_),_) = deconstructAbs abs
             abs' = changeVar abs (domCon c)
             (_,it@(_,t,sortT),u) = deconstructAbs abs' in
         inferSort si c t >>= \sortT' ->
         checkSortsEqual sortT sortT' >>
         inferTypeSort si (mkDecl it `addC` c) u >>= \(typeU,sortU) ->
         let (ruleOk,sortA) = rule12 si sortT sortU in
         if not ruleOk then
             errorRule12 si (ET abs) sortT sortU
         else
         return (mkAll it typeU,sortA)

-- Extension: Subtyping:
inferType si c abs | isSubAbs abs = 
         let (_,(oldv,_,_,_),_) = deconstructSubAbs abs
             abs' = changeVar abs (domCon c)
             (_,it@(v,b,t,sortT),u) = deconstructSubAbs abs' in
         inferType si c b >>= \(typeB,sortB) ->
         inferType si c t >>= \_ ->
         checkSubtype si c typeB t >>
         inferTypeSort si (mkSubDecl it `addC` c) u >>= \(typeU,sortU) ->
         let (ruleOk,sortA) = ruleSub12 si sortT sortU in
         if not ruleOk then
             errorSubRule12 si (ET abs) sortT sortU
         else
         return (mkSubAll it typeU,sortA)
-- End Extension: Subtyping

inferType si c all | isAll all = 
         let (_,(oldv,_,_),_) = deconstructAll all
             all' = changeVar all (domCon c)
             (_,it@(_,t,sortT),u) = deconstructAll all' in
         inferSort si c t >>= \sortT' ->
         checkSortsEqual sortT sortT' >>
         inferSort si (mkDecl it `addC` c) u >>= \sortU ->
         let (ruleOk,sortA) = rule12 si sortT sortU in
         if not ruleOk then
             errorRule12 si (ET all) sortT sortU
         else
         return (mkSrt sortA,typeSort si sortA)

-- Extension: Subtyping:
inferType si c all | isSubAll all = 
         let (_,(oldv,_,_,_),_) = deconstructSubAll all
             all' = changeVar all (domCon c)
             (_,it@(v,b,t,sortT),u) = deconstructSubAll all' in
         inferType si c b >>= \(typeB,sortB) ->
         inferType si c t >>= \_ ->
         checkSubtype si c typeB t >>
         checkSortsEqual sortT sortB >>
         inferSort si (mkSubDecl it `addC` c) u >>= \sortU ->
         let (ruleOk,sortA) = ruleSub12 si sortT sortU in
         if not ruleOk then
             errorSubRule12 si (ET all) sortT sortU
         else
         return (mkSrt sortA,typeSort si sortA)
-- End Extension: Subtyping

-- this clause is a combination of rules d-form and d-intro
inferType si c delta | isDelta delta =   
       let (_,(oldv,_,_,_),_) = deconstructDelta delta
           delta' = changeVar delta (domCon c)
           (_,it@(v,d,typeD,sortD),u) = deconstructDelta delta' in
       inferType si c d >>= \(typeD',sortD') ->
       checkSortsEqual sortD sortD' >>
       inferTerm si c typeD >>= \_ ->
       checkSubtype si c typeD' typeD >>
       inferType si (mkDef it `addC` c) u >>= \(typeU,sortU) ->
       handle (redToSort' si c typeU (ET u))     -- is u typable with a sort?
       (\_ -> return (mkDelta it typeU, sortU))  -- No, then d-intro
       (\typeU2 -> return (mkSrt typeU2, sortU)) -- Yes, then d-form
                                      
-- Extension: Records:
inferType si c recValue | isRecValue recValue =
       let (_,fields) = deconstructRecValue recValue
           (labels,ts) = unzip fields in
       if not (allDifferent labels) then
          typeErrT "Term " recValue " has duplicate labels"
       else
       findSortOfRecords si (ET recValue) >>= \sortRec ->
       mapL (inferTypeFixedSort si c sortRec) ts >>= \typs ->
       return (mkRecType (zip labels typs), sortRec)

inferType si c recType | isRecType recType =
       let (_,fields) = deconstructRecType recType
           (labels,ts) = unzip fields in
       if not (allDifferent labels) then
          typeErrT "Term " recType " has duplicate labels"
       else
       findSortOfRecords si (ET recType) >>= \sortRec ->
       maplComs (inferSortFixedSort si c sortRec) ts >>
       return (mkSrt sortRec, typeSort si sortRec)

inferType si c recSelect | isRecSelect recSelect =
       let (_,t,l) = deconstructRecSelect recSelect in
       inferType si c t >>= \(typ,sort) ->
       let typ' = bdswhnf c typ
           (isRec,fs) = deconstructRecType typ' 
           selected = filter ((l==).fst) fs in
       if not isRec then
          typeErrT "Term " t " does not have a record-type"
       else
       if null selected then
          typeErrT "Term " t (" does not have label "++l)
       else
       return (snd (head selected), sort)

inferTypeFixedSort :: SyntaxInfo -> Context -> Sort -> Term -> E Term
inferTypeFixedSort si c srt t = 
       inferType si c t >>= \(typ,sort) ->
       if srt == sort then
          return typ
       else
          typeErrT "Term " t (" doesn't have sort "++ printSortSt si srt)

inferSortFixedSort :: SyntaxInfo -> Context -> Sort -> Term -> E ()
inferSortFixedSort si c s1 t = 
       inferSort si c t >>= \s2 ->
       if s1 == s2 then 
          return ()
       else
          typeErrTT "Term " t " doesn't have type " (mkSrt s1) ""

findSortOfRecords :: SyntaxInfo -> ErrorElem -> E Sort
findSortOfRecords si errorElem = 
                    findSortOfExt si Records 
                    [ES "No records ",errorElem,ES " in this type system"]
-- End Extension: Records:

findSortOfExt :: SyntaxInfo -> Extension -> Error -> E Sort
findSortOfExt si ext error = 
                    let ss = filter ((ext==).snd) (extractExSys si) in
                    if null ss then
                       typeErr error
                    else
                       return (fst (head ss))
       
checkSortsEqual :: Sort -> Sort -> E ()
checkSortsEqual s t = if s==t then
                         skip
                      else
                         internalErr "Sort annotation not correct"
                            
checkSubtype :: SyntaxInfo -> Context -> Term -> Term -> E ()
checkSubtype si c t u = if subtype si c t u then
                            skip
                        else
                            internalErr "Type or sort annotation not correct"
 
-----------------------------------------------------
-- O T H E R   I N F E R E N C E   R O U T I N E S --
-----------------------------------------------------

-- inferTypeSort    |- t : T? : s?            t is typable and has a sort
inferTypeSort :: SyntaxInfo -> Context -> Term -> E (Term,Sort) 
inferTypeSort si con t = inferType si con t >>= \(typ,psort) ->
                         if not (isProperSort psort) then
                            typeErrT "" t " has no sort"
                         else
                         return (typ,psort)
                                        
-- inferSort        |- t : s?                  t is typable with a sort
inferSort :: SyntaxInfo -> Context -> Term -> E Sort
inferSort si con t = inferType si con t >>= \(sortT,_) ->
                     redToSort' si con sortT (ET t) >>= \sortT2 ->
                     if not (isProperSort sortT2) then
                        typeErrT "" t " has no type"
                     else
                     return sortT2

-- inferTerm            |- t : T?     t is a term, because T may be top-sort
inferTerm :: SyntaxInfo -> Context -> PseudoTerm -> E PseudoTerm
inferTerm si _ srt | isSort srt = 
           let (_,s) = deconstructSort srt in
           if not (isProperSort s) then
              internalErr ("Topsort isn't supposed to be made by user.")
           else
              return (mkSrt (typeSort si s))
inferTerm si con  t = fmap fst (inferType si con t)

-------------------
-- MISCELLANEOUS --
-------------------

errorRule12 :: SyntaxInfo -> ErrorElem -> Sort -> Sort -> E a
errorRule12 si ee s1 s2 = 
          typeErr [ee, ES (" cannot be formed since there is no rule " ++
                           printRule12St si s1 s2)]
           
-- Extension: Subtyping:
errorSubRule12 :: SyntaxInfo -> ErrorElem -> Sort -> Sort -> E a
errorSubRule12 si ee s1 s2 = 
          typeErr [ee, ES (" cannot be formed since there is no <: rule " ++
                           printRule12St si s1 s2)]
-- End Extension: Subtyping
           
-- deconstructWhnfAll checks if a term, reduced to weak head normal form,
-- is an All construct and delivers the variable, its type and sort,
-- and the body
deconstructWhnfAll :: Context -> Term -> (Bool,(Vari,Term,Sort),Term)
deconstructWhnfAll c t = deconstructAll (bdwhnf c t)
      
        
                                     
-- redToSort checks whether a term bds-reduces to a sort
-- (and delivers that sort)
redToSort :: SyntaxInfo -> Context -> Term -> E Sort
redToSort si c t =
                 let t' = bdswhnf c t
                     (isSort,s) = deconstructSort t' in
                 if isSort && isProperSort s then
                    return s
                 else
                    typeErrT "" t " is no sort"
       
-- redToSort' does the same, but generates a nicer error message
-- when an inhabitant of the type is given        
redToSort' :: SyntaxInfo -> Context -> Term -> ErrorElem -> E Sort
redToSort' si c t ee =
                 let t' = bdswhnf c t
                     (isSort,s) = deconstructSort t' in
                 if isSort && isProperSort s then
                    return s
                 else
                    typeErr [ES "The type of ", ee, ES " is ", ET t,
                             ES " which is not a sort"]

          
-----------------------------------------------
--   E X T E N S I O N : S U B T Y P I N G   --
-----------------------------------------------

-- The current implementation of the subtype routine is very inefficient.

-- Extension: Subtyping:
-- Precondition for subtype si c t1 t2: t1 and t2 are well-formed terms in c.
subtype :: SyntaxInfo -> Context -> Term -> Term -> Bool
subtype si c t1 t2 | hasSubtyping si = 
    subtype' si c (bdwhnf c t1) (bdwhnf c t2)
subtype si c t1 t2 | otherwise =
    bdEqual c t1 t2

-- Precondition: t1 and t2 in bdwhnf, there is subtyping
subtype' si c t1 t2 | bdEqual c t1 t2 = True       
-- Extension: Records:
subtype' si c t1 t2 | isRecType t1 && isRecType t2 =
         let (_,lts1) = deconstructRecType t1
             (_,lts2) = deconstructRecType t2
             fieldSub (l,t2f) = let (existsF,t1f) = findAL lts1 l in
                                existsF && subtype si c t1f t2f in
         all fieldSub lts2
-- End Extension: Records
subtype' si c t1 t2 | isAbs t1 && isAbs t2=
         let (_,(v1,typ1,s1),u1) = deconstructAbs t1
             (_,(v2,typ2,s2),u2) = deconstructAbs t2 in
         bdEqual c typ1 typ2 &&
         (let (v12,u1',u2') = equateVarsBinders (domCon c) (v1,u1) (v2,u2)
              c' = mkDecl (v12,typ2,s2) `addC` c in
          subtype si c' u1' u2')
{- No subtyping on bounded abstractions
subtype' si c t1 t2 | isSubAbs t1 && isSubAbs t2=
         let (_,(v1,b1,typ1,s1),u1) = deconstructSubAbs t1
             (_,(v2,b2,typ2,s2),u2) = deconstructSubAbs t2 in
         bdEqual c b1 b2 &&
         (let (v12,u1',u2') = equateVarsBinders (domCon c) (v1,u1) (v2,u2)
              c' = mkSubDecl (v12,b2,typ2,s2) `addC` c in
          subtype' si c' u1' u2')
-}
subtype' si c t1 t2 | isAll t1 && isAll t2=
         let (_,(v1,typ1,s1),u1) = deconstructAll t1
             (_,(v2,typ2,s2),u2) = deconstructAll t2 in
         subtype si c typ2 typ1 &&
         (let (v12,u1',u2') = equateVarsBinders (domCon c) (v1,u1) (v2,u2)
              c' = mkDecl (v12,typ2,s2) `addC` c in
          subtype si c' u1' u2')
subtype' si c t1 t2 | isSubAll t1 && isSubAll t2=
         let (_,(v1,b1,typ1,s1),u1) = deconstructSubAll t1
             (_,(v2,b2,typ2,s2),u2) = deconstructSubAll t2 in
         bdEqual c b1 b2 &&  
         bdEqual c typ1 typ2 &&
         (let (v12,u1',u2') = equateVarsBinders (domCon c) (v1,u1) (v2,u2)
              c' = mkSubDecl (v12,b2,typ2,s2) `addC` c in
          subtype si c' u1' u2')
subtype' si c t1 t2 = let (reduces,t1') = swhRed c t1 in
                      reduces && subtype' si c (bdwhnf c t1') t2
-- End Extension: Subtyping

typeErrSuffix :: String         
typeErrSuffix = " (type error)"
                                                             
typeErr :: Error -> E a
typeErr e = err (e ++ [ES typeErrSuffix])

typeErrS :: String -> E a
typeErrS s = typeErr [ES s]

typeErrT :: String -> Term -> String -> E a
typeErrT s1 t s2 = typeErr [ES s1, ET t, ES s2]

typeErrTT :: String -> Term -> String -> Term -> String -> E a
typeErrTT s1 t1 s2 t2 s3 = typeErr [ES s1, ET t1, ES s2, ET t2, ES s3]

typeErrTI :: String -> TermIT -> String -> E a
typeErrTI s1 t s2 = typeErr [ES s1, eTI t, ES s2] 
