-- File: FancyTy
-- Description: This module contains the fancy type checking routine.
--              Fancy means that three things are inserted automatically:
--               - implicit arguments
--               - sort annotations in all kind of binders
--               - type annotations in local definitions (if absent)
--              This means that all these typing routines return the
--              complete term.
--              Furthermore nicer error message are given, because a term
--              is always paired with an InfoTree.

module FancyTy(PseudoTermIT, lContOkRet,
              inferTermRet, inferTypeRet, inferTypeSortRet, inferSortRet,
              oldVarG, checkDef, peelAll
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
import Typing
import Matchin


-------------------------------
-------------------------------
--  S M A R T   T Y P I N G  --
-------------------------------
-------------------------------

-- Smart typing means annotation and implicit arguments are filled in.

type PseudoTermIT = TermIT

-- checkDef si con term type  checks a definition clause of the form
--  v:= term:type  or v:=term  (in which case type is dummyTerm)
checkDef :: SyntaxInfo -> Context -> TermIT -> TermIT -> 
            E (Term,Term,PseudoSort)
checkDef si c term (typ,_) | typ == dummyTerm =
       inferTypeRet si c term
checkDef si c term typ =
       inferTypeRet si c term >>= \(term',typTerm,ps) ->
       -- is type a term? (type doesn't have to be typable!)
       inferTermRet si c typ >>= \(typ',_) ->
       if not (subtype si c typTerm typ') then
          typeErr [ES "Type ", eTI typ, ES " not equal to ", ET typTerm]
       else
          return (term',typ',ps)
    
-- Extension: Subtyping:
-- checkBound si con term type  checks a bound clause of the form
--  v <: term:type  or v <: term  (in which case type is dummyTerm)
-- we also check whether type lives in a subtyping sort!
checkBound :: SyntaxInfo -> Context -> TermIT -> TermIT -> 
            E (Term,Term,PseudoSort)
checkBound si c term (typ,_) | typ == dummyTerm =
       inferTypeRet si c term >>= \(term',typTerm,ps) ->
       checkSubtypingSortIT si "The type of " term ps >>
       return (term',typTerm,ps)
checkBound si c term typ =
       inferTypeRet si c term >>= \(term',typTerm,ps) ->
       inferTermRet si c typ >>= \(typ',_) ->
       if not (subtype si c typTerm typ') then
          typeErr [ES "Type ", eTI typ, ES " not equal to ", ET typTerm]
       else
          checkSubtypingSortIT si "" typ ps >>
          return (term',typ',ps)
-- End Extension: Subtyping
 
checkSubtypingSortIT :: SyntaxInfo -> String -> TermIT -> Sort -> E ()
checkSubtypingSortIT si txt t s = 
    if s `elem` extractSortsSub si then
        skip
    else
        typeErrTI txt t " does not live in a subtyping sort"
 
--------------
-- CONTEXTS --
--------------
   
-- contnOkRet checks whether the local context is OK
-- The first InfoTree is for the type occuring in the declaration, the
-- second for the definition or the bound.
-- If the InfoTree is dummy, we make the corresponding info-tree

lContOkRet :: SyntaxInfo -> Context -> LContext -> InfoTree -> InfoTree ->
              E LContext
lContOkRet si c lCon it1 it2 | isEmptyI lCon = return lCon
lContOkRet si c lCon it1 it2 = 
              let ce@(var,_) = headI lCon
                  tlCon = tailI lCon in
              lContOkRet si c tlCon it1 it2 >>= \tlCon' ->
              let totCon = tlCon' `addLoc` c in
              handle (conElemOkRet si totCon ce it1 it2)
              (\e -> err (init e ++ [ES (" at "++var), last e]))
              (\ce' -> return (ce' `addC` tlCon'))

conElemOkRet si c ce it1 it2 | isDecl ce = 
    let (_,(v,t,_)) = deconstructDecl ce  in
    fresh si c v >>
    inferSortRet si c (makeOkTerm (t,it1)) >>= \(t',s) ->
    return (mkDecl (v,t',s))
conElemOkRet si c ce it1 it2 | isDef ce = 
    let (_,(v,d,t,_)) = deconstructDef ce in
    checkDef si c (makeOkTerm (d,it2)) (makeOkTerm (t,it1)) >>= \(d',t',s) ->
    return (mkDef (v,d',t',s))
conElemOkRet si c ce it1 it2 | isSubDecl ce = 
    let (_,(v,b,t,_)) = deconstructSubDecl ce in
    checkBound si c (makeOkTerm (b,it2)) (makeOkTerm (t,it1)) >>= \(b',t',s) ->
    return (mkSubDecl (v,b',t',s))

makeOkTerm :: TermIT -> TermIT
makeOkTerm (t,it) | it == dummyIT = termToTermIT t
makeOkTerm tit | otherwise = tit

                                         
-----------------------------
-- I N F E R T Y P E R E T --
-----------------------------

-- inferTypeRet si c t is similar to inferType, but there are 2 differences:
-- - t may be a pseudo-term; all annotation and implicit arguments are
--     filled in, and the complete term is returned.
-- - all place annotation in t is deleted
--
-- inferTypeRet is intended to be used for terms fresh from the keyboard;
-- internally inferType should be used.
                
-- Some details about handling implicit arguments:
-- Implicit arguments can only occur between a variable and some (explicit)
-- arguments, and the implicit arguments are then derived from the explicit
-- arguments. So when typing application, a list of explicit arguments is
-- build up that only is used when typing a variable that has implicit
-- arguments.

-- inferTypeRet may be made more efficient by maintaining a list of
-- variables declared in the context.

-- inferTypeRet          |- t : T? : s?      t is typable, s may be top-sort
inferTypeRet :: SyntaxInfo -> Context -> PseudoTermIT ->
                E (Term,Term,PseudoSort) 

inferTypeRet si c (srt,it) | isSort srt =
                  let (_,s) = deconstructSort srt
                      (hasT,typeS) = axiom si s in
                  if not hasT then
                     typeErrTI "" (srt,it) " has no type"
                  else
                  return (srt,mkSrt typeS,typeSort si typeS)

inferTypeRet si c (vr,it) | isVar vr = 
                  let (_,v) = deconstructVar vr
                      (found,res) = findTypeSort c v in
                  if not found then
                     typeErrTI "Undeclared variable " (vr,it) ""
                  else
                  let  (typeV,sortV) = res in
                  return (vr,typeV,sortV)

inferTypeRet si c t@(app,_) | isApp app = 
                  inferTypeSortRetImp si c t []

inferTypeRet si c (abs,IT pi [_,tit,_,uit]) | isAbs abs =
   let (_,(oldv,_,_),_) = deconstructAbs abs
       abs' = changeVar abs (domCon c)
       (_,(v,t,_),u) = deconstructAbs abs' in
   inferSortRet si c (t,tit) >>= \(t',sortT) ->
   let it = (v,t',sortT) in
   inferTypeSortRet si (mkDecl it `addC` c) (u,uit) >>= \(u',typeU,sortU) ->
   let (ruleOk,sortA) = rule12 si sortT sortU in
   if not ruleOk then
       errorRule12 si (ETP (abs,pi)) sortT sortU
   else
   return (oldVar oldv mkAbs it u',mkAll it typeU,sortA)
     --  oldVar : restore renaming and delete place-info

-- Extension: Subtyping:
inferTypeRet si c (abs,IT pi [_,tit,_,uit,bit]) | isSubAbs abs = 
         let (_,(oldv,_,_,_),_) = deconstructSubAbs abs
             abs' = changeVar abs (domCon c)
             (_,(v,b,t,_),u) = deconstructSubAbs abs' in
         checkBound si c (b,bit) (t,tit) >>= \(b',typeB,sortB) ->
         let it = (v,b',typeB,sortB) in
         inferTypeSortRet si (mkSubDecl it `addC` c) (u,uit) 
                                                    >>= \(u',typeU,sortU) ->
         let (ruleOk,sortA) = ruleSub12 si sortB sortU in
         if not ruleOk then
             errorSubRule12 si (ETP (abs,pi)) sortB sortU
         else
         return (oldVarD oldv mkSubAbs it u',mkSubAll it typeU,sortA)
-- End Extension: Subtyping

inferTypeRet si c (all,IT pi [_,tit,_,uit]) | isAll all = 
         let (_,(oldv,_,_),_) = deconstructAll all
             all' = changeVar all (domCon c)
             (_,(v,t,_),u) = deconstructAll all' in
         inferSortRet si c (t,tit) >>= \(t',sortT) ->
         let it = (v,t',sortT) in
         inferSortRet si (mkDecl it `addC` c) (u,uit) >>= \(u',sortU) ->
         let (ruleOk,sortA) = rule12 si sortT sortU in
         if not ruleOk then
             errorRule12 si (ETP (all,pi)) sortT sortU
         else
         return (oldVar oldv mkAll it u',mkSrt sortA,typeSort si sortA)

-- Extension: Subtyping:
inferTypeRet si c (all,IT pi [_,tit,_,uit,bit]) | isSubAll all = 
         let (_,(oldv,_,_,_),_) = deconstructSubAll all
             all' = changeVar all (domCon c)
             (_,(v,b,t,_),u) = deconstructSubAll all' in
         checkBound si c (b,bit) (t,tit) >>= \(b',typeB,sortB) ->
         let it = (v,b',typeB,sortB) in
         inferSortRet si (mkSubDecl it `addC` c) (u,uit) >>= \(u',sortU) ->
         let (ruleOk,sortA) = ruleSub12 si sortB sortU in
         if not ruleOk then
             errorSubRule12 si (ETP (all,pi)) sortB sortU
         else
         return (oldVarD oldv mkSubAll it u',mkSrt sortA,typeSort si sortA)
-- End Extension: Subtyping

-- this clause is a combination of rules d-form and d-intro
inferTypeRet si c (delta,IT pi [_,tit,_,uit,dit]) | isDelta delta =   
    let (_,(oldv,_,_,_),_) = deconstructDelta delta
        delta' = changeVar delta (domCon c)
        (_,(v,d,t,_),u) = deconstructDelta delta' in
    checkDef si c (d,dit) (t,tit) >>= \(d',typeD,sortD) ->
    let it = (v,d',typeD,sortD) in
    inferTypeRet si (mkDef it `addC` c) (u,uit) >>= \(u',typeU,sortU) ->
    let u'' = oldVarD oldv mkDelta it u' in
    handle (redToSort' si c typeU (eTI (u,uit))) -- is u typable with a sort?
    (\_ -> return (u'',mkDelta it typeU, sortU))   -- No, then d-intro
    (\typeU2 -> return (u'', mkSrt typeU2, sortU)) -- Yes, then d-form

-- Extension: Records:
inferTypeRet si c (recValue,it@(IT pi its)) | isRecValue recValue =
       let (_,fields) = deconstructRecValue recValue
           (labels,ts) = unzip fields in
       if not (allDifferent labels) then
          typeErrTI "Term " (recValue,it) " has duplicate labels"
       else
       findSortOfRecords si (ETP (recValue,pi)) >>= \sortRec ->
       mapL (inferTypeRetFixedSort si c sortRec) (zip ts its) >>= \termtyps->
       let (terms,typs) = unzip termtyps in
       return (mkRecValue (zip labels terms),
               mkRecType  (zip labels typs), sortRec)

inferTypeRet si c (recType,it@(IT pi its)) | isRecType recType =
       let (_,fields) = deconstructRecType recType
           (labels,ts) = unzip fields in
       if not (allDifferent labels) then
          typeErrTI "Term " (recType,it) " has duplicate labels"
       else
       findSortOfRecords si (ETP (recType,pi)) >>= \sortRec ->
       mapL (inferSortRetFixedSort si c sortRec) (zip ts its) >>= \terms ->
       return (mkRecType (zip labels terms), 
               mkSrt sortRec, typeSort si sortRec)


inferTypeRet si c (recSelect,IT pi [it]) | isRecSelect recSelect =
       let (_,t,l) = deconstructRecSelect recSelect in
       inferTypeRet si c (t,it) >>= \(term,typ,sort) ->
       let typ' = bdswhnf c typ
           (isRec,fs) = deconstructRecType typ' 
           selected = filter ((l==).fst) fs in
       if not isRec then
          typeErrTI "Term " (t,it) " does not have a record-type"
       else
       if null selected then
          typeErrTI "Term " (t,it) (" does not have label "++l)
       else
       return (mkRecSelect term l, snd (head selected), sort)


inferTypeRetFixedSort :: SyntaxInfo -> Context -> Sort -> TermIT -> 
                         E (Term,Term)
inferTypeRetFixedSort si c srt t = 
       inferTypeRet si c t >>= \(term,typ,sort) ->
       if srt == sort then
          return (term,typ)
       else
          typeErrTI "Term " t (" doesn't have sort "++ printSortSt si srt)

inferSortRetFixedSort :: SyntaxInfo -> Context -> Sort -> TermIT -> E Term
inferSortRetFixedSort si c s1 t = 
       inferSortRet si c t >>= \(term,s2) ->
       if s1 == s2 then
          return term
       else
          typeErr [ES "Term ", eTI t, ES " doesn't have type ", ET (mkSrt s1)]
-- End Extension: Records:



-- inferTypeSortRetImp has an extra list, giving the arguments of the
-- application. This is used when these are applied to a variable with
-- implicit arguments
inferTypeSortRetImp :: SyntaxInfo -> Context -> PseudoTermIT -> 
                       [(Term,Sort)] -> E (Term,Term,Sort)
inferTypeSortRetImp si c (vr,it) args | isVar vr =
     inferTypeSortRet si c (vr,it) >>= \(_,t,s) ->
     let (_,v) = deconstructVar vr
         n = getImplicit si v 
         lArgs = length args
         types = peelAll si c t in
     -- When do we have implicit arguments ?
     -- Under the following conditions:
     -- 1. Option that arguments can be implicit is turned on
     -- 2. This variable can have implicit arguments
     -- 3. There are arguments
     -- 4. The (n+1)th sort in the type of the variable and 
     --    the sort of the first argument are equal
     if not (extractOptImplicit si) || n == 0 || lArgs == 0 ||
        snd (fst3 (snd (types!!n))) /= snd (head args) then
         return (vr,t,s)
     else
     let exCon = listToLocCon (reverse (take n types))
         restTypes = drop n types       -- the types corresponding to the
                                        -- explicit arguments, containing
                                        -- variables standing for the
                                        -- implicit arguments
         m = length args `min` length restTypes
         patterns = map (fst.fst3.snd) (take m restTypes) in
     -- catch errors !
     handle (inferImplicits si c exCon patterns
                    (map fst (take m args)))
     (\[ES mess] -> typeErrTI (mess++" for ") (vr,it) "")
     (\impl-> let term = foldl mkApp vr impl in
              inferTypeSort si c term >>= \(typ,sort) ->
              return (term,typ,sort))
         -- do an extra check, to ensure inference has found right
         -- arguments. This may be left out, but then the type of the
         -- application to the implicit arguments has to be determined here.

inferTypeSortRetImp si c (app,IT _ [tit,uit]) args | isApp app =
     -- this is the normal application rule for 't u',
     -- except that in typing 't', u is supplied so implicit arguments can
     -- be inserted
     let (_,t,u) = deconstructApp app in
     inferTypeSortRet si c (u,uit) >>= \(u',typeU,sortU) ->
     inferTypeSortRetImp si c (t,tit) ((typeU,sortU):args) 
                             >>= \(t',typeT,sortT) ->
     let typeT' = bdswhnf c typeT
         (isGenAll,(vr,typeU2,sortU2),constrs,cts,typeApp) = 
                                                 deconstructGenAll typeT' in
     if not isGenAll then
         typeErrTI "Term " (t,tit) " has no function type"
     else
     if not (subtype si c typeU typeU2) then
         typeErr [eTI (t,tit), ES " expects a ", ET typeU2, 
              ES " but is applied to ", eTI (u,uit), ES " with type ",
              ET typeU]
     else
     (case constrs of
           CNone -> return (rules13 si sortU sortT)
           CSub -> let [bound] = cts in
                   -- u has the proper type, and t sits in the proper sort
                   -- (otherwise the bounded quantification couldn't have
                   -- been made), so we can just check the subtyping.
                   if not (subtype si c u bound)
                   then 
                      typeErr [eTI (u,uit),ES " is not <: ", ET bound]
                   else return (rulesSub13 si sortU sortT)
     ) >>= \(resultSort:moreSorts) ->
     let resultType = subst typeApp vr u' in
     (if null moreSorts then
           -- the sort of the application must be resultSort
          return resultSort
      else -- the sort of the application can also be an element of
           -- moreSorts, so type 'resultType' to get the correct sort.
          inferSort si c resultType
     ) >>= \resultSort ->
     return (mkApp t' u',resultType,resultSort)  

          
-- for other terms, forget these arguments
inferTypeSortRetImp si c t args = inferTypeSortRet si c t
                        
-- oldVar v make i u  renames the variable in the item and deletes
--     the place-info
oldVar :: Vari -> (Item -> Term -> Term) -> Item -> Term -> Term
oldVar v make (v',t,s) u = 
    make (v,t,s) (subst u v' (mkVr v))

-- oldVarD v make i u  renames the variable in the item and deletes
--     the place-info 
oldVarD :: Vari -> (ItemD -> Term -> Term) -> ItemD -> Term -> Term
oldVarD v make (v',d,t,s) u = 
    make (v,d,t,s) (subst u v' (mkVr v))

-- oldVarG v make i u  renames the variable in the item and deletes
--     the place-info
oldVarG :: Vari -> ((Item,Constraints,[Term]) -> Term -> Term) -> 
           (Item,Constraints,[Term]) -> Term -> Term
oldVarG v make ((v',t,s),cts,ts) u = 
    make ((v,t,s),cts,ts) (subst u v' (mkVr v))

      
      

               

-----------------------------------------------------
-- O T H E R   I N F E R E N C E   R O U T I N E S --
-----------------------------------------------------

-- inferTypeSortRet    |- t : T? : s?        t is typable and has a sort
--                                           (the sort is not top-sort)
inferTypeSortRet :: SyntaxInfo -> Context -> PseudoTermIT -> 
                    E (Term,Term,Sort)
inferTypeSortRet si c t = 
                          inferTypeRet si c t >>= \(t',typ,psort) ->
                          if not (isProperSort psort) then
                             typeErrTI "" t " has no sort"
                          else
                          return (t',typ,psort)

-- inferSortRet       |- t : s?             t is typable with a sort
inferSortRet :: SyntaxInfo -> Context -> PseudoTermIT -> E (Term,Sort)
inferSortRet si c t = inferTypeRet si c t >>= \(t',sortT,_) ->
                      redToSort' si c sortT (eTI t) >>= \sortT2 ->
                      if not (isProperSort sortT2) then
                         typeErrTI "" t " has no type"
                      else
                      return (t',sortT2)

-- inferTermRet      |- t : T?       t is a term (because T may be top-sort)
inferTermRet :: SyntaxInfo -> Context -> PseudoTermIT -> E (Term,PseudoTerm)
inferTermRet si _ (srt,_) | isSort srt = 
           let (_,s) = deconstructSort srt in
           if not (isProperSort s) then
              internalErr ("Topsort isn't supposed to be made by user.")
           else
           return (srt, mkSrt (typeSort si s))
inferTermRet si c t = inferTypeRet si c t >>= \(t',typ,_) ->
                      return (t',typ)


-------------------------------------------------------------------
-- R O U T I N E S   F O R   I M P L I C I T   A R G U M E N T S --
-------------------------------------------------------------------

-- peelAll term   returns the 'context' of all pi's at the head of the term
-- This context is in reverse order.
-- E.g. peelAll '@A:*. @x:A. ..' = [A:*,x:A]
peelAll :: SyntaxInfo -> Context -> Term -> [ContextE]
peelAll si c term0 = 
    let term = bdwhnf c term0 in
    if isGenAll term then
       let term' = changeVar term (domCon c)
           (_,it,cts,ts,u) = deconstructGenAll term'
           ce = mkGenDecl (it,cts,ts) in
        ce : peelAll si (ce `addC` c) u
    else []


-- inferImplicits si c exCon pats terms  matches all patterns pats with
--         terms to find a substitution for the variables in exCon.
-- example:
-- inferImplicits si c [A:*:>>,B:*:>>,C:*:>>] [B->C,A->B] [Int->Real,Nat->Int]
-- should deliver [Nat,Int,Real]
-- inferImplicits may only deliver string errors 
inferImplicits :: SyntaxInfo -> Context -> LContext ->
                  [Term] -> [Term] -> E [Term]
inferImplicits si c exCon pats terms =
             let totalCon = exCon `addLoc` c
                 problems = zip4 (repeat totalCon) (repeat exVars) pats terms
                 exVars = domDeclLCon exCon
                 substs = matchSupers alwaysUnfold si problems
                 subst = head substs
                 notFoun = notFound exVars subst in
             if null substs then
                errS "Inference of implicit arguments didn't succeed"
             else                
             if not (null notFoun) then 
                errS ("Couldn't infer implicit arguments " ++
                      printVarListSt si (removeDoubles notFoun))
             else
                return (map (applySubst subst . mkVr) (reverse exVars))
