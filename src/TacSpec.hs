-- File: TacSpec
-- Description: This module defines the special tactics for the 
--   prove-mode of the proof assistant.
--   Special tactics are tactics that use some fixed lemma.

module TacSpec(qGiveUseFor, qUseFor,
               rewriteRToL, rewriteLToR, rewriteRToLin, rewriteLToRin, reflTac,
               andITac, andELTac, andERTac, andETac,
               orILTac, orIRTac, orETac, notITac, notETac, falseETac,
               existsITac, existsETac) where

import HaTuple
import General
import Collect
import HaMonSt
import Basic
import Paths
import SyntaxI
import Typing
import Matchin
import FancyTy(PseudoTermIT)
import Reduce
import ProvDat
import MainSta
import YarMsg
import GenComs
import Tactics
import Tactals

-------------------------------------------------
--   T A C T I C S   F O R   E Q U A L I T Y   --
-------------------------------------------------

-- rewriteRToL t (path,n) rewrites the subterm g' of goal indicated by path
-- with equality t
-- it finds the nth subterm of t' of the form
-- (left-hand-side of t), and rewrites it to the right hand side
-- any hypotheses in the equality become new goals
rewriteRToL :: (TermPath,Int) -> ExtTermTS -> Tactic
rewriteRToL = rewriteGen False


-- rewriteLToR t (path,n) rewrites the subterm g' of goal indicated by path
-- with equality t
-- it finds the nth subterm of t' of the form
-- (right-hand-side of t), and rewrites it to the left hand side
rewriteLToR :: (TermPath,Int) -> ExtTermTS -> Tactic
rewriteLToR = rewriteGen True

rewriteRToLin :: (TermPath,Int) -> Vari -> ExtTermTS -> Tactic
rewriteRToLin = rewriteGenIn False

rewriteLToRin :: (TermPath,Int) -> Vari -> ExtTermTS -> Tactic
rewriteLToRin = rewriteGenIn True

-- Not very efficient implementation
rewriteGenIn :: Bool -> (TermPath,Int) -> Vari -> ExtTermTS -> Tactic
rewriteGenIn lToR (p,n) hyp extTerm qd@(goal,locCon,gi,totCon) =
          let (foundHyp,tsHyp) = findTypeSort locCon hyp in
          if not foundHyp then
             genErrS ("No variable "++hyp++" in local context")
          else
             (firstTac tsHyp `thenTac` 
              [exact (mkVr hyp,fst tsHyp,snd tsHyp),
               -- rewrite only left of arrow. Bit of a hack.
               rewriteGen lToR (1:p,n) extTerm `thenLastTac`
               intro]) qd
              

-- rewriteGen  rewrites in the indicated direction.
-- In fact, rewrite is almost the same as pattern lhs followed by apply term.
rewriteGen :: Bool -> (TermPath,Int) -> ExtTermTS -> Tactic
rewriteGen lToR occ extTerm (goal,locCon,gi,totCon) =
    doExtTermEq extTerm totCon >>= \(term,exCon,typ,sigma) ->
    fetchSyn >>= \si ->  
    let (isConn, args) = deconstructAppMax typ
        (ok1,isConnective) = deconstructVar isConn
        len = length args
        ok2 = len >= 2
        lhs = args !! (len-2)
        rhs = args !! (len-1)
        restArgs = take (len-2) args
        (search,repl) = if lToR then (lhs,rhs) else (rhs,lhs) in
    if not (ok1 && ok2) then
       errTermWrongForm
    else
    let exTotCon = exCon `addLoc` totCon in
    getType exTotCon (foldl mkApp isConn restArgs) >>= \(eqPiType,_) ->
    let (_,(_,lhsType,lhsSort),_) = deconstructAll eqPiType in
    -- getType exTotCon lhs >>= \(lhsType,lhsSort) ->
    getSort totCon goal >>= \resultSort ->
    let var = findNiceFree lhsSort 
                      (occurVar goal +++ domCon totCon) dummyVar in
    makePatternPat si lToR totCon goal (exCon, search) var lhsType
                   lhsSort occ >>= \(sigma',apppred) ->
    let (_,pred,_) = deconstructApp apppred
        lhs' = applySubst sigma' lhs
        rhs' = applySubst sigma' rhs
        restArgs' = map (applySubst sigma') restArgs
        exCon' = applyLConSubst sigma' exCon in
    rewrite1Subst term exCon' (sigma++sigma') isConnective restArgs'
                  lhs' rhs' pred lToR resultSort (goal,locCon,gi,totCon)
    

doExtTermEq :: ExtTermTS -> Context -> M (Term, LContext, Term, Subst)
doExtTermEq ((term,typ,sort),termtyps) totCon =
     fetchSyn >>= \si ->
     let termtyps' = forgetSorts termtyps
         trips = combinePrems alwaysUnfold si totCon typ termtyps' in
     checkExtSolutions trips >>
     let (exCon,typ',sigma) = head trips -- only use first solution.
                                         -- maybe it's useful to try all
                                         -- solutions.
         -- peel off last pi's
         (exCon',typ'') = shiftPrem totCon (exCon,typ') in 
     return (term, exCon', typ'', sigma)

 
rewrite1Subst :: Term -> LContext -> Subst -> Vari ->
                 [Term] -> Term -> Term -> Term -> Bool -> Sort -> 
                 Tactic
rewrite1Subst term exCon sigma eqVar typeArgs lhs rhs
              pred lToR resultSort (goal,locCon,gi,totCon) =
   checkExConConcl (exCon,sigma) >>
   let tacName = if lToR then rewriteName else lewriteName
       repl = if lToR then rhs else lhs in
   findSpecialLemma (eqVar,tacName,[resultSort]) >>= \isEProof ->
   -- Making the proof term:
   -- We abuse the pAppQQ and pAppGQ tactics a bit, since we don't give
   -- a proper type as argument (but dummySort and dummyTerm respectively).
   -- This is no problem, since immediately a term corresponding to the type
   -- is given.
   -- The proof term is "isEProof lhsType lhs rhs pred (term ?2 .. ?n) ?1"
   -- where ?2 .. ?n are made by apply1Subst
   (pAppQQ (bnfNC (pred `mkApp` repl),dummySort) `then1Tac`
    let totalEProof = foldl mkApp isEProof typeArgs `mkApp`
                                            lhs `mkApp` rhs `mkApp` pred in
    pAppGQ dummyTerm totalEProof `then1Tac`
    makeProof term (exCon,sigma)
   ) (goal,locCon,gi,totCon)             


rewriteName = "Rewrite"
lewriteName = "Lewrite"


-- roughly, 'apply is_refl'
reflTac :: Tactic
reflTac (goal,locCon,gi,totCon) =
       let (isConn,args) = deconstructAppMax goal 
           (ok,isConnective) = deconstructVar isConn in
       if not ok then errGoalWrongForm else
       findSpecialLemma (isConnective,reflName,[]) >>= \reflP ->
       getType totCon reflP >>= \(reflT,reflS) ->
       -- onlyTermUnfold makes sure that the equality eq in 'eq x x'
       -- is never unfolded. Unfolding the term is allowed, so all
       -- bd-convertible terms are considered equal.
       handleS (primApplyMaxTac onlyTermUnfold (reflP,reflT,reflS) 
                                         (goal,locCon,gi,totCon))
       (\errMess -> genErrS "Terms are not bd-convertible")
       return

reflName = "Refl"





-------------------------------------------------
--  P R O P O S I T I O N A L   T A C T I C S  --
-------------------------------------------------

-- all these tactics (except AndE) use (prim)ApplyMaxTax.
-- In all elimination tactics, the matching options are neverUnfold,
-- in all introduction tactics, the matching options are onlyTermUnfold.
           
-- 'andi' = 'apply And_i'
andITac :: Tactic
andITac tr@(goal,_,_,totCon) =
       let (ok,andConnective,conj1,conj2) = deconstructAppVQQ goal in
       if not ok then errGoalWrongForm else
       findSpecialLemma (andConnective,andIName,[]) >>= \prf ->
       getType totCon prf >>= \(pT,pS) ->
       primApplyMaxTac onlyTermUnfold (prf,pT,pS) tr

andIName = "AndI"

andELTac :: ExtTermTS -> Tactic
andELTac = extendTac primAndELTac

primAndELTac = primAndETacS andELName True

andELName = "AndEL"

andERTac :: ExtTermTS -> Tactic
andERTac = extendTac primAndERTac

primAndERTac = primAndETacS andERName False

andERName = "AndER"
                   
-- 'andel t' = 'forward And_el on t' 
primAndETacS :: String -> Bool -> (Term,Term,Sort) -> Tactic
primAndETacS tacName left tts@(_,typ,_) (goal,locCon,gi,totCon) =
    let (ok,andConnective,conj1,conj2) = deconstructAppVQQ typ in
    if not ok then errTermWrongForm else
    findSpecialLemma (andConnective,tacName,[]) >>= \prf ->
    getType totCon prf >>= \(pTyp,pSort) ->
    forwardTac neverUnfold ((prf,pTyp,pSort),[tts]) (goal,locCon,gi,totCon)


andETac :: ExtTermTS -> Tactic
andETac = extendTac primAndETac

primAndETac :: (Term,Term,Sort) -> Tactic
primAndETac tts = primAndELTac tts `thenTac` [
                  primAndERTac tts `thenTac` [tryHideTac (fst3 tts)]] 

                                                
redToSortB :: SyntaxInfo -> Context -> Term -> (Bool,Sort)
redToSortB si con t = handle (redToSort si con t)
                      (\_ -> (False,undefined))
                      (\s -> (True,s))

orILTac :: Tactic
orILTac = orITac orILName

orILName = "OrIL"

orIRTac :: Tactic
orIRTac = orITac orIRName

orIRName = "OrIR"                                   

-- 'OrIL' = 'apply Or_IL'
orITac :: String -> Tactic
orITac tacName tr@(goal,_,_,totCon) =
       let (ok,orConnective,disj1,disj2) = deconstructAppVQQ goal in
       if not ok then errGoalWrongForm else
       findSpecialLemma (orConnective,tacName,[]) >>= \prf ->
       getType totCon prf >>= \(pTyp,pSort) ->
       primApplyMaxTac onlyTermUnfold (prf,pTyp,pSort) tr


orETac :: ExtTermTS -> Tactic
orETac = extendTac primOrETac
                         
-- 'OrE H' = 'apply Or_E on H' 
primOrETac :: (Term,Term,Sort) -> Tactic
primOrETac tts@(term,typ,_) (goal,locCon,gi,totCon) =
       let (ok,orConnective,disj1,disj2) = deconstructAppVQQ typ in
       if not ok then errTermWrongForm else
       getSort totCon goal >>= \sortResult ->
       findSpecialLemma (orConnective,orEName,[sortResult]) >>= \prf ->
       getType totCon prf >>= \(pTyp,pSort) ->       
       (applyMaxTac neverUnfold ((prf,pTyp,pSort),[tts])
        `thenTac` 
        replicate 2 (intro `thenTac` [tryHideTac term]))
       (goal,locCon,gi,totCon)

orEName = "OrE"
               

extendTac :: ((Term,Term,Sort) -> Tactic) -> ExtTermTS -> Tactic
extendTac primTac (tts@(_,typ,_),[]) | not (isGenAll typ) = primTac tts
extendTac primTac extTerm =
    forwardUltTac alwaysUnfold extTerm 
    (\(goal,locCon,gi,totCon) ->
     let (_,(lastVar,t,s)) = deconstructDecl (headI locCon)
         tts = (mkVr lastVar, t, s) in
     primTac tts (goal,locCon,gi,totCon))

-- 'NotI' = 'apply Not_i'
notITac :: Tactic
notITac (goal,locCon,gi,totCon) =
       let (ok,notConnective,arg) = deconstructAppVQ goal in
       if not ok then errGoalWrongForm else
       findSpecialLemma (notConnective,notIName,[]) >>= \prf ->
       getType totCon prf >>= \(pT,pS) ->       
       (primApplyMaxTac (onlyTermUnfold) (prf,pT,pS) `then1Tac` intro)
       (goal,locCon,gi,totCon)

notIName = "NotI"
  

notETac :: ExtTermTS -> Tactic
notETac = extendTac primNotETac

-- 'NotE H' = 'apply Not_e on H'
primNotETac :: (Term,Term,Sort) -> Tactic
primNotETac tTs@(term,typ,sort)  (goal,locCon,gi,totCon) =
     let (ok,notConnective,arg) = deconstructAppVQ typ in
     if not ok then errTermWrongForm else
     getType totCon goal >>= \(typeResult,_) ->
     let (ok2,falseVar) = deconstructVar goal in
     if not ok2 then errGoalWrongForm else 
     findSpecialLemma (notConnective,notEName,[]) >>= \prf ->
     getType totCon prf >>= \(pT,pS) ->       
     applyMaxTac neverUnfold ((prf,pT,pS),[tTs])
     (goal,locCon,gi,totCon)

notEName = "NotE"



getUnaryType :: Vari -> GContext -> M (Term,Sort)
getUnaryType oper con =
       getType (globToTot con) (mkVr oper) >>= \(typeOper,_) ->
       let -- we use deconstructAll so we can also get the sort of the
           -- argument, which is needed later on.
           (ok,(_,typeArg,sortArg),_) = deconstructAll typeOper in
       if not ok then
          errConnectiveWrongType oper
       else
       return (typeArg,sortArg)
  



                
-- 'FalseE' = 'apply ex_falso'
falseETac :: Tactic
falseETac (goal,locCon,gi,totCon) =
       getSort totCon goal >>= \sortGoal ->
       findSpecialLemmaBare ("",falseEName,[sortGoal]) >>= \(found,~(res,_)) ->
       (if found then
          -- currently, the number of additional arguments is never used.
          return (mkVr res)
        else
          fetchSyn >>= \si ->
          genErrS (falseEName ++ " not defined for inhabitants of sort "++ 
                   printSortSt si sortGoal ++ ". Use the command 'use " ++
                   falseEName ++"' first.")) >>= \prf ->
       getType totCon prf >>= \(pT,pS) ->       
       primApplyMaxTac neverUnfold (prf,pT,pS) (goal,locCon,gi,totCon)

falseEName = "FalseE"
 

-- 'ExistsI t' = 'apply Exists_i on t'
existsITac :: (Term,Term,Sort) -> Tactic
existsITac tTs (goal,locCon,gi,totCon) =
       let (exConn,args) = deconstructAppMax goal 
           (ok, exConnective) = deconstructVar exConn in
       if not ok then 
          errGoalWrongForm 
       else
       findSpecialLemma (exConnective,existsIName,[]) >>= \eIP ->
       getType totCon eIP >>= \(eIPt,eIPs) ->
       applyMaxTac onlyTermUnfold ((eIP,eIPt,eIPs),[tTs]) 
                (goal,locCon,gi,totCon)

existsIName = "ExistsI"


existsETac :: ExtTermTS -> Tactic
existsETac = extendTac primExistsETac

-- roughly, 'existse t' is 'apply exists_elim on t then intros 2'
primExistsETac :: (Term,Term,Sort) -> Tactic
primExistsETac tTs@(t,typeT,_) (goal,locCon,gi,totCon) =
    let (exConn,args) = deconstructAppMax typeT
        (ok1, exConnective) = deconstructVar exConn
        ok2 = not (null args)
        pred = last args
        (isLambda,(nameVar,_,sort),_) = deconstructAbs pred in
    if not (ok1 && ok2) then errTermWrongForm else
    getSort totCon goal >>= \sortResult ->
    findSpecialLemma (exConnective,existsEName,[sortResult])>>= \eEP ->
    (if isLambda then
        -- try to keep original name
        allForbiddenVars locCon >>= \forVars ->
        let nameVar' = findNiceFree sort forVars nameVar in
        return (introVar [nameVar'])
     else return intro) >>= \properIntro ->
    getType totCon eEP >>= \(eEPt,eEPs) ->
    (applyMaxTac neverUnfold ((eEP,eEPt,eEPs),[tTs]) `thenTac` 
     [properIntro `then1Tac` intro `then1Tac` tryHideTac t])
    (goal,locCon,gi,totCon)

existsEName = "ExistsE"

getExistsType :: Vari -> GContext -> M (Term,Term)
getExistsType exConnective con =
     getType (globToTot con) (mkVr exConnective) >>= \(typeExConnective,_) ->
     let (ok1,(_,typeA,_),typeBody) = deconstructAll typeExConnective
         (ok2,_,typeR) = deconstructArrow typeBody in  
     if not (ok1 && ok2) then
        errConnectiveWrongType exConnective
     else
     return (typeA,typeR)


errGoalWrongForm :: M a
errGoalWrongForm = genErrS "Goal not of correct form"

errTermWrongForm :: M a
errTermWrongForm = genErrS "Term not of correct form"

errConnectiveWrongType :: Vari -> M a
errConnectiveWrongType conn = genErrS ("Type of operation "++conn++
                                    "is not of correct form")

-- findSpecialLemma looks a lemma up, given the key.
findSpecialLemma :: (Vari,String,[Sort]) -> M Term
findSpecialLemma key@(conn,tacName,_) = 
      findSpecialLemmaBare key >>= \(found,~(res,_)) ->
      if found then
         -- currently, the number of additional arguments is never used.
         return (mkVr res)
      else
         fetchSyn >>= \si ->
         genErrS (tacName++" not defined for connective " ++ 
                  printVarSt si conn ++
                  ". Use the command 'use "++tacName++"' first.")

-- findSpecialLemmaBare looks a lemma up, given the key. Produces no errors.
findSpecialLemmaBare :: (Vari,String,[Sort]) -> M (Bool,(Vari,Int))
findSpecialLemmaBare key@(conn,tacName,_) = 
      fetchLemmas >>= \lemmas ->
      return (findI lemmas key)


-----------------------------------------------
--  R E P L A C E M E N T   R O U T I N E S  --
-----------------------------------------------

-- Used for the rewriting lemmas. 

-- replace1Pat  replaces in t1 the selected subterm that matches t2
-- (with variables exVars) with t3, and return the substitution found.
-- If not such a subterm is found, false is returned.
-- make sure no variables of t3 will be bound by subterms of t1!
replace1Pat :: (Collection c, Collection d) =>
               SyntaxInfo -> Context -> LContext -> c Vari -> Term ->
               d Vari -> Term -> Term -> Int -> (Term,(Bool,Subst))
replace1Pat si totCon subCon vl t1 exVars t2 t3 occ =
   let f (t,subCon,st@(0,_)) = (t,st)
       f (t,subCon,st@(occToGo,_)) =
                -- use "weak" matching, for efficiency.
                let substs = match neverUnfold si (totCon, exVars, t2, t)
                    locVars = domLCon subCon
                    hasLocVars = anyC (`elemC` locVars) (fv t) in
                if hasLocVars || null substs then
                   (t,st)
                else
                if occToGo/=1 then
                   (t,(occToGo-1,dummySubst))
                else
                   (t3,(0,head substs))
       res = (occ,dummySubst) in
   doSnd (doFst (0==)) (changeSubterms0 subCon f res vl t1)

-- makePatternPat  beta-expands t1 so it is applied to
-- the first subterm of form t2 (with exis. variables exVars).
-- the name of the variable is v, its type is typ with any exis. variables
-- substituted.
-- it would be neat to check whether this abstraction is admitted or not
makePatternPat :: SyntaxInfo -> Bool -> Context -> Term -> (LContext,Term) ->
                  Vari -> Term -> Sort -> (TermPath,Int) -> 
                  M (Subst,Term)
makePatternPat si lToR con t1 (exCon,t2) v typ sort (path,select) =
   let exTotCon = exCon `addLoc` con
       exVars = domLCon exCon
       f (term,subCon,vl) = replace1Pat si exTotCon subCon vl term exVars t2 
                                        (mkVr v) select in
   changeSubterm f (domCon exTotCon) t1 path >>= \(t1',(b,sigma)) ->
   if not b then 
      let name = if lToR then "lhs" else "rhs" in
      genErrT ("Couldn't find "++name++": ") t2 ""
   else
      -- Check whether the abstraction is admitted.
      let abstrac = mkAbs (v,applySubst sigma typ,sort) t1' in
      handleS (getType con abstrac)
      (\_ -> genErrS "This rewriting is not allowed") -- type error -> fail.
      (\_ ->                                          -- well-typed -> OK
             return (sigma,mkApp abstrac (applySubst sigma t2)))

{-
makePatternPat :: Collection c =>
                  SyntaxInfo -> Context -> Term -> c Vari -> Term ->
                  Vari -> Term -> Sort -> (TermPath,Int) -> 
                  M (Bool,Subst,Term)
makePatternPat si c t1 exVars t2 v typ sort (path,select) =
   let f (term,subCon,vl) = replace1Pat si c subCon vl term exVars t2 
                                        (mkVr v) select in
   changeSubterm f (domCon c) t1 path >>= \(t1',(b,s)) ->
   if not b then return (False,dummySubst,dummyTerm)
   else
      return (True,s,mkApp (mkAbs (v,applySubst s typ,sort) t1')
                           (applySubst s t2))
-}


-----------------------------------------------------
--  F O R M S   O F   S P E C I A L   L E M M A S  --
-----------------------------------------------------      

qGiveUseFor :: M Result
qGiveUseFor = fetchLemmas >>= \lemmas ->
              return (RUseForIs (sort (map (\((a,b,_),(c,_)) -> (b,a,c)) 
                                           (indexedToListIL lemmas))))

qUseFor :: String -> Vari -> M Result
qUseFor tacName v =
          fetchCon >>= \con ->
          getType (globToTot con) (mkVr v) >>= \(typ,_) ->
          qUseFor' tacName typ >>= \(ok,prefTacName,connective,sorts,noAA) ->
          if ok then
             setLemma (connective,prefTacName,sorts) (v,noAA) >>
             qGiveUseFor
          else
             genErrS ("The lemma is not in the correct form for "++
                     prefTacName)

qUseFor' :: String -> Term -> M (Bool,String,Vari,[Sort],Int)
qUseFor' name typ | name `eqNC` andIName =
     -- check typ is of the following form:
     -- @P,Q:s1. P -> Q -> and P Q
     let (ok1,(v1,s1),(v2,s1'),u1) = deconstructAllSSQ typ
         ok2 = s1 == s1'
         v1' = mkVr v1
         v2' = mkVr v2
         (ok3,u2) = deconstructArrowGGQ u1 v1' v2'
         (ok4,andConnective) = deconstructAppVGG u2 v1' v2' in
     return (ok1 && ok2 && ok3 && ok4, andIName, andConnective, [],0)
qUseFor' name typ | name `eqNC` andELName =return (qUseForAndEHelp True typ)
qUseFor' name typ | name `eqNC` andERName =return (qUseForAndEHelp False typ)
qUseFor' name typ | name `eqNC` orILName = return (qUseForOriHelp True typ)
qUseFor' name typ | name `eqNC` orIRName = return (qUseForOriHelp False typ)
qUseFor' name typ | name `eqNC` orEName =
     -- check typ is of the following form:
     -- @P,Q:s1. @R:sort2. or P Q -> (P->R) -> (Q->R) -> R
     let (ok1,(v1,s1),(v2,s1'),u1) = deconstructAllSSQ typ
         ok2 = s1 == s1'
         (ok3,(v3,sort2),u2) = deconstructAllSQ u1
         v1' = mkVr v1
         v2' = mkVr v2
         v3' = mkVr v3
         (ok4,orTerm,u3) = deconstructArrow u2
         (ok5,u4,u5) = deconstructArrowQQG u3 v3'
         ok6 = deconstructArrowGG u4 v1' v3' 
         ok7 = deconstructArrowGG u5 v2' v3' 
         (ok8,orConnective) = deconstructAppVGG orTerm v1' v2' in
      return (ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8,
              orEName, orConnective, [sort2],0)
qUseFor' name typ | name `eqNC` notIName =
      -- check typ is of the following form:
      -- @P:sort. (P -> False) -> not P
      let (ok1,(v1,sort),u1) = deconstructAllSQ typ
          v1' = mkVr v1
          (ok2,dom,cod) = deconstructArrow u1
          (ok3,false) = deconstructArrowGV dom v1'
          (ok4,notConnective) = deconstructAppVG cod v1' in
      return (ok1 && ok2 && ok3 && ok4, notIName, notConnective, [],0)
qUseFor' name typ | name `eqNC` notEName =
      -- check typ is of the following form:
      -- @P:sort. not P -> P -> False
      let (ok1,(v1,sort),u1) = deconstructAllSQ typ
          v1' = mkVr v1
          (ok2,dom,cod) = deconstructArrow u1
          (ok3,notConnective) = deconstructAppVG dom v1'
          (ok4,false) = deconstructArrowGV cod v1' in
      return (ok1 && ok2 && ok3 && ok4, notEName, notConnective, [],0)
qUseFor' name typ | name `eqNC` falseEName =
      -- check typ is of the following form:
      -- @P:sort. False -> P
      let (ok1,(v1,sort),u1) = deconstructAllSQ typ
          v1' = mkVr v1
          (ok2,falseConnective) = deconstructArrowVG u1 v1' in
      return (ok1 && ok2, falseEName, "" , [sort],0) 
      -- "" is correct! We can't have more than one false-construction
      -- (given the sort), since the tactic 'falsee' doesn't have a
      -- false-construction available.
qUseFor' name typ | name `eqNC` existsIName =
      -- check typ is of the following form:
      -- @x1:t1. .. @xn:tn. @X:B. @P:B->s. P X -> Ex x1 .. xn P
      --  (x1 .. xn may occur free in B)
      let (cis, u1) = deconstructGenAllMax typ
          ok1 = length cis >= 3
          (hPx:pBs:xB:xts) = cis
          (ok2,(vX,b,_)) = deconstructDecl xB
          (ok3,(vP,bs,_)) = deconstructDecl pBs
          (ok4,(_,px,_)) = deconstructDecl hPx
          (ok5,s) = deconstructArrowGS bs b
          vX' = mkVr vX
          vP' = mkVr vP
          ok6 = px == vP' `mkApp` vX'
          (ok7,exConn,args) = deconstructAppN u1 (length xts+1)
          ok8 = and (zipWith (==) args (reverse (vP' : map (mkVr.fst) xts)))
          (ok9, exConnective) = deconstructVar exConn in
      return (ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9, 
              existsIName, exConnective, [], length cis - 3)
qUseFor' name typ | name `eqNC` existsEName =
      -- check typ is of the following form:
      -- @x1:t1. .. @xn:tn. @P:B->s1. @R:s2. Ex x1 .. xn P -> 
      --    (@x:B. P x -> R) -> R
      let (cis, u1) = deconstructGenAllMax typ
          ok1 = length cis >= 4
          (hI: hEx: rs: pBs1 : xts) = cis
          (ok2, (vP, bs1, _)) = deconstructDecl pBs1
          vP' = mkVr vP
          (ok3, b, s1) = deconstructArrowQS bs1
          (ok4, (vR, s2', _)) =deconstructDecl rs
          vR' = mkVr vR
          (ok5, s2) = deconstructSort s2'
          (ok6, (_,ex,_)) = deconstructDecl hEx
          (ok7,exConn,args) = deconstructAppN ex (length xts+1)
          (ok8,exConnective) = deconstructVar exConn
          ok9 = and (zipWith (==) args (reverse (vP' : map (mkVr.fst) xts)))
          (ok10, (_,i,_)) = deconstructDecl hI
          (ok11, (x,b',_),ib) = deconstructAll i
          ok12 = b' == b && ib == mkArrow (vP' `mkApp` mkVr x,s1) vR'
          ok13 = vR' == u1 in
      return (and [ok1,ok2,ok3,ok4,ok5,ok6,ok7,ok8,ok9,ok10,ok11,ok12,ok13],
              existsEName, exConnective, [s2], length cis - 4)
qUseFor' name typ | name `eqNC` reflName =
    -- check typ is of the following form:
    -- @x1:t1. .. @xn:tn. @x:t. is x1 .. xn x x
    let (cis, u1) = deconstructGenAllMax typ
        ok1 = length cis >=1
        (xT:xts) = cis
        (ok2, (vX,t,_)) = deconstructDecl xT
        (ok3, isConn,args) = deconstructAppN u1 (length xts+2)
        vX' = mkVr vX
        ok4 = and (zipWith (==) args (reverse (vX':vX': map (mkVr.fst) xts)))
        (ok5, isConnective) = deconstructVar isConn in
    return (ok1 && ok2 && ok3 && ok4 && ok5, reflName, isConnective, [],
            length cis - 1)
qUseFor' name typ | name `eqNC` rewriteName = 
      return (qUseForRewriteHelp True typ)
qUseFor' name typ | name `eqNC` lewriteName = 
      return (qUseForRewriteHelp False typ)
qUseFor' tac _ = genErrS (tac ++ " is no (special) tactic")
    
-- eqNC checks if two strings are equal, ignoring the case
eqNC s1 s2 = toLowers s1 == toLowers s2

qUseForRewriteHelp :: Bool -> Term -> (Bool,String,Vari,[Sort],Int)
qUseForRewriteHelp lToR typ =
    -- check typ is of the following form:
    -- lToR => @x1: t1. .. @xn:tn. @x,y:t. @P:t->sort. eq x1 .. xn x y ->
    --         P y -> P x
    -- rToL => @x1: t1. .. @xn:tn. @x,y:t. @P:t->sort. eq x1 .. xn x y ->
    --         P x -> P y
   let (cis, u1) = deconstructGenAllMax typ
       ok1 = length cis >= 5
       (hPyx:hEqTerm:pTs:yt:xt:xts) = cis
       (ok2,(_,pYx,_)) = deconstructDecl hPyx
       (ok3,(_,eqTerm,_)) = deconstructDecl hEqTerm
       (ok4,(vP,tS,_)) = deconstructDecl pTs
       (ok5,(vY,t2,_)) = deconstructDecl yt
       (ok6,(vX,t1,_)) = deconstructDecl xt
       vP' = mkVr vP
       vX' = mkVr vX
       vY' = mkVr vY
       (vPrem,vConc) = if lToR then (vY',vX') else (vX',vY')
       ok7 = u1 == vP' `mkApp` vConc
       ok8 = pYx == vP' `mkApp` vPrem
       (ok9,isConn,args) = deconstructAppN eqTerm (length xts + 2)
       ok10 = and (zipWith (==) args (reverse (vY':vX': map (mkVr.fst) xts)))
       (ok11,isConnective) = deconstructVar isConn
       (ok12,sort) = deconstructArrowGS tS t1
       ok13 = t1 == t2 in
   (ok1 && ok2 && ok3 && ok4 && ok5 && ok6 && ok7 && ok8 && ok9 && ok10 &&
    ok11 && ok12 && ok13,
    if lToR then rewriteName else lewriteName, 
    isConnective, [sort], length cis - 5)


      
qUseForOriHelp :: Bool -> Term -> (Bool,String,Vari,[Sort],Int)
qUseForOriHelp left typ =
     -- check typ is of the following form:
     -- @P,Q:s1. P/Q -> or P Q
     let (ok1,(v1,s1),(v2,s1'),u1) = deconstructAllSSQ typ
         ok2 = s1 == s1'                      
         v1' = mkVr v1
         v2' = mkVr v2
         hv = if left then v1' else v2'
         (ok3,orTerm) = deconstructArrowGQ u1 hv
         (ok4,orConnective) = deconstructAppVGG orTerm v1' v2' in
     (ok1 && ok2 && ok3 && ok4,
      if left then orILName else orIRName,
      orConnective, [], 0)

qUseForAndEHelp :: Bool -> Term -> (Bool,String,Vari,[Sort],Int)
qUseForAndEHelp left typ =
   -- check typ is of the following form:
   -- @P,Q:s1. and P Q -> P/Q
   let (ok1,(v1,s1),(v2,s1'),u1) = deconstructAllSSQ typ
       ok2 = s1 == s1'
       v1' = mkVr v1
       v2' = mkVr v2
       hv = if left then v1' else v2'
       (ok3,andTerm) = deconstructArrowQG u1 hv
       (ok4,andConnective) = deconstructAppVGG andTerm v1' v2' in
   (ok1 && ok2 && ok3 && ok4,
    if left then andELName else andERName,
    andConnective, [], 0)

--------------------------------------------------------------
-- M O R E   D E C O N S T R U C T O R   F U N C T I O N S  --
--------------------------------------------------------------

{-      
In this section we define more deconstructor functions which are needed
for these special tactics.
The names for these functions consist of the name for the ordinary
deconstructor followed by at least two capital letters.
These indicate a pattern, as follows
 Q means the subterm can be anything,    return this subterm
 V means the subterm must be a Variable, return this variable
 S means the subterm must be a Sort,     return this sort
 G means the subterm must be equal to an argument, nothing is returned.
-}

-- ALL

-- dec '@x:s. a'  =  ((x,s),a)
deconstructAllSQ :: Term -> (Bool,(Vari,Sort),Term)
deconstructAllSQ term = let (ok1,(v,t,_),u) = deconstructAll term
                            (ok2,sort) = deconstructSort t in
                        (ok1 && ok2, (v,sort), u)

-- dec '@x1:s1.@x2:s2. a'  =  ((x1,s1),(x2,s2),a)
deconstructAllSSQ :: Term -> (Bool,(Vari,Sort),(Vari,Sort),Term)
deconstructAllSSQ term = let (ok1,it1,u1) = deconstructAllSQ term
                             (ok2,it2,u2) = deconstructAllSQ u1 in
                         (ok1 && ok2, it1, it2, u2)

-- dec '@x:a. b' a =  (x,b)
deconstructAllGQ :: Term -> Term -> (Bool,Vari,Term)
deconstructAllGQ term dom = let (ok1,(v,dom',_),u) = deconstructAll term
                                ok2 = dom == dom' in
                            (ok1 && ok2, v, u)

-- ARROW

-- dec 'a -> b' a  =  b
deconstructArrowGQ :: Term -> Term -> (Bool,Term)
deconstructArrowGQ t dom = let (ok1,dom',u) = deconstructArrow t
                               ok2 = dom == dom' in
                           (ok1 && ok2, u)
                            
-- dec 'a -> b -> c' a b  =  c
deconstructArrowGGQ :: Term -> Term -> Term -> (Bool,Term)
deconstructArrowGGQ t dom1 dom2 = 
               let (ok1,u) = deconstructArrowGQ t dom1
                   (ok2,v) = deconstructArrowGQ u dom2 in
               (ok1 && ok2, v)
                                               
-- dec 'a -> x' a  =  x
deconstructArrowGV :: Term -> Term -> (Bool,Vari)
deconstructArrowGV t dom = let (ok1,u) = deconstructArrowGQ t dom
                               (ok2,v) = deconstructVar u in
                           (ok1 && ok2, v)
                            
-- dec 'a -> s' a  =  s
deconstructArrowGS :: Term -> Term -> (Bool,Sort)
deconstructArrowGS t dom = let (ok1,u) = deconstructArrowGQ t dom
                               (ok2,s) = deconstructSort u in
                           (ok1 && ok2, s)
                            
-- dec 'a -> s'  =  (a,s)
deconstructArrowQS :: Term -> (Bool,Term,Sort)
deconstructArrowQS t = let (ok1,u, v) = deconstructArrow t
                           (ok2,s) = deconstructSort v in
                       (ok1 && ok2, u, s)
                            
-- dec 'a -> b' b = a
deconstructArrowQG :: Term -> Term -> (Bool,Term)
deconstructArrowQG t cod = let (ok1,u,cod') = deconstructArrow t
                               ok2 = cod == cod' in
                           (ok1 && ok2, u)

-- dec 'x -> a' a  =  x
deconstructArrowVG :: Term -> Term -> (Bool,Vari)
deconstructArrowVG t cod = let (ok1,u) = deconstructArrowQG t cod
                               (ok2,v) = deconstructVar u in
                           (ok1 && ok2, v)        

-- dec 'a -> b' a b = True
deconstructArrowGG :: Term -> Term -> Term -> Bool
deconstructArrowGG t dom cod = let (ok1,cod') = deconstructArrowGQ t dom
                                   ok2 = cod == cod' in
                               ok1 && ok2

-- dec 'a -> b -> c' a b c = True
deconstructArrowGGG :: Term -> Term -> Term -> Term -> Bool
deconstructArrowGGG t dom cod1 cod2 = 
                      let (ok1,u) = deconstructArrowGQ t dom
                          ok2 = deconstructArrowGG u cod1 cod2 in
                      ok1 && ok2

-- dec 'a -> b -> c' c = (a,b)
deconstructArrowQQG :: Term -> Term -> (Bool,Term,Term)
deconstructArrowQQG t cod2 = 
                      let (ok1,u1,u2) = deconstructArrow t
                          (ok2,v2) = deconstructArrowQG u2 cod2 in
                      (ok1 && ok2, u1, v2)  
              


                       
-- APPLICATION     
                                               
-- dec 'a b' b  =  a
deconstructAppQG :: Term -> Term -> (Bool,Term)
deconstructAppQG t arg = let (ok1,fun,arg') = deconstructApp t
                             ok2 = arg==arg' in
                         (ok1 && ok2, fun)

-- dec 'a b c' b c  =  a
deconstructAppQGG :: Term -> Term -> Term -> (Bool,Term)
deconstructAppQGG t arg1 arg2 = let (ok1,u) = deconstructAppQG t arg2
                                    (ok2,fun) = deconstructAppQG u arg1 in
                                (ok1 && ok2, fun)

-- dec 'a b c d' b c d  =  a
deconstructAppQGGG :: Term -> Term -> Term -> Term -> (Bool,Term)
deconstructAppQGGG t arg1 arg2 arg3 = 
                         let (ok1,u) = deconstructAppQGG t arg2 arg3
                             (ok2,fun) = deconstructAppQG u arg1 in
                         (ok1 && ok2, fun)

-- dec 'x a' a  =  a
deconstructAppVG :: Term -> Term -> (Bool,Vari)
deconstructAppVG t arg = let (ok1,fun) = deconstructAppQG t arg
                             (ok2,v) = deconstructVar fun in
                         (ok1 && ok2, v)

-- dec 'x a b' a b  =  x
deconstructAppVGG :: Term -> Term -> Term -> (Bool,Vari)
deconstructAppVGG t arg1 arg2 = let (ok1,u) = deconstructAppQGG t arg1 arg2
                                    (ok2,v) = deconstructVar u in
                                (ok1 && ok2, v)

-- dec 'x a b c' a b c =  x
deconstructAppVGGG :: Term -> Term -> Term -> Term -> (Bool,Vari)
deconstructAppVGGG t arg1 arg2 arg3 = 
                         let (ok1,u) = deconstructAppQGGG t arg1 arg2 arg3
                             (ok2,v) = deconstructVar u in
                         (ok1 && ok2, v)
                                          
-- dec 'x a' = (x,a)
deconstructAppVQ :: Term -> (Bool,Vari,Term)
deconstructAppVQ t =
       let (ok,conTerm,oper) = deconstructApp t
           (ok2,connective) = deconstructVar conTerm in
       (ok && ok2,connective,oper)
                    
-- dec 'x a b' = (x,a,b)
deconstructAppVQQ :: Term -> (Bool,Vari,Term,Term)
deconstructAppVQQ t =
       let (ok,conTerm,oper1,oper2) = deconstructApp2 t
           (ok2,connective) = deconstructVar conTerm in
       (ok && ok2,connective,oper1,oper2)
                        
-- dec 'x a b c' = (x,a,b,c)
deconstructAppVQQQ :: Term -> (Bool,Vari,Term,Term,Term)
deconstructAppVQQQ t =
       let (ok,conTerm,typ,oper1,oper2) = deconstructApp3 t
           (ok2,connective) = deconstructVar conTerm in
       (ok && ok2,connective,typ,oper1,oper2)

