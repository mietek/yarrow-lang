-- File: Matchin
-- Description: This module contains the basic definitions for substitution
--              and the matching routine.

module Matchin(Subst, emptySubst,  dummySubst, domSubst, 
               applySubst, applyConSubst, applyLConSubst,
               defVar, defVar', 
               MatchOptions,
               alwaysUnfold, neverUnfold, onlyPatternUnfold, onlyTermUnfold,
               mayUnfoldPattern, mayUnfoldTerm,
               match, matches, matchSupers, notFound) where

import Collect
import HaMonSt
import Basic
import Paths
import PTSys
import Reduce
import SyntaxI
import Typing

--------------------------------
--  S U B S T I T U T I O N S --
--------------------------------

-- list of variables that may be substituted
type VarList = [Vari]                      

-- substitution is an association list
type Subst = [(Vari,Term)]

emptySubst :: Subst               
emptySubst = []
              
dummySubst = []

-- domSubst delivers the variables defined in a substitution
domSubst :: Subst -> [Vari]
domSubst = map fst            

-- applySubst applies a substitution to a term                             
applySubst :: Subst -> Term -> Term
applySubst [] t = t
applySubst ((v,sub):sigmas) t = applySubst sigmas (subst t v sub)


-- applyConSubst applies a substitution to a context
-- This routine doesn't substitute variables declared in the context.
applyConSubst :: Subst -> Context -> Context
applyConSubst sigma = mapI (applyConESubst sigma)

applyLConSubst :: Subst -> LContext -> LContext
applyLConSubst sigma = mapI (applyConESubst sigma)

applyConESubst :: Subst -> ContextERest -> ContextERest
applyConESubst sigma ((typ,sort),cat,ts) = 
              ((applySubst sigma typ,sort),cat,map (applySubst sigma) ts)


-- defVar delivers the definition of a variable in a substitution
defVar :: Vari -> Subst -> [Term]
defVar v sigma = map snd (filter ((v==) . fst) sigma)
                  
-- !!! Kun je defVar nu niet weglaten?
defVar' :: Vari -> Subst -> (Bool,Term)
defVar' v sigma = let ts = defVar v sigma in
                  if null ts then 
                     (False, undefined)
                  else
                     (True, head ts)


----------------------------------------
--          M A T C H I N G           --
----------------------------------------

-- We have a slight extension of first order matching.
-- First order matching means the routine doesn't know
-- anything about beta or delta reduction. 
-- There are three extensions:
-- - beta-delta equal terms are matched
-- - definitions are unfolded under some circumstances
-- - If the pattern is of the form x x1 .. xn where we may substitute for
--   x then the substitution <x := \x1 .. xn. term> is delivered (roughly).
--   This is called lambda-patterns.
-- This matching routine delivers at most one substitution.
--
-- match con exVars p t 
--     Pre: con\exVars |- t : T
--          con |- p : P
--     Post: s in (match con p t) ->
--           1) s(p) =beta t
--           2) s(con) |- s(p) : s(P)
--           3) s(con) |- s(P) <: T
--           By 2 and 3 s(con) |- s(p) : T
                                                          

type MatchOptions = (Bool,Bool)
--                    ^    ^
-- unfold pattern ----/    |
-- unfold term ------------/

mayUnfoldPattern :: MatchOptions -> Bool
mayUnfoldPattern = fst

mayUnfoldTerm :: MatchOptions -> Bool
mayUnfoldTerm = snd

alwaysUnfold :: MatchOptions
alwaysUnfold = (True,True)

neverUnfold :: MatchOptions
neverUnfold = (False,False)

onlyPatternUnfold :: MatchOptions
onlyPatternUnfold = (True,False)

onlyTermUnfold :: MatchOptions
onlyTermUnfold = (False,True)



-- match is the matching function, that solves one matching problem.
-- match uses the 'matches' routine that matches multiple problems.
--
-- The variable exVars holds the existential variables, i.e. the variables
-- that may be substituted for. These must be declared in the context.
-- The variable p (pattern) is the term in which these existential
-- variables may occur. The variable t holds the term to which p has to be
-- matched.
   
-- ghc does not handle the type annotation of match, lambdaPat and 
--   matches correctly, so we omit the type annotation.               
{-
match :: Collection c =>
       MatchOptions -> SyntaxInfo -> (Context, c Vari, Term, Term) -> [Subst]
-}

-- Precondition: con should be of form
match options si prob = 
                        {- -- FOR TRACES
                        let (con, exVars, p, t) = prob 
                            prT t = printTerm displayString si dummyPath t in
                           trace ("Matching: "++
                                 --prCon si (conToList (fst con)) ++ "|- " ++
                                 prT p ++" =? "++
                                 prT t++"\n") -}
                                match'' options si prob



-- Pattern is a basic that can't be a redex (so not a variable)
match'' options si (con, exVars, Basic pcat, t) | neverRedexBasic pcat =
    let (isBasic,tcat) = deconstructBasic (bdwhnf con t) in
    if not (isBasic && pcat == tcat) then
       []
    else
       [[]]

-- Pattern is a non-binder that can't be a redex (so not an application)
match'' options si (con, exVars, Nonb pcat pts, t) | neverRedexNonb pcat =
    let (isNonb,tcat,tts) = deconstructNonb (bdwhnf con t) in
    if not (isNonb && pcat == tcat) then
       []
    else
    matches options si
             (zipWith (\ptsn ttsn -> (con, exVars, ptsn,ttsn)) pts tts)

-- Pattern is a binder that can't be a redex (so not a local definition)
match'' options si (con, exVars, Bind pcat pts pi@(pv0,pt,ps) pu0, t) 
     | neverRedexBind pcat =
     let (isBind,tcat,tts,(tv0,tt,ts),tu0) = deconstructBind (bdwhnf con t)
         -- force both the variables in p and t to the same (fresh) name
         (v,pu,tu) = equateVarsBinders (domCon con) (pv0,pu0) (tv0,tu0)
         conPlusV = mkDecl (v,tt,ts) `addC` con in
    -- if ps == ts then .. else []   for efficiency
    if not (isBind && pcat == tcat) then
       []
    else
    matches options si  
             ([(con, exVars, pt,tt)] ++
              zipWith (\ptsn ttsn -> (con, exVars, ptsn,ttsn)) pts tts ++
              [(conPlusV,exVars,pu,tu)])

-- pattern is existential variable
match'' options si (con, exVars, p, t) 
    | isVar p && (snd (deconstructVar p)) `elemC` exVars=
    let (_,v) = deconstructVar p in
    -- check t is well-defined in v's context !
    -- we could reduce t some to make it defined before v
    -- however, this is expensive or complicated, so we don't do that.
    let ((exCon:_),_) = unLAOT con in -- we need only 'local' context
    if not (definedBefore exCon v t) then
        []
    else
    let (_,pVar) = deconstructVar p
        (_,(pType,_),pconstrs,pcts) = findGenDecl con pVar
        (tType,_) = admitNoErr (inferType si con t) in
    map ((v,t):)
       (
        (case pconstrs of
         CSub ->
            -- t must be a subtype of the bound of p.
            combineMatch (matchSuper options si (con, exVars, head pcts, t))
         CNone ->
            id
         otherwise -> error (internalErrorString ++
                             "Unknown constraint in matching")
        )
           -- for the types we always use the strongest version of matching.
        (matchSuper alwaysUnfold si) (con, exVars, pType, tType)
       )

match'' options si (con, exVars, p, t) 
    | mayUnfoldTerm options && bdEqual con p t = [[]]
                                  
-- Now handle all the cases where pattern is a construction that may be
-- a redex. First we handle some special cases, then we proceed with the
-- rest.

-- Special case: pattern is a local definition
match'' options si (con, exVars, p, t) | isDelta p = 
    let (_,it,pu) = deconstructDelta (changeVar p (domCon con)) in
    match options si (mkDef it `addC` con, exVars, pu, t)

-- Now we proceed with the general cases.
-- This case is never used at the moment.
match'' options si prob@(con, exVars, Basic pcat, t)
    {- | maybeRedexBasic pcat -} =
    let (isBasic,tcat) = deconstructBasic t in
    if isBasic && pcat == tcat then
       [[]]
    else
       despair options si prob
                                

match'' options si prob@(con, exVars, Nonb pcat pts, t) 
    {- | maybeRedexNonb pcat -} =
    let (isNonb,tcat,tts) = deconstructNonb t 
        ss = matches options si
               (zipWith (\ptsn ttsn -> (con, exVars, ptsn,ttsn)) pts tts) in
    if isNonb && pcat == tcat && not (null ss) then
       ss
    else
       -- Special case for application: try lambda-patterns
       if pcat == App then
          lambdaPat options si prob
       else
       despair options si prob
                                
-- This case is never used at the moment.
match'' options si prob@(con, exVars, Bind pcat pts pi@(pv0,pt,ps) pu0, t) 
     {- | maybeRedexBind pcat -} =
     let (isBind,tcat,tts,(tv0,tt,ts),tu0) = deconstructBind (bdwhnf con t)
         -- force both the variables in p and t to the same (fresh) name
         (v,pu,tu) = equateVarsBinders (domCon con) (pv0,pu0) (tv0,tu0)
         conPlusV = mkDecl (v,tt,ts) `addC` con 
         ss = matches options si
                 ([(con, exVars, pt, tt)] ++
                  zipWith (\ptsn ttsn -> (con, exVars, ptsn,ttsn)) pts tts ++
                  [(conPlusV, exVars, pu, tu)]) in
    if isBind && pcat == tcat && not (null ss) then
       ss
    else
       despair options si prob
    




-- lambdaPat _ (_, _, p, t)  does two things:
-- if p == x x1 .. xn where x existential then it makes a lambda pattern, i.e.
--       it matches x with \x1,..xn. t
-- if that doesn't work, matching despairs.
{- ghc does not handle the type annotation of match, lambdaPat and 
   matches correctly, so we omit the type annotation.
lambdaPat :: Collection c =>
             SyntaxInfo -> (Context, c Vari, Term, Term) -> [Subst]
-}
lambdaPat options si (con, exVars, p, t) = 
    let ts = unwindApps2 p
        ok1 = all isVar ts
        ok2 = length ts > 1
        vs = map (snd.deconstructVar) ts
        x = last vs
        ok3 = x `elemC` exVars
        xns = init vs
        mapf x = let (_,(xt,xs)) = findTypeSort con x in (x,xt,xs)
        xtsns = map mapf xns
        t' = foldl (flip mkAbs) t xtsns in
    if ok1 && ok2 && ok3 then
       -- Check t' is well-typed, i.e. all abstractions are well-formed,
       -- and no weird thing going on.
       handle (inferType si con t')
       (\_ -> despair options si (con, exVars, p, t))  -- Error
       (\_ -> match options si (con, exVars, mkVr x, t')) -- Typing is OK
    else
      despair options si (con, exVars, p, t)

-- unwindApps2 (t1 t2 t3 .. tn) = [tn,..,t3,t2,t1]
unwindApps2 :: Term -> [Term]                    
unwindApps2 t | isApp t = let (_,t1,t2) = deconstructApp t in
                          t2 : unwindApps2 t1
unwindApps2 t = [t]

{- OLD VERSION:
lambdaPat options si (con, exVars, p, t) = 
      let (pApp,pt,pu) = deconstructApp p
          (puVar,v) = deconstructVar pu
          -- ptOk limits pt to the form x x1 .. xn where x existential.
          -- This decreases the number of recursive calls a lot, and
          -- is not very restrictive in practice.
          ptOk = let (sptH:sptT) = standard pt
                     (ok1,x) = deconstructVar sptH
                     ok2 = x `elemC` exVars
                     ok3 = all isVar sptT in
                 ok1 && ok2 && ok3
          (_,(vt,vs)) = findTypeSort con v 
          (tType,tSort) = admitNoErr si (inferType si con t) 
          (absOk,_) = rule12 si vs tSort in
      if pApp && puVar && v `notElemC` exVars && ptOk && absOk then
         -- abstract over v
         match' options si (con, exVars, pt, mkAbs (v,vt,vs) t) 
      else 
      despair options si (con, exVars, p, t)
-}

-- last attempt:
--   if pattern beta-reduces, try that.
--   otherwise, bd-reduce t one step, and bring t to bwhnf
despair options si (con, exVars, p, t) =
      if mayUnfoldPattern options then
         let (pRed,p') = bwhRed con p in
         if pRed then
            match options si (con, exVars, bwhnf p', t)
         else despair2
      else
         despair2
  where despair2 =
         if mayUnfoldTerm options then
            let (tRed,t') = bdwhRed con t in
            if tRed then
               match options si (con, exVars, p, bwhnf t')
            else
               []
         else
            []
    
-- matchSuper p t tries to find a substitution s such that t < s(p)
-- Note that now the first argument is the term (instead of the pattern)
-- at the moment we have a very naive implementation
matchSuper options si (con, exVars, p, t) =
    let sigmas = match options si (con, exVars, p, t) in
    if null sigmas && hasSubtyping si then
        if subtype si con t p then [[]] else []
    else
        sigmas

matchSupers options si [] = [[]]
matchSupers options si (prob:ps) =
    combineMatches (matchSuper options si prob) (matchSupers options si) ps
{- 
      let substs = matchSuper' options si prob
          subst = head substs
          ps' = map (applyProbSubst subst) ps in
      if null substs then
         []
      else                 
      map (subst++) (matchSupers options si ps')
-}


-- multiple matching problems with same set of substitutable vars
-- tries first to solve the first problem of the list, which may help solve
-- following problems and so on.
-- This routine uses the fact that match delivers at most one substitution
{- ghc does not handle the type annotation of match, lambdaPat and 
   matches correctly, so we omit the type annotation.
matches :: Collection c =>
           SyntaxInfo -> [(Context,c Vari,Term,Term)] -> [Subst]
-}
matches options si [] = [[]]
matches options si (prob:ps) = 
    combineMatches (match options si prob) (matches options si) ps
{-
      let substs = match options si prob
          subst = head substs
          ps' = map (applyProbSubst subst) ps in
      if null substs then
         []
      else                 
      map (subst++) (matches options si ps')
-}
              
-- apply a substitution to a problem
applyProbSubst :: Collection c =>
                  Subst -> (Context,c Vari,Term,Term) -> 
                  (Context,c Vari,Term,Term)
applyProbSubst subst (c,e,p,t) = 
         -- or exVars without the variables determined by subst
     (applyConSubst subst c, e, applySubst subst p,t)

-- combine the substitutions found for one matching problem with a second
-- matching problem
combineMatch :: Collection c =>
                [Subst] -> ((Context,c Vari,Term,Term) -> [Subst]) -> 
                (Context,c Vari,Term,Term) -> [Subst]
combineMatch [] match prob = []
combineMatch [subst] match prob = 
    map (subst ++) (match (applyProbSubst subst prob))

combineMatches:: Collection c =>
                 [Subst] -> ([(Context,c Vari,Term,Term)] -> [Subst]) -> 
                 [(Context,c Vari,Term,Term)] -> [Subst]
combineMatches [] match probs = []
combineMatches [subst] match probs = 
    map (subst ++) (match (map (applyProbSubst subst) probs))


            
       
         
-- notFound exVars subst  delivers all variables of exVars for which no
--                        substitution is found
notFound :: [Vari] -> Subst -> [Vari]
notFound exVars subst =  exVars \\ domSubst subst
            

definedBefore :: LContext -> Vari -> Term -> Bool
definedBefore con v t = let vcon' = con `afterVar` v
                            fvt = fv t in
                        not (any (`elemC` fvt) vcon') 

afterVar :: LContext -> Vari -> [Vari]
afterVar con v =  map fst (fst (breakIL (==v) con))
