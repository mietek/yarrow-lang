-- File: Reduce
-- Description: This module defines beta and delta-reduction and associated
--   notions. It has contains an efficient routine for checking equivalence
--   of terms.

module Reduce(Reduction, 
              maybeRedexBasic, maybeRedexNonb, maybeRedexBind, 
              neverRedexBasic, neverRedexNonb, neverRedexBind, 
              bdcom, bcom, dcom, bnf, bnfNC, redSeq, bwhRed, bdwhRed, swhRed,
              bwhnf, bdwhnf, bdswhnf, bEqual, bdEqual,
              standard, unwindApps, unstandard) where

import HaTuple
import General
import Basic
import Collect


-- a reduction relation can be dependend on the context. The boolean says
-- whether the term could be reduced
type Reduction = Context -> Term -> (Bool,Term)
  

-----------------------
-- R E D U C T I O N --
-----------------------

-- these reduction routines could be coded more neatly with deconstruct 
-- instead of pattern matching, but this is not done for efficiency

-- beta-reduction
bRed :: Reduction
bRed _ (Nonb App [Bind (Abs _) _ (x,_,_) e, u]) = (True,subst e x u)
-- Extension: Records:    
bRed _ (Nonb (RecSelect l) [Nonb (RecValue ls) ts]) =
       (True, snd (head (filter ((l==).fst) (zip ls ts))))
-- End Extension: Records:
bRed _ t = (False,t)   

-- Make sure that reduction only inspects the head of the term,
-- which is in our representation the head of the list of subterms.
-- In this way sound weak head reduction (and so matching) are ensured.
-- Counterexamples:
--       1. A representation of application, where the argument is the head
--       2. Inductive datatypes, so that we have, for example
--            recursor (S n) b f  > f (recursor n b f)
--          where all spaces are applications.
--          We have to adapt our scheme for this case.

-- delta-reduction
dRed :: Reduction
dRed c (Basic (Vr x)) = findDef c x
dRed c (Bind Delta _ (x,_,_) t) | x `notElemC` fv t = (True,t)
dRed _ t  = (False,t)
                             

-- Extension: Subtyping:
-- sigma-reduction lets a variable reduce to its bound
sRed :: Reduction
sRed c (Basic (Vr x)) = findSubBound c x
sRed _ t  = (False,t)
-- End Extension: Subtyping

                             

--------------------
-- WHEN REDUCTION --
--------------------

-- These functions determine which categories of basic, non-binder and
-- binder terms maybe redices. Their definitions can be easily derived
-- from the functions bRed and dRed above.
-- These functions help to make an efficient matching routine.

maybeRedexBasic :: BasicCat -> Bool
maybeRedexBasic (Vr _) = True
maybeRedexBasic (Srt _) = False

neverRedexBasic :: BasicCat -> Bool
neverRedexBasic = not . maybeRedexBasic


maybeRedexNonb :: NonbCat -> Bool
maybeRedexNonb App = True      
-- Extension: Records:
maybeRedexNonb (RecValue _) = False
maybeRedexNonb (RecType _) = False
maybeRedexNonb (RecSelect _) = True
-- End Extension: Records

neverRedexNonb :: NonbCat -> Bool
neverRedexNonb = not . maybeRedexNonb


maybeRedexBind :: BindCat -> Bool
maybeRedexBind (Abs _) = False
maybeRedexBind (All _) = False
maybeRedexBind Delta = True

neverRedexBind :: BindCat -> Bool
neverRedexBind = not . maybeRedexBind

neverRedex :: Term -> Bool
neverRedex (Basic cat) = neverRedexBasic cat
neverRedex (Nonb cat _) = neverRedexNonb cat
neverRedex (Bind cat _ _ _) = neverRedexBind cat

                             

-- compat makes a reduction relation compatible in a left-most way
-- Recursive calls of comp have to adjust the context, because of
-- definitions.

compat :: Reduction -> Reduction
compat red c t = let (res,t2) = red c t in
                 if res then (res,t2)
                 else compat2 red c t
                                                  
compat2 :: Reduction -> Reduction
compat2 _ _ b | isBasic b = (False,b)
compat2 red c nb | isNonb nb = let (_,cat,ts) = deconstructNonb nb
                                   (res,ts') = compatHelp red c ts in
                               (res, mkNonb cat ts')
compat2 red c bi | isBind bi = 
                let (_,cat,ts,it@(v,t,s),u) = deconstructBind bi
                    (res,ts') = compatHelp red c ts in
                if res then
                    (res,mkBind cat ts' it u)
                else
                let (res,t') = compat red c t in
                if res then
                    (res,mkBind cat ts (v,t',s) u)
                else
                let (Bind cat' ts' it' u') = changeVar bi (domCon c)
                    c' = mkContextE (convBindToCont cat') ts' it' `addC` c
                    (res,u'') = compat red c' u' in
                (res,mkBind cat' ts' it' u'')
            

compatHelp :: Reduction -> Context -> [Term] -> (Bool,[Term])
compatHelp red c [] = (False,[])
compatHelp red c (t:ts) = let (res,t') = compat red c t in
                          if res then
                             (res, t':ts)
                          else
                             doSnd (t:) (compatHelp red c ts)


-- compose two reduction relations
compose :: Reduction -> Reduction -> Reduction
compose red1 red2 c t = let (res,t2) = red1 c t in
                        if res then (res,t2)
                        else red2 c t
        
bdRed :: Reduction                   
bdRed = compose bRed dRed
  
-- Extension: Subtyping:
bdsRed :: Reduction
bdsRed = compose bdRed sRed  
-- End Extension: Subtyping

bdcom :: Reduction                   
bdcom = compat bdRed

bcom :: Reduction                   
bcom = compat bRed                   

dcom :: Reduction                   
dcom = compat dRed                   


---------------------------
--  S T R A T E G I E S  --
---------------------------
                                  
redSeq :: Reduction -> Context -> Term -> [Term]
redSeq red c t = t:(
                 let (reduced,rt) = red c t in
                 if reduced then redSeq red c rt
                 else [])

nf :: Reduction -> Context -> Term -> Term
nf red c t = let (reduced,rt) = red c t in
              if reduced then
                 nf red c rt
              else
                 t
                                                 
-- nf' says if a reduction was done
nf' :: Reduction -> Context -> Term -> (Bool,Term)
nf' red c t = let (reduced,rt) = red c t in
              if reduced then
                 (True, nf red c rt)
              else
                 (False,t)

-- beta delta normal form
bdnf :: Context -> Term -> Term                
bdnf = nf (compat bdRed)


-- beta normal form
bnf :: Context -> Term -> Term                    
bnf = nf (compat bRed)
                     
-- For beta-reduction, the context is not relevant, so we have a special
-- version that doesn't need the context as argument.
bnfNC :: Term -> Term                                
bnfNC = bnf emptyCon
 
  
-- wh strategy
-- wh red does, if possible, a red-reduction in the head
-- i.e. only if the red-reduction is possible right away, or in the left-side
-- of an application (or in general, of a non-binder construct).
wh :: Reduction -> Reduction
wh red c t =  let (res,t') = red c t in
              if res then (res,t')
              else 
              let (isNonb,cat,ts) = deconstructNonb t in
              if isNonb && maybeRedexNonb cat && not (null ts) then
                 let (t1:ts') = ts in
                 doSnd (\h -> Nonb cat (h:ts')) (wh red c t1)
              else
              -- We may ignore basic terms, since they have no subterms.
              -- We ignore binder terms, since currently they don't
              -- wh-reduce.
                 (False,t)

bwhRed :: Reduction
bwhRed = wh bRed

 
-- weak head delta strategy
-- whdRed does, if possible, one OR MORE reductions in the head
-- it totally unfolds local definitions, this corresponds to multiple 
-- ordinary delta reduction steps. This is more efficient than doing them one
-- at a time.
-- whdRed should only be applied to (combined) delta reduction routines.
whdRed:: Reduction -> Reduction
whdRed red c t =
             let (res,t') = red c t in
             if res then (res,t')
             else 
             let (isNonb,cat,ts) = deconstructNonb t in
             if isNonb && maybeRedexNonb cat && not (null ts) then
                let (t1:ts') = ts in
                doSnd (\h -> Nonb cat (h:ts')) (whdRed red c t1)
             else
             let (isDelta,(v,d,_,_),u) = deconstructDelta t in
             if isDelta then
                (True, subst u v d)
             else
                -- We may ignore basic terms, since they have no subterms.
                -- There are no other reducing binder constructs, currently.
                (False,t)
         
                   
bdwhRed :: Reduction
bdwhRed = whdRed bdRed

-- Extension: Subtyping:
swhRed :: Reduction
swhRed = wh sRed

-- weak head beta delta sigma reduction
bdswhRed :: Reduction
bdswhRed = whdRed bdsRed
-- End Extension: Subtyping
   

-- beta weak head normal form (no context is expected)
bwhnf :: Term -> Term                  
bwhnf = nf bwhRed emptyCon

-- beta delta weak head normal form
bdwhnf :: Context -> Term -> Term                   
bdwhnf = nf bdwhRed
     
-- Extension: Subtyping:
-- beta delta sigma weak head normal form
bdswhnf :: Context -> Term -> Term                   
bdswhnf = nf bdswhRed
-- End Extension: Subtyping
    
bdwhnf' :: Context -> Term -> (Bool,Term)
bdwhnf' = nf' bdwhRed



-- checks whether two terms are equal up to bd-reduction
-- a more efficient check is implemented by bdEqual below.
slowbdEqual c t u = (bdnf c t) == (bdnf c u)
                          
bEqual :: Term -> Term -> Bool
bEqual t1 t2 = bnf emptyCon t1 == bnf emptyCon t2

----------------------------------------------------
--  E Q U I V A L E N C E   O F   T E R M S       --
----------------------------------------------------

-- We could check beta-delta-equivalence of terms just by comparing
-- the normal forms. However, this is very inefficient.
-- So here follows a more efficient test for equivalence.


-- standard form brings (typable) term to beta weak head normal form
-- 1) t t1 .. tn        , where t is a variable or local definition
-- 2) \x:t1.t2
-- 3) @x:t1.t2
-- 4) let x:=t1.t2
-- in case 1, the list [x,t1,..tn] is returned, in the other cases
-- just a singleton
standard :: Term -> [Term]
standard t = unwindApps (bwhnf t)

unwindApps :: Term -> [Term]
unwindApps t = unwindApps' t []     

unwindApps' :: Term -> [Term] -> [Term]                    
unwindApps' t l | isApp t = let (_,t1,t2) = deconstructApp t in
                            unwindApps' t1 (t2:l)
unwindApps' t l = t:l


unstandard :: [Term]->Term
unstandard = foldl1 mkApp  

bdEqual :: Context -> Term -> Term -> Bool 
bdEqual c t u = bdEqual' c (bwhnf t) (bwhnf u)


{-
-- FOR TESTING (TRACES) ONLY.
prT si t = printTerm displayString si dummyPath t
-}

bdEqual' con t u =  -- FOR TESTING (TRACES) ONLY
                    {- trace ("bdEqual: "++
                                 prT dummySyntax t ++" =? "++
                                 prT dummySyntax u++"\n") -}
                         bdEqual'' con t u


-- Plan for bdEqual'' c t u
-- Consider the terms in the following order
-- 1. Both are a variable or an application
-- 2. At least one of the terms can never reduce.
-- 3. Both terms belong to may reduce
bdEqual'' :: Context -> Term -> Term -> Bool        

-- We make a special case for the frequent occurring situation that
-- both sides are applications or variables. This is purely for efficiency.
-- 1) unwind all applications, this results in two lists.
-- 2) check on alpha-equality of the heads and bd-equality of the tails.
--    If that's the case, we know the terms are equal without reducing the
--    heads.
-- 3) Otherwise we reduce one or two of the heads, and try again.
bdEqual'' c t u | (isVar t || isApp t) && 
                  (isVar u || isApp u) =
                 let lt = unwindApps t
                     lu = unwindApps u
                     sameHead = head lt == head lu
                     sameLength = length lt == length lu
                     sameTerms = and (zipWith (bdEqual c)
                                              (tail lt) (tail lu)) in
                 (sameHead && sameLength && sameTerms) ||
                 -- It seems more efficient to reduce at most one head.
                 -- If both are variables, it probably is
                 -- best to unfold the newest definition.             
                 -- Experiments with this in practice are discouraging.
                 -- Other experiments to improve this as well.
                 (let (isRedext,t') = reduceHead c lt
                      (isRedexu,u') = reduceHead c lu
                      newT = if isRedext then bwhnf t' else t
                      newU = if isRedexu then bwhnf u' else u in
                  (isRedext || isRedexu) && bdEqual' c newT newU) 

-- The next three clauses handle the cases where at least one of the sides
-- can never reduce (in DPTSs sort, lambda and all).
bdEqual'' c t u | neverRedex t && neverRedex u =
    case (t,u) of
      (Basic cat1, Basic cat2) | cat1 == cat2 ->
                      True
      (Nonb cat1 ts1, Nonb cat2 ts2) | cat1 == cat2 ->
                      and (zipWith (bdEqual c) ts1 ts2)
      (Bind cat1 ts1 i1 u1, Bind cat2 ts2 i2 u2) | cat1 == cat2 ->
                      bdEqualHelp c cat1 ts1 i1 u1 ts2 i2 u2
      _ -> False
bdEqual'' c t u | neverRedex u = let (ok,t') = bdwhnf' c t in
                                 ok && bdEqual' c t' u
bdEqual'' c t u | neverRedex t = let (ok,u') = bdwhnf' c u in
                                 ok && bdEqual' c t u'

-- Now the ordinary cases for reducable categories.
-- If two terms are bd-equivalent, either they are the same category and
-- all subterms are equivalent, or one of the terms is not yet in
-- head normal form.
bdEqual'' c t u =
    case (t,u) of
      (Basic cat1, Basic cat2) | cat1 == cat2 -> 
            True
      (Nonb cat1 ts1, Nonb cat2 ts2) | cat1 == cat2 ->
            and (zipWith (bdEqual c) ts1 ts2) || defaul
      (Bind cat1 ts1 i1 u1, Bind cat2 ts2 i2 u2) | cat1 == cat2 ->
            bdEqualHelp c cat1 ts1 i1 u1 ts2 i2 u2 || defaul
      _ -> defaul
    where defaul = 
           let (isRedext,t') = bdwhRed c t
               (isRedexu,u') = bdwhRed c u
               newT = if isRedext then (bwhnf t') else t
               newU = if isRedexu then (bwhnf u') else u in
           (isRedext || isRedexu) && bdEqual' c newT newU
            

reduceHead :: Context-> [Term] -> (Bool,Term)
reduceHead c l = let (reduces,head') = bdwhRed c (head l) in
                 if reduces then
                    (True,unstandard (head' : tail l))
                 else
                    (False,dummyTerm)


-- The check on sorts is not necessary but helps improve efficiency slightly.
bdEqualHelp c cat ts1 it@(v1,t1,s1) u1 ts2 (v2,t2,s2) u2 =
          s1 == s2 &&
          bdEqual c t1 t2 &&
          and (zipWith (bdEqual c) ts1 ts2) && (
          let (v12',u1',u2') = equateVarsBinders (domCon c) (v1,u1) (v2,u2)
              c' = (v12',((t1,s1),convBindToCont cat,ts1)) `addC` c in
          bdEqual c' u1' u2'
          )
