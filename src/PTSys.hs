-- File: PTSys
-- Description: In this module we define
--   + a number of PTS's
--   + routines for determing whether a system normalizes 
-- Note: The definition of the type "System" and topSort is in module basic
 
module PTSys(axiom, typeSort, rule12, rule13, rules13, ruleSub12, rulesSub13,
             normalizing, nonNormalizing, systemLWL, systemC, partSystem,
             updateSortsOfDefsInContext, updateSortsOfDefsInContextEList
            ) where
 
import General
import HaTuple
import Basic
import SyntaxI
import Collect

----------------------------
-- SOME PURE TYPE SYSTEMS --
----------------------------
                        
noExtensions :: ExSystem
noExtensions = ([])

ptsToPtsSub :: ([Sort],[(Sort,Sort)],[(Sort,Sort,Sort)]) -> PTSystem
ptsToPtsSub (s,a,r) = (s,a,r,[],[])

systemLWL =    
  let set = SORT "*s"
      setkind =  SORT "#s"
      prop =  SORT "*p"
      propkind =  SORT "#p"

      sorts = [set,setkind,prop,propkind]
      axioms = [(set,setkind),(prop,propkind)]
      rules = makeTriples
              [(prop,prop),(propkind,prop),(propkind,propkind),
               (set,prop),(set,propkind),(setkind,prop),(setkind,propkind),
               (set,set),(setkind,set),(setkind,setkind)
              ] in
  (ptsToPtsSub (sorts,axioms,rules),noExtensions)

systemC :: System
systemC = 
  let star = SORT "*"
      block = SORT "#"
      sorts = [star,block]
      axioms = [(star,block)]
      rules = makeTriples
              [(star,star), (block,star),
               (star,block),(block,block)
              ] in
  (ptsToPtsSub (sorts,axioms,rules),noExtensions)
                         
-- systemC + records.
systemCR :: System
systemCR = (fst systemC, [(SORT "*",Records)])


systemUm :: System
systemUm =
  let star = SORT "*"
      block = SORT "#"
      triangle = SORT "##"
      sorts = [star,block,triangle]
      axioms = [(star,block),(block,triangle)]
      rules = makeTriples
              [(star,star),(block,star),
               (block,block),(triangle,block)
              ] in
  (ptsToPtsSub (sorts,axioms,rules),noExtensions)


makeTriples :: [(Sort,Sort)] -> [(Sort,Sort,Sort)]
makeTriples = map (\(s1,s2) -> (s1,s2,s2))

     
-------------------------------
-- FUNCTIONS USED FOR TYPING --
-------------------------------
                       
-- contains the axioms of the system
axiom :: SyntaxInfo -> Sort -> (Bool,Sort)
axiom si s = foundAL (extractAxioms si) topSort s
                                    
-- typeSort si s  gives the type of a sort, and type topSort to to
--                top-sorts
-- according to the axioms
typeSort :: SyntaxInfo -> Sort -> Sort
typeSort si s = snd (axiom si s)

-- rule12 contains the rules R of the functional type system
-- (s1,s2,s3) in R <=> s3 = rule12 s1 s2
rule12 :: SyntaxInfo -> Sort -> Sort -> (Bool,Sort)
rule12 si s1 s2 = let rules = extractRules si
                      rules' = map (\(s1,s2,s3) -> ((s1,s2),s3)) rules in
                  foundAL rules' topSort (s1,s2)
                                                    
-- rule13 contains the rules R of the bijective type system, in another way
-- (s1,s2,s3) in R <=> s2 = rule13 s1 s3
rule13 :: SyntaxInfo -> Sort -> Sort -> (Bool,Sort)    
rule13 si s1 s3 = let rules = extractRules si
                      rules' = map (\(s1,s2,s3) -> ((s1,s3),s2)) rules in
                  foundAL rules' topSort (s1,s3)

-- rules13 contains the rules R of the functional type system, in another way
-- (s1,s2,s3) in R <=> s2 in rules13 s1 s3
rules13 :: SyntaxInfo -> Sort -> Sort -> [Sort]    
rules13 si s1 s3 = let rules = extractRules si
                       rules' = map (\(s1,s2,s3) -> ((s1,s3),s2)) rules in
                   findAll rules' (s1,s3)

-- Extension: Subtyping:
-- ruleSub12 contains the rules Rsub of the functional type system
-- (s1,s2,s3) in Rsub <=> s3 = ruleSub12 s1 s2
ruleSub12 :: SyntaxInfo -> Sort -> Sort -> (Bool,Sort)
ruleSub12 si s1 s2 = 
              let rules = extractRulesSub si
                  rules' = map (\(s1,s2,s3) -> ((s1,s2),s3)) rules in
              foundAL rules' topSort (s1,s2)

-- rulesSub13 contains the rules Rsub of the functional type system,
-- in another way
-- (s1,s2,s3) in Rsub <=> s2 in rulesSub13 s1 s3
rulesSub13 :: SyntaxInfo -> Sort -> Sort -> [Sort]    
rulesSub13 si s1 s3 = let rules = extractRulesSub si
                          rules' = map (\(s1,s2,s3) -> ((s1,s3),s2)) rules in
                      findAll rules' (s1,s3)
-- End Extension: Subtyping


-----------------------------------
-- NORMALIZATION OF TYPE SYSTEMS --
-----------------------------------

-- first define mappings from one list to another

type Mapping a b = [(a,b)]

makeAllMappings :: [a] -> [b] -> [Mapping a b]
makeAllMappings [] ys = [[]]       -- the empty mapping
makeAllMappings (x:xs) ys = 
        let maps = makeAllMappings xs ys in
        concat (map (\p -> map (p:) maps) (map (pair x) ys))
                 
type MappingS = Mapping Sort Sort


-- preserveR1  expresses that a mapping preserves an unary relation
-- preserveR1 :: (Eq a,Eq b) => 
--              [a] -> [b] -> Mapping a b -> Bool
preserveR1 r1 r2 mapping =
         let pres1so s1 = let s1' = snd (findAL mapping s1) in
                          s1' `elem` r2 in
         all pres1so r1

-- preserveR2  expresses that a mapping preserves a binary relation
-- preserveR2 :: (Eq a,Eq (b,b)) => 
--              [(a,a)] -> [(b,b)] -> Mapping a b -> Bool
preserveR2 r1 r2 mapping =
         let pres1ax (s1,s2) = let s1' = snd (findAL mapping s1)
                                   s2' = snd (findAL mapping s2) in
                               (s1',s2') `elem` r2 in
         all pres1ax r1

-- preserveR3  expresses that a mapping preserves a tertiary relation
-- preserveR3 :: (Eq a,Eq (b,b,b)) => 
--               [(a,a,a)] -> [(b,b,b)] -> Mapping a b -> Bool
preserveR3 r1 r2 mapping =
         let pres1ax (s1,s2,s3) = let s1' = snd (findAL mapping s1)
                                      s2' = snd (findAL mapping s2)
                                      s3' = snd (findAL mapping s3) in
                                  (s1',s2',s3') `elem` r2 in
         all pres1ax r1


-- subSystem sys1 sys2  returns True iff sys1 is a sub-system of sys2, i.e.
-- if sys1 can be mapped to sys2
subSystem :: System -> System -> Bool
subSystem ((s1,a1,r1,ss1,rs1),ex1) ((s2,a2,r2,ss2,rs2),ex2) = 
       let maps = makeAllMappings s1 s2 in
       any (\m -> let applyM = snd.findAL m 
                      applyMEx exS = map (doFst applyM) exS in
                  preserveR2 a1 a2 m && 
                  preserveR3 r1 r2 m &&
                  preserveR1 ss1 ss2 m &&
                  preserveR3 rs1 rs2 m &&
                  applyMEx ex1 `partExSystem` ex2)
           maps

-- A PTS is normalizing if it is a sub-system of lambda-CR
normalizing :: System -> Bool
normalizing s = s `subSystem` systemCR

-- A PTS is non-normalizing if lambda-U-minus is a sub-system of it
nonNormalizing :: System -> Bool
nonNormalizing s = systemUm `subSystem` s


partSystem :: System -> System -> Bool
partSystem (pts1,exs1) (pts2,exs2) = pts1 `partPTSystem` pts2 &&
                                     exs1 `partExSystem` exs2
                                
-- sys1 `partPTSystem` sys2  return True iff sys1 is a part of sys2, i.e.
-- 1. the sorts  of sys1 are a subset of the sorts  of sys2.
-- 2. the axioms of sys1 are a subset of the axioms of sys2.
-- 3. the rules  of sys1 are a subset of the rules  of sys2.
partPTSystem :: PTSystem -> PTSystem -> Bool
partPTSystem (s1,a1,r1,ss1,rs1) (s2,a2,r2,ss2,rs2) = 
          s1 `sublist` s2 && a1 `sublist` a2 && r1 `sublist` r2 &&
          ss1 `sublist` ss2 && rs1 `sublist` rs2
                                            
-- partExSystem checks whether one list of extensions is a subset of another.
-- In the future, this may depend on specific extensions.
partExSystem :: ExSystem -> ExSystem -> Bool
partExSystem exS1 exS2 = exS1 `sublist` exS2




----------------------------
-- Moving to a bigger PTS --
----------------------------

-- When we move a context from a PTS to a bigger PTS, it is still valid...
-- ALMOST!
-- The sort annotation in definitions may become faulty. This happens only
-- when the annotated sort is Top (the additional sort above all top-level
-- sorts), but in the new system there is an ordinary sort for this 
-- definition.
-- E.g. in lambda-C
--          s := * : # : Top
--      moving to a system where # has a type:
--          system (*,#,##), (*:#,#:##), ..
--      the correct sort annotation is as follows:
--          s := * : # : ##
-- This section updates all sorts in global and local definitions.

-- Pre: oldSys `partSystem` newSys
-- This function makes sure that all global and local definitions have the
-- correct sort annotation when moving to a bigger type-system.
-- The only time when a sort annotation has to be adapted, is when this
-- sort is Top, and this is not correct in newSys.
-- In this case the type of the definition is such a top-level sort in 
-- oldSys, which is no longer a top-level sort in newSys.
updateSortsOfDefsInContext :: System -> System -> GContext -> GContext
updateSortsOfDefsInContext oldSys newSys@((_,newAxs,_,_,_),_) con = 
      let updateTyps = newTopLevelSorts oldSys newSys in
      if null updateTyps then
          -- Nothing to change
          con
      else
          let update' x = snd (updateSortsOfDefsInCE updateTyps 
                                                     newAxs (undefined,x)) in
          mapI update' con

updateSortsOfDefsInContextEList :: System -> System -> [ContextE] -> 
                                   [ContextE]
updateSortsOfDefsInContextEList oldSys newSys@((_,newAxs,_,_,_),_) con = 
      let updateTyps = newTopLevelSorts oldSys newSys in
      if null updateTyps then
          -- Nothing to change
          con
      else
          map (updateSortsOfDefsInCE updateTyps newAxs) con

updateSortsOfDefsInCE :: [Term] -> [(Sort,Sort)] -> ContextE -> ContextE
updateSortsOfDefsInCE updateTyps newAxs ce | isDef ce =
    let (_,(v,d,t,s)) = deconstructDef ce in
    if t `elem` updateTyps then
        let (_,s') = findAL newAxs (snd (deconstructSort t))
            d' = updateSortsOfDefs updateTyps newAxs d in
        mkDef (v,d',t,s')
    else
        updateSortsOfDefsInCE' updateTyps newAxs ce
updateSortsOfDefsInCE updateTyps newAxs ce = 
    updateSortsOfDefsInCE' updateTyps newAxs ce 

updateSortsOfDefsInCE' :: [Term] -> [(Sort,Sort)] -> ContextE -> ContextE
updateSortsOfDefsInCE' updateTyps newAxs (v,((t,s),cat,ts)) =
            (v,((updateSortsOfDefs updateTyps newAxs t, s), cat,
                map (updateSortsOfDefs updateTyps newAxs) ts))

updateSortsOfDefs :: [Term] -> [(Sort,Sort)] -> Term -> Term
updateSortsOfDefs updateTyps newAxs def | isDelta def = 
    let (_,(v,d,t,s),u) = deconstructDelta def in
    if t `elem` updateTyps then
        let (_,s') = findAL newAxs (snd (deconstructSort t))
            d' = updateSortsOfDefs updateTyps newAxs d
            u' = updateSortsOfDefs updateTyps newAxs u in
        mkDelta (v,d',t,s') u'
    else
        updateSortsOfDefs' updateTyps newAxs def
updateSortsOfDefs updateTyps newAxs t = 
    updateSortsOfDefs' updateTyps newAxs t

updateSortsOfDefs' :: [Term] -> [(Sort,Sort)] -> Term -> Term
updateSortsOfDefs' updateTyps newAxs bas | isBasic bas = bas
updateSortsOfDefs' updateTyps newAxs nonb | isNonb nonb =
    let (_,cat,ts) = deconstructNonb nonb in
    mkNonb cat (map (updateSortsOfDefs updateTyps newAxs) ts)
updateSortsOfDefs' updateTyps newAxs bind | isBind bind =
    let (_,cat,ts,(v,t,s),u) = deconstructBind bind in
    mkBind cat (map (updateSortsOfDefs updateTyps newAxs) ts)
               (v, updateSortsOfDefs updateTyps newAxs t, s)
               (updateSortsOfDefs updateTyps newAxs u)



topLevelSorts :: System -> [Sort]
topLevelSorts ((s,a,_,_,_),_) = filter (not . fst . findAL a) s

newTopLevelSorts :: System -> System -> [Term]
newTopLevelSorts oldSys newSys = 
    map mkSrt (topLevelSorts oldSys \\ topLevelSorts newSys) 