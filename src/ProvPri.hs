-- File: ProvPri
-- Description: This module defines functions for printing in the prove-mode
--              of the proof assistant.

module ProvPri(printGoal, showNumHistory, showHistory, printTermSt, printOcc)
              where

import HaTuple
import General
import Collect(AssocList(..))

--import Basic
--import Paths(Path,dummyPath)
--import SyntaxI
--import ProvDat
import Engine

import Display
import Printer

---------------------------------------
-- P R I N T I N G   R O U T I N E S --
---------------------------------------

-- printGoal print a goal without its local context
printGoal :: DisplayTerm a -> SyntaxInfo -> Path -> (Hnum,Goal) -> a
printGoal stuff@(conc,_,bas,label) si path (n,(term,_,_)) =
        conc[bas (if extractOptShowProofterm si then
                     printHnumSt si n ++ " : "
                  else
                     ""),
             printTerm stuff si path term]
  
-------------------------------------
-- P R I N T I N G   T A C T I C S --
-------------------------------------

showNumHistory :: SyntaxInfo -> ([TacPath],TacticTree) -> [String]
showNumHistory si (tacPaths,tacTree) =
    if null tacPaths then
       map snd (printStructTacTree si tacTree)
    else
       let tacPath = head tacPaths
           len = length tacPath                 
           showNumBas n = show (len - n) ++ ") "
           maxShowLen = length (showNumBas 0)
           showNum n = let s = showNumBas n in
                       s ++ replicate (maxShowLen - length s) ' ' 
           makeNum path = if tacPath `beginsWith` path then
                             showNum (length path)
                          else
                             replicate maxShowLen ' '
           makeString (path,s) = makeNum path ++ s in
       map makeString (printStructTacTree si tacTree)

-- this command is used when exiting the prover
showHistory :: SyntaxInfo -> String -> TacticTree -> [String]
showHistory si s tacTree = printTacTree si tacTree ++ [s]
   
-- printTacTree just prints the tree pre-order          
printTacTree :: SyntaxInfo -> TacticTree -> [String]
printTacTree si (TTHole (_,_)) = ["?"]
printTacTree si (TTTac tac _ trees) =
   printTac si tac :
   concat (map (printTacTree si) trees)

dummyTacPath :: TacPath
dummyTacPath = [-1]

-- printStructTacTree prints the tree in a structured way, and annotates
-- each line that displays a tactic with the path of that tactic
printStructTacTree :: SyntaxInfo -> TacticTree -> [(TacPath,String)]   
printStructTacTree si tacTree = printStructTacTree' si (tacTree,[])

printStructTacTree' :: SyntaxInfo -> (TacticTree,TacPath) -> 
                       [(TacPath,String)]   
printStructTacTree' si (TTHole (_,_), tp) = [(tp,"?")]
printStructTacTree' si (TTTac tac _ trees, tp) =
   (tp,printTac si tac) :
   printStructTacTrees si (zip trees (map (\n -> tp++[n]) [0..]))

printStructTacTrees si [] = []
printStructTacTrees si [tree] = printStructTacTree' si tree
printStructTacTrees si trees = printStructTacTrees' si trees

printStructTacTrees' si [tree] =
    (dummyTacPath,"|") :
    indent "+- " "   " (printStructTacTree' si tree)
printStructTacTrees' si (tree:trees) =
    (dummyTacPath,"|") :
    (indent "+- " "|  " (printStructTacTree' si tree) ++
     printStructTacTrees' si trees)

indent :: String -> String -> [(TacPath,String)] -> [(TacPath,String)]
indent s1 s2 (s:ss) = (doSnd (s1++) s) : map (doSnd (s2++)) ss


printTac :: SyntaxInfo -> TacticTerm -> String
printTac si =                                               
   -- Set all the number of implicit arguments for each variable to zero,
   -- since the terms
   -- in tactics are pseudo-terms; they are not typed, and implicit
   -- arguments have not been inserted.
   -- (Switching off the option for implicit gives some strange side-effects
   --  for infix-operators with implicit arguments)
   let si' = insertImplicit (const emptyI) si in
   printTacticTerm si'

printTacticTerm :: SyntaxInfo -> TacticTerm -> String
printTacticTerm si t = let deconstructElse (t1 `TElse` t2) = (True,t1,t2)
                           deconstructElse _ = (False,undefined,undefined)
                           ts = breakListR deconstructElse t in
                       prList (printTacticFactor si) " Else " ts
                           
printTacticFactor :: SyntaxInfo -> TacticTerm -> String
printTacticFactor si t = let deconstructThen (t1 `TThen` ts) = (True,t1,ts)
                             deconstructThen _ = (False,undefined,undefined)
                             (t1,ts) = breakListL' deconstructThen t in
                         printTactic si t1 ++
                         prList' (printTacticAltList si) " Then " ts

prList' :: (a->[b]) -> [b] -> [a] -> [b]
prList' f sep ts = concat (map (\x -> sep ++ f x) ts)

breakListL' :: (a->(Bool,a,b)) -> a -> (a,[b])
breakListL' dec x = let (ok,l,r) = dec x
                        (l',rs) = breakListL' dec l in
                    if ok then
                       (l',rs++[r])
                    else
                       (x,[])

printTacticAltList si [t] = printTactic si t
printTacticAltList si ts = "(" ++ prList (printTac si) " | " ts ++ ")"
                            

printTactic :: SyntaxInfo -> TacticTerm -> String
printTactic si (TIntroVar vs) =        "Intro " ++ printVarListSt si vs
printTactic si TIntro =                "Intro"
printTactic si TIntros =               "Intros"
printTactic si (TIntrosNum n) =        "Intros " ++ show n
printTactic si TAssumption =           "Assumption"
printTactic si (TLet v t) =            "Let " ++ printShortDefSt si (v,t)
printTactic si (TLetW v t u) =         "Let " ++ printDefSt si (v,t,u)
printTactic si (TUnfold (occ,v)) =     "Unfold " ++ printOccs occ ++
                                       printVarSt si v 
printTactic si (TUnfoldIn (occ,v,h)) = "Unfold " ++ printOccs occ ++
                                       printVarSt si v ++ " In " ++
                                       printVarSt si h
printTactic si TSimplify =             "Simplify"
printTactic si (TConvert t) =          "Convert " ++ printTermITSt si t
printTactic si (TCut t) =              "Cut " ++ printTermITSt si t
printTactic si (TFirst t) =            "First " ++ printTermITSt si t
printTactic si (TForward t) =          "Forward "++ printExtTermITSt si t
printTactic si (TExact t) =            "Exact " ++ printTermITSt si t
printTactic si (TLewrite (occ,t)) =    "Lewrite " ++ printMaybeOcc occ ++
                                       printExtTermITSt si t
printTactic si (TRewrite (occ,t)) =    "Rewrite " ++ printMaybeOcc occ ++
                                       printExtTermITSt si t
printTactic si (TLewriteIn (occ,t,h))= "Lewrite " ++ printMaybeOcc occ ++
                                       printExtTermITSt si t ++ " In " ++
                                       printVarSt si h
printTactic si (TRewriteIn (occ,t,h))= "Rewrite " ++ printMaybeOcc occ ++
                                       printExtTermITSt si t ++ " In " ++
                                       printVarSt si h
printTactic si TRefl =                 "Refl"
printTactic si TAndI =                 "AndI"
printTactic si (TAndEL t) =            "AndEL " ++ printExtTermITSt si t
printTactic si (TAndER t) =            "AndER " ++ printExtTermITSt si t
printTactic si (TAndE t) =             "AndE " ++ printExtTermITSt si t
printTactic si TOrIL =                 "OrIL"
printTactic si TOrIR =                 "OrIR"
printTactic si (TOrE t) =              "OrE " ++ printExtTermITSt si t
printTactic si TNotI =                 "NotI"
printTactic si (TNotE t) =             "NotE " ++ printExtTermITSt si t
printTactic si TFalseE =               "FalseE"
printTactic si (TExistsI t) =          "ExistsI " ++ printTermITSt si t
printTactic si (TExistsE t) =          "ExistsE " ++ printExtTermITSt si t
printTactic si (TApply t) =            "Apply " ++ printExtTermITSt si t
printTactic si (TPattern (occ,t)) =    "Pattern " ++ printOccs occ ++ 
                                       printTermITSt si t
printTactic si (THide vs) =            "Hide " ++ printVarListSt si vs
printTactic si (TUnhide vs) =          "Unhide " ++ printVarListSt si vs
printTactic si TUnhideAll =            "Unhide"
printTactic si (TRepeat t)=            "Repeat " ++ printTactic si t
printTactic si (TTry t)=               "Try " ++ printTactic si t
printTactic si t =                     "(" ++ printTacticTerm si t ++ ")"

printOcc :: Occurrence -> String
printOcc (NumOccurrence n) = show n
printOcc (PathOccurrence p) = prList show " " (0:p)

printMaybeOcc :: Occurrence -> String
printMaybeOcc (NumOccurrence 1) = ""
printMaybeOcc occ = printOcc occ ++ " "

printOccs :: [Occurrence] -> String
printOccs [] = ""
printOccs occs = commas (map printOcc occs) ++ " "


printDefSt :: SyntaxInfo -> (Vari,TermIT,TermIT) -> String
printDefSt si (v,d,t) = printVarSt si v ++ " := "  ++ 
                        printTermITSt si d ++ " : " ++
                        printTermITSt si t

printShortDefSt :: SyntaxInfo -> (Vari,TermIT) -> String
printShortDefSt si (v,d) = printVarSt si v ++ " := " ++ printTermITSt si d
    
printTermITSt :: SyntaxInfo -> TermIT -> String
printTermITSt si t = printTermSt si (forgetIT t)

printExtTermITSt :: SyntaxInfo -> ExtTermIT -> String
printExtTermITSt si (t,[]) = printTermITSt si t
printExtTermITSt si (t,ts) = printTermITSt si t ++ " On " ++
                             printTermsITSt si ts

printTermsITSt :: SyntaxInfo -> [TermIT] -> String
printTermsITSt si (t:ts) = printTermITSt si t ++ 
                           concat (map ((", "++).printTermITSt si) ts)

printTermSt :: SyntaxInfo -> Term -> String
printTermSt si t = printTerm displayString si dummyPath t

