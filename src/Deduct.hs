-- File: Deduct
-- Description: This module defines the function PrintProof, which prints a
--              proof in natural-deduction style.



module Deduct(printDeduct) where

import HaMonSt
import HaTuple
import Collect(AssocList(..),findAL,indexedToListIL)
import General
import Basic
import Paths(genErrS,errS,admitNoErr,internalErr)
import SyntaxI
import Printer
import Reduce
import Typing
import FancyTy(oldVarG)
import MainSta(SpecialLemmas)
import ProvPri(printTermSt)
import Errors(errorToStrings)
import LatexPr
import Command(OutputMode(..))

-------------------
--  B L O C K S  --
-------------------
                           
type Label = Int

data Block = Composite [Block] |     -- 0 or more blocks
             Line OneLine | 
             Flag Label [OneLine] Block   -- 1 or more declarations


                              
type Justif = (String,[Refer])
data Refer = RS String | RL Label | RF Formula

type Formula = String

type OneLine = (Label,String,Justif)

                      

         
hypJustif :: Justif
hypJustif = ("hyp",[])

ex1 :: Block
ex1 = Flag 1000 [(950, "P : *p",hypJustif),
                 (951, "Q : *p",hypJustif),
                 (1001,"P",hypJustif)]
                (Line (1002,"Q\\/P", ("\\/Ir",[RL 1001])))

ex2 :: Block
ex2 = Flag 1010 [(1011,"Q",hypJustif)]
                (Line (1012,"Q\\/P", ("\\/Il",[RL 1011])))

ex3 :: Block
ex3 = Flag 900 [(901,"P\\/Q",hypJustif)]
               (Composite [ex1,
                           ex2, 
                           Line (902,"Q\\/P", ("\\/E",[RL 901,RL 1000,RL 1010]))
                          ]
               )


data ReferTerm = RefLine String | RefTerm Term | RefRange ReferTerm ReferTerm

------------------------------
-- PRINTING BLOCKS IN ASCII --
------------------------------


 

printBlock :: DedOptions -> Block -> [String]
printBlock opt block =
   let (_,eTrips) = runState (1,[]) (printBlock1 opt 0 block) in
   handle eTrips
   (\e -> [])
   (\trips -> showTable3 " " "  " (RightAl,LeftAl,LeftAl) trips)

                 
test :: Block -> String
test block = concat (map (++"\n") (printBlock testOptions block))
                                      
testOptions = (False,False,False,False,False,False,False,False,False,False,
               OutAscii)

-- Labels and how they should be printed --|
-- Current number of hypotheses --|        |
-- Current line number --|        |        |
--                       v        v        v
type B a =      State ( Int,          [(Label,ReferTerm)]) a

fetchLineNo :: B Int
fetchLineNo = map fst fetchS4
            -- hbc 0.9999.4 will complain if we replace fetchS4 above by fetch,
            -- so we need a fetchS4 function with a more restricted type.

fetchS4 :: State s s
fetchS4 = fetch

incLineNo :: B ()
incLineNo = update' (doFst (+1))

{-
fetchHypsNo :: B Int
fetchHypsNo = map snd3 fetch
-}
         
lookupLabel :: Label -> B ReferTerm
lookupLabel label = map snd fetchS4 >>= \table ->
                    let (ok,ref) = findAL table label in
                    if ok then
                       return ref
                    else
                       internalErr "Unknown label"

addLabel :: Label -> ReferTerm -> B ()
addLabel label ref = update' (doSnd ((label,ref):))



printBlock1 :: DedOptions -> Int -> Block -> B [(String,String,String)]
printBlock1 opt noHyps (Composite blocks) = 
        map concat (mapL (printBlock1 opt noHyps) blocks)
printBlock1 opt noHyps (Line line) =
     map (\x -> [x]) (printLine opt noHyps "" "" line)
printBlock1 opt noHyps (Flag label lines block) =
     fetchLineNo >>= \lineStart ->
     let sizeFlag = maximum (map (length.snd3) lines)
         bar = replicate (4+sizeFlag) '-'
         trips0 = [("",pole noHyps ++ bar,"")]
         trips2 = [("",pole noHyps ++ '|':tail bar,"")]
         printLine' line@(_,form,_) = 
            printLine opt noHyps "| " 
                      (replicate (sizeFlag-length form) ' ' ++ " |") line in
     mapL printLine' lines >>= \trips1 ->
     printBlock1 opt (noHyps+1) block >>= \trips3 ->
     fetchLineNo >>= \lineEnd ->
     addLabel label (RefRange (RefLine (show lineStart)) 
                              (RefLine (show (lineEnd-1)))) >>
     return (trips0++trips1++trips2++trips3)

printLine opt noHyps extraBefore extraAfter (label,form,just) =
     fetchLineNo >>= \lineNo ->
     printJustif opt just >>= \justifString ->
     addLabel label (RefLine (show lineNo)) >>
     incLineNo >>
     return (show lineNo, 
             pole noHyps ++ extraBefore ++ form ++ extraAfter,
             justifString)

pole noHyps = concat (replicate noHyps "| ")
     

printJustif :: DedOptions -> Justif -> B String
printJustif opt (s,refers) = printRefers opt refers >>= \ss ->
                             return (s++" "++commas ss)

printRefers :: DedOptions -> [Refer] -> B [String]
printRefers opt [] = return []
printRefers opt (refer:refers) = 
    printRefer refer >>= \r ->
    map (r:) (mapL printRefer refers)


printRefer :: Refer -> B String
printRefer (RS s) = return s
printRefer (RF s) = return s
printRefer (RL label) = map printRef (lookupLabel label)

printRef :: ReferTerm -> String
printRef (RefLine n) = n
printRef (RefRange ref1 ref2) = printRef ref1 ++ "-" ++ printRef ref2
                          
------------------------------
-- PRINTING BLOCKS IN JAVA --
------------------------------

-- Borrows from ASCII printing:
-- 
-- type B a =      State ( Int,          [(Label,ReferTerm)]) a
-- fetchLineNo :: B Int
-- incLineNo :: B ()
-- lookupLabel
-- addLabel
-- printJustif
  
javaPrintBlock :: DedOptions -> Block -> [String]
javaPrintBlock opt block =
   let (_,ss) = runState (1,[]) (javaPrintBlock1 opt (flattenBlock block)) in
   handle ss
   (\e -> [])
   (\ss -> ss)

-- flattenBlock removes as many composites as possible
flattenBlock :: Block -> Block
flattenBlock bl = case flattenBlock' bl of
                  [b] -> b
                  bs -> Composite bs

flattenBlock' :: Block -> [Block]
flattenBlock' (Composite blocks) = 
  concat (map flattenBlock' blocks)
flattenBlock' l@(Line _) = [l]
flattenBlock' (Flag label lines block) = 
  [Flag label lines (flattenBlock block)]



addHead :: String -> [String] -> [String]
addHead s [] = [s]
addHead s (s1:ss) = (s++s1) : ss

addTail :: String -> [String] -> [String]
addTail s [] = [s]
addTail s [s1] = [s1++s]
addTail s (s1:ss) = s1 : addTail s ss

javaPrintBlock1 :: DedOptions -> Block -> B [String]
javaPrintBlock1 opt (Composite blocks) = 
     map (addHead "C ") (javaPrintList (javaPrintBlock1 opt) blocks)
javaPrintBlock1 opt (Line line) =
     map (addHead "L ") (javaPrintLine opt line)
javaPrintBlock1 opt (Flag label lines block) =
     fetchLineNo >>= \lineStart ->
     javaPrintList (javaPrintLine opt) lines >>= \ss1 ->
     javaPrintBlock1 opt block >>= \ss2 ->
     fetchLineNo >>= \lineEnd ->
     addLabel label (RefRange (RefLine (show lineStart)) 
                              (RefLine (show (lineEnd-1)))) >>
     return (addHead "F " ss1 ++ ss2)

javaPrintList :: (a -> B [String]) -> [a] -> B [String]
javaPrintList printItem items = 
     mapL printItem items >>= \pItems ->
     (return . addHead "(" . addTail ")" . concat) (map (addHead ",") pItems)

javaPrintLine opt (label,form,just) =
     fetchLineNo >>= \lineNo ->
     printJustif opt just >>= \justifString ->
     addLabel label (RefLine (show lineNo)) >>
     incLineNo >>
     return ["\"" ++ show lineNo ++ "\" \"" ++ form ++ "\" \"" ++ 
             justifString ++ "\""]
     
                   
------------------------------
-- PRINTING BLOCKS IN LaTeX --
------------------------------

-- Additional LaTeX commands generated:

-- Total proof
-- \begin{derivation}
-- \end{derivation}

-- Subproofs
-- \derline
-- \flagstart
-- \flagend

-- In justification
-- \dedconv
-- \dedsubsum
-- \leibnizrl
-- \leibnizlr

-- In flags
-- \has
-- \sub
-- \isd

latexPrintBlock :: Vari -> DedOptions -> Block -> [String]
latexPrintBlock name opt block =
   let (_,eTrips) = runState (1,[]) (latexPrintBlock1 name opt block) in
   handle eTrips
   (\e -> [])
   (\trips -> ["\\begin{derivation}"] ++
              trips ++
              ["\\end{derivation}"])

latexPrintBlock1 :: Vari -> DedOptions -> Block -> B [String]
latexPrintBlock1 name opt (Composite blocks) = 
     map concat (mapL (latexPrintBlock1 name opt) blocks)
latexPrintBlock1 name opt (Line line) =
     latexPrintLine name opt "\\derline" line
latexPrintBlock1 name opt (Flag label lines block) =
     fetchLineNo >>= \lineStart ->
     latexPrintHyps name opt lines >>= \trips1 ->
     latexPrintBlock1 name opt block >>= \trips2 ->
     fetchLineNo >>= \lineEnd ->
     addLabel label (RefRange (RefLine (show lineStart ++ flagInf ++ "1"))
                              (RefLine (show (lineEnd-1)))) >>
     return (trips1++trips2++["\\flagend"])

-- this routine and the resulting LaTeX input is a hack, but it performs
-- quite well
latexPrintHyps name opt lines =
     fetchLineNo >>= \lineNo ->
     latexPrintJustif name opt (thd3 (head lines)) >>= \justifString ->
     maplComs (\((l,_,_),fl) -> addLabel l 
                                (RefLine (show lineNo ++ flagInf ++ show fl))) 
              (zip lines [1..]) >>
     incLineNo >>
     return ["\\flagstart{" ++ name ++ show lineNo ++ flagInf ++ "}{" ++
             show (length lines) ++ "}{\\begin{array}{l}" ++
             concat (map ((++"\\\\").snd3) lines) ++ "\\end{array}}{" ++
             justifString++"}"]

-- flagInf is used to separate the number of the flag and the number of the
-- formula of the flag
flagInf = "f"
     
latexPrintLine name opt com (label,form,just) =
     fetchLineNo >>= \lineNo ->
     latexPrintJustif name opt just >>= \justifString ->
     addLabel label (RefLine (show lineNo)) >>
     incLineNo >>
     return [com ++ "{" ++ name ++ show lineNo ++ "}{" ++
             form ++ "}{"++justifString++"}"]
     
latexPrintJustif :: Vari -> DedOptions -> Justif -> B String
latexPrintJustif name opt (s,refers) = 
    latexPrintRefers name opt refers >>= \ss ->
    return (s++" "++commas ss)

latexPrintRefers :: Vari -> DedOptions -> [Refer] -> B [String]
latexPrintRefers name opt [] = return []
latexPrintRefers name opt (refer:refers) = 
    latexPrintRefer name refer >>= \r ->
    map (r:) (mapL (latexPrintRefer name) refers)
                                                                               
latexPrintRefer :: Vari -> Refer -> B String
latexPrintRefer _ (RS s) = return s
latexPrintRefer _ (RF s) = return ("$"++s++"$")
latexPrintRefer name (RL label) = map (latexPrintRef name) (lookupLabel label)

latexPrintRef :: Vari -> ReferTerm -> String
latexPrintRef name (RefLine n) = "\\ref{" ++ name ++ n ++ "}"
latexPrintRef name (RefRange ref1 ref2) = 
    latexPrintRef name ref1 ++ "-" ++ latexPrintRef name ref2


-----------------------
-- MAKING DEDUCTIONS --
-----------------------

type D a = State Int a

newLabel :: D Int
newLabel = update (+1)

type SLemmas = [(Vari,(Int,Vari,String))]

type Stuff = (SyntaxInfo, DedOptions, SLemmas, Context, Sort, [(Vari,Refer)])

printDeduct :: SyntaxInfo -> SpecialLemmas -> Context -> Vari -> 
               (Term,Term,Sort) -> Int -> OutputMode -> E [String]
printDeduct si lemmas con name (t,typ,sort) opt0 outputMode = 
  let opt = makeOpt opt0 outputMode
      lemmas' = map (\((a,b,_),(c,d)) -> (c,(d,a,b))) (indexedToListIL lemmas)
      (_,eBlock) = runState 100 
                   (makeDeduct' (si,opt,lemmas',con,sort,[]) (t,typ,sort)) in
  handle eBlock
  (\e -> err e)
  (\block -> return ((case outputMode of 
                      OutLatex -> latexPrintBlock name
                      OutAscii -> printBlock
                      OutJava -> javaPrintBlock) opt block))
                            

type DedOptions = (Bool,Bool,Bool,Bool,Bool,Bool,Bool,Bool,Bool,Bool,OutputMode)

makeOpt :: Int -> OutputMode -> DedOptions 
makeOpt (-1) latex = makeOpt 0 latex
makeOpt n0 latex = 
             let shift n = (n `mod` 10 /= 0, n `div` 10)
                 (optTerm,n1) = shift n0
                 (optVar,n2) = shift n1
                 (optBindType,n3) = shift n2
                 (optAllSorts,n4) = shift n3
                 (optMax1App,n5) = shift n4
                 (optCutFree,n6) = shift n5
                 (optIgnoreConv,n7) = shift n6
                 (optBetaConv,n8) = shift n7
                 (optTermJust,n9) = shift n8 
                 (optSmallFlags,n10) = shift n9 in
             (optTerm,optVar,optBindType,optAllSorts,optMax1App,optCutFree,
              optIgnoreConv,optBetaConv,optTermJust,optSmallFlags,latex)

 
-- Options -> False = shorter          
    
-- print also terms?
optTerm :: DedOptions -> Bool
optTerm (b,_,_,_,_,_,_,_,_,_,_) = b

-- print a separate line for variables?
optVar :: DedOptions -> Bool
optVar (_,b,_,_,_,_,_,_,_,_,_) = b

-- Make subdeduction for types in flags?
optBindType :: DedOptions -> Bool
optBindType (_,_,b,_,_,_,_,_,_,_,_) = b

-- print inhabitants of all sorts, or only proofterms
optAllSorts :: DedOptions -> Bool
optAllSorts (_,_,_,b,_,_,_,_,_,_,_) = b  

-- maximal one application at a time? (Also prohibits special lemmas)
optMax1App :: DedOptions -> Bool
optMax1App (_,_,_,_,b,_,_,_,_,_,_) = b

-- keep cuts (True) or eliminate cuts in the deduction (False)
optKeepCut :: DedOptions -> Bool
optKeepCut (_,_,_,_,_,b,_,_,_,_,_) = b

-- Ignore conversions?
optIgnoreConv :: DedOptions -> Bool
optIgnoreConv (_,_,_,_,_,_,b,_,_,_,_) = b

-- Also beta-conversions?
optBetaConv :: DedOptions -> Bool
optBetaConv (_,_,_,_,_,_,_,b,_,_,_) = b

-- print terms in justification?
optTermJust :: DedOptions -> Bool
optTermJust (_,_,_,_,_,_,_,_,b,_,_) = b

-- print terms in justification?
optSmallFlags :: DedOptions -> Bool
optSmallFlags (_,_,_,_,_,_,_,_,_,b,_) = b

-- latex/java/ascii output?
-- java is very similar to latex  
optOutputMode :: DedOptions -> OutputMode
optOutputMode (_,_,_,_,_,_,_,_,_,_,m) = m

-- optLatex means real latex or java
optLatex :: DedOptions -> Bool
optLatex opt = case optOutputMode opt of
                  OutLatex -> True 
                  OutJava -> True
                  otherwise -> False

optJava :: DedOptions -> Bool
optJava opt = case optOutputMode opt of
                  OutJava -> True
                  otherwise -> False

-- Shortcomings:                                             
--   * Conversions are not always shown
--     (In the existential quantification special lemma, and in the
--      cut elimination scheme)
--   * For @E arguments can sometimes be made implicit.
--   * A special lemma with more arguments is depicted in an ugly way,
--     just as if it was an ordinary lemma. Does this occur ?
--   * It would be nice not to repeat pieces of derivations that have
--     occurred before.
--   * Sometimes it is nice to have multiple conversion steps.
--     See e.g. lemma pb (from practic.ys) 
--   * Rewriting is often done in two steps; one @ elimination and a proper
--     rewrite step. It would nice to combine the two steps into one step.
--   * The Rewrite In tactic results in ugly proof-terms.


-- There are two kinds of routines here.
-- 1. makeDeductBla t :: (Block,Refer)
--    These routines deliver a complete deduction for a term, and a 
--    reference to that deduction.                           
--    E.g. a result could be (block below, 12)
--      11 P/\Q    @E 6,10
--      12 P       /\EL 11
-- 2. makeSubDeductBla t :: (Block,Justif)
--    These routines deliver a deduction for all subterms of t, and a 
--    justification how t is obtained from thos subterms.
--    E.g. the result for the same term would be (thing below, /\EL 11)
--      11 P/\Q    @E 6,10

-- makeDeduct makes a deduction from a term. Only terms of sort
-- ps are considered logical proof-terms; only those terms generate
-- structured deductions.
makeDeduct' :: Stuff -> (Term,Term,Sort) -> D Block
makeDeduct' stuff@(_,opt,_,_,_,_) tts = 
      map fst (makeDeduct stuff tts)
                                       
dedNf opt term = if optBetaConv opt then term else bnf emptyCon term

-- makeDeduct delivers apart from the block also a reference to that block.
-- the variable type is the expected type of the term. (This not necessarily
-- syntactically equal to the actual type, which is the type of the term
-- delivered by the typing routine.
-- Of course the expected and the actual type are bd-convertible.)
makeDeduct :: Stuff -> (Term,Term,Sort) -> D (Block,Refer)
-- first: is the term is not of the proper sort, make a fake block.
makeDeduct stuff@(_,opt,_,_,ps,_) tts@(_,_,sort) 
       | not (optAllSorts opt || sort == ps) =
    fakeDeduct stuff tts
makeDeduct stuff tts@(var,_,_) | isVar var =
    makeDeductVar stuff False tts      
makeDeduct stuff@(si,opt,lemmas,con,ps,varRefs) tts@(term,_,_) 
                                                      | isCut stuff term =
    -- make a cut-free proof from a term which has a cut
    let (_,abs,arg) = deconstructApp term in
    makeDeductGT stuff arg >>= \(block1,refer) ->
    let abs' = tchangeVar "plaats 1" abs (domCon con)
        (_,it@(v,_,_),u) = deconstructAbs abs'
        varRefs' = (v,refer) : varRefs
        con' = mkDecl it `addC` con
        stuff' = (si,opt,lemmas,con',ps,varRefs') in
    makeDeductGT stuff' u >>= \(block2,ref) ->
    return (Composite [block1,block2], ref)
makeDeduct stuff@(si,opt,_,con,ps,varRefs) (term,typ,sort) = 
    let tts = (term, dedNf opt typ, sort) in
    makeSubDeduct stuff tts >>= \res ->
    subDeductToDeduct stuff res tts

tchangeVar s term l | isBind term = changeVar term l
tchangeVar s term l = error ("Unpermitted changeVar at "++s) 

isCut :: Stuff -> Term -> Bool
isCut stuff@(si,opt,_,con,ps,_) term =   
  let (isMaybeCut,term1,term2) = deconstructApp term
      (typ2,sort2) = getTypSort stuff con term2 in
  not (optKeepCut opt) && isMaybeCut && isAbs term1 && sort2 == ps

-- addDeductConv gets a block with reference, a type for the subderiv. and a
-- type for thw whole derivation as argument.
-- It adds a conversion/subsumption step if necessary from the inferred type
-- to the desired type to the block, if this option is set.
addDeductConv :: Stuff -> (Block,Refer) -> Term -> (Term,Term,Sort) -> 
                   D (Block,Refer)
addDeductConv stuff@(si,opt,_,_,_,_) (block,refer) subderivTyp 
              (term,derivTyp,sort) =
 if optIgnoreConv opt || deductEqual opt subderivTyp derivTyp then
    return (block,refer)
 else
    subDeductToDeduct stuff (block,(mkJust stuff subderivTyp derivTyp,[refer]))
                      (term,derivTyp,sort)

-- addSubDeductConv is similar, but works with a SubDeduction.
addSubDeductConv :: Stuff -> (Block,Justif) -> Term -> (Term,Term,Sort) -> 
                   D (Block,Justif)
addSubDeductConv stuff@(si,opt,_,_,_,_) bj subderivTyp (term,derivTyp,sort)=
  if optIgnoreConv opt || deductEqual opt subderivTyp derivTyp then
     return bj
  else
     subDeductToDeduct stuff bj (term,subderivTyp,sort) >>= \(block,ref)->
     return (block,(mkJust stuff subderivTyp derivTyp,[ref]))

mkJust stuff@(si,opt,_,con,_,_) infTyp desTyp =
    if hasSubtyping si && not (bdEqual con infTyp desTyp) then
        mkSubsum opt
    else
        mkConv opt

mkConv opt | optLatex opt = "\\dedconv"
mkConv opt | otherwise = "conv"

mkSubsum opt | optLatex opt = "\\dedsubsum"
mkSubsum opt | otherwise = "subsum"



-- fakeDeduct just delivers an empty block, and as reference the printed
-- term.
fakeDeduct :: Stuff -> (Term,Term,Sort) -> D (Block,Refer)
fakeDeduct stuff@(si,opt,_,con,_,_) (term,typ,sort) = 
       let prin = myPrintTermSt si con opt term
           prin' = if isVar term then prin else "(" ++ prin ++ ")" in
       return (Composite [], RF prin')

-- makeDeductVar delivers a block of zero to two lines for a variable.
-- force makes certain the block will consist of at least one line
-- Examples:
-- A) if optVar and we have conversion
--   125 |  H : odd 7          var 123
--   126 |  H : not (even 7)   conv 125
--   reference = 126
-- B) if optVar and we have no conversion
--   125 |  H : odd 7          var 123
--   reference = 125
-- C) if not optVar and we have conversion
--   125 |  H : not (even 7)   conv 123
--   reference = 125
-- D) if not optVar and we have no conversion and not force
--   empty block, reference = 123
-- E) if not optVar and we have no conversion and force
--   125 |  H : odd 7          var 123
--   reference = 125
-- So force plays only a role when not optVar and no conversion 
makeDeductVar :: Stuff -> Bool -> (Term,Term,Sort) -> D (Block,Refer)
makeDeductVar stuff@(si,opt,_,con,_,varRefs) force (var,typ,sort) =
    let (_,v) = deconstructVar var
        (found,vref) = findAL varRefs v
        block1 = Composite []
        refer1 = if found then vref else RF (myPrintVarSt si con opt v)
        (typ',_) = getTypSort stuff con (mkVr v)
        basicVarDeduct = subDeductToDeduct stuff (block1,("var",[refer1]))
                         (var,typ',sort) in
    (if optVar opt then
        basicVarDeduct
     else
        return (block1,refer1)
    ) >>= \(block2,refer2) ->
    addDeductConv stuff (block2,refer2) typ' 
                  (mkVr v,typ,sort) >>= \(block3,refer3) ->
    let isEmpty (Composite []) = True
        isEmpty _ = False in
    if force && isEmpty block3 then
       -- if force is set, we may not deliver an empty block
       basicVarDeduct
    else
       return (block3,refer3)

{- old code
    let (_,v) = deconstructVar var
        (found,vref) = findAL varRefs v
        block1 = Composite []
        refer1 = if found then vref else RF (myPrintVarSt si con opt v)
        (typ',_) = getTypSort stuff con (mkVr v)
        equal = deductEqual opt typ' typ in
    (if optVar opt || (force && (equal || optIgnoreConv opt)) then
        subDeductToDeduct stuff (block1,("var",[refer1])) (var,typ',sort)
     else
        return (block1,refer1)
    ) >>= \(block2,refer2) ->
    if equal then
       return (block2,refer2)  
    else
       addDeductConv stuff (block2,refer2) typ' (mkVr v,typ,sort)
-}

deductEqual :: DedOptions -> Term -> Term -> Bool
deductEqual opt = (if optBetaConv opt then (==) else bEqual)


subDeductToDeduct :: Stuff -> (Block,Justif) -> (Term,Term,Sort) -> 
                     D (Block,Refer)
subDeductToDeduct stuff@(si,opt,_,con,_,_) (block,just) (term,typ,sort) =
        let body0 = if optTerm opt then
                       myPrintTermSt si con opt term ++ hasString opt
                    else []
            body = body0 ++ myPrintTermSt si con opt typ in
        newLabel >>= \label ->
        return (Composite [block,Line (label, body, just)],
                RL label)


                   


-- makeSubDeduct does not print the type of the term itself, but prints
-- deductions for real subterms, and delivers a justification for the term.
-- makeSubDeduct checks if the type is of the proper form, and if not so
-- adds a line with the conversion step
-- Pre: typ in dedNf
makeSubDeduct :: Stuff -> (Term,Term,Sort) -> D (Block,Justif)
makeSubDeduct stuff@(si,opt,_,con,_,_) (term,typ,sort) = 
    let (isOk,okTyp) 
            -- isOk==True means that we do not wish a conversion step
            --            e.g. we want to postpone such a step
            -- isOk==False means that we want a conversion step if necessary.
          | isApp term   = let (typApp,_) = getTypSort stuff con term in
                           (False, typApp)
          | isDelta term = let term' = tchangeVar "plaats 2" term (domCon con)
                               (_,it@(vt,dt,_,_),_) = deconstructDelta term'
                               (isDelT,(vT,dT,_,_),bT) = deconstructDelta typ
                               goodForm = isDelT && bdEqual con dt dT in
                           if goodForm then
                              (True, typ)
                           else
                              let okType = mkDelta it typ in
                              -- conversion step is silly, so ignore
                              (True, okType)
          | isGenAbs term= (isGenAll typ, bdswhnf con typ)
                           {- old code, that unfolds the type till there are
                              just as many @'s as lambda's.
                           if optSmallFlags opt then
                              (isGenAll typ, bdswhnf con typ)
                           else
                              let noAbss = countAbss term in
                              (countAlls typ >= noAbss, mkAlls con noAbss typ)
                              we prefer to do first some introductions,
                              then conversion, then introductions again,
                              because this gives smaller propositions in the
                              deduction.
                           -}
          | isGenAll term= (False, bdswhnf con typ)
          | isSort term  = (False, bdswhnf con typ)
          | otherwise    = (True, typ) in
                           -- leave conversion steps to makeSubDeduct2 
    makeSubDeduct2 stuff (term,okTyp,sort) >>= \br ->
    if isOk then
       return br
    else 
       addSubDeductConv stuff br okTyp (term,typ,sort)

countAbss :: Term -> Int
countAbss (Bind (Abs _) ts it body) = 1+countAbss body
countAbss _ = 0

countAlls :: Term -> Int
countAlls (Bind (All _) ts it body) = 1+countAlls body
countAlls _ = 0

-- Pre: the type is already of the proper form (see makeSubDeduct), i.e.
--      the most outer construct in the term and in the type correspond.
makeSubDeduct2 :: Stuff -> (Term,Term,Sort) -> D (Block,Justif)
makeSubDeduct2 stuff@(si,opt,_,con,_,_) (app,typ,sort) | isApp app = 
     if optMax1App opt then
        let (_,t1,t2) = deconstructApp app in
        makeDeductApp stuff t1 [t2]
     else
        let (hd:tl) = unwindApps app in
        makeDeductApp stuff hd tl

makeSubDeduct2 stuff@(si,opt,_,con,_,_) (abs,all,sort) | isGenAbs abs =
    (if optBindType opt then
        let -- we ignore constraints on the variable, e.g. we don't print
            -- a type derivation for the bound in a bounded abstraction.
            (_,(_,t,_),_,_,_) = deconstructGenAll all
            -- can be made more efficient!
            (tType,tSort) = getTypSort stuff con t in
        makeDeduct stuff (t,tType,tSort) >>= \(typeBlock,refType) ->
        return (\bodyBlock -> Composite [typeBlock,bodyBlock],[refType])
     else
        return (id, [])) >>= \(mkTotal, refsHyp) ->
    let noAlls = if optSmallFlags opt then
                    1
                 else
                    min (countAlls all) (countAbss abs) in
    makeAbsFlag stuff noAlls (abs,all,sort) refsHyp>>= \(block,refer) ->
    return (mkTotal block,(allIntroString stuff all,[refer]))

makeSubDeduct2 stuff@(si,opt,_,con,_,_) (all,typ,sort) | isGenAll all  =
    (if optBindType opt then
        let -- we ignore constraints on the variable, e.g. we don't print
            -- a type derivation for the bound in a bounded quantification.
            (_,(_,t,_),_,_,_) = deconstructGenAll all
            -- can be made more efficient!
            (tType,tSort) = getTypSort stuff con t in
        makeDeduct stuff (t,tType,tSort) >>= \(typeBlock,refType) ->
        return (\bodyBlock -> Composite [typeBlock,bodyBlock],[refType])
     else
        return (id, [])) >>= \(mkTotal, refsHyp) ->
    makeFlag stuff (all,typ,sort) refsHyp>>= \(block,refer) ->
    return (mkTotal block,(allFormString stuff all,[refer]))    

makeSubDeduct2 stuff@(_,opt,_,_,_,_) (delta,typ,sort) | isDelta delta =
    (if optBindType opt then
        let (_,(_,d,t,s),_) = deconstructDelta typ in
        makeDeduct stuff (d,t,s) >>= \(typeBlock,refType) ->
        return (\bodyBlock -> Composite [typeBlock,bodyBlock],[refType])
     else
        return (id, [])) >>= \(mkTotal, refsHyp) ->
    makeCombFlag stuff 1 (delta,typ,sort) refsHyp>>= \(block,refer) ->
    return (mkTotal block,(defIntroString,[refer]))
  
-- Only necessary for elaborate representations
makeSubDeduct2 stuff (sort,_,_) | isSort sort =
    return (Composite [],("axiom",[]))

makeSubDeduct2 _ _ = genErrS "Can't make deductions for this kind of term"


allFIEString (si,opt,_,con,_,_) all =
    if optLatex opt then 
       let (_,it,cts,ts,body) = deconstructGenAll all
           con' = mkGenDecl (it,cts,ts) `addC` con
           s = noErrDed si (inferSort si con' body) in
       if isArrow all then
          maybeDollar opt ("\\arrow" ++ sortToName s)
       else
          maybeDollar opt ("\\pi" ++ sortToName s)
    else 
       if isArrow all then
          "->"
       else
          "@"

maybeDollar opt s =
    let (ds,de) = if optJava opt then ("{","}") else ("$","$") in
    ds ++ s ++ de
 

allFormString  si all = allFIEString si all ++ "F"
allIntroString si all = allFIEString si all ++ "I"  
allElimString  si all = allFIEString si all ++ "E"  
defIntroString = "defI"                        

hasString opt = if optLatex opt then "\\has" else " : "  
subString opt = if optLatex opt then "\\sub" else " <: "  
isDefString opt = if optLatex opt then "\\isd" else " := "

makeDeductApp :: Stuff -> Term -> [Term] -> D (Block,Justif)
makeDeductApp stuff@(si,opt,lemmas,con,_,_) t args =
 -- Improvement to be made for variables: don't print implicit arguments.
 let (isVar,v) = deconstructVar t
     (isLemma,~(noAA,conn,nameLemma)) = findAL lemmas v
     defaul = makeDeductAppNoLemma stuff t args in
 if not (optMax1App opt) && isVar && isLemma then
    let --  hack to delete brackets around variable
        pconn1 = myPrintVarSt si con opt conn
        pconn2 = if head pconn1 == '(' then 
                    drop 1 (take (length pconn1 -1) pconn1)
                 else
                    pconn1
        pconn = if optLatex opt then maybeDollar opt pconn2 else pconn2 
        (typ,_) = getTypSort stuff con t
        args' = drop noAA (addTypesSorts con typ args) in
    handleS (makeDeductLemma nameLemma pconn stuff args')
    (\mess -> case mess of
              [ES s] | s == mdlError -> defaul   -- | False -> err mess
              otherwise -> err mess)
    (\(rest,bj) -> if null rest then 
                         return bj
                      else
                         let usedArgs = take (length args-length rest) args
                             tUsedArgs = unstandard (t:usedArgs)
                             (typ,sort) = getTypSort stuff con tUsedArgs in
                         subDeductToDeduct stuff bj 
                                           (tUsedArgs,typ,sort) >>= \br ->
                         makeDeductAppTail stuff (br,tUsedArgs,typ,sort) 
                                           (map fst3 rest))
 else
    defaul

makeDeductAppNoLemma :: Stuff -> Term -> [Term] -> D (Block,Justif)
makeDeductAppNoLemma stuff@(si,opt,lemmas,con,_,_) t args =
 let (typ,sort) = getTypSort stuff con t in
 makeDeduct stuff (t,typ,sort) >>= \br ->
 makeDeductAppTail stuff (br,t,typ,sort) args

makeDeductAppTail :: Stuff -> ((Block,Refer),Term,Term,Sort) -> [Term] ->
                     D (Block,Justif)
makeDeductAppTail stuff@(_,opt,_,con,ps,_) (br,t,typ,sort) args =
 (if isGenAllN typ (length args) then
     return (br,typ)
  else
     let typ' = mkAlls con (length args) typ in
     addDeductConv stuff br typ (t,typ',sort) >>= \br' ->
     return (br',typ')
 ) >>= \(br',typ') ->
 -- Now typ' has (length args) all's, so we can extract the types in
 -- the all's
 let args' = addTypesSorts con typ' args
     args'' = if optTermJust opt then
                 args'
              else
                 filter ((== ps).thd3) args' in
 combineLinesGen' stuff (map (pair makeDeduct) args'') >>= \brs ->
 let brs' = br':brs in
 return (Composite (map fst brs'), (allElimString stuff typ', map snd brs'))

-- mkAlls con n term  tries to convert term such that it starts with n @'s.
-- if this doesn't succeed, then it starts with as many @'s as possible.
-- it would be nice to use two application steps in such a case.
mkAlls con 0 term = term
mkAlls con n term =
     let term' = bdswhnf con term
         (isAll,(oldv,_,_),_,_,_) = deconstructGenAll term'
         term'' = tchangeVar "plaats 3" term' (domCon con)
         (_,it,cts,ts,u) = deconstructGenAll term''
         con' = mkGenDecl (it,cts,ts) `addC` con in
     if isAll then
        oldVarG oldv mkGenAll (it,cts,ts) (mkAlls con' (n-1) u)     
     else
        term

addTypesSorts :: Context -> Term -> [Term] -> [(Term,Term,Sort)]
addTypesSorts con typ args = 
     let typs = typeOfArgs con typ args in
     zipWith (\term (typ,sort) -> (term,typ,sort)) args typs


-- typeOfArgs "@A,B:*.A -> (A->B) -> B" "[Nat,Bool,f,g]" = 
--            "[(*,#),(*,#),(Nat,*),(Nat->Bool,*)]"
-- Pre for typeOfArgs typ args: there are at least (length args) all's in typ
typeOfArgs :: Context -> Term -> [Term] -> [(Term,Sort)]
typeOfArgs con typ [] = []
typeOfArgs con typ (arg:args) = 
    let typ' = bdswhnf con typ
        (_,(v,t,s),_,_,u) = deconstructGenAll typ' in
    (t,s) : typeOfArgs con (subst u v arg) args

makeDeductLemma :: String -> Vari -> Stuff -> [(Term,Term,Sort)] ->
                   D ([(Term,Term,Sort)],(Block,Justif))
makeDeductLemma "AndI" conn stuff (_:_:lhs:rhs:rest) =
  map (pair rest) (combineLines stuff [lhs,rhs] (conn ++ "I"))
                                             
makeDeductLemma ('A':'n':'d':'E':dir) conn stuff (_:_:conj:rest) =
  map (pair rest) (combineLines stuff [conj] (conn++"E"++dir++" "))

makeDeductLemma ('O':'r':'I':dir) conn stuff (_:_:t:rest) =
  map (pair rest) (combineLines stuff [t] (conn ++ "I" ++ dir))

makeDeductLemma "OrE" conn stuff (_:_:_:disj:lhs:rhs:rest) =
  map (pair rest) (
  combineLinesGen stuff [(makeDeduct,disj),
                         (makeAbsFlagNH,lhs),
                         (makeAbsFlagNH,rhs)] (conn++"E"))
   
makeDeductLemma "NotI" conn stuff (_:t:rest) =
  map (pair rest) (combineLinesGen stuff [(makeAbsFlagNH,t)] (conn ++ "I"))

makeDeductLemma "NotE" conn stuff (_:t1:t2:rest) =
  map (pair rest) (combineLines stuff [t1,t2] (conn ++ "E"))

makeDeductLemma "FalseE" conn stuff (_:t:rest) =
  map (pair rest) (combineLines stuff [t] "FalseE")
      
makeDeductLemma "ExistsI" conn stuff (wit:_:t:rest) =
  map (pair rest) (combineLines stuff [wit,t] (conn ++ "I"))

makeDeductLemma "ExistsE" conn stuff (_:_:quant:elim:rest) =
  map (pair rest) (
  combineLinesGen stuff [(makeDeduct,quant),
                         (makeAbsFlag2,elim)] (conn++"E"))

makeDeductLemma "Refl" conn stuff (_:rest) =
  map (pair rest) (combineLines stuff [] (conn++"refl"))

makeDeductLemma "Rewrite" conn stuff (_:_:_:eq:prop:rest) =
  map (pair rest) (combineLines stuff [eq,prop] (rewrJust stuff conn True))

makeDeductLemma "Lewrite" conn stuff (_:_:_:eq:prop:rest) =
  map (pair rest) (combineLines stuff [eq,prop] (rewrJust stuff conn False))

makeDeductLemma s _ stuff args = errS mdlError
{-
   genErrS ("Strange application of special tactic: "++s ++ " "++
            show (length args)++" arguments")
-}

mdlError = "MDL"

rewrJust stuff@(_,opt,_,_,_,_) conn True | optLatex opt =
    "\\leibnizrl{" ++ conn ++ "}"
rewrJust stuff@(_,opt,_,_,_,_) conn False | optLatex opt =
    "\\leibnizlr{" ++ conn ++ "}"
rewrJust stuff@(_,opt,_,_,_,_) conn True  = conn ++ "<-"
rewrJust stuff@(_,opt,_,_,_,_) conn False = conn ++ "->"
                                 
makeDeductGT :: Stuff -> Term -> D (Block,Refer)
makeDeductGT stuff@(si,_,_,con,_,_) term =
       let (typ,sort) = getTypSort stuff con term in
       makeDeduct stuff (term,typ,sort)

combineLines :: Stuff -> [(Term,Term,Sort)] ->
                String -> D (Block,Justif)
combineLines stuff terms just =
    let funTerms = map (pair makeDeduct) terms in
    combineLinesGen stuff funTerms just
      
-- t is typically (Term,Term,Sort)
combineLinesGen :: Stuff -> [(Stuff->t->D (Block,Refer) , t)] ->
                   String -> D (Block,Justif)
combineLinesGen stuff funTerms just = 
   combineLinesGen' stuff funTerms >>= \ress ->
   return (Composite (map fst ress), (just,map snd ress))
                                     
-- t is typically (Term,Term,Sort)
combineLinesGen' :: Stuff -> [(Stuff->t->D (Block,Refer) , t)] ->
                    D [(Block,Refer)]
combineLinesGen' stuff [] = return []
combineLinesGen' stuff ((f,term):terms) =
   f stuff term >>= \res ->
   map (res :) (combineLinesGen' stuff terms)


-- no references for hypothesis
makeAbsFlagNH stuff tts = 
    makeAbsFlag stuff 1 tts [] 

-- Pre: typ is an all-type
--makeAbsFlag :: Stuff -> Int -> (Term,Term,Sort) -> a -> 
makeAbsFlag stuff@(si,_,_,con,_,_) n trip@(term,typ,sort) hypRefs= 
    if isGenAbs term then
       makeCombFlag stuff n trip hypRefs
    else                    
       makeDeduct stuff trip
  
-- Pre: term and typ are n times the same kind of binders
makeCombFlag stuff@(si,_,_,con,_,_) n (term,typ,sort) hypRefs= 
    newLabel >>= \labelF ->
    doNHyp stuff n (term,typ) hypRefs >>= \(stuff',(u, uType), l) ->
    let (_,_,_,con',_,_) = stuff'
        uSort = getSor si con' uType in
    (if isVar u then                 
        -- This is a bit of heck, but very necessary to prevent empty blocks.
        makeDeductVar stuff' True (u,uType,uSort)
     else
        makeDeduct stuff' (u,uType,uSort)
    ) >>= \(block,_) ->
    return (Flag labelF l block,
            RL labelF)

-- Pre: term and typ are n times the same kind of binders
doNHyp :: Stuff -> Int -> (Term,Term) -> [Refer] ->
          D (Stuff, (Term,Term), [(Label, String, Justif)])
doNHyp stuff@(_,_,_,con,_,_) 0 (term,typ) hypRefs =
    return (stuff, (term,typ), [])
doNHyp stuff@(si,_,_,con,_,_) n (term,typ) hypRefs=
    let (_,_,_,(typVar,_,_),_) = deconstructBind typ
        (typ',term') = -- name of var: preference for the name occuring in the
                       -- type, unless it is a silly name.
                       if isDummyVar typVar then
                          (\(a,b)->(b,a)) (changeVar2 (term,typ) (domCon con))
                       else
                          changeVar2 (typ,term) (domCon con)
        (_,_,_,_,u) = deconstructBind term'
        (_,cat, ts, it, uType) = deconstructBind typ' in
    newLabel >>= \labelH ->
    let (hyp,just,stuff'@(_,_,_,con',_,_)) = doHyp stuff (cat,ts,it) labelH in
    map (doThd3 ((labelH, hyp, (just,hypRefs)):))
        (doNHyp stuff' (n-1) (u,uType) hypRefs)
{-
doNHyp stuff@(_,_,_,con,_,_) 1 (term,typ) hypRefs=
    let (typ',term') = changeVar2 (typ,term) (domCon con)
        (_,_,_,_,u) = deconstructBind term'
        (_,cat, ts, it, uType) = deconstructBind typ' in
    newLabel >>= \labelH ->
    let (hyp,just,stuff'@(_,_,_,con',_,_)) = doHyp stuff (cat,ts,it) labelH in
    return (stuff', (u, uType), [(labelH, hyp, (just,hypRefs))])
-}
  
-- Pre: term is an binder
makeFlag stuff@(si,_,_,con,_,_) (term,typ,sort) hypRefs = 
    let term' = tchangeVar "plaats 4" term (domCon con)
        (_,cat,ts,it,u) = deconstructBind term' in
    newLabel >>= \labelF ->
    newLabel >>= \labelH ->
    let (hyp,just,stuff'@(_,_,_,con',_,_)) = doHyp stuff (cat,ts,it) labelH
        (uType,uSort) = getTypSort stuff con' u in
    (if isVar u then                 
        -- This is a bit of heck, but very necessary to prevent empty blocks.
        makeDeductVar stuff' True (u,uType,uSort)
     else
        makeDeduct stuff' (u,uType,uSort)
    ) >>= \(block,_) ->
    return (Flag labelF [(labelH, hyp, (just,hypRefs))]
                  block,
            RL labelF)
  
-- makeAbsFlag2 prints a flag with two items, if the term consists of
-- two abstractions
makeAbsFlag2 stuff@(_,_,_,con,_,_) tts@(term,_,_) =
  let isAbs1 = isAbs term
      term' = tchangeVar "plaats 5" term (domCon con)
      (_,it1,b1) = deconstructAbs term'
      isAbs2 = isAbs b1
      b1' = tchangeVar "plaats 6" b1 (domCon con)
      (_,it2,b2) = deconstructAbs b1' in
  if not (isAbs1 && isAbs2) then
     makeAbsFlagNH stuff tts
  else
  newLabel >>= \labelF ->
  newLabel >>= \labelH1 ->
  newLabel >>= \labelH2 ->
  let (hyp1,stuff1) = doAbsHyp stuff it1 labelH1
      (hyp2,stuff2) = doAbsHyp stuff1 it2 labelH2 in
  makeDeductGT stuff2 b2 >>= \(block,_) ->
  return (Flag labelF [(labelH1, hyp1, ("hyp",[])),
                       (labelH2, hyp2, ("hyp",[]))]
               block,
          RL labelF)

doAbsHyp :: Stuff -> Item -> Label -> (String,Stuff)
doAbsHyp (si,opt,lemmas,con,ps,varRefs) it@(v,t,s) label =
  let isLogical = s == ps
      con' = mkDecl it `addC` con
      hyp1 = if isLogical && not (optTerm opt) then 
                "" 
             else 
                myPrintVarSt si con' opt v ++ hasString opt
      varRefs' = if isLogical then (v,RL label) : varRefs else varRefs in
  (hyp1 ++ myPrintTermSt si con opt t, (si,opt,lemmas,con',ps,varRefs'))
              
doHyp :: Stuff -> (BindCat,[Term],Item) -> Label -> (String,String,Stuff)
doHyp (si,opt,lemmas,con,ps,varRefs) (cat,ts,it@(v,t,s)) label = 
  let isLogical = s == ps
      contCat = convBindToCont cat
      con' = mkContextE contCat ts it `addC` con
      -- we have to supply new context for correct latex-printing, which
      -- needs declaration of vars in context
      (hyp,just) = 
             case contCat of
             Decl CNone -> (if isLogical && not (optTerm opt) then 
                               myPrintTermSt si con' opt t
                            else 
                               myPrintVarSt si con' opt v ++ hasString opt ++ 
                               myPrintTermSt si con' opt t,
                            "hyp")
             Decl CSub -> (myPrintVarSt si con' opt v ++ subString opt ++
                           myPrintTermSt si con' opt (head ts) ++
                           hasString opt ++ myPrintTermSt si con' opt t,
                           "hyp")
             Def -> (myPrintVarSt si con' opt v ++ isDefString opt ++ 
                     myPrintTermSt si con' opt (head ts) ++ hasString opt ++ 
                     myPrintTermSt si con' opt t,
                     "def")
             otherwise -> error "Can't handle these binders"
      varRefs' = if isLogical then (v,RL label) : varRefs else varRefs in
  (hyp, just, (si,opt,lemmas,con',ps,varRefs'))
           
{- For testing
printCon si con = concat (map (++"\n") (printContext displayString si (const True) (tol con)))

tol :: Ord k => ListsAndOTree k v -> [(k,v)]
tol (LAOT as t) = take 5 (concat (map indexedToListIL as) ++ indexedToListTWO t)
-}
 
getTypSort :: Stuff -> Context -> Term -> (Term,Sort)  
getTypSort stuff@(si,opt,_,_,_,_) con t = 
    let (typ,sort) = noErrDed si (inferType si con t) in
    (dedNf opt typ, sort)


myPrintTermSt si con opt = if optLatex opt then 
                              latexPrintTermSt si con
                           else
                              printTermSt si
myPrintVarSt si con opt = if optLatex opt then
                             latexPrintVarSt si con
                          else 
                             printVarSt si

