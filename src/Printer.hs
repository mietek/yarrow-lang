-- File: Printer
-- Description: This module contains the pretty-printer for terms.

module Printer(-- polymorphic printing routines, e.g. of type
               -- DisplayTerm a -> .. -> a
               DisplayTerm,
               printTerm, printSort, printVar,printTermS,
               printContextE, printContext,

               dropImplic, newNum, deconstructSpecOper,
               breakListL, breakListLRev, breakListR
               ) where

-- This module defines polymorphic printing routines for terms and
-- contexts.
-- The polymorphism means that these routines can be used both by a
-- textual and a graphical user interface.
-- This polymorphism is described in mode Display.

-- Here the labels are paths (as defined in module Basic).
--
-- The printing routines for terms carry a parameter 'path', which is used
-- to label subterms.
--
-- All printing routines have as parameter the syntactic info, which 
-- contains the precedence and number of implicit arguments of variables.
-- This information is needed to print expressions with as little brackets
-- as possible and without implicit arguments.             

import HaTuple(space)
import General
import Display

--import Basic
--import Paths
--import SyntaxI
import Engine

import Scanner
      
{- for testing. Will only work under Gofer 
instance Text (Vari,Path) where
   showsPrec _ (v,path) = (v ++ concat (map show path))++                
-}
 
type DisplayTerm a = Display Path a

--------------------------
-- PRINTING EXPRESSIONS --
--------------------------
       
-- TERM  
printTerm :: DisplayTerm a -> SyntaxInfo -> Path -> Term -> a
printTerm stuff@(_,_,_,label) si path term = 
    label path (printTerm' stuff si path term)

printTerm' :: DisplayTerm a -> SyntaxInfo -> Path -> Term -> a
printTerm' stuff si path abs | isAbs abs = 
        let (_,(v,t,_),u) = deconstructAbs abs in
        printLambdaTerm stuff si path [v] t u
        -- for alternative version, with more nested boxes:
        --conc (bas "\\" :
        --      printVar stuff si (mkPathBindVar path) v :
        --      printLambdaTerm stuff si path t u)
printTerm' stuff si path all | isRealAll all =
        let (_,(v,t,_),u) = deconstructAll all in
        printAllTerm stuff si path [v] t u
-- Extension: Subtyping:
printTerm' stuff si path abs | isSubAbs abs =
        let (_,(v,b,t,_),u) = deconstructSubAbs abs in
        printBinderOne stuff si path "\\" v " <: " b t u isSubAbs 
printTerm' stuff si path all | isSubAll all =
        let (_,(v,b,t,_),u) = deconstructSubAll all in
        printBinderOne stuff si path "@" v " <: " b t u isSubAll 
-- End Extension: Subtyping
printTerm' stuff si path delta | isDelta delta =
        let (_,(v,d,t,_),u) = deconstructDelta delta in 
        printBinderOne stuff si path "let " v " := " d t u isDelta
printTerm' stuff si path app | isApp app =
   let l = breakListL deconstructApp app
       h = head l
       (isVar,v) = deconstructVar h
       isBind = extractBind si v
       numImp = getImplicit si v
       implicits = extractOptImplicit si
       l' = if isVar && implicits then dropImplic numImp l else l
       lArg = last l' in
       -- an operator is always printed infix if it has least 2 arguments 
       -- UNLESS it has implicit arguments that must be printed since
       -- this option is turned off.
       -- This exception is necessary to prevent the printing to get ugly.
   if isVar && isBind && length l' == 2 && isAbs lArg then
      printBinderTerm stuff si path v lArg 
   else
      printSmall stuff si path app
printTerm' stuff si path t = printSmall stuff si path t

printBinderTerm stuff@(conc,_,bas,_) si path bv abs = 
    let (_,(v,t,s),u) = deconstructAbs abs
        path' = mkPathAppArg path in
    conc [bas bv,  -- not with printVar as this gives brackets.
          bas " ",
          printVar stuff si v,
          bas ":",
          printTerm stuff si (mkPathBindTyp path') t,
          bas ". ",
          printTerm stuff si (mkPathBindBody path') u]

printBinderOne :: DisplayTerm a -> SyntaxInfo -> Path ->
                  String -> Vari -> String -> Term -> Term -> Term ->
                  (Term -> Bool) -> a
printBinderOne stuff@(conc,_,bas,_) si path s1 v s2 d t u isFun =
        conc [bas s1, printVar stuff si {-(mkPathBindVar path-} v,
              bas s2, printTerm stuff si (mkPathLetDef path) d,
              bas " : ",  printTerm stuff si (mkPathBindTyp path) t,
              bas (if isFun u then "." else ". "),
                          printTerm stuff si (mkPathBindBody path) u]
       

-- abstractions with the same type are contracted
-- consecutive abstractions have no space between them
printLambdaTerm stuff@(conc,_,bas,_) si path vl typ term =
        let (isAbs,(v,t,s),u) = deconstructAbs term in
        if isAbs && typ == t then
           printLambdaTerm stuff si (mkPathBindBody path) (vl++[v]) typ u
        else
           conc [bas "\\", printVarList stuff si vl,
                 bas ":", printTerm stuff si (mkPathBindTyp path) typ,
                 bas (if isAbs then "." else ". "),
                          printTerm stuff si (mkPathBindBody path) term]

{- alternative version, with more nested boxes 
printLambdaTerm stuff si path term =
        let (isAbs,(v,t,s),u) = deconstructAbs term in
        if isAbs && typ == t then
           -- all the rest is in the body of the original term
           let path' = mkPathBindBody path in
          conc (bas "," :
                 printVar stuff si {-(mkPathBindVar path')-} v :
                 printLambdaTerm stuff si path' typ u)
        else
           conc [bas ":", printTerm stuff si (mkPathBindTyp path) typ,
                 bas (if isAbs then "." else ". "),
                          printTerm stuff si (mkPathBindBody path) term]
-}

-- same comment as for printLambdaTerm
printAllTerm stuff@(conc,_,bas,_) si path vl typ term =
        let (isAll,(v,t,s),u) = deconstructAll term in
        if isAll && typ == t then
           printAllTerm stuff si (mkPathBindBody path) (vl++[v]) typ u
        else
           conc [bas "@", printVarList stuff si vl,
                 bas ":", printTerm stuff si (mkPathBindTyp path) typ,
                 bas (if isRealAll term then "." else ". "),
                          printTerm stuff si (mkPathBindBody path) term]

                           
-- 'SMALL' terms
printSmall stuff si path t = 
     fst (prListConsSpaceR stuff (printFactor stuff si 0)
                            path "->" mkPathBindTyp mkPathBindBody
                            (breakListR deconstructArrow t))

        
-- FACTOR
-- printFactor delivers a pair, where the first element is the 'string',
-- and the second element is a number designating the number of
-- spaces lower precedence operators should have around them.
-- If the term is an application, this number is always 1,
-- if the term is bracketed, this number is always 0. 
-- For the other cases, see prListSpace below
printFactor :: DisplayTerm a -> SyntaxInfo -> Int -> Path -> 
               Term -> (a,Int)
printFactor stuff@(conc,_,bas,_) si n path t = 
   let l = breakListL deconstructApp t
       h = head l
       (isVar,v) = deconstructVar h
       isOp = isVar && isOper v
       isBind = extractBind si v
       numImp = getImplicit si v
       implicits = extractOptImplicit si
       l' = if isVar && implicits then dropImplic numImp l else l in
       -- an operator is always printed infix if it has least 2 arguments 
       -- UNLESS it has implicit arguments that must be printed since
       -- this option is turned off.
       -- This exception is necessary to prevent the printing to get ugly.
   if isOp && length l' > 2 && not (not implicits && numImp > 0) then 
      -- print INFIX !
      let (pr,as) = extractPrec si v
          pArgs (t1:t2:[]) = -- two arguments
              let prF = printFactor stuff si (pr+1) 
                  mkPathLeft = mkPathAppArg . mkPathAppFun
                  mkPathRight = mkPathAppArg
                  mkPathConn = mkPathAppFun . mkPathAppFun in
              case as of
              NoAssoc -> prListSpaceR stuff prF path v [t1,t2]
              LeftAssoc -> 
                  let opl = breakListLRev (deconstructSpecOper v numImp) in
                  prListSpaceL stuff prF path v ([t2] ++ opl t1)
              RightAssoc ->
                  let opr = breakListR (deconstructSpecOper v numImp) in
                  prListSpaceR stuff prF path v ([t1] ++ opr t2)
          pArgs (t1:t2:l) = -- more than two arguments
                       (conc [bas "(", fst (pArgs [t1,t2]),
                              bas ") ", printPrefixApps stuff si path l],1)
          res = pArgs (tail l') in
      if pr >= n then 
         res
      else -- enclose in parentheses
         (conc [bas "(", fst res, bas ")"], 0)
   else
   if isVar && isBind && length l' == 2 && isAbs (last l') then
      -- binder, so don't print as application
      (printBasic2 stuff si path t, 0)
   else
      -- print PREFIX !
      (printPrefixApps stuff si path l', if length l'>1 then 1 else 0)
       -- a proper application has one space; a single element zero

printPrefixApps :: DisplayTerm a -> SyntaxInfo -> Path -> [Term] -> a
printPrefixApps stuff si path l = prListApp stuff si path (reverse l)
                                           
-- dropImplic n l  drops n arguments in l if explicit arguments will be left
dropImplic :: Int -> [Term] -> [Term]
dropImplic n l = 
     if (length l -1) > n then
        -- the first n arguments are left out, when at least
        -- one explicit argument remains.
        -- Sometimes this is too optimistic and the implicit
        -- arguments can not be determined any more in this
        -- notation.
        head l : drop n (tail l)
     else
        l


-- prListConsSpaceR prints spaces around right-associative constructors. 
prListConsSpaceR ::  DisplayTerm a -> (Path -> Term -> (a,Int)) ->
                     Path -> String ->
                     (Path->Path) -> (Path->Path) ->
                     [Term] -> (a,Int)
prListConsSpaceR stuff@(conc,_,bas,label) prin path sep mkPathL mkPathR l =
   let labelsFun path [_] = [path]
       labelsFun path (_:xs) = mkPathL path : labelsFun (mkPathR path) xs
       labels = labelsFun path l
       ll =  zipWith prin labels l
       numSpac = maximum (map snd ll)
       spaces = space numSpac
       printSubtermsR path [x] = x
       printSubtermsR path (x:xs) = 
            conc [label (mkPathL path) x,
                  bas (spaces++sep++spaces),
                  let path' = mkPathR path in
                  label path' (printSubtermsR path' xs)] in
   (printSubtermsR path (map fst ll), newNum l numSpac)

-- prListConsSpaceL is not needed at the moment

-- prListApp prints a list of applications.
prListApp :: DisplayTerm a -> SyntaxInfo -> Path -> [Term] -> a
prListApp stuff si path [t] = printBasic2 stuff si path t
prListApp stuff@(conc,_,bas,label) si path (t:ts) = 
             conc [let path' = mkPathAppFun path in
                   label path' (prListApp stuff si path' ts),
                   bas " ",
                   let path' = mkPathAppArg path in
                   label path' (printBasic2 stuff si path' t)]


-- prListSpaceR prints a right-associative operator with a list of arguments,
-- e.g. prListSpaceR (+) [a,b,c] = "a + b + c"
-- The difficulty lies in the combination of:
--     * Giving all subterms the correct path and labelling
--       them, this is very important for the graphical user interface.
--     * The rules for spacing, which demand that all subterms of the list
--       should be printed before the whole term can be printed.
prListSpaceR ::  DisplayTerm a -> (Path -> Term -> (a,Int)) ->
                 Path -> String ->
                 [Term] -> (a,Int)
prListSpaceR stuff@(conc,_,bas,label) prin path sep l =
   let labelsFun path [_] = [path]
       labelsFun path (_:xs) = mkPathAppArg (mkPathAppFun path) :
                               labelsFun (mkPathAppArg path) xs
       labels = labelsFun path l
       ll =  zipWith prin labels l
       numSpac = maximum (map snd ll)
       spaces = space numSpac
       printSubtermsR path [x] = x
       printSubtermsR path (x:xs) = 
            conc [let path' = mkPathAppFun path in
                  label path' (conc [label (mkPathAppArg path') x,
                                     bas spaces,
                                     label (mkPathAppFun path') (bas sep)]),
                  bas spaces,                                     
                  let path' = mkPathAppArg path in
                  label path' (printSubtermsR path' xs)] in
   (printSubtermsR path (map fst ll), newNum l numSpac)


-- prListSpaceL prints a right-associative operator with a list of arguments,
-- e.g. prListSpaceR (-) [a,b,c] = "c - b - a"
-- The argument is reversed, this makes this function less difficult and more
-- efficient.
prListSpaceL ::  DisplayTerm a -> (Path -> Term -> (a,Int)) ->
                 Path -> String ->
                 [Term] -> (a,Int)
prListSpaceL stuff@(conc,_,bas,label) prin path sep l =
   let labelsFun path [_] = [path]
       labelsFun path (_:xs) = mkPathAppArg path :
                               labelsFun (mkPathAppArg (mkPathAppFun path)) xs
       labels = labelsFun path l
       ll =  zipWith prin labels l
       numSpac = maximum (map snd ll)
       spaces = space numSpac
       printSubtermsL path [x] = x
       printSubtermsL path (x:xs) = 
            conc [let path' = mkPathAppFun path 
                      path'' = mkPathAppArg path' in
                  label path' (conc [label path'' (printSubtermsL path'' xs),
                                     bas spaces,
                                     label (mkPathAppFun path') (bas sep)]),
                  bas spaces,                                     
                  label (mkPathAppArg path) x] in
   (printSubtermsL path (map fst ll), newNum l numSpac)

    
-- The number of spaces around LOWER priority operatos is specified
-- in newNum. Some alternatives (with an example that shows the results
-- for each alternative):
-- newNum = 1+numSpac -> One more space around them, e.g.
--                       x^y * z  +  square a   =   O
-- newNum = 1         -> Always one space for lower priority operators, e.g.
--                       x^y * z + square a = O     
-- newNum = numSpac   -> Only a space if there is an application, e.g.
--                       x^y*z + square a = O
newNum l numSpac = if length l==1 then
                      -- silly case
                      numSpac
                   else
                      1

-- Extension: Records:   
printBasic2 stuff@(conc,_,bas,label) si path r | isRecSelect r =           
                      let (_,t,l) = deconstructRecSelect r 
                          path' = mkPathNonb 0 path in
                      conc [label path' (printBasic2 stuff si path' t),
                            bas ("`"++l)]
printBasic2 stuff si path t = printBasic stuff si path t
-- End Extension: Records:

-- BASIC
printBasic stuff si path srt | isSort srt = let (_,s) = deconstructSort srt in
                                 printSort stuff si s
printBasic stuff si path vr | isVar vr = let (_,v) = deconstructVar vr in
                                 printVar stuff si v    
printBasic stuff@(_,_,bas,_) si path hole | isHole hole = 
                                   let (_,hnum) = deconstructHole hole in
                                   bas (printHnumSt si hnum)      
-- Extension: Records:
printBasic stuff@(conc,_,bas,_) si path r | isRecValue r =       
           let (_,fs) = deconstructRecValue r in
           conc ([bas "{"] ++
                 printList stuff si path (printField stuff si "= ") fs ++
                 [bas "}"])
printBasic stuff@(conc,_,bas,_) si path r | isRecType r =       
           let (_,fs) = deconstructRecType r in
           conc ([bas "{|"] ++
                 printList stuff si path (printField stuff si ":") fs ++
                 [bas "|}"])
-- End Extension: Records:
printBasic stuff@(conc,_,bas,_) si path t =
                            conc [bas "(", printTerm' stuff si path t, bas ")"]

-- Extension: Records:
printList :: DisplayTerm a -> SyntaxInfo -> Path -> (Path -> b -> a) ->
             [b] -> [a]
printList stuff si path f ts = printList' stuff si path f ts 0

printList' stuff si path f [] n = []
printList' stuff si path f [t] n = 
              [f (mkPathNonb n path) t]
printList' stuff@(_,_,bas,_) si path f (t:ts) n = 
                   [f (mkPathNonb n path) t, bas ","] ++
                   printList' stuff si path f ts (n+1)
            
printField :: DisplayTerm a -> SyntaxInfo -> String -> Path -> 
              (RecLabel,Term) -> a 
printField stuff@(conc,_,bas,_) si s path (l,t) = 
                            conc [bas (l++s), printTerm stuff si path t]
-- End Extension: Records:


printSort :: DisplayTerm a -> SyntaxInfo -> Sort -> a
printSort stuff@(_,_,bas,_) si s = bas (printSortSt si s)
                  
printVar :: DisplayTerm a -> SyntaxInfo -> Vari -> a
printVar stuff@(_,_,bas,_) si v = bas (printVarSt si v)
 
printVarList :: DisplayTerm a -> SyntaxInfo -> [Vari] -> a
printVarList stuff si [v] = printVar stuff si v
printVarList stuff@(conc,_,bas,_) si (v:vs) =  
                            conc [printVar stuff si v,
                                  bas ",",
                                  printVarList stuff si vs]

deconstructSpecOper :: Vari -> Int -> Term -> (Bool,Term,Term)
deconstructSpecOper op numImp t = 
                           let (ok1,t1,ts) = deconstructAppN t (numImp+2)
                               ok2 = deconstructSpecVar t1 op 
                               [t2,t3] = drop numImp ts in
                           (ok1 && ok2, t2, t3)

                                               
-----------------------------
-- OTHER PRINTING ROUTINES --
-----------------------------

                              
-- printContextE prints a context item. The boolean function specifies 
-- for which definitions the definiens is fully printed (and not abbreviated
-- to "..")
printContextE :: DisplayTerm a -> SyntaxInfo -> (Sort -> Bool) ->
                 ContextE -> a
printContextE stuff@(conc,_,bas,label) si _ ce | isGenDecl ce =
            let (_,(v,t,s),constrs,cts) = deconstructGenDecl ce in
            conc ([label (mkPathConVar v) (printVar stuff si v)] ++
                  (case constrs of
                   CNone -> []
                   -- Extension: Subtyping:
                   CSub ->  [bas " <: ",
                             printTerm stuff si (mkPathConOther v 0) 
                                       (head cts)]
                   -- End Extension: Subtyping
                  ) ++
                  [bas " : ",
                   printTermS stuff si v (t,s)])
printContextE stuff@(conc,_,bas,label) si pDef ce | isDef ce =
            let (_,(v,d,t,s)) = deconstructDef ce in
            conc [label (mkPathConVar v) (printVar stuff si v), bas " := ",
                  let path' = mkPathConDef v in
                  label path' (if pDef s then
                                  printTerm' stuff si path' d 
                               else
                                  bas ".."),
                  bas " : ", printTermS stuff si v (t,s)]


-- print term and a sort, but only if the corresponding option is turned on
-- and if the sort is a proper sort
printTermS :: DisplayTerm a -> SyntaxInfo -> Vari -> (Term,Sort) -> a
printTermS stuff@(conc,_,bas,_) si v (t,u) | extractOptShowSort si && isProperSort u =
      conc [printTerm stuff si (mkPathConTyp v) t,
            bas " : ", printSort stuff si {- (mkPathConSort v)-} u]
printTermS stuff si v (t,u) = printTerm stuff si (mkPathConTyp v) t
  

printContext :: DisplayTerm a -> SyntaxInfo -> (Sort->Bool) -> [ContextE] ->
                [a]
printContext stuff si pDef c = map (printContextE stuff si pDef) (reverse c)

  
------------------------------------
-- GENERAL FUNCTIONS FOR PRINTING --
------------------------------------
        
-- breakListL breaks a term into a list
-- e.g. breakListL br (((a $ b) $ c) $ d) = [a,b,c,d]
--      when br (a $ b) = (True,a,b)
breakListL :: (a -> (Bool,a,a)) -> a -> [a]
breakListL break t = let (contin,t1,t2) = break t in
                     if contin then
                         breakListL break t1 ++ [t2]
                     else
                         [t]

-- breakListLRev breaks a term into a list
-- e.g. breakListLRev br (((a $ b) $ c) $ d) = [d,c,b,a]
--      when br (a $ b) = (True,a,b)                
-- breakListRev = reverse . breakList
breakListLRev :: (a -> (Bool,a,a)) -> a -> [a]
breakListLRev break t = let (contin,t1,t2) = break t in
                        if contin then
                            [t2] ++ breakListL break t1
                        else
                            [t]

-- breakListR is the dual of breakListL
-- e.g. breakListR br (a $ (b $ (c $ d))) = [a,b,c,d]
--      when br (a $ b) = (True,a,b)
breakListR :: (a -> (Bool,a,a)) -> a -> [a]
breakListR break t = let (contin,t1,t2) = break t in
                     if contin then
                         [t1] ++ breakListR break t2
                     else
                         [t]
