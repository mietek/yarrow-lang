-- File: MainPri
-- Description: This module defines functions for printing in the main-mode
--              of the proof assistant.

module MainPri(showListModules, showModules,  printSystemSt,
               printSortExsSt, printAxiomsSt, printRulesSt) where

import General
import HaMonSt

--import Basic
--import SyntaxI
--import MainSta
import Engine

import Printer

-----------------------------------
-- S H O W I N G   M O D U L E S --
-----------------------------------

showListModules :: M [String]
showListModules = fetchModulesInfo >>= \mi ->
                  if null mi then
                     return []
                  else
                     map (++[""]) showModules

showModules :: M [String]
showModules = fetchModulesInfo >>= \mi ->
              if null mi then
                 return ["No modules"]
              else
              fetchSyn >>= \si ->
              let showM (n,(firstV,lastV),cs) = 
                           "  \""++ n ++ "\": " ++ 
                           if firstV == dummyVar then 
                              "(empty)"
                           else if firstV==lastV then
                              printVarSt si firstV
                           else 
                              printVarSt si firstV ++
                                ".." ++ printVarSt si lastV in
              return ("Current modules:" :
                      map showM (reverse mi))

printSystemSt :: SyntaxInfo -> System -> (String,String,String,String,String)
printSystemSt si sys = let (s,a,r,ss,rs) = systemToQuintuple sys in
                       (printSortExsSt si s,
                        printAxiomsSt si a,
                        printRulesSt si r,
                        printSortsSt si ss,
                        printRulesSt si rs)

systemToQuintuple :: System ->
                     ([(Sort,[Extension])], 
                      [(Sort,Sort)], 
                      [(Sort,Sort,Sort)],
                      [Sort], 
                      [(Sort,Sort,Sort)])
systemToQuintuple ((ss,as,rs,sss,rss),exS) =
                  let exsFor s = (s, map snd (filter ((s==).fst) exS)) in
                  (map (exsFor) ss,as,rs,sss,rss)

printSortExsSt :: SyntaxInfo -> [(Sort,[Extension])] -> String
printSortExsSt si s = commas (map (printSortExSt si) s)

printSortExSt :: SyntaxInfo -> (Sort,[Extension]) -> String
printSortExSt si (s,exs) = printSortSt si s ++ 
                           concat (map (("->"++).printExtension) exs)
                                
printExtension :: Extension -> String
-- Extension: Records:
printExtension Records = "records"
-- End Extension: Records:

printSortsSt :: SyntaxInfo -> [Sort] -> String
printSortsSt si s = commas (map (printSortSt si) s)

printAxiomsSt :: SyntaxInfo -> [(Sort,Sort)] -> String
printAxiomsSt si a = prStrings ", " (map (printAxiomSt si) a)

printAxiomSt :: SyntaxInfo -> (Sort,Sort) -> String
printAxiomSt si (s1,s2) = printSortSt si s1 ++ ":" ++ printSortSt si s2

printRulesSt :: SyntaxInfo -> [(Sort,Sort,Sort)] -> String
printRulesSt si r = prStrings ", " (map (printRuleSt si) r)

printRuleSt :: SyntaxInfo -> (Sort,Sort,Sort) -> String
printRuleSt si (s1,s2,s3) | s2==s3 = "(" ++ printSortSt si s1 ++ "," ++
                                            printSortSt si s2 ++ ")"
printRuleSt si (s1,s2,s3)          = "(" ++ printSortSt si s1 ++ "," ++
                                            printSortSt si s2 ++ "," ++
                                            printSortSt si s3 ++ ")"
