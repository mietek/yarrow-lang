-- File: Errors
-- Description: This module defines functions which convert the type Error
--              to a string.

module Errors(errorToStrings) where

import HaTuple

--import Basic  
--import SyntaxI
import Engine

import Printer
import ProvPri(printTermSt)

-- for printing nice error messages, it is necessary to know how big the
-- prompt is. Well, it is always two characters long ("> " or "$ ").
promptLength :: Int
promptLength = 2

-- The following code for indicating the place of an error is not perfect,
-- but should perform well in 'normal' cases.
-- It is still much better than the indication given by Coq :-)
--
-- The type placeInfo is given in module basic
                                              
-- showErrorPosition pi  designates with ^s the place determined by pi
--                       it also prints the line number of the place
showErrorPosition :: PlaceInfo -> [String]
showErrorPosition pi = showErrorPositionSym pi '^'

showErrorPositionSym ((ls,s),(le,e)) sym = 
                  if ls == le then
                     [makeLine (showL ls) s (replicate (e-s) sym)]
                  else
                     [makeLine (showL ls) s ([sym]++"..") ,
                      makeLine (showL le) (e-3) (".."++[sym])]

makeLine :: String -> Int -> String -> String
makeLine ln pl s = let start = ln
                       rest = replicate (promptLength+pl) ' ' ++ s in
                   ln ++ drop (length ln) rest

showL ln = "l" ++ show ln


-- showErrorPosition2 pi1 pi2 designates with ^s and ~s the places determined
--                       by pi1 and pi2
--                       it also prints the line number of the places
showErrorPosition2 :: PlaceInfo-> PlaceInfo->[String]
showErrorPosition2 pi1@((ls1,s1),(le1,e1)) pi2@((ls2,s2),(le2,e2)) =
               let mes1 = showErrorPositionSym pi1 '^'
                   mes2 = showErrorPositionSym pi2 '~' in
               if ls1 == le2 then
                  -- both errors entirely on one line
                  mergeLines mes1 mes2
               else
                  mes1 ++ mes2


mergeLines [s1] [s2] = let lens1 = length s1
                           lens2 = length s2
                           maxLen = max lens1 lens2
                           s1' = s1 ++ replicate (maxLen -lens1) ' ' 
                           s2' = s2 ++ replicate (maxLen -lens2) ' '
                           comb (' ',c) = c
                           comb (c,_)   = c in
                       [map comb (zip s1' s2')] 
 

-- A bit of a hack
errorToStrings :: SyntaxInfo -> Error -> [String]
errorToStrings si [EP pi, ES s] = showErrorPosition pi ++ [s]
errorToStrings si ees =
    let replaceETP (ETP (t,pi)) = if fst pi == dummyPlace ||
                                     snd pi == dummyPlace then
                                     ET t
                                  else
                                     EP pi
        replaceETP ee = ee 
        replaceET (ET t) = ES (printTermSt si t)
        replaceET ee = ee 
        (ss,s) = errorToStrings0 (map (replaceET.replaceETP) ees) in
    ss++[s]

errorToStrings0 :: Error -> ([String],String)
errorToStrings0 [] = ([],[])
errorToStrings0 (ES s :ees) =   doSnd (s++)   (errorToStrings0  ees)
errorToStrings0 (EP pi : ees) = doSnd ("^"++) (errorToStrings1 pi ees)

errorToStrings1 pi1 [] = (showErrorPosition pi1,[])
errorToStrings1 pi1 (ES s :ees) = 
                                doSnd (s++)   (errorToStrings1 pi1 ees)
errorToStrings1 pi1 (EP pi2 : ees) = 
                                doSnd ("~"++) (errorToStrings2 pi1 pi2 ees)

errorToStrings2 pi1 pi2 [] = (showErrorPosition2 pi1 pi2,[])
errorToStrings2 pi1 pi2 (ES s :ees) = 
                                doSnd (s++)   (errorToStrings2 pi1 pi2 ees)
