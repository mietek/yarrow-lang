-- File: General
-- Description: This module contains general-purpose functions.
           
module General(pair, flipPair, const', beginsWith, endsWith, takeWhiles',
               splitFilter,
               allDifferent, changeList1, doInList, sublist, sortOrd, notELem,
               readNum, prStrings, prList, commas, commaSpaces, plusCR,
               toLowers, Align(..),showTable3) where

import HaTuple
import Char(isDigit,toLower)



----------------------------
-- VERY GENERAL FUNCTIONS --
----------------------------


pair :: a -> b -> (a,b)
pair a b = (a,b)       
                                                                   
flipPair :: (a,b) -> (b,a)
flipPair (a,b) = (b,a)

const' :: a -> b -> b
const' a b = b

-- beginsWith xs ys  checks whether xs begins with the list ys
-- beginsWith :: Eq a => [a] -> [a] -> Bool
beginsWith xs ys = take (length ys) xs == ys

-- endsWith xs ys  checks whether xs ends with the list ys
-- endsWith :: Eq a => [a] -> [a] -> Bool
endsWith xs ys = beginsWith (reverse xs) (reverse ys)
            
-- takeWhile' p l  splits the list l in two parts, so that the first part
-- just doesn't satisfy p
takeWhile' :: ([a] -> Bool) -> [a] -> ([a],[a])
takeWhile' = tW [] where
                     tW xs p [] = (xs,[])
                     tW xs p (x:xs') = let xs'' = xs ++ [x] in
                                       if p xs'' then 
                                          tW xs'' p xs'
                                       else
                                          (xs,x:xs')                 

-- takeWhiles' p xs  splits xs so that every part satisfies p
takeWhiles' :: ([a] -> Bool) -> [a] -> [[a]]
takeWhiles' p [] = []
takeWhiles' p xs = let (x,xs') = takeWhile' p xs in
                   x : takeWhiles' p xs'

-- splitFilter p xs  divides xs into two lists, all elements of the first
--                   list satisfy p, all elements of the second list don't
splitFilter :: (a -> Bool) -> [a] -> ([a],[a])
splitFilter p [] = ([],[])
splitFilter p (x:xs) = (if p x then doFst else doSnd) (x:) (splitFilter p xs)

-- allDifferent checks whether all elements in a list are unique
allDifferent :: Eq a => [a] -> Bool
allDifferent [] = True
allDifferent (x:xs) = x `notELem` xs && allDifferent xs

-- changeList1 xs f  performs f on the first element of xs that satisfies f
changeList1 :: (a -> (Bool,a)) -> [a] -> [a]
changeList1 f [] = []
changeList1 f (x:xs) = let (b,x') = f x in
                       if b then
                          x' : xs
                       else
                          x : changeList1 f xs

doInList :: Int -> (a->a) -> [a] -> [a]
doInList i f l = take i l ++ (f (l!!i) : drop (i+1) l)


sublist :: Eq a => [a] -> [a] -> Bool
sublist s t = all (`elem` t) s

-- sortOrd is the same as the standard function sort, but with the ordering
-- as parameter.
sortOrd :: (a->a->Bool) -> [a] -> [a]
sortOrd ord = foldr (insertOrd ord) []

insertOrd :: (a->a->Bool) -> a -> [a] -> [a]
insertOrd ord x [] = [x]
insertOrd ord x (y:ys) | x `ord` y = x:y:ys
                       | otherwise = y:insertOrd ord x ys

-- due to an error in the definition of notElem in the Glasgow
-- Haskell compiler we have to give our own definition of notElem.
notELem :: Eq a => a -> [a] -> Bool
notELem x = not . elem x 



----------------------
-- TEXT PROCESSING  --
----------------------

-- readnum interprets a string as a number, and returns the part of the
-- string not starting with digits
readNum :: String -> (Int,String)
readNum = readNum' 0
              where readNum' n [] = (n,[])
                    readNum' n (c:s) | isDigit c = readNum' (10*n+ord c-48) s
                    readNum' n s = (n,s)
 
-- prstrings prints a list of strings, with a marker between
prStrings :: [a] -> [[a]] -> [a]
prStrings _ [] = []
prStrings _ [s] = s
prStrings m (s:ls) = s ++ m ++ prStrings m ls
                      
-- prthings prints a list of things, with a marker between
prList :: (b->[a])->[a]->[b]->[a]
prList f m l = prStrings m (map f l)  

commas :: [String] -> String
commas = prStrings ","

commaSpaces :: [String] -> String
commaSpaces = prStrings ", "

plusCR :: String -> String
plusCR = (++"\n")
                    
toLowers :: String -> String
toLowers = map toLower             

-- pretty-printing of tables
                         
data Align = LeftAl | CentreAl | RightAl

align :: Align -> String -> Int -> String
align LeftAl   s max = s ++ space (max - length s)
align CentreAl s max = let nsp = max - length s
                           nsp2 = nsp `div` 2 in
                       space nsp2 ++ s ++ space (nsp - nsp2)
align RightAl  s max = space (max - length s) ++ s

showTable3 :: String -> String -> (Align,Align,Align) -> 
              [(String,String,String)] -> [String]
showTable3 sep1 sep2 (al1,al2,al3) table =
        let max1 = maximum (map (length.fst3) table)
            max2 = maximum (map (length.snd3) table)
            max3 = maximum (map (length.thd3) table)
            showEntry (a,b,c) = align al1 a max1 ++ sep1 ++
                                align al2 b max2 ++ sep2 ++
                                align al3 c max3 in
        map showEntry table

