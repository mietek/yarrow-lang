-- File: HText
-- Description: This module is used to format text, used only in displaying
--   help texts. It uses a sort of mini-html format.

module HText(Paragraph,parseFancy,format) where

import General
import HaTuple
import Char(isSpace)
import Display

----------------
-- FANCY TEXT --
----------------

-- a paragraph can be a body of text or an item, consisting of a
-- description of items and some FancyText for that item.
data Paragraph = Text [Word] |
                 Para FancyText |
                 Description [([Word],FancyText)]

-- FancyText is a list of paragraphs
type FancyText = [Paragraph]
type Word = ([Char], HLink)

data HLink = NoHLink | HLink String

begDes = "DL"
endDes = "/DL"
begDesCom = "DL COMPACT"  -- difference between DL is that all descriptions
                          -- have the same indentation
endDesCom = "/DL"
defT = "DT"
defD = "DD"
begEnu = "OL"
endEnu = "/OL"
begIte = "UL"
endIte = "/UL"
itemT = "LI"
begPar="P"
endPar="/P"
breakT = "BR"
begVar="VAR"
-- the following commands are ignored
endVar="/VAR"
begVer = "CODE"
endVer = "/CODE"
begEmp = "EM"
endEmp = "/EM"
begAnc = "A"      -- actually every command starting with this is ignored
endAnc = "/A"
begRef = "HREF=\""

-- We use the following definition for our 'mini-HTML' language:
-- Fancy ::= Paragraph*
-- Paragraph ::= Piece |
--               <P> Fancy </P> |
--               <UL> (<LI> Fancy)* </UL> |
--               <OL> (<LI> Fancy)* </OL> |
--               <DL> (<DT> Word <DD> Fancy)* </DL> |
-- Piece ::= Text <BR>*
-- Text ::= Word+ |                   
--
-- Note: <CODE>, </CODE> and </VAR> tags are ignored;
--       <VAR> places '<' and '>' around the first word.
--       This is a bit of a hack, but what the hack!


-------------
-- SCANNER --
-------------

data HToken = HWord Word | HCom String

hScan :: String -> [HToken]
hScan s = fst (hScan' s)

hScan' :: String -> ([HToken],String)
hScan' "" = ([],"")
hScan' (c:s) | isSpace c = hScan' s
-- comments
hScan' ('<':'!':'-':'-':s)= let drop ('-':'-':'>':s) = s
                                drop (_:s) = drop s in
                            hScan' (drop s)
hScan' ('<':s) = let (com,_:s') = break (=='>') s in
                 -- ignore verbatim and some other tags
                 if com == begVer || com == endVer || com == endVar ||
                    com == endAnc ||
                    com == begEmp || com == endEmp then 
                    hScan' s'
                 else if com `beginsWith` begAnc then
                    let restCom = drop (length begAnc + 1) com in
                    if restCom `beginsWith` begRef then  
                       let (lnk,_) = break (=='"') 
                                           (drop (length begRef) restCom)
                           (tok:toks,s'') = hScan' s'
                           addLink (HWord (wrd,_)) = HWord (wrd, HLink lnk)
                           addLink c = c in
                       (addLink tok : toks,s'')
                    else -- ignore command
                       hScan' s'
                 else if com == begVar then
                    let (wrd,s'') = scanWord' s' 
                        bracket s = "<"++s++">" in
                    doFst (HWord (bracket wrd,NoHLink) :) (hScan' s'')
                 else
                    doFst (HCom com :) (hScan' s')
hScan' s = let (wrd,s') = scanWord s in
           doFst (HWord wrd :) (hScan' s')


scanWord :: String -> (Word,String)
scanWord s = let (w,s') = scanWord' s in
             ((w,NoHLink),s')

scanWord' :: String -> ([Char],String)
scanWord' "" = ("","")
scanWord' s@('<':_) = ("",s)
scanWord' s@(c:_) | isSpace c= ("",s)
scanWord' ('&':s) = let (sym,_:s') = break (==';') s in
                   doFst (symToAsc sym :) (scanWord' s')
scanWord' (c:s) = doFst (c:) (scanWord' s)


symToAsc :: String -> Char
symToAsc "lt" = '<'
symToAsc "gt" = '>'       
symToAsc "amp" = '&'       
symToAsc _ = '?'


------------
-- PARSER --
------------

-- This parser works by representing failure with an empty list, and
-- success with a singleton list.
-- Note that internally, all sorts of html-lists are represented in the same
-- way.

parseFancy :: String -> FancyText
parseFancy s = let (fan,s') = parseFancyText (hScan s) in
               if not (null s') then
                  [Text [("Error in help-text",NoHLink)]]
               else
                  head fan

parseFancyText :: [HToken] -> ([FancyText],[HToken])
parseFancyText = parseStar parseParagraph

-- parseParagraph delivers zero (failure) or one paragraph (success)
parseParagraph :: [HToken] -> ([Paragraph],[HToken])
parseParagraph (HCom c :ts) | c == begPar = 
              rbracket Para parseFancyText endPar ts
parseParagraph (HCom c :ts) | c == begDes =
              rbracket Description parseDefItems endDes ts
parseParagraph (HCom c :ts) | c == begDesCom =
              let f its = let maxWidth = maximum (map (length'.fst) its)
                              addSpace (t,d) = ([("  ",NoHLink)]++t++
                                                [(space (maxWidth-length' t),NoHLink)],d) in
                          Description (map addSpace its) in
              rbracket f parseDefItems endDesCom ts
parseParagraph (HCom c :ts) | c == begIte =
              let f its = Description (map (\(_,fan) -> ([("  -",NoHLink)],fan)) its) in
              rbracket f parseListItems endIte ts
parseParagraph (HCom c :ts) | c == begEnu =
              let f its = Description (map (\((_,fan),num) -> ([(num,NoHLink)],fan))
                             (zip its (map ((++".") . show) [1..]))) in
              rbracket f parseListItems endEnu ts
parseParagraph s = doFst (map Text) (parseTextBS s)
--parseParagraph s = ([],s)      -- failure

length' :: [Word] -> Int
length' = length . unwords . map fst

rbracket :: (a->b) -> ([HToken] -> ([a],[HToken])) -> String ->
            [HToken] -> ([b],[HToken])
rbracket f p rb ts = doFst (map f) ((parseThen p (parseComV rb) const) ts)


parseListItems :: [HToken] -> ([[([Word],FancyText)]],[HToken])
parseListItems = 
          parseStar (parseThen (parseCom itemT)
                               (mapP (pair []) parseFancyText) const')

parseDefItems :: [HToken] -> ([[([Word],FancyText)]],[HToken])
parseDefItems  = 
          parseStar (parseThen (parseThen (parseCom defT) parseText const')
                          (parseThen (parseCom defD) parseFancyText const')
                     pair)


parseTextBS :: [HToken] -> ([[Word]],[HToken])
parseTextBS = parseThen parseText (parseStar (parseCom breakT)) const

parseText :: [HToken] -> ([[Word]],[HToken])
parseText = parsePlus parseWord

parseWord :: [HToken] -> ([Word],[HToken])
parseWord (HWord w:ts) = ([w],ts)
parseWord ts = ([],ts)

parseCom :: String -> [HToken] -> ([()],[HToken])
parseCom c (HCom c':ts) | c==c' = ([()],ts)
parseCom c ts = ([],ts)

-- Alleen voor testen
parseComV :: String -> [HToken] -> ([()],[HToken])
parseComV c (HCom c':ts) | c==c' = ([()],ts)
--parseCom c ts = ([],ts)



-- more general functions for parsing

parsePlus :: ([HToken] -> ([a],[HToken])) -> [HToken] -> ([[a]],[HToken])
parsePlus p = parseThen p (parseStar p) (:)

parseStar :: ([HToken] -> ([a],[HToken])) -> [HToken] -> ([[a]],[HToken])
parseStar p = parsePlus p `parseElse` parseEmpty               


parseThen :: ([HToken] -> ([a],[HToken])) -> ([HToken] -> ([b],[HToken])) ->
             (a->b->c) -> [HToken] -> ([c],[HToken])
parseThen p q f ts = let (as,ts') = p ts in
                     if null as then ([],ts)
                     else
                     let (bs,ts'') = q ts' in
                     if null bs then ([],ts)
                     else ([f (head as) (head bs)],ts'')

parseElse :: ([HToken] -> ([a],[HToken])) -> ([HToken] -> ([a],[HToken])) ->
             [HToken] -> ([a],[HToken])
parseElse p q ts = let (as,ts') = p ts in
                  if null as then q ts
                  else (as,ts')

parseEmpty :: [HToken] -> ([[a]],[HToken])
parseEmpty ts = ([[]],ts)

mapP :: (a->b) -> ([HToken] -> ([a],[HToken])) -> 
                  ([HToken] -> ([b],[HToken]))
mapP f p ts = doFst (map f) (p ts)




----------------
-- FORMATTING --
----------------

  
{-                                                                 
-- splitLines is used in the gencoms module
splitLines :: [Word] -> String
splitLines text = concat (map plusCR (splitILines lineLength text))
-}

-- A labels is a string
type DisplayHelp a = Display String a

format :: DisplayHelp a -> Int -> FancyText -> a
format stuff@(_,vconc,_,_) lineLength fancy = 
            vconc (formatFan stuff lineLength fancy)

formatFan :: DisplayHelp a -> Int -> FancyText -> [a]
--formatFan ll = concat . (map (formatPar ll))
formatFan stuff ll [] = []
-- insert an empty line before a paragraph that follows something
formatFan stuff@(_,_,basic,_) ll (p : f@(Para _:_)) =
                formatPar stuff ll p ++ [basic ""] ++ formatFan stuff ll f
formatFan stuff ll (p:f) = formatPar stuff ll p ++ formatFan stuff ll f

formatPar :: DisplayHelp a -> Int -> Paragraph -> [a]
formatPar stuff ll (Text s) = splitILines stuff ll s 
formatPar stuff ll (Para p) = formatFan stuff ll p
formatPar stuff ll (Description d) = concat (map (formatItem stuff ll) d)

formatItem :: DisplayHelp a -> Int -> ([Word],FancyText) -> [a]
formatItem stuff@(hconc,_,basic,_) ll (ws,fancyText) =
    let ws' = map (formatWord stuff) ws
        name' = hconc (map fst ws')
        len = sum (map snd ws')
        restLl = ll - len
        (line1:lines) = formatFan stuff restLl fancyText
        addSpace line = hconc [basic (replicate len ' '), line] in
    (hconc [name', line1]) : (map addSpace lines)

splitILines :: DisplayHelp a -> Int -> [Word] -> [a]
splitILines stuff@(_,_,basic,_) lengt [] = [basic ""]
splitILines stuff@(hconc,_,_,_) lengt ws = 
                       let p l = sum (map snd l) <= lengt in
                       map (hconc . map fst) 
                           (takeWhiles' p (map (formatWord stuff) ws))
                                   

formatWord :: DisplayHelp a -> Word -> (a,Int)
formatWord stuff@(_,_,basic,label) (w,mlnk) =
              let w' = basic (w++" ")
                  w'' = case mlnk of
                           NoHLink -> w'
                           HLink lnk -> label lnk w' in
              (w'',length w+1)

{-

-- the rest of this module is used only for testing
testText :: String -> Imp () ()
testText file = readFil file `bind` \contents ->
                out (format (parseFancy contents))

doTest file = goSte (testText file) ()
                                      

instance Text Paragraph where
     showsPrec _ (Text ws) = (("Text:\""++unwords ws++"\"")++)
     showsPrec _ (Description d) = 
              (concat (map (\(ws,t) -> "\\item[" ++ unwords ws ++ "]" ++ 
                       show t) d)++)
           
testText2 :: String -> Imp () ()
testText2 file = readFil file `bind` \contents ->
                 out (show (parseFancy contents))

doTest2 file = goSte (testText2 file) ()
-}          
