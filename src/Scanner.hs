-- File: Scanner
-- Description: This module defines the scanner.
--   Scanning is complicated by two things:
--    + The scanner must deliver not simply a list of tokens, but tokens with
--      place information, that can be used to give nice error messages
--    + Instead of keyboard-input, also input from a file must be handled
--      as if it were input by keyboard, so it must echoed to the screen.
--   In this module also a 'reverse' scanner is given, which transform a
--   token to a string.

module Scanner(Token(..), Tokens, scanLine, isInputComplete, nacs) where
import General
import HaTuple
import HaMonSt
import Char(isAlpha,isAlphaNum,isDigit)

--import SyntaxI
--import Basic(PlaceInfo,Error,ErrorElem(..))
--import Paths(errS,errP)
import Engine



----------------------
-- S C A N N I N G  --
----------------------

-- Token might be called Terminal, but that could be confused with Term

data Token = Lambda | At | Dot | LeftP | RightP | Colon | Comma | On | In |
--               \    @     .      (       )        :      ,      on   in
             Arrow | Let | Then | Else | Bar |  Is | Conv | Ident String |
--            ->     let   then   else   |      :=   :=:    ident
             Oper String | Num Int | Filename String |
--            +<> etc    | number      "string"
             Eoln |
--           CR
             Space | Newline |
--             for printing
-- Extension: Records:
             LeftB | RightB | LeftBB | RightBB | Backquote |
--           {           }        {|         |}         `
-- End Extension: Records
-- Extension: Subtyping:
             LEC
--           <:
-- End Extension: Subtyping



instance Eq Token where Lambda    == Lambda    = True
                        At        == At        = True
                        Dot       == Dot       = True
                        LeftP     == LeftP     = True
                        RightP    == RightP    = True
                        Colon     == Colon     = True
                        Eoln      == Eoln      = True
                        Arrow     == Arrow     = True
                        Comma     == Comma     = True
                        On        == On        = True
                        In        == In        = True
                        Let       == Let       = True
                        Then      == Then      = True
                        Else      == Else      = True
                        Bar       == Bar       = True
                        Is        == Is        = True
                        Conv      == Conv      = True
                        Ident v   == Ident w   = v==w
                        Oper v    == Oper w    = v==w
                        Num m     == Num n     = m==n
                        Filename s== Filename t= s==t
                        -- Extension: Records:
                        LeftB     == LeftB     = True
                        RightB    == RightB    = True
                        LeftBB    == LeftBB    = True
                        RightBB   == RightBB   = True
                        Backquote == Backquote = True
                        -- End Extension: Records
                        -- Extension: Subtyping:
                        LEC       == LEC       = True
                        -- End Extension: Subtyping
                        _         == _         = False

type Tokens = [(Token,PlaceInfo)]

-------------------------------
-- IDENTIFIERS AND OPERATORS --
-------------------------------

-- isV1 checks this character can be the start of a variable
isV1 :: Char -> Bool
isV1 '*' = True
isV1 '#' = True
isV1 c = isAlpha c

-- isV checks this character can occur after the first character of
-- a variable
isV :: Char -> Bool
isV '*' = True
isV '#' = True
isV '\'' = True
isV '_' = True
isV c = isAlphaNum c


---------------------
-- S C A N N I N G --
---------------------

-- scanLine s ln  scans line n containing s and delivers
-- a list of tokens paired with placemarkers saying at which
-- character in the input string the token started and ended
-- (so the difference is the length of the token)
scanLine :: (Functor m,ErrorSMonad m) =>
            String -> Int -> m [(Token,PlaceInfo)]
scanLine s ln = let len = length s in
                fmap (fmap (\(t,(s,e)) -> (t,((ln,len-s),(ln,len-e)))))
                    (scanLine' s len ln)

scanLine' :: (Functor m,ErrorSMonad m) =>
             String -> Int -> Int -> m [(Token,(Int,Int))]
scanLine' "" len ln = return [(Eoln,(0,-1))]
scanLine' (' ':s) len ln = scanLine' s len ln
scanLine' ('-':'-':s) len ln = return [(Eoln,(length s +2,length s))]
                               -- comment at end of line
scanLine' s' len ln = handleS (scan' s')
                      (\[ES mes] -> let p = len - length s' in
                                    errP ((ln,p),(ln,p+1)) mes)
                      (\(t,s'') ->
                        fmap ((t,(length s',length s'')) :)
                            (scanLine' s'' len ln))

-- isInputComplete checks whether a list of tokens constitutes a complete
--                 command. The interface will read another line if not;
--                 it is the responsibility of the interface to stop
--                 reading more lines if an empty line (just one Eoln token)
--                 is entered!
--                 A list of tokens is incomplete if it ends with
--                 '.' '->' ',' ':=:', ':=', an operator or has an unmatched
--                 number of parantheses.
-- Precondition: length toks >= 2
isInputComplete :: Tokens -> Bool
isInputComplete toks =
       let skipEoln = tail (reverse toks)
           lastTok = fst (head skipEoln)
           isOper (Oper _) = True
           isOper _ = False
           parantDiff = countMatch (fmap fst toks) in
       not (lastTok `elem` [Dot,Arrow,Colon,Comma,Conv,Is] ||
            isOper lastTok || parantDiff > 0)


-- countMatch toks  returns the difference between the number of ('s and
--                  the number of )'s
countMatch :: [Token] -> Int
countMatch [] = 0
countMatch (LeftP :toks) = countMatch toks + 1
countMatch (RightP:toks) = countMatch toks - 1
countMatch (_:toks) = countMatch toks

-- scan' s  scans one token from s
-- scan' may only deliver errors in the form of a string
scan' :: (Functor m,ErrorSMonad m) => String -> m (Token,String)
scan' (':':'=':':':s) = return (Conv,s)
scan' (':':'=':s) = return (Is,s)
scan' ('"':s) = let (f,s2) = span (/='"') s in
                if null s2 then
                   scanErrS "Filename not terminated"
                else return (Filename f,tail s2)
-- Extension: Records:
scan' ('{':'|':s) = return (LeftBB,s)
scan' ('{':s) = return (LeftB,s)
scan' ('|':'}':s) = return (RightBB,s)
scan' ('}':s) = return (RightB,s)
scan' ('`':s) = return (Backquote,s)
-- End Extension: Records
-- Extension: Subtyping:
scan' ('<':':':s) = return (LEC,s)
-- End Extension: Subtyping
scan' (c:s) | isO1 c = let (v,s2) = span isO (c:s)
                           special "\\" = Lambda
                           special "@" = At
                           special "->" = Arrow
                           special "|" = Bar
                           special v = Oper v in
                       return (special v,s2)
scan' (c:s) | isV1 c = let (v,s2) = span isV (c:s)
                           lowV = toLowers v
                           special v | lowV == "let"  = Let
                           special v | lowV == "then" = Then
                           special v | lowV == "else" = Else
                           special v | lowV == "on"   = On
                           special v | lowV == "in"   = In
                           special v = Ident v in
                       return (special v,s2)
scan' (c:s) | isDigit c = let (n,s2) = readNum (c:s) in
                          return (Num n,s2)
scan' (c:s) = fmap (`pair` s) (scan1 c)

scan1 :: PreErrorMonad m => Char -> m Token
scan1 '.'  = return Dot
scan1 '('  = return LeftP
scan1 ')'  = return RightP
scan1 ':'  = return Colon
scan1 ','  = return Comma
scan1 s    = scanErrS ("Unknown symbol "++[s])

scanErrSuffix :: String
scanErrSuffix = " (scanner error)"

scanErrS :: PreErrorMonad m => String -> m a
scanErrS s = errS (s++scanErrSuffix)

{-
-- Some functions to test the scanner
-- Not used
testLoop :: Int -> Scan ()
testLoop n = putSt ("\n"++show n++" ") >>
           printErrorsS scan
           (\(_,s) -> putSt (tostring s)) >>
           testLoop (n+1)
               where tostring [] = ""
                     tostring ((t,(i,j)):l) = "(" ++ nacs1 t ++ " " ++
                          show i ++ ".." ++ show j ++ ")," ++ tostring l

testScan = goSte (putSt "Type some string to be scanned" >> testLoop 0)
                  (SCANS testSyntax)
-}

---------------------
-- TOKEN TO STRING --
---------------------

-- nacs prints one token
nacs :: Token -> String
nacs Lambda = "\\"
nacs At = "@"
nacs Dot = "."
nacs LeftP = "("
nacs RightP = ")"
nacs Colon = ":"
nacs Comma = ","
nacs On = "on"
nacs In = "in"
nacs Then = "then"
nacs Else = "else"
nacs Bar = "|"
nacs Is = ":="
nacs Conv = ":=:"
nacs Arrow = "->"
nacs Let = "let"
nacs (Ident s) = s
nacs (Oper s) = s
nacs (Num n) = show n
nacs (Filename f) = "\"" ++ f ++ "\""
nacs Space = " "
nacs Newline ="\n"
nacs Eoln = "end of line"
-- Extension: Records:
nacs LeftB = "{"
nacs RightB = "}"
nacs LeftBB = "{|"
nacs RightBB = "|}"
nacs Backquote = "`"
-- End Extension: Records
-- Extension: Subtyping:
nacs LEC = "<:"
-- End Extension: Subtyping
