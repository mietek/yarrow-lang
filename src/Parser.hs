-- File: Parser
-- Description: This module contains the parser and pretty-printer for terms.

module Parser(-- GENERAL PARSING STUFF
              ParseS(..), Parse, readToken, nextToken, readToken', startsWith,
              eat, eateat, eatIdent, eatOper, eatNum,
              -- PARSING EXPRESSIONS
              parseTerm, parseDecls, parseContextE, parseContext, parseDef, 
              stop, parseVar, parseVarList, parseIdAsSort, parseFilename,
              -- MISCELLANEOUS
              startNum, startVar, startBasic, pErr, separator, 
              parseList, parseList1, parseList0) where

import General
import Collect
import HaMonSt

--import Basic
--import Paths(errP)
--import SyntaxI
import Engine

import Scanner

-- Important exported routines:
-- For parsing:
--  + parseTerm


---------------------
---------------------
--  P A R S I N G  --
---------------------
---------------------

-- we use a recursive-descent parser, not very different from an
-- implementation in an imperative language. Of course, we do this with
-- help of monads.

-- the state used in the parser consists of 
-- syntaxinfo and a list of tokens (with place-information)
data ParseS = PARSES (SyntaxInfo,Tokens)

type Parse a = State ParseS a
                    
instance PartSyntax ParseS where
     extractSyn (PARSES (si,_)) = si
     insertSyn f (PARSES (si,t)) = PARSES (f si,t)


---------------------------------------
-- CONSTRUCTOR FUNCTIONS FOR PARSING --
---------------------------------------

-- the constructors, but now with place information
-- difference with the basic constructors:
--      1. place information is combined
--      2. dummies are inserted for sorts in Abs, All and Delta
mkAppIT :: TermIT -> TermIT -> TermIT
mkGenAbsIT :: (Vari,TermIT,Constraints,[TermIT]) -> TermIT -> PlaceInfo -> 
              TermIT
mkGenAllIT :: (Vari,TermIT,Constraints,[TermIT]) -> TermIT -> PlaceInfo -> 
              TermIT
mkDeltaIT :: (Vari,TermIT,TermIT) -> TermIT -> PlaceInfo -> TermIT
mkVrIT :: Vari -> PlaceInfo -> TermIT
mkSrtIT :: Sort -> PlaceInfo -> TermIT
mkHoleIT :: Hnum -> PlaceInfo -> TermIT
mkArrowIT :: TermIT -> TermIT -> TermIT
-- Extension: Records:
mkRecValueIT :: [(RecLabel,TermIT)] -> PlaceInfo -> TermIT
mkRecTypeIT :: [(RecLabel,TermIT)] -> PlaceInfo -> TermIT
mkRecSelectIT :: TermIT -> (RecLabel,PlaceInfo) -> TermIT
-- End Extension: Records:

mkAppIT (t,tit) (u,uit) = (mkApp t u, IT (combineIT tit uit) [tit,uit])
mkGenAbsIT = mkBindIT0 mkGenAbs
mkGenAllIT = mkBindIT0 mkGenAll
mkDeltaIT = mkBindIT1 mkDelta
mkVrIT v pi = (mkVr v,IT pi [])
mkSrtIT s pi = (mkSrt s,IT pi [])
mkHoleIT h pi = (mkHole h,IT pi [])
mkArrowIT (t,tit) (u,uit) = 
           (mkArrow (t,dummySort) u,
            IT (combineIT tit uit) [dummyIT,tit,dummyIT,uit])
-- Extension: Records:
mkRecValueIT ltits pi = let (ls,tits) = unzip ltits
                            (ts,its) = unzip tits in
                        (mkRecValue (zip ls ts),IT pi its)
mkRecTypeIT ltits pi = let (ls,tits) = unzip ltits
                           (ts,its) = unzip tits in
                       (mkRecType (zip ls ts),IT pi its) 
mkRecSelectIT (t,it@(IT pil _)) (l,pir) = 
           (mkRecSelect t l, IT (combinePlace pil pir) [it])
-- End Extension: Records:

-- mkBindIT0 is an auxilary function for mkGenAbsIT and mkGenAllIT etc.
mkBindIT0 :: (((Vari,Term,Sort),Constraints,[Term])->Term->Term) -> 
             (Vari,TermIT,Constraints,[TermIT]) -> TermIT ->
             PlaceInfo -> TermIT
mkBindIT0 bind (v,(t,tit),constrs,tits) (u,uit@(IT upi _)) pi = 
       (bind ((v,t,dummySort),constrs,map fst tits) u, 
        IT (combinePlace pi upi) ([dummyIT,tit,dummyIT,uit] ++ map snd tits))

mkBindIT1 :: ((Vari,Term,Term,Sort)->Term->Term) -> (Vari,TermIT,TermIT) ->
             TermIT -> PlaceInfo -> TermIT
mkBindIT1 bind (v,(d,dit),(t,tit@(IT upi _))) (u,uit) pi = 
         (bind (v,d,t,dummySort) u, 
          IT (combinePlace pi upi) [dummyIT,tit,dummyIT,uit,dit])

                                                            
----------------------------
-- BASIC PARSING ROUTINES --
----------------------------

-- everything is build up with readToken and nextToken

-- readToken  inspects first token of input and also gives the place-info
readToken :: Parse (Token,PlaceInfo)
readToken = fetchS3 >>= \(PARSES (_,t:_)) ->
            -- hbc 0.9999.4 will complain if we replace fetchS3 above by fetch,
            -- so we need a fetchS3 function with a more restricted type.
            return t

fetchS3 :: State s s
fetchS3 = fetch
 
-- nextToken  skips the first token
nextToken :: Parse ()
nextToken = update' (\(PARSES (si,_:t)) -> PARSES (si,t))

-- readToken'  inspects first token of input
readToken' :: Parse Token
readToken' = map fst readToken

startsWith :: Token -> Parse Bool
startsWith t = map fst (startsWith' t)

startsWith' :: Token -> Parse (Bool,PlaceInfo)
startsWith' t = readToken >>= \(t',pi) ->
                return (t==t',pi)

              
eat :: Token -> String -> Parse ()
eat t s = eat' t s >>= \_ ->
          return ()
      
eat' :: Token -> String -> Parse PlaceInfo
eat' t s = readToken >>= \(t',pi) ->
           if t==t' then
              nextToken >>
              return pi
           else
              pErr ("Expected " ++ nacs t ++ s)

eateat :: [Token] -> Parse ()
eateat []  = skip
eateat (t:ts) = eat t "" >>
                eateat ts
     
readIdent :: String -> Parse (String,PlaceInfo)
readIdent s = readToken >>= \(t,pi) ->
              case t of
              Ident i -> nextToken >> return (i,pi)
              otherwise -> pErr s

-- consistent name would be readIdent'
eatIdent :: String -> Parse String
eatIdent s = map fst (readIdent s)

eatOper :: String -> Parse String
eatOper s = readToken' >>= \t ->
            case t of
            Oper o -> nextToken >> return o
            otherwise -> pErr s

eatNum :: Parse Int
eatNum = readToken' >>= \t ->
         case t of
         Num n -> nextToken >> return n
         otherwise -> pErr "Expected number"


-------------------------
-- PARSING EXPRESSIONS --
-------------------------
       
     
-- operators in order of precedence (weakest binders first)
-- \, @, let
-- ->          (right associative)
-- user defined operators (associativity and precedence can be defined)
-- application (left associative)          
  

-- so the context-free grammar for lambda-terms is
--
-- Term       = lambda ItemC dot Term | 
--              all    ItemC dot Term |
--              let    ItemI dot Term | 
--              binder ItemC dot Term |
--              Small
-- Small      = Factor_1 arrow Small | Factor_1
-- Factor_i   = Factor_i+1 oper_n_i Factor_i+1 |  
-- (i=1..9)     Factor_i   oper_l_i Factor_i+1 |
--              Factor_i+1 oper_r_i Factor_i   |
--              Factor_i+1
-- Factor_10  = Factor_10 Basic | Basic
-- Basic      = sort | Var | '(' Expression ')'
-- Var        = ident | '(' oper ')'
-- Decls      = VarList colon Expression
-- Def        = Var is Expression [colon Expression]    
-- VarList    = Var | Var ',' VarList
--
-- we wrote oper_l_i  for left-associative operators of precedence i 
--          oper_r_i  for right-associative operators of precedence i 
--          oper_n_i  for non-associative operators of precedence i
--          oper      for any operator 

-- lambda-term 
parseTerm :: Parse TermIT
parseTerm = readToken >>= \(t,pi) ->
 case t of
 Lambda -> nextToken >>
           map (changeStart pi) 
               (parseTermHelpL parseDecls (repeated mkGenAbsIT))
 At ->     nextToken >>
           map (changeStart pi) 
               (parseTermHelpL parseDecls (repeated mkGenAllIT))
 Let ->    nextToken >>
           map (changeStart pi) 
           (parseTermHelpD parseDef mkDeltaIT')
               where mkDeltaIT' ((v,pi),d,t) body =
                            mkDeltaIT (v,d,t) body pi
 -- for binders:
 (Ident bv)->fetchBind bv >>= \b ->
             if b then
               nextToken >>
               readToken' >>= \tok ->
               case tok of
                 RightP -> return (mkVrIT bv pi)
                 otherwise-> parseDecl >>= \((w,pi'),t,c,cts) ->
                             eat Dot "" >>
                             parseTerm >>= \bd ->
                             return (mkAppIT (mkVrIT bv pi)
                                             (mkGenAbsIT (w,t,c,cts) bd pi'))
             else
                parseSmall
 otherwise -> parseSmall

{- parseTermHelp :: Parse a -> (a -> Term -> Term) -> Parse Term
   this polymorphic definition is not accepted, so we have to have two
   copies of this function -}

parseTermHelpD :: Parse ((Vari,PlaceInfo),TermIT,TermIT) -> 
                  (((Vari,PlaceInfo),TermIT,TermIT) -> TermIT -> TermIT) -> 
                  Parse TermIT
parseTermHelpD parseI const = parseI >>= \it ->
                              eat Dot "" >>
                              map (const it) parseTerm

parseTermHelpL :: 
    Parse ([(Vari,PlaceInfo)],TermIT,Constraints,[TermIT]) -> 
    (([(Vari,PlaceInfo)],TermIT,Constraints,[TermIT]) -> TermIT -> TermIT) ->
    Parse TermIT
parseTermHelpL parseI const = parseI >>= \it ->
                              eat Dot "" >>
                              map (const it) parseTerm


-- repeated make  generalizes make so it accepts a list of variables 
repeated :: 
    ((Vari,TermIT,Constraints,[TermIT]) ->TermIT->PlaceInfo->TermIT) ->
    ([(Vari,PlaceInfo)],TermIT,Constraints,[TermIT]) -> TermIT->TermIT
repeated make ([],_,_,_) body = body
repeated make ((v,pi):vl,t,c,cts) body =
           make (v,t,c,cts) (repeated make (vl,t,c,cts) body) pi

-- Declarations, e.g. x1,x2,x3 : E
parseDecls :: Parse ([(Vari,PlaceInfo)],TermIT,Constraints,[TermIT])
parseDecls = parseVarPiList >>= \vl ->
             parseDeclsRest "Expected : or , or <:" >>= \(t,c,cts) ->
             return (vl,t,c,cts)

-- One declarations, e.g. x1 : E or x1 <: t : A
--parseDecl :: Parse ((Vari,PlaceInfo),TermIT,Constraints,[TermIT])
parseDecl =  parseVarPi >>= \v ->
             parseDeclsRest "Expected : or <:" >>= \(t,c,cts) ->
             return (v,t,c,cts)

parseDeclsRest :: String ->
                 Parse (TermIT,Constraints,[TermIT])
parseDeclsRest s =
             readToken' >>= \tok ->
             case tok of
             Colon -> nextToken >>
                      parseTerm >>= \t->
                      return (t,CNone,[]) 
             -- Extension: Subtyping:
             LEC -> nextToken >>
                    parseTerm >>= \subConstr ->
                    readToken' >>= \tok ->
                    case tok of
                    Colon -> nextToken >>
                             parseTerm >>= \t ->
                             return (t,CSub,[subConstr])
                    otherwise -> return (dummyTermIT,CSub,[subConstr])
             -- End Extension: Subtyping
             otherwise -> pErr s
 
-- A definition, e.g. x := E or x := E : E                             
parseDef :: Parse ((Vari,PlaceInfo),TermIT,TermIT)
parseDef = parseVarPi >>= \v ->
           eat Is "" >>
           parseDefRest >>= \(d,t) ->
           return (v,d,t)

parseDefRest :: Parse (TermIT,TermIT)
parseDefRest = 
           parseTerm >>= \d ->
           readToken' >>= \tok ->
           case tok of
           Colon -> nextToken >> 
                    parseTerm >>= \t -> 
                    return (d,t)
           otherwise -> return (d,dummyTermIT)


-- 'small' terms
parseSmall = map (foldr1 mkArrowIT)
                 (parseList1 (separator Arrow) (parseFactor 0))
           

-- Factor

                              
-- parseFactor doesn't always give the full place info !
parseFactor n | n <= maxPrec = 
     parseFactor (n+1) >>= \f ->
     readToken' >>= \t ->
     case t of
     Oper v -> fetchPrec v >>= \(vpred,vassoc) ->
               if vpred /= n then
                  return f
               else
               nextToken >>
               let plist = map (f:) (parseList1 (separator (Oper v))
                                                (parseFactor (n+1)))
                   oper l@(_,IT lpi _) r@(_,IT rpi _) = 
                             changeStartEnd (combinePlace lpi rpi)
                                (mkAppIT (mkAppIT (mkVrIT v dummyPI) l) r) in
               case vassoc of
               NoAssoc ->  map (oper f) (parseFactor (n+1))
               LeftAssoc    ->  map (foldl1 oper) plist
               RightAssoc   ->  map (foldr1 oper) plist
     otherwise -> return f

-- Factor_10      
parseFactor n = map (foldl1 mkAppIT)
                             (parseList1 startBasic parseBasic2)


-- Extension: Records:
parseBasic2 = parseBasic >>= \t ->
{-
              separator Backquote >>= \b ->
              if b then
                 readIdent "" >>= \l ->
                 return (mkRecSelectIT t l)
              else
                 return t
-}
              map (foldl mkRecSelectIT t)
                  (parseList0 (separator Backquote) (readIdent ""))
-- End Extension: Records:

-- Basic
parseBasic = 
        readToken >>= \(t,pi) ->
        case t of
        Ident v -> fetchBind v >>= \b ->
                   if b then
                       parseTerm
                   else 
                     nextToken >>
                     fetchSyn >>= \si ->
                     if isIdentSort si v then
                        return (mkSrtIT (identToSort v) pi)
                     else
                        return (mkVrIT v pi)
        LeftP -> nextToken >>
                 readToken' >>= \t' ->
                 case t' of
                 Oper v -> nextToken >>
                           eat' RightP "" >>= \rpi ->
                           return (mkVrIT v (combinePlace pi rpi))
                 otherwise -> parseTerm >>= \e ->
                              eat' RightP "" >>= \rpi ->
                              return (changeStartEnd (combinePlace pi rpi) e)
-- Extension: Records:
        LeftB  -> nextToken >>
                  parseList startVar
                            (separator Comma) parseFieldValue >>= \fields ->
                  eat' RightB " or label or ," >>= \rpi ->
                  return (mkRecValueIT fields (combinePlace pi rpi))
        LeftBB  -> nextToken >>
                   parseList startVar
                             (separator Comma) parseFieldType >>= \fields ->
                   eat' RightBB " or label or ," >>= \rpi ->
                   return (mkRecTypeIT fields (combinePlace pi rpi))
-- End Extension: Records:
        Lambda -> parseTerm
        At     -> parseTerm
        Let    -> parseTerm
        otherwise -> pErr "Expected term"     

-- for internal use
parseVarPi :: Parse (Vari,PlaceInfo)
parseVarPi = let parseVError = pErr "Expected var" in
        readToken >>= \(t,pi) ->
        case t of
        Ident v -> fetchSyn >>= \si ->
                   if isIdentSort si v then
                      parseVError
                   else
                   nextToken >>
                   return (v,pi)
        LeftP -> nextToken >>
                 eatOper "Expected operator" >>= \v ->
                 eat' RightP "" >>= \rpi ->
                 return (v,combinePlace pi rpi)
        otherwise -> parseVError

parseVarPiList :: Parse [(Vari,PlaceInfo)]
parseVarPiList = parseList1 (separator Comma) parseVarPi
                 
-- Extension: Records:
parseFieldValue :: Parse (RecLabel,TermIT)
parseFieldValue = eatIdent "Expected label" >>= \label ->
                  eat (Oper "=") "" >>
                  parseTerm >>= \t ->
                  return (label,t)

parseFieldType :: Parse (RecLabel,TermIT)
parseFieldType = eatIdent "Expected label" >>= \label ->
                 eat Colon "" >>
                 parseTerm >>= \t ->
                 return (label,t)
-- End Extension: Records:



----------------------------
-- OTHER PARSING ROUTINES --
----------------------------

-- these routines are only used outside this module


-- stop p  performes parsing routine p and then removes the end-of-line
-- marker
-- a is typically Term or some command-type
stop :: Parse a -> Parse a
stop p = p >>= \a ->
         eat Eoln "" >>
         return a
                                      

parseContextE :: Parse ContextE
parseContextE =
    parseVar >>= \v ->
    readToken' >>= \tok ->
    case tok of
    Colon -> nextToken >>
             parseTerm >>= \t ->
             return (mkDecl (v,forgetIT t,dummySort))
    LEC ->   nextToken >>
             parseDefRest >>= \(b,t) ->
             return (mkSubDecl (v,forgetIT b,forgetIT t,dummySort))
    Is ->    nextToken >>
             parseDefRest >>= \(d,t) ->
             return (mkDef (v,forgetIT d,forgetIT t,dummySort))
    otherwise -> pErr "Expected : or :="

parseContext :: Parse LContext
parseContext = map (listToLocCon . reverse)
                   (parseList startVar (separator Comma) parseContextE)

parseVar :: Parse Vari
parseVar = map fst parseVarPi
                        
parseVarList :: Parse [Vari]
parseVarList = map (map fst) parseVarPiList
              
-- parseIdAsSort  for use only of the "System" command, where a new
--                set of sorts is introduced
parseIdAsSort :: Parse Sort
parseIdAsSort = map SORT (eatIdent "Expected sort")
  
parseFilename :: Parse String
parseFilename = readToken' >>= \t ->
                case t of
                Filename f -> nextToken >> return f
                otherwise -> pErr "Expected filename between \"s"


-------------------
-- MISCELLANEOUS --
-------------------
                                                       
-- functions that give the first tokens a non-terminal can start with

-- startBasic  determines the set of tokens that a Basic can begin with
startBasic = readToken' >>= \t ->
         case t of
         Ident v -> return True
         LeftP ->   return True            
         Lambda ->  return True
         At     ->  return True
         Let    ->  return True            
         -- Extension: Records:
         LeftB  ->  return True
         LeftBB ->  return True
         -- End Extension: Records:
         otherwise -> return False
                       
-- startVar  determines the set of tokens that a Var can begin with
startVar = startBasic  -- ???

-- startNum  determines the set of tokens that a number can begin with
startNum = readToken' >>= \t ->
           case t of
           Num _ -> return True
           otherwise -> return False 


-- error routines   
   
parseErrSuffix :: String
parseErrSuffix = " (parser error)"

-- pErr  gives an error with the place-indication at the current token
pErr :: String -> Parse a
pErr s = readToken >>= \(_,pi) ->
         errP pi (s ++ parseErrSuffix)


-----------------------------------
-- GENERAL FUNCTIONS FOR PARSING --
-----------------------------------

-- separator t  returns True iff t is on the head (in which case t is eaten)
separator :: Token -> Parse Bool
separator t = readToken' >>= \u ->
             if t == u then
                nextToken >>
                return True
             else
                return False
                                                                       
-- parseList1 sep pp tl  parses a list of pp's from tl; sep determines
-- if parseList must continue (eating tokens by sep for each element),
-- or if it has to stop. parseList1 works for tl's of the form   
-- 'pp' 'sep' 'pp' 'sep' 'pp' etc, at least one 'pp'
-- a is typically Term or Item
-- typically used for non-empty lists
parseList1 :: (Functor p,Monad p) => p Bool -> p a -> p [a]
parseList1 sep pp = pp >>= \term ->
                    map (term:) (parseList0 sep pp)

-- parseList st sep pp tl  parses a list of pp's from tl;
-- st determines whether the list has one element or not
-- st shouldn't '"eat" anything!
-- 'pp' 'sep' 'pp' 'sep' 'pp' etc, or the empty list
-- a is typically Term or Item
parseList :: (Functor p,Monad p) => p Bool -> p Bool -> p a -> p [a]
parseList st sep pp = st >>= \b ->
                      if b then
                         parseList1 sep pp
                      else
                         return []

-- parseList0 sep pp tl  parses a list of pp's from tl;
-- 'sep' 'pp' 'sep' 'pp' 'sep' 'pp' etc, or the empty list
-- a is typically Term or Item
parseList0 :: (Functor p,Monad p) => p Bool -> p a -> p [a]
parseList0 sep pp = sep >>= \b ->
                    if b then
                       pp >>= \term ->
                       map (term:) (parseList0 sep pp)
                    else
                       return []
