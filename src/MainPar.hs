-- File: MainPar
-- Description: this module holds the parsing routine for commands

module MainPar(parseCommand,
               parseSortExs,parseAxioms,parseRules) where

import HaTuple
import General
import HaMonSt

--import Basic
--import Paths
--import SyntaxI
--import ProvDat
--import MainSta(ModuleName,OptList)
import Engine

import Parser
import Scanner
import ProvPar
import Command

---------------------------
--    P A R S I N G      --
---------------------------
         
-- parseCommand has as argument the number of the task it was typed in.
parseCommand :: TaskId -> Parse Command
parseCommand taskNr =
  parseMCommand taskNr >>= \gc ->
  case gc of
  CNoParse -> parseProverCommand >>= \pc ->
              case pc of
              PNoParse -> parseTacticTerm >>= \tac ->
                          return (CTactic taskNr tac)
              otherwise -> return (CProverCommand taskNr pc)
  otherwise -> return gc


                            
                     

-- commands are no terminals because this is easier. Furthermore the
-- command-structure is not so complex that it is needed.
parseMCommand :: TaskId -> Parse Command
parseMCommand taskNr = 
  readToken' >>= \t0 ->
  let t = toLowerIdent t0 in
  case t of
  Ident "bdred" -> nextToken >> fmap (CGiveBDReductionPath taskNr . 
                                     pair emptyLCon) parseTerm
  Ident "bred"  -> nextToken >> fmap (CGiveBReductionPath  taskNr . 
                                     pair emptyLCon) parseTerm
  Ident "dred"  -> nextToken >> fmap (CGiveDReductionPath  taskNr . 
                                     pair emptyLCon) parseTerm
  Ident "type"  -> nextToken >> fmap (CGiveType taskNr . 
                                     pair emptyLCon) parseTerm
  Ident "check" -> nextToken >> 
                   parseTerm >>= \t1 ->
                   readToken' >>= \tok ->
                   let makeC f t2 = f taskNr (emptyLCon,t1,t2) in
                   case tok of
                      Colon -> nextToken >>
                               fmap (makeC CCheckTyping) parseTerm
                      Conv  -> nextToken >>
                               fmap (makeC CCheckBDConv) parseTerm
                      -- Extension: Subtyping:
                      LEC   -> nextToken >>
                               fmap (makeC CCheckSubtype) parseTerm
                      -- End Extension: Subtyping
                      otherwise -> pErr "Expected : or :=:"
  Ident "print" -> nextToken >> fmap (CPrintVar taskNr) parseVar
  Ident "deduction"-> parseDeduction taskNr OutAscii
  Ident "latexdeduction"-> parseDeduction taskNr OutLatex
  Ident "javadeduction"-> parseDeduction taskNr OutJava
  Ident "show"    -> nextToken >>
                     readNumDef1 >>= \goalNr ->
                     return (CShow taskNr goalNr)
  Eoln            -> return CSkip
  Ident "abort"   -> nextToken >> return (CProverExit taskNr Abort)
  Ident "exit"    -> nextToken >> return (CProverExit taskNr Exit)
  Ident "history" -> nextToken >> return (CHistory taskNr)
  Ident "context" -> nextToken >>
                     parseGiveContext OutAscii
  Ident "latexcontext" -> nextToken >>
                     parseGiveContext OutLatex
  Ident "javacontext" -> nextToken >>
                     parseGiveContext OutJava
  Ident "frankcontext" -> nextToken >>
                     parseGiveContext OutFrank
  Ident "size"    -> nextToken >> return CSize
  Ident "help"    -> nextToken >>
                     startsWith Eoln >>= \b ->
                     if b then
                        return CHelp
                     else
                        readTokensTillEoln >>= \ts ->
                        return (CHelpOn (concat (fmap nacs ts)))
  Ident "option"  -> nextToken >>
                     startsWith Eoln >>= \b ->
                     if b then
                        return CGiveOptions
                     else
                        fmap CSetOptions parseOption
  Ident "infix"   -> infHelp NoAssoc
  Ident "infixr"  -> infHelp RightAssoc
  Ident "infixl"  -> infHelp LeftAssoc
  Ident "binder"  -> nextToken >>
                     fmap CSetBinder parseVar
  Ident "latexvar"-> impHelp CSetLaTeX
  Ident "implicit"-> impHelp CSetImplArgs
  Ident "read"    -> nextToken >> 
                      parseFilename >>= \f ->
                      return (CRead f)
  Ident "quit"    -> nextToken >> return CQuit
  Ident "prove"   -> nextToken >> 
                     parseVar >>= \v ->
                     eat Colon "" >>
                     parseTerm >>= \t ->
                     return (CProveVar (v,t))
  Ident "def"     -> nextToken >> parseComHelp CDefVarW parseDef doFst3
  Ident "var"     -> nextToken >>
                     parseDecls >>= \(vs,t,constrs,cts) ->
                     case constrs of
                     CNone -> return (CDeclareVars ((fmap fst vs),t))
                     -- Extension: Subtyping:
                     CSub -> if (fst t)==dummyTerm then
                                -- then t wasn't given by user
                                return (CDeclareVarsSub 
                                                 ((fmap fst vs),head cts))
                             else
                                return (CDeclareVarsSubW 
                                                 ((fmap fst vs),head cts,t))
                     -- End Extension: Subtyping
  Ident "reset"   -> nextToken >> fmap CDelFromVar parseVar
  Ident "system"  -> nextToken >> 
                     readToken' >>= \t ->
                     case t of
                     LeftP -> fmap CSetTypingSystem parseSystem
                     otherwise -> return CGiveTypingSystem
  Ident "use"     -> nextToken >>
                     startsWith Eoln >>= \b ->
                     if b then
                        return CGiveUseFor
                     else
                        readToken' >>= \t ->
                        case t of
                        Ident tacName -> nextToken >>
                                         parseVar >>= \vari ->
                                         return (CUseFor tacName vari)
                        otherwise -> pErr "expected tactic"
  Ident "load"    -> nextToken >> 
                     readToken' >>= \t ->
                     case t of
                     Eoln -> return CGiveModules
                     otherwise -> fmap CLoadModule parseFilename
  Ident "save"    -> nextToken >> 
                     fmap CSaveModule parseFilename
  Ident "clear"   -> nextToken >> return CClearModule
  Ident "path"    -> nextToken >>
                     readToken' >>= \t ->
                     case t of
                     Eoln -> return CShowPath
                     otherwise -> fmap CAddPath parseFilename
  Ident "task" ->    nextToken >> 
                     readToken' >>= \t ->
                     case t of
                     Eoln -> return CGiveTasks
                     otherwise -> fmap CSetTask parseVar
  -- ! Just for testing !      
  Ident "zmatch" ->  nextToken >>
                     eat LeftP "" >>
                     parseContext >>= \con ->
                     eat RightP "" >>
                     eat Comma "" >>
                     eat LeftP "" >>
                     parseVarList >>= \exVars ->
                     eat RightP "" >>
                     eat Comma "" >>
                     parseTerm >>= \pat ->
                     eat Comma "" >>
                     parseTerm >>= \t ->
                     return (CZMatch taskNr (con,exVars,pat,t))
  Ident "zwerver" -> nextToken >>
                     parseTerm >>= \t1 ->
                     eat Comma "" >>
                     parseTerm >>= \t2 ->
                     return (CZwerver (t1,t2))
  otherwise       -> return CNoParse
 
parseComHelp com pars extract = fmap (com . extract fst) pars

parseGiveContext latex =
       startBasic >>= \b ->
       (if b then
           parseVar >>= \v1 ->
           readToken' >>= \tok ->
           case tok of
           Dot -> eat Dot "" >>
                  eat Dot "" >>
                  parseVar >>= \v2 ->
                  return (ConRange (v1,v2))
           otherwise -> return (ConRange (v1,v1))
        else
        readToken' >>= \tok ->
        case tok of
        (Filename s) -> nextToken >>
                        return (ConModule s)
        _ -> return ConAll) >>= \part ->
       startsWith Colon >>= \b ->
       (if b then
           nextToken >>
           parseList startVar (separator Comma) parseIdAsSort >>= \sl ->
           return sl
        else
           return []) >>= \sortList ->
       parseConFile >>= \conTo ->
       return (CGiveContext latex part sortList conTo)

parseConFile :: Parse ConToFile
parseConFile = 
    readToken' >>= \tok ->
    case tok of
    On -> nextToken >>
          parseFilename >>= \fil ->
          return (ConToFile fil)
    Eoln -> return ConToScreen
    _ -> pErr "Expected end of line, or On"

parseDeduction :: TaskId -> OutputMode -> Parse Command
parseDeduction taskNr latex =
    nextToken >>
    parseVar >>= \v ->
    readToken' >>= \tok ->
    (case tok of
     Num n -> nextToken >>
              return n
     _ -> return (-1)) >>= \n ->
    parseConFile >>= \conFile ->
    return (CDeduction latex taskNr v n conFile)

            
infHelp assoc = impHelp (\(v,i) -> CSetPrecAndAss (v,i,assoc))

impHelp com = nextToken >>
              eatNum >>= \n ->
              fmap (com . flip pair n) parseVar

parseOption = let errMess = "Expected +opt or -opt" in
              eatOper errMess >>= \v ->
              eatIdent errMess >>= \o ->
              case v of
              "+" -> return (o,True)
              "-" -> return (o,False)
              otherwise -> pErr errMess
                                      
readTokensTillEoln :: Parse [Token]
readTokensTillEoln = readToken' >>= \t ->
                     case t of
                     Eoln -> return []
                     otherwise -> nextToken >>
                                  fmap (t:) readTokensTillEoln



----------------------
-- PARSING A SYSTEM --
----------------------

-- System = '(' SortExs ')' ',' '(' Axioms ')' ',' '(' Rules ')' 
--          [',' '(' SortsSub ')' ',' '(' Rules ')']
-- SortExs = List SortEx
-- SortEx = Ident MaybeAttrS
-- Axioms = List Axiom
-- Axiom = Ident ':' Ident
-- Rules = List Rule
-- Rule = '(' Ident ',' Ident ')' |
--        '(' Ident ',' Ident ',' Ident ')' |
-- Sorts = List Sort
-- Sort = Ident
-- MaybeAttrS = empty | '->' AttrS
-- AttrS = 'records' | 'subtyping'
-- List xxx = empty | xxx | xxx ',' .. xxx
          
parseSystem :: Parse System
parseSystem = eat LeftP "" >>
              parseSortExs >>= \sorts ->
              eateat [RightP,Comma,LeftP] >>
              parseAxioms >>= \axioms ->
              eateat [RightP,Comma,LeftP] >>
              parseRules >>= \rules ->
              eat RightP "" >>
              readToken' >>= \tok ->
              (case tok of
               Comma -> nextToken >>
                        eat LeftP "" >>
                        parseSorts >>= \sortsSub ->
                        eateat [RightP,Comma,LeftP] >>
                        parseRules >>= \rulesSub ->
                        eat RightP "" >>
                        return (sortsSub,rulesSub) 
               otherwise -> return ([],[])
              ) >>= \(sortsSub,rulesSub) ->
              return (quintupleToSystem 
                                   (sorts,axioms,rules,sortsSub,rulesSub))

quintupleToSystem :: ([(Sort,[Extension])], 
                      [(Sort,Sort)], 
                      [(Sort,Sort,Sort)],
                      [Sort], 
                      [(Sort,Sort,Sort)]) -> 
                     System
quintupleToSystem (sorts',axioms,rules, sortsSub, rulesSub) =
              let mkExs (s,exs) = fmap (pair s) exs in
              ((fmap fst sorts', axioms, rules, sortsSub, rulesSub), 
               concat (fmap mkExs sorts'))

parseSortExs :: Parse [(Sort,[Extension])]
parseSortExs = parseList startBasic (separator Comma) parseSortEx

parseSortEx :: Parse (Sort,[Extension])
parseSortEx = parseIdAsSort >>= \s ->
              parseExtensions >>= \exts ->
              return (s,exts)

parseSorts :: Parse [Sort]
parseSorts = parseList startBasic (separator Comma) parseIdAsSort


parseExtensions :: Parse [Extension]
parseExtensions = parseList0 (separator Arrow) parseExtension

parseExtension :: Parse Extension
parseExtension = eatIdent "name of extension" >>= \exs ->
                 let errMess = pErr "Expected name of extension" in
                 case exs of
                 -- Extension: Records:
                 "records" -> return Records
                 -- End Extension: Records:
                 otherwise -> errMess

parseAxioms :: Parse [(Sort,Sort)]
parseAxioms = parseList startBasic (separator Comma) parseAxiom 

parseAxiom :: Parse (Sort,Sort)
parseAxiom = parseIdAsSort >>= \s1 ->
             eat Colon "" >>
             parseIdAsSort >>= \s2 ->
             return (s1,s2)
                
parseRules :: Parse [(Sort,Sort,Sort)]
parseRules = parseList startBasic (separator Comma) parseRule

parseRule :: Parse (Sort,Sort,Sort)
parseRule = eat LeftP "" >>
            parseIdAsSort >>= \s1 ->
            eat Comma "" >>
            parseIdAsSort >>= \s2 ->
            startsWith RightP >>= \b ->
            if b then
               nextToken >>
               return (s1,s2,s2)
            else
               eat Comma "" >>
               parseIdAsSort >>= \s3 ->
               eat RightP "" >>
               return (s1,s2,s3)


