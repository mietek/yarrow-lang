-- File: Command
-- Description: this module holds the data structure for commands

module Command(Command(..),ConPart(..),ConToFile(..),OutputMode(..)) where

import HaTuple
import General

--import Basic
--import Paths(Path)
--import SyntaxI
--import ProvDat
--import MainSta(OptList,ModuleName)
import Engine

--------------------------------
-- COMMAND STRUCTURE FOR MAIN --
--------------------------------  

data OutputMode = OutAscii | OutLatex | OutJava | OutFrank

data Command = 
-- all commands that are available in both prover and main mode
-- (and do not depend on the context)
                   CSkip | CHelp | CHelpOn String | 
                   CGiveContext OutputMode ConPart [Sort] ConToFile | 
                   CSize |
                   CSetOptions OptList | CGiveOptions |
                   CSetPrecAndAss (Vari,Int,Assoc) |
                   CSetBinder Vari | 
                   CSetImplArgs (Vari,Int) |
                   CSetLaTeX (Vari,Int) |
                   CGiveUseFor |
                   CUseFor String Vari |
                   CProveVar (Vari,TermIT) |
                   CDefVar (Vari,TermIT) |
                   CDefVarW (Vari,TermIT,TermIT) | 
                   CDeclareVars ([Vari],TermIT) |
                   -- Extension: Subtyping:
                   CDeclareVarsSub ([Vari],TermIT) |
                   CDeclareVarsSubW ([Vari],TermIT,TermIT) |
                   -- End Extension: Subtyping

                   CRead String |
                   CGiveTypingSystem |
                   CGiveModules | CLoadModule ModuleName | 
                   CSaveModule ModuleName | CClearModule |
                   CAddPath String | CShowPath |
                   CSetTask TaskId | CGiveTasks |

-- commands that are available in both prover and main mode
-- that depend on the context
                   CGiveBReductionPath TaskId (LContext,TermIT) |
                   CGiveDReductionPath TaskId (LContext,TermIT) |
                   CGiveBDReductionPath TaskId (LContext,TermIT) |
                   CGiveType TaskId (LContext,TermIT) | 
                   CCheckTyping TaskId (LContext,TermIT,TermIT) | 
                   -- Extension: Subtyping:
                   CCheckSubtype TaskId (LContext,TermIT,TermIT) | 
                   -- End Extension: Subtyping
                   CCheckBDConv TaskId (LContext,TermIT,TermIT) |
                   CZMatch TaskId (LContext,[Vari],TermIT,TermIT) |
                   CPrintVar TaskId Vari |
                   CDeduction OutputMode TaskId Vari Int ConToFile |

-- commands only available in the main mode
                   CQuit |
                   CSetTypingSystem System |
                   CDelFromVar Vari |

-- Commands for the prover
                   CTactic TaskId TacticTerm |
                   CProverExit TaskId TaskExitMode |
                   CProverCommand TaskId ProverCommand |
                   CHistory TaskId |
                   CShow TaskId GoalNr |
                                    
-- Commands for testing
                   CZwerver (TermIT,TermIT) |
-- CNoParse is delivered when an unknown command is offered for parsing
                   CNoParse


data ConPart = ConAll |
               ConModule String |
               ConRange (Vari,Vari)

data ConToFile = ConToScreen |
                 ConToFile String