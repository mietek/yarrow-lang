-- File: ProvDat
-- Description: This module contains the data-structures for prover-commands,
--              including tactics

module ProvDat(GoalNr, TaskId, noTask, dummyTask,
               Goal, GoalInfo, dummyGoal, initHnum, nextHnum, 
               TacticTree(..), TacPath, Task,
               Goals, ToProve, ExtTermTS, ExtTermIT,
               TacticTerm(..),ProverCommand(..),
               Occurrence(..), TaskExitMode(..), showExitMode
               ) where

import General
import Basic
import Paths
import SyntaxI


type GoalNr = Int

type TaskId = Vari


-- noTask is used in the commands GiveBNormalForm etc. to indicate that
-- the command shouldn't use any local context.
noTask :: TaskId
noTask = ""

-- dummyTask is used only by the graphical user interface               
dummyTask :: TaskId
dummyTask = " "

-----------------------------------------------------
--  S T A T E   I N   T H E   P R O O F - M O D E  --
-----------------------------------------------------
                                     
-- A goal is a type in some local context, with some additional info
type Goal = (Term,LContext,GoalInfo)                                
                
-- currently, the GoalInfo is a list of booleans that says whether the
-- corresponding element in the local context should be shown
type GoalInfo = [Bool]
                 
-- dummyGoal is only used by the graphical user interface  
dummyGoal :: Goal
dummyGoal = (dummyTerm,emptyLCon,undefined)

-- Each hole has a unique identification (called Hnum).
-- This type is already defined in module 'basic'
-- data Hnum = N Int


initHnum :: Hnum    
initHnum = N 1                

nextHnum :: Hnum->Hnum
nextHnum (N n) = N (n+1)                

-- All tactics that have been performed in a task are stored in a TacticTree
-- There is a direct correspondence between the 
-- Apart from the tactic itself and its sons, also the following things are
-- stored:
-- 1) The goal to which this tactic was applied
-- 2) The hole-number of this goal
-- 3) The proof-term delivered by this tactic delivered, its 
-- An incomplete TacticTree has also holes, in which only the hole-number
-- and the goal are stored
data TacticTree = TTTac TacticTerm (Hnum,Goal,Term) [TacticTree] |
                  TTHole (Hnum,Goal)

-- We refer to subtrees of a tacticTree with a TacPath
type TacPath = [Int]

-- Finally, the additional state in the prove-mode                           
-- The item holds the name of the lemma, the lemma itself, and its type.
-- Invariant: the tacPaths points once to each TTHole in the tacicTree
type Task = (Item,TacticTree,[TacPath],Hnum)

-- For communication to the User Interface, the following two definitions are
-- useful:

-- The association-list Goals binds a goal to each hole-identification.
type Goals = [(Hnum,Goal)]

-- ToProve contains the proof-term (with holes) and the goals (the type
-- of each hole)
type ToProve = (Term,Goals)


-- many tactics have a so-called 'extended term' as argument.
-- ExtTermTS is the type of well-typed extended terms.
type ExtTermTS = ((Term,Term,Sort),[(Term,Term,Sort)])


                         



-----------------------
-- COMMAND STRUCTURE --
-----------------------
                    
-- used to designate certain subterms in a term
data Occurrence = NumOccurrence Int | PathOccurrence TermPath
 
data TaskExitMode = Exit | Abort

showExitMode Exit = "Exit"
showExitMode Abort = "Abort"

data TacticTerm  = TIntro | TIntroVar [Vari] | TIntros | TIntrosNum Int |
                   TAssumption |
                   TLet Vari TermIT | TLetW Vari TermIT TermIT |
                   TSimplify | TUnfold ([Occurrence],Vari) | 
                   TUnfoldIn ([Occurrence],Vari,Vari) | 
                   TConvert TermIT |
                   TCut TermIT | TFirst TermIT | TForward ExtTermIT |
                   TExact TermIT | TApply ExtTermIT | 
                   TPattern ([Occurrence],TermIT) |
                   TRewrite (Occurrence,ExtTermIT) | 
                   TLewrite (Occurrence,ExtTermIT) |
                   TRewriteIn (Occurrence,ExtTermIT,Vari) | 
                   TLewriteIn (Occurrence,ExtTermIT,Vari) |
                   TRefl |
                   TAndI | 
                   TAndEL ExtTermIT | TAndER ExtTermIT | TAndE ExtTermIT |
                   TOrIL | TOrIR | TOrE ExtTermIT |
                   TNotI | TNotE ExtTermIT |
                   TFalseE |
                   TExistsI TermIT | TExistsE ExtTermIT |
                   TRepeat TacticTerm |
                   TThen TacticTerm [TacticTerm] |
                   TElse TacticTerm TacticTerm |
                   TTry TacticTerm |

                   THide [Vari] | TUnhide [Vari] | TUnhideAll |
                   TNoParse

type ExtTermIT = (TermIT,[TermIT])
                                                              
data ProverCommand = PUndo Int | PRestart | PFocus GoalNr |
                     PNoParse

