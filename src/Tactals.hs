-- File: Tactals
-- Description: This module defines the tacticals for the 
--   prove-mode of the proof assistant.

module Tactals(Tactic, newHnum,
               idTac, elseTac, tryTac,
               then1Tac, thenTac, thenLastTac, thenTryTac,
               forDoTac, repeatFinTac, forTac, repeatTac) where

import HaMonSt
import Basic
import Collect(removeDoubles)
import Paths(genErrS)
import MainSta
import GenComs
import ProvDat

infixr 5 `thenTac`
infixr 5 `then1Tac`

   
-- A tactic finds a term for a goal, and delivers new goals
-- corresponding to the holes in this term.
-- For convenience, also the total context (which is always the local
-- context concatenated to the global context) is given as parameter.
type Tactic = (Term,LContext,GoalInfo,Context) -> M (Term,Goals)


-------------------------
-- AUXILIARY FUNCTIONS --
-------------------------


-- newHnum delivers a new hole-identification
newHnum :: M Hnum
newHnum = fetchHnumS >>= \gnum->
          setHnumS (nextHnum gnum) >>
          return gnum

                   
----------------------------------------------
--             T A C T I C A L S            --
----------------------------------------------
 
-- A tactical combines tactics to a (more complex) tactic

-- the idTac tactic does nothing
idTac :: Tactic
idTac (goal,locCon,gi,globCon) = 
    newHnum >>= \gnum ->
    return (mkHole gnum,[(gnum,(goal,locCon,gi))])



-- tac1 `elseTac` tac2 executes tac1, if that fails it executes tac2
elseTac :: Tactic -> Tactic -> Tactic
elseTac tac1 tac2 goal = handleS (tac1 goal)
                         (\s -> tac2 goal)
                         return

-- the try tactical tries a tactic, if it is not succesful,
-- it does nothing (not even generate an error)
tryTac :: Tactic -> Tactic
tryTac tac = tac `elseTac` idTac


-- The then1tac tactical tries the first tactic.
-- If that gives an error, it aborts with that error
-- Otherwise it applies the second tactic to the FIRST subgoal generated.
-- If the second tactic delivers an error, the first IS undone
-- ONLY FOR INTERNAL USE, since it crashes if no subgoal is generated
then1Tac :: Tactic -> Tactic -> Tactic
then1Tac tac1 tac2 goal =
     tac1 goal >>= \(proof,(goalNum2,(goal2,locCon2,gi2)):otherGoals) ->
     fetchCon >>= \globCon ->
     let totCon2 = locCon2 `addLocG` globCon in
     tac2 (goal2,locCon2,gi2,totCon2) >>= \(proof2,newGoals2) ->
     let proof' = replace proof (goalNum2,proof2) in
     return (proof',(newGoals2++otherGoals))   -- Note order of new goals !

-- The thenTac tactical tries the first tactic.
-- If that gives an error, it aborts with that error.
-- Otherwise it applies the list of tactics to the subgoals generated 
-- (If there are not enough tactics, the last tactic in the list is repeated)
-- If the second tactic delivers an error, the first IS undone
-- In other words:
-- tac1 `thenTac` tac2  is the same as  try tac1 `forall` tac2
thenTac :: Tactic -> [Tactic] -> Tactic
thenTac tac1 tacs =
    let makeTactics n = if n>= length tacs then 
                           tacs ++ replicate (n - length tacs) (last tacs)
                        else
                           take n tacs in
    thenFunTac tac1 makeTactics

-- The thenTac tactical tries the first tactic.
-- If that gives an error, it aborts with that error.
-- Otherwise it applies 'makeTac' to the number of subgoals generated,
-- expecting a list of tactics of the same length.
-- Then it applies this list of tactics to the subgoals generated 
-- If the second tactic delivers an error, the first IS undone
-- In other words:
-- tac1 `thenFunTac` tac2  is the same as  try tac1 `forall` tac2
thenFunTac :: Tactic -> (Int -> [Tactic]) -> Tactic
thenFunTac tac1 makeTacs goal =
    tac1 goal >>= \(proof,newGoals) ->
    fetchCon >>= \globCon ->
    let tacs = makeTacs (length newGoals) in
    let doList proof newGoals restTacs otherGoals =
           if null newGoals then
               return (proof,otherGoals)
           else
           let (goalNum2,(goal2,locCon2,gi2)) = head newGoals
               totCon2 = locCon2 `addLocG` globCon in
           (head restTacs) (goal2,locCon2,gi2,totCon2) 
                                              >>= \(proof2,newGoals2) ->
           let proof' = replace proof (goalNum2,proof2) in
           doList proof' (tail newGoals) (tail restTacs)
                  (otherGoals++newGoals2) in
    doList proof newGoals tacs []

-- The thenLastTac tactical tries the first tactic.
-- If that gives an error, it aborts with that error.
-- Otherwise it applies the second tactic to the last subgoals generated
-- If the second tactic delivers an error, the first IS undone
thenLastTac :: Tactic -> Tactic -> Tactic
thenLastTac tac1 tac2 =
    let makeTactics n = replicate (n-1) idTac ++ [tac2] in
    thenFunTac tac1 makeTactics

thenTryTac :: Tactic -> Tactic -> Tactic
thenTryTac tac1 tac2 = tac1 `thenTac` [tryTac tac2] 


-- forDoTac n  repeats a tactic until it fails, with a maximum of n times.
forDoTac :: Int -> Tactic -> Tactic
forDoTac 1 t = t
forDoTac n t | n>1=  t `thenTryTac` forDoTac (n-1) t
forDoTac _ _ = \_ -> genErrS "At least one repetition"

repeatFinTac = forDoTac 10

-- forTac n  repeats a tactic n times
forTac :: Int -> Tactic -> Tactic
forTac 1 t = t
forTac n t | n>1=  t `thenTac` [forTac (n-1) t]
forTac _ _ = \_ -> genErrS "At least one repetition"


-- repeatTac  repeats a tactic until it fails, only for internal use,
-- since for some tactics this may never end.
repeatTac :: Tactic -> Tactic
repeatTac t =  t `thenTryTac` repeatTac t
 
