-- file: YarMsg.hs
-- description: This file contains the Query and Result datatypes, which
--              will be used for communication between Yarrow and the
--              user-interface.      

module YarMsg(Query(..),Result(..)) where

-- Various datatypes, declared in Yarrow's modules are used here,
-- so they should be imported:
import Basic(Vari,Term,TermIT,GContext,LContext,ContextE,System,Sort,Hnum,
             Error)
import SyntaxI(Assoc(..),SyntaxInfo,BoolOptions)
import MainSta(ModuleName,ModuleInfo,StatusLoad,StatusSave)
import ProvDat(ToProve,GoalNr,TaskId,TacticTerm,ProverCommand,
               TaskExitMode,TacticTree,TacPath)


-- These are the messages that a user-interface can send to Yarrow,
-- to ask Yarrow for specific information:
data Query = 
  -- Commands

  QTactic TaskId TacticTerm |    
  QCommand TaskId ProverCommand |
  QProverExit TaskId TaskExitMode |
  QProveVar (Vari,TermIT) |
                                      
  QLoadModuleInput ModuleName String |
  QContinueLoad StatusLoad |
  QSaveModule ModuleName | 
  QSaveCompleted StatusSave |
  QClearModule |
  QGiveModules |
  QGiveModuleContents ModuleName |

  QDeclareVars ([Vari],TermIT) |
  -- Extension: Subtyping:
  QDeclareVarsSub ([Vari],TermIT) |
  QDeclareVarsSubW ([Vari],TermIT,TermIT) |
  -- End Extension: Subtyping
  QDefVar (Vari,TermIT)| 
  QDefVarW (Vari,TermIT,TermIT) |
  QDelFromVar Vari |

  QSetPrecAndAss (Vari,Int,Assoc) |        
  QSetBinder Vari |        
  QSetLaTeX (Vari,Int) |        
  QSetImplArgs (Vari,Int) |                     
  QSetOptions BoolOptions |
  QSetTypingSystem System |
  QUseFor String Vari |
                                              
  QGiveBReductionPath TaskId (LContext,TermIT) |
  QGiveDReductionPath TaskId (LContext,TermIT) |
  QGiveBDReductionPath TaskId (LContext,TermIT) |
  QCheckBDConv TaskId (LContext,TermIT,TermIT) |
  QCheckTyping TaskId (LContext,TermIT,TermIT) |
  -- Extension: Subtyping:
  QCheckSubtype TaskId (LContext,TermIT,TermIT) |
  -- End Extension: Subtyping  
  QGiveType TaskId (LContext,TermIT) |
  QZMatch TaskId (LContext,[Vari],TermIT,TermIT) |
  QGiveHistory TaskId |

  -- Requests for information
  QGiveGlobCon |
  QGivePossibleImplArgs Vari |
  QGiveSyntaxInfo |
  QGiveTask TaskId |
  QGiveUseFor |

  -- Special for the GUI
  QTerminate

-- These are the messages that contain requested information:
data Result =                                
  RTactic (Hnum,Term) ToProve |        
  RExit [ContextE] (Vari,Term,TacticTree,TaskExitMode) | 
                      -- the new part of the global context and 
                      -- the tactics that yielded the proof, with the name 
                      -- and lemma which was proved.
  RProofTaskId TaskId ToProve |

  RLoadList [ModuleName] |  
  RLoadMessage String StatusLoad |
  RTrySaveThis String StatusSave |
  RModulesAre [ModuleInfo] |
  RModuleContentsIs [ContextE] |

  RGlobConIs GContext | RGlobConExt [ContextE] |

  RPossibleImplArgsAre [Int] |
  RTypingSystemOk String |

  -- For convenience, RReductionPathIs, RCheckIs and RTypeIs also return
  -- the 'superlocal' context
  RReductionPathIs ([Term],LContext) |
  RCheckIs (Bool,LContext) |
  RTypeIs ((Term,Term,Sort),LContext) |
  RZMatchIs [[(Vari,Term)]] | -- [Subst]
  RHistoryIs ([TacPath],TacticTree) |
  RTaskIs ToProve |                                            
  RUseForIs [(String,Vari,Vari)] | -- tactic, connective, lemma

  RSyntaxInfoIs SyntaxInfo |

  RDone |     
  RError Error
