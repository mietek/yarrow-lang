-- File: Platfor
-- Description: This module contains all info that is platform-dependent.
-- This version is for the Unix binary distribution.

module Platfor(fileHelp,extensSep,dirSep,currentDir,standardPathName,
               getYarrowDir) where

import IO
import System(getEnv)
import HaMonSt
import HaMonIO


getEnvi :: String -> Imp s String
getEnvi s = convertIOtoImp (getEnv s)
                           ("environment variable "++s++" is not set")

getYarrowDir :: Imp s String
getYarrowDir = getEnvi "YARROW"

-- the name of every helpfile is truncated to 8 characters
fileHelp :: String -> String -> String
fileHelp mainDir key = mainDir ++ dirSep ++ "helpdir" ++ dirSep ++ take 8 key

dirSep = "/"
extensSep = "."
parentDir = ".."
currentDir = "."

standardPathName :: String -> String
standardPathName = correctDirSeps

correctDirSeps :: String -> String
correctDirSeps "" = ""
correctDirSeps ('/':s) = dirSep ++ correctDirSeps s
correctDirSeps ('\\':s) = dirSep ++ correctDirSeps s
correctDirSeps ('.':'.':s) = parentDir ++ correctDirSeps s
correctDirSeps ('.':s) = currentDir ++ correctDirSeps s
correctDirSeps (c:s) = c : correctDirSeps s
