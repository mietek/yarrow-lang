-- File: Service
-- Description: groups together all modules that form the service routines.

module Service(module Scanner,
               module Printer,
               module Parser,
               module MainPri,
               module ProvPri,
               module Command,
               module ProvPar,
               module MainPar,
               module Errors,
               module HText) where

import Scanner
import Printer
import Parser
import MainPri
import ProvPri
import Command
import ProvPar
import MainPar
import Errors
import HText
