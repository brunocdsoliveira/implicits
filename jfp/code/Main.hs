module Main where

import Parser
import Syntax
import TypeCheck

import qualified SystemF as F

import System.Environment

topLevel :: String -> IO ()
topLevel p =
 let t  = parseTerm p in
 let mct = checkTerm t in
 do section "Parsed Term" t
    case mct of
      Left msg 
        -> putStrLn msg
      Right ((ct, f), msgs)
        -> do mapM_ putStrLn msgs
              section "Checked Type" ct
              section "System F Elaboration" f
              section "System F Evaluation" (F.eval f)
              case F.checkTerm f of
                Left msg -> putStrLn msg
                Right ty -> do section "System F Checked Type" ty
                               section "Type Sanity Check" (elabCT ct == ty)
 
mainInteractive :: IO ()
mainInteractive
 = do putStr "> "
      getLine >>= topLevel
      mainInteractive

main :: IO ()
main 
  = do [file] <- getArgs
       readFile file >>= topLevel
  


section :: Show a => String -> a -> IO ()
section title x
  = do putStrLn "================================================================================"
       putStrLn title
       putStrLn "--------------------------------------------------------------------------------"
       print x
