module SourceElaborationMain where

import Data.Maybe (fromJust)

import SrcParser
import SourceElaboration
import SyntaxSource
import CoreElaboration
import SystemFSemantics
import System.Environment
import qualified Data.Map as M

pgm = "(? : forall a b c. {a -> a, b -> b, {a -> b} => b -> c} => a -> b -> c)"

pgm2 = "((\\x : Int. x) : Int -> Int)"

pgm3 = "let u : forall a. a -> a = \\x : a. x in u : Int -> Int"

pgm4 = "let u : forall a. a -> a = \\x : a. x in implicit { u } in ?(Int -> Int)"

pgm5 = "interface Ord a = { ord : a -> a -> Int; eq : a -> a -> Int } " ++
       "let ordIntImpl : Ord Int = Ord { ord = ? (Int -> Int -> Int), " ++
       "eq = ? (Int -> Int -> Int) } : Ord Int in " ++
       "(ord : Ord Int -> Int -> Int -> Int) (ordIntImpl : Ord Int)"

pgm6 = "interface Succ a = { succ : a -> a } " ++
       "let succIntImpl : Succ Int = Succ { succ = ? (Int -> Int) } : Succ Int in " ++
       "(succ : Succ Int -> Int -> Int) (succIntImpl : Succ Int)"

pgm7 = "interface Succ a = { succ : a -> a } " ++
       "let sc : forall a. {Succ a} => a -> a = (succ : Succ a -> a -> a) (? (Succ a)) in " ++
       "let succIntImpl : Succ Int = Succ { succ = \\x : Int. x } : Succ Int in " ++
       "implicit { succIntImpl } in " ++
       "(sc : Int -> Int) 1"

pgm8 = "interface Succ a = { succ : a -> a } " ++
       "let succIntImpl : Succ Int = Succ { succ = \\x : Int. x } : Succ Int in " ++
       "implicit { succIntImpl } in (? (Succ Int))"

main = do
  args <- getArgs
  let pgm3' = fromJust $ srcparse pgm3
  let pgm4' = fromJust $ srcparse pgm4
  let pgm5' = fromJust $ srcparse pgm5
  let pgm6' = fromJust $ srcparse pgm6
  let pgm7' = fromJust $ srcparse pgm7
  let pgm8' = fromJust $ srcparse pgm8
  putStrLn (showPgm pgm3')
  putStrLn (show (translateSrcPgm pgm3') ++ "\n")
  putStrLn (showPgm pgm4')
  putStrLn (show (translateSrcPgm pgm4') ++ "\n")
  putStrLn (showPgm pgm5')
  putStrLn (show (translateSrcPgm pgm5') ++ "\n")
  putStrLn (showPgm pgm6')
  putStrLn (show (translateSrcPgm pgm6') ++ "\n")
  putStrLn (showPgm pgm7')
  putStrLn (show (translateSrcPgm pgm7') ++ "\n")
  let pgm7'' = translateSrcPgm pgm7'
  putStrLn (show (translate pgm7'') ++ "\n")
  putStrLn (showPgm pgm8')
  putStrLn (show (translateSrcPgm pgm8') ++ "\n")
  let pgm8'' = translateSrcPgm pgm8'
  putStrLn (show (translate pgm8'') ++ "\n")
  let (Just pgm8''') = translate pgm8''
  putStrLn (show (evalAll pgm8''') ++ "\n")

