{-# LANGUAGE TemplateHaskell #-}

module Main where

import Game
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Monoid

subsets :: Ord t => Set t -> [Set t]
subsets s = map Set.fromList (f $ Set.elems s) where
  f [] = [[]]
  f (x : xl) = s ++ map (x :) s where
    s = f xl

games :: [Set Game]
games = map g [0..] where
  g n = flip (Set.\\) low $ Set.fromList $ do
    l <- sets
    r <- sets
    return $ game l r
    where
    low = mconcat $ take n games
    sets = subsets low

printAll :: IO ()
printAll = mapM_ pn [0..] where
  pn n = do
    let gs = Set.elems $ games !! n
    putStrLn $ "birthday "++show n++", games "++show (length gs)
    mapM_ print gs
    putStrLn ""

main = do
  printAll
