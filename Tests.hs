{-# LANGUAGE TemplateHaskell #-}

module Main where

import Test.Framework
import Game

main = do
  let g = read "{0|{0|*}}" :: Game
      g' = read "{0|*}" :: Game
  print g
  print $ rawShow g
  print $ isnumber g
  print $ zero <* g'
  defaultMain [
    gameTests ] 
