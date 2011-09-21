{-# LANGUAGE TemplateHaskell #-}

module Main where

import Test.Framework
import Game

main =
  defaultMain [
    gameTests ] 
