{-# LANGUAGE TemplateHaskell #-}
-- | Combinatorial Games

module Game 
  ( Game(..)
  , PartialOrd(..)
  , isnumber, unnumber
  , sections, left, right
  , zero, star, up, down
  , gameTests
  ) where

import Data.List
import Data.Ratio
import Data.Bits hiding (shift)
import Test.QuickCheck hiding ((.&.))
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2

data Game = Game [Game] [Game]

-- Comparison operators
-- Game comparison isn't a total order, so we use special operators

infix 4 <., <=., >=., >.

class PartialOrd t where
  (<=.) :: t -> t -> Bool
  (<.) :: t -> t -> Bool
  (>=.) :: t -> t -> Bool
  (>.) :: t -> t -> Bool
  x >=. y = y <=. x
  x <. y = x <=. y && not (y <=. x)
  x >. y = y <. x

instance PartialOrd Game where
  x@(Game xL _) <=. y@(Game _ yR) = not $ any (<=. x) yR || any (y <=.) xL

-- Equality behaves nicely, so use the normal operators

instance Eq Game where
  x == y = x <=. y && y <=. x

-- Display

instance Show Game where
  -- show x | Just n <- unnumber x = show n
  -- show x | x == star = "*"
  show (Game l r) = "{" ++ s l ++ "|" ++ s r ++ "}" where
    s g = intercalate "," $ map show g

-- Numbers

instance Num Game where
  negate (Game xL xR) = Game (map negate xR) (map negate xL)

  x@(Game xL xR) + y@(Game yL yR) = Game (map (x +) yL ++ map (y +) xL)
                                         (map (x +) yR ++ map (y +) xR)

  x@(Game xL xR) * y@(Game yL yR) = Game (p xL yL ++ p xR yR) (p xL yR ++ p xR yL) where
    p xS yS = do
      x' <- xS
      y' <- yS
      return $ x'*y + x*y' - x'*y'
  
  fromInteger n = if n >= 0 then pos n else neg (-n) where
    pos 0 = zero
    pos k = Game [pos (k-1)] []
    neg 0 = zero
    neg k = Game [] [neg (k-1)]

  abs = error "games have no absolute values"
  signum = error "games have no signs"

-- Conversion from games back to numbers

isPowerOfTwo :: (Integral t, Bits t) => t -> Bool
isPowerOfTwo x = (x .&. (x-1)) == 0

number :: Rational -> Game
number x =
  if not $ isPowerOfTwo $ denominator x then
    error $ "number "++show x++" cannot be represented as a short game"
  else f (numerator x) (denominator x) where
    f n 1 = fromInteger n
    f a b = Game [f (quot (a-1) 2) (quot b 2)] [f (quot (a+1) 2) (quot b 2)]

isnumber :: Game -> Bool
isnumber (Game ll rr) = all (\l -> all (l <.) rr) ll

-- Either slightly to the left of a number, or slightly to the right
data Side = SLeft | SRight deriving (Eq, Show)
data Section = Section Rational Side deriving (Eq, Show)

instance Ord Section where
  Section x SRight <= Section y SLeft = x < y
  Section x _ <= Section y _ = x <= y

sections :: Game -> (Section, Section)
sections (Game l r) = if lv < rv then (Section mv SLeft, Section mv SRight) else (lv,rv) where
  lv = maximum $ Section (-large) SLeft : map right l
  rv = minimum $ Section   large  SLeft : map left r
  mv = between lv rv
  large = 100000

left :: Game -> Section
left g = fst $ sections g

right :: Game -> Section
right g = snd $ sections g

between :: Section -> Section -> Rational
between (Section x xs) (Section y ys) = half (shift x xs) (shift y ys) where
  small = 1 % (2 * max (denominator x) (denominator y))
  shift n SRight = n + small
  shift n SLeft = n
  half x y = if c < y then c else half (x+x) (y+y) / 2 where
    c = fromIntegral (ceiling x :: Integer)

unnumber :: Game -> Maybe Rational
unnumber x | isnumber x = Just n where Section n _ = left x
unnumber _ = Nothing

-- Simple games

zero = Game [] []
star = Game [zero] [zero]
up = Game [zero] [star]
down = Game [star] [zero]

-- Testing

instance Arbitrary Game where
  arbitrary = sized g where 
    g 0 = return zero
    g n = do
      let children = resize (n-1) arbitrary
      l <- children
      r <- children
      return $ Game l r

prop_number n = Just n == unnumber (number n)

gameTests = $(testGroupGenerator)
