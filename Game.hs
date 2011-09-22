{-# LANGUAGE PatternGuards, TemplateHaskell #-}
-- | Combinatorial Games

module Game 
  ( Game(..)
  , PartialOrd(..)
  , Dyadic, half
  , isnumber, number, unnumber
  , sections, leftSection, rightSection
  , zero, star, up, down
  , gameTests
  ) where

import Data.List
import Data.Ratio
import Data.Bits hiding (shift)
import Test.QuickCheck hiding ((.&.))
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Util

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
  show x | Just n <- unnumber x = show n
  show x | x == star = "*"
  show (Game l r) = "{" ++ s l ++ "|" ++ s r ++ "}" where
    s g = intercalate "," $ map show g

-- Dyadic rationals

newtype Dyadic = Dyadic { unDyadic :: Rational }
  deriving (Eq, Ord)

instance Show Dyadic where
  show (Dyadic x) | denominator x == 1 = show (numerator x)
  show (Dyadic x) = show (numerator x) ++ "/" ++ show (denominator x)

instance Num Dyadic where
  Dyadic x + Dyadic y = Dyadic $ x + y
  Dyadic x * Dyadic y = Dyadic $ x * y
  negate (Dyadic x) = Dyadic $ negate x
  fromInteger = Dyadic . fromInteger
  abs (Dyadic x) = Dyadic $ abs x
  signum (Dyadic x) = Dyadic $ signum x

half :: Dyadic -> Dyadic
half (Dyadic x) = Dyadic $ x / 2

instance Arbitrary Dyadic where
  arbitrary = sized g where
    g s = do
      a <- choose (-s,s)
      b <- shiftL 1 =.< choose (0,s)
      return $ Dyadic $ toInteger a % b

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

number :: Dyadic -> Game
number = f . unDyadic where
  f x | denominator x == 1 = fromInteger $ numerator x
  f x = Game [f ((a-1) % b)] [f ((a+1) % b)] where
    a = numerator x
    b = denominator x

isnumber :: Game -> Bool
isnumber (Game ll rr) = all (\l -> all (l <.) rr) ll

-- Either slightly to the left of a number, or slightly to the right
data Side = SLeft | SRight deriving (Eq, Show)
data Section = Section Dyadic Side deriving (Eq, Show)

instance Ord Section where
  Section x SRight <= Section y SLeft = x < y
  Section x _ <= Section y _ = x <= y

sections :: Game -> (Section, Section)
sections (Game l r) = if lv < rv then (Section mv SLeft, Section mv SRight) else (lv,rv) where
  lv = maximum $ Section (-large) SLeft : map rightSection l
  rv = minimum $ Section   large  SLeft : map leftSection r
  mv = between lv rv
  large = 100000

leftSection :: Game -> Section
leftSection g = fst $ sections g

rightSection :: Game -> Section
rightSection g = snd $ sections g

between :: Section -> Section -> Dyadic
between (Section x xs) (Section y ys) = find (shift x xs) (shift y ys - small) where
  small = Dyadic $ 1 % (2 * max (denominator $ unDyadic x) (denominator $ unDyadic y))
  shift n SRight = n + small
  shift n SLeft = n
  -- find the simplest dyadic rational in a closed dyadic rational interval
  find :: Dyadic -> Dyadic -> Dyadic
  find x y = if nx <= ny then fromInteger ns else half $ find (x+x) (y+y) where
    nx = ceiling $ unDyadic x
    ny = floor $ unDyadic y
    ns = if nx >= 0 then nx else if ny <= 0 then ny else 0

unnumber :: Game -> Maybe Dyadic
unnumber x | isnumber x = Just n where Section n _ = leftSection x
unnumber _ = Nothing

-- Simple games

zero = Game [] []
star = Game [zero] [zero]
up = Game [zero] [star]
down = Game [star] [zero]

-- Testing

instance Arbitrary Game where
  arbitrary = sized (g . min 4) where 
    g 0 = return zero
    g n = do
      let children = resize 2 $ listOf $ g (n-1)
      l <- children
      r <- children
      return $ Game l r

prop_equal :: Game -> Bool
prop_equal x = x == x

prop_numberEqual :: Dyadic -> Dyadic -> Bool
prop_numberEqual x y = (x == y) == (number x == number y)

prop_number :: Dyadic -> Bool
prop_number n = Just n == unnumber (number n)

prop_negate :: Game -> Bool
prop_negate x = negate (negate x) == x

prop_plus_commute :: Game -> Game -> Bool
prop_plus_commute x y = x + y == y + x

{- These are currently too slow:
-- prop_plus_assoc :: Game -> Game -> Game -> Bool
-- prop_plus_assoc x y z = debug (x,y,z) $ (x + y) + z == x + (y + z)

-- prop_times_commute :: Game -> Game -> Bool
-- prop_times_commute x y = x * y == y * x

-- prop_times_assoc :: Game -> Game -> Game -> Bool
-- prop_times_assoc x y z = (x * y) * z == x * (y * z)

-- prop_distribute :: Game -> Game -> Game -> Bool
-- prop_distribute x y z = (x + y) * z == x * z + y * z
-}

gameTests = $(testGroupGenerator)
