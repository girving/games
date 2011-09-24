{-# LANGUAGE PatternGuards, TemplateHaskell #-}
-- | Combinatorial Games

module Game 
  ( Game
  , PartialOrd(..)
  , Dyadic, half
  , isnumber, number, unnumber
  , sections, leftSection, rightSection
  , zero, star, up, down
  , gameTests, rawShow
  ) where

import Prelude hiding (any, all, minimum, maximum)
import Data.List hiding (any, all, minimum, maximum)
import Data.Maybe
import Data.Ratio
import Data.Bits hiding (shift)
import Test.QuickCheck hiding ((.&.))
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2
import Util hiding (left, right)
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.MemoCombinators as Memo
import Data.Monoid
import Data.Foldable
import Text.Parsec hiding (between)
import qualified Text.Parsec.Token as P
import Text.ParserCombinators.Parsec.Expr
import Text.Parsec.Language (emptyDef)

-- A form is a possibly unsimplified game, but where all options are simplified

data Form = Form (Set Game) (Set Game)
  deriving (Eq, Ord)

-- In order to avoid exponential complexities, we ensure that games
-- are always stored in simplified form.  As a consequence, equality is simple.
-- We also define Ord, which unfortunately differs from true game comparison
-- since the latter isn't a total order.  Use <=* and the like for real comparison.

newtype Game = Game {unGame :: Form}
  deriving (Eq, Ord)

left :: Game -> Set Game
left (Game (Form l _)) = l

right :: Game -> Set Game
right (Game (Form _ r)) = r

-- Memo combinators for games

class Memoize t where
  memoize :: Memo.Memo t

memoize2 :: (Memoize a, Memoize b) => (a -> b -> r) -> a -> b -> r 
memoize2 = Memo.memo2 memoize memoize

instance Memoize t => Memoize [t] where
  memoize = Memo.list memoize

instance (Ord t, Memoize t) => Memoize (Set t) where
  memoize = Memo.wrap Set.fromList Set.elems memoize

instance (Memoize a, Memoize b) => Memoize (a,b) where
  memoize = Memo.pair memoize memoize

instance Memoize Form where
  memoize = Memo.wrap (\ (l,r) -> Form l r) (\ (Form l r) -> (l,r)) memoize

instance Memoize Game where
  memoize = Memo.wrap Game unGame memoize

-- Comparison operators
-- Game comparison isn't a total order, so we use special operators

infix 4 <*, <=*, >=*, >*

class PartialOrd t where
  (<=*) :: t -> t -> Bool
  (<*) :: t -> t -> Bool
  (>=*) :: t -> t -> Bool
  (>*) :: t -> t -> Bool
  x >=* y = y <=* x
  x <* y = x <=* y && not (y <=* x)
  x >* y = y <* x

instance PartialOrd Form where
  (<=*) = memoize2 le where
    le x@(Form xL _) y@(Form _ yR) = not $ any ((<=* x) . unGame) yR || any ((y <=*) . unGame) xL

instance PartialOrd Game where
  Game x <=* Game y = x <=* y
  x <* y = x <=* y && x /= y

-- Simplification

game :: Set Game -> Set Game -> Game
game l r = Game $ fix $ Form l r where
  fix x = if z == y then y else fix z where
    y = undominate x
    z = reverse y
  undominate (Form l r) = Form (prune (<*) l) (prune (>*) r) where
    prune c xs = Set.filter (\x -> not $ any (c x) xs) xs
  reverse g@(Form l r) = Form (assemble (<=*) right left l) (assemble (>=*) left right r) where
    assemble c r l o = mconcat $ map (\x -> reverse c l x (Set.elems $ r x)) (Set.elems o)
    reverse _ _ o [] = Set.singleton o
    reverse c l o (or : orl) = if c (unGame or) g then l or else reverse c l o orl

-- Display

rawShow :: Game -> String
rawShow x | x == zero = "0"
rawShow x | x == star = "*"
rawShow (Game (Form l r)) = "{" ++ s l ++ "|" ++ s r ++ "}" where
  s g = intercalate "," $ map rawShow (Set.elems g)

instance Show Game where
  show x | Just n <- unnumber x = show n
  show x | x == star = "*"
  show (Game (Form l r)) = "{" ++ s l ++ "|" ++ s r ++ "}" where
    s g = intercalate "," $ map show (Set.elems g)

-- Parsing

instance Read Game where
  readsPrec _ s = [(reads s,"")] where
    reads s = case parse prog "" s of
      Left err -> error $ show err
      Right g -> g
    prog = do { e <- exp; eof; return e }
    exp = buildExpressionParser table term
    table = [[op "+" (+) AssocLeft, op "-" (-) AssocLeft]]
    op s f assoc = Infix (do { _ <- string s; return f }) assoc
    term = do { _ <- symbol "-"; negate =.< term } <|> multiple
    multiple = prim <|> do { n <- decimal; r <- rest; case r of Left m -> number =.< dyadic n m; Right g -> return $ number (fromInteger n) * g }
    rest = do { _ <- symbol "/"; Left =.< decimal } <|> (Right =.< multiple) <|> return (Right 1)
    dyadic a b | isPowerOfTwo b = return $ Dyadic (a % b)
    dyadic a b = fail $ show "invalid fraction "++show a++"/"++show b++"; denominator is not a power of two"
    prim = (star .< symbol "*") <|> form
    form = do { _ <- symbol "{"; l <- commaSep exp; _ <- symbol "|"; r <- commaSep exp; _ <- symbol "}"; return $ game (Set.fromList l) (Set.fromList r) }
    -- Token parsing
    lexer = P.makeTokenParser emptyDef -- Can't use haskellStyle because {-1,1} parses as the start of a comment
    symbol = P.symbol lexer
    decimal = P.decimal lexer
    commaSep = P.commaSep lexer

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
  negate (Game (Form xL xR)) = Game (Form (Set.map negate xR) (Set.map negate xL))

  (+) = memoize2 plus where
    plus x@(Game (Form xL xR)) y@(Game (Form yL yR)) = game (Set.union (Set.map (x +) yL) (Set.map (y +) xL))
                                                            (Set.union (Set.map (x +) yR) (Set.map (y +) xR))

  (*) = memoize2 times where
    times x@(Game (Form xL xR)) y@(Game (Form yL yR)) = game (Set.union (p xL yL) (p xR yR)) (Set.union (p xL yR) (p xR yL)) where
      p xS yS = Set.fromList $ do
        x' <- Set.elems xS
        y' <- Set.elems yS
        return $ x'*y + x*y' - x'*y'
  
  fromInteger n = if n >= 0 then pos n else neg (-n) where
    pos 0 = zero
    pos k = Game $ Form (Set.singleton $ pos (k-1)) Set.empty
    neg 0 = zero
    neg k = Game $ Form Set.empty (Set.singleton $ neg (k-1))

  abs = error "games have no absolute values"
  signum = error "games have no signs"

-- Conversion from games back to numbers

isPowerOfTwo :: (Integral t, Bits t) => t -> Bool
isPowerOfTwo x = (x .&. (x-1)) == 0

number :: Dyadic -> Game
number = f . unDyadic where
  f x | denominator x == 1 = fromInteger $ numerator x
  f x = Game $ Form (Set.singleton $ f ((a-1) % b)) (Set.singleton $ f ((a+1) % b)) where
    a = numerator x
    b = denominator x

isnumber :: Game -> Bool
isnumber = isJust . unnumber

-- Either slightly to the left of a number, or slightly to the right
data Side = SLeft | SRight deriving (Eq, Show)
data Section = Section Dyadic Side deriving (Eq, Show)

instance Ord Section where
  Section x SRight <= Section y SLeft = x < y
  Section x _ <= Section y _ = x <= y

sections :: Game -> (Section, Section)
sections (Game (Form l r)) = if lv < rv then (Section mv SLeft, Section mv SRight) else (lv,rv) where
  lv = maximum $ Section (-large) SLeft : map rightSection (Set.elems l)
  rv = minimum $ Section   large  SLeft : map leftSection  (Set.elems r)
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
unnumber = memoize un where
  un x = case sections x of
    (Section n SLeft, Section n' SRight) | n == n' -> Just n
    _ -> Nothing

-- Simple games

zero = game Set.empty Set.empty
star = game (Set.singleton zero) (Set.singleton zero)
up = game (Set.singleton zero) (Set.singleton star)
down = game (Set.singleton star) (Set.singleton zero)

-- Testing

instance Arbitrary Game where
  arbitrary = sized (g . min 4) where 
    g 0 = return zero
    g n = do
      let children = resize 2 $ listOf $ g (n-1)
      l <- children
      r <- children
      return $ game (Set.fromList l) (Set.fromList r)

prop_reflex :: Game -> Bool
prop_reflex x = x <=* x

prop_numberEqual :: Dyadic -> Dyadic -> Bool
prop_numberEqual x y = (x == y) == (number x == number y)

prop_number :: Dyadic -> Bool
prop_number n = Just n == unnumber (number n)

prop_negate :: Game -> Bool
prop_negate x = negate (negate x) == x

prop_parse :: Game -> Bool
prop_parse g = g == read (show g)

prop_plus_commute :: Game -> Game -> Bool
prop_plus_commute x y = x + y == y + x

prop_plus_assoc :: Game -> Game -> Game -> Bool
prop_plus_assoc x y z = (x + y) + z == x + (y + z)

-- Multiplication is commutative for all games, but way too slow
-- prop_times_commute :: Game -> Game -> Bool
-- prop_times_commute x y = x * y == y * x

-- Multiplication is not associative for general games
-- prop_times_assoc :: Game -> Game -> Game -> Bool
-- prop_times_assoc x y z = (x * y) * z == x * (y * z)

-- Multiplication is not distributive for general games
-- prop_distribute :: Game -> Game -> Game -> Bool
-- prop_distribute x y z = (x + y) * z == x * z + y * z

gameTests = $(testGroupGenerator)
