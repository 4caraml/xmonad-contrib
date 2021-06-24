{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}

module XMonad.Layout.ResizableMultiColumns
  ( IncColN(..)
  , ResizeAt(..)
  , rmc
  ) where

import           Control.Monad
import           Data.Ratio
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as M
import           XMonad
import           XMonad.Layout.ResizableTile (MirrorResize(..))
import qualified XMonad.StackSet as W
import           XMonad.Util.Types

type Grid = IntMap (Rational, IntMap Rational)

data RMC a = RMC
  { cdef  :: !Rational
  , rdef  :: ![Rational]
  , delta :: !Rational
  , keep  :: !Int
  , grid  :: !Grid
  } deriving (Show, Read)

toList :: Grid -> [(Rational, [Rational])]
toList = map (fmap (map snd . M.toList). snd) . M.toList

fromList :: [(Rational, [Rational])] -> Grid
fromList = M.fromList
  . zipWith (\k (c,rs) -> (k, (c, M.fromList $ zip [0..] rs))) [0..]

rmc :: Rational -> [Rational] -> Rational -> Int -> [(Rational, [Rational])]
    -> RMC a
rmc c r d k = RMC c r d k . fromList

data IncColN = IncColN !Int deriving Typeable
instance Message IncColN

data ResizeAt = Resize :@ Direction2D deriving Typeable
instance Message ResizeAt

deriving instance Eq Resize
deriving instance Eq MirrorResize


fi :: (Integral a, Num b) => a -> b
fi = fromIntegral

takes :: Int -> [[a]] -> [[a]]
takes _ [] = []
takes 0 _  = []
takes n (xs:xss)
  | n < m     = [take n xs]
  | otherwise = xs : takes (n-m) xss
  where m = length xs

dropEnd :: Int -> IntMap a -> IntMap a
dropEnd 0 xs = xs
dropEnd n xs
  | M.size xs < 2 = xs
  | otherwise = dropEnd (n-1) $ M.deleteMax xs

appendN :: Int -> a -> IntMap a -> IntMap a
appendN n el xs = xs <> M.fromList ys
  where
    s  = M.size xs
    ys = zip [s .. s + n - 1] (repeat el)

modifyAt :: Int -> (a->a) -> IntMap a -> IntMap a
modifyAt i f xs = M.adjust f i xs

-- | pull the @n@th element to the front
raiseFocused :: Int -> [a] -> [a]
raiseFocused i xs = el ++ before ++ after
  where
    (before,rest) = splitAt i xs
    (el,after) = splitAt 1 rest

getStack :: X (Maybe (W.Stack Window))
getStack = gets (W.stack . W.workspace . W.current . windowset)

coords :: RMC a -> Int -> (Int,Int)
coords RMC{..} = go 0
  where
    go i k = case grid M.!? i of
      Just (_, xs) ->
        let m = M.size xs in
          if k < M.size xs then (i, k) else go (i+1) (k-m)
      Nothing -> (i + k `div` r, k `mod` r)

    r = length rdef

cols3 = rmc 1 [1,1,1] (1%100) 3 [(1%2,[1]),(1,[3,1]),(1%4,[1])]

size :: W.Stack a -> Int
size (W.Stack _ ls rs) = 1 + length ls + length rs

numCols :: RMC a -> W.Stack b -> Int
numCols l = succ . fst . coords l . pred . size

focusedCoords :: RMC a -> W.Stack b -> (Int, Int)
focusedCoords l = coords l . length . W.up

withStack :: (W.Stack Window -> b) -> X (Maybe b)
withStack f = fmap f <$> getStack

-- | straight up the same as in XMonad.Layout.ResizableTile
splitV, splitH :: [Rational] -> Int -> Rectangle -> [Rectangle]
splitV [] _ r = [r]
splitV _ n r | n < 2 = [r]
splitV (f:fs) n (Rectangle sx sy sw sh) = Rectangle sx sy sw smallh :
    splitV fs (n-1) (Rectangle sx (sy+fi smallh) sw (sh-smallh))
  where smallh = min sh (floor $ fi (sh `div` fi n) * f)

splitH fs n = map mirrorRect . splitV fs n . mirrorRect

instance LayoutClass RMC a where
  description _ = "ResizableMultiColumns"
  emptyLayout _ _ = pure ([], Nothing)
  doLayout l@RMC{..} r s@(W.Stack f ls rs) =
      pure (wrects, if grid' /= grid then Just l {grid = grid'} else Nothing)
    where
      c = numCols l s
      infGrid = toList grid ++ repeat (cdef, rdef)
      cweights = take c (fst <$> infGrid)
      crects = splitH cweights c r

      rweightss = takes (size s) (snd <$> infGrid)
      rectss = zipWith (\fs -> splitV fs (length fs)) rweightss crects

      ws = f : reverse ls ++ rs

      wrects = zip ws $ raiseFocused (length ls) (concat rectss)

      grid' | keep < 0  = grid
            | otherwise = fromList $ take (c + keep) infGrid

  handleMessage l@RMC{..} m' = fmap join . withStack $ \s ->
      let
        ij@(i,_) = focusedCoords l s
        maxX = numCols l s
        maxY = length
             $ takes (size s) (map snd (toList grid) ++ repeat rdef) !! i
      in msum
        [ resize ij =<< fromMessage m'
        , resizeG Expand L R fst maxX ij =<< fromMessage m'
        , resizeG MirrorExpand U D snd maxY ij =<< fromMessage m'
        , incColN =<< fromMessage m'
        , incMasterN i =<< fromMessage m'
        ]
    where
      resize (i,j) m =
        let
          sets f k k' = Just l {grid = f k k' grid}
          inc x = min 1 (x + delta)
          dec x = max (1%1000) (x - delta)
          col = sets $ \k k' ->
              modifyAt k  (\(x, ns) -> (inc x, ns))
            . modifyAt k' (\(x, ns) -> (dec x, ns))
          row = sets $ \k k' ->
            modifyAt i (modifyAt k dec . modifyAt k' inc <$>)
        in case m of
          Expand :@ U -> row j (j-1)
          Expand :@ L -> col i (i-1)
          Expand :@ D -> row j (j+1)
          Expand :@ R -> col i (i+1)
          Shrink :@ U -> row (j-1) j
          Shrink :@ L -> col (i-1) i
          Shrink :@ D -> row (j+1) j
          Shrink :@ R -> col (i+1) i

      -- non-directional expand/shrink behave different at edge
      resizeG expand bwd fwd proj bd ij x
        | x == expand
        , proj ij == bd - 1 = resize ij (Shrink :@ bwd)
        | x == expand       = resize ij (Expand :@ fwd)
        | proj ij == 0 = resize ij (Shrink :@ fwd)
        | otherwise    = resize ij (Expand :@ bwd)

      incColN (IncColN n)
        | n < 0 = Just l {grid = dropEnd (-n) grid}
        | 0 < n = Just l {grid = appendN n (cdef, M.fromList (zip [0..] rdef)) grid}
        | otherwise = Nothing

      incMasterN i (IncMasterN n) =
        if | n < 0 -> Just l {grid = modifyAt i (dropEnd (-n) <$>) grid}
           | 0 < n -> Just l {grid = modifyAt i (appendN n 1 <$>) grid}
           | otherwise -> Nothing
