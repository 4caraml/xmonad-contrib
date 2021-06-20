{-# LANGUAGE ExistentialQuantification, FlexibleContexts, FlexibleInstances,
             LambdaCase, MultiParamTypeClasses, MultiWayIf,
             NoMonomorphismRestriction, RecordWildCards, TupleSections #-}

module XMonad.Layout.ResizableMultiColumns
  ( ncolumns
  , DMsg(..), ModNCol(..)
  ) where

import           Data.Functor
import           Data.List
import           Control.Monad
import           Data.Ratio
import           XMonad
import qualified XMonad.StackSet as W
import           XMonad.Util.Types


-- TODO: remove
notify :: Show a => a -> X ()
notify x = spawn $ "notify-send '" ++ show x ++ "'"

-- | invariants that should hold @length nums == length widths@,
-- @0 < length nums@ and @sum widths == 1@
data NColumns a = NColumns
  { nums   :: ![Int]
  , widths :: ![Ratio Int]
  , delta  :: !(Ratio Int)
  } deriving (Show, Read)

ncolumns = NColumns [1] [1] (1%100)

data DMsg = DMsg deriving Typeable
instance Message DMsg

data ModNCol = ModNCol !Int deriving Typeable
instance Message ModNCol

data DResize = ExpandL | ExpandR | ShrinkL | ShrinkR
  deriving Typeable
instance Message DResize

instance LayoutClass NColumns a where
  description NColumns{..} = "NColumns " ++ show (length nums)
  emptyLayout l _ = pure ([], Nothing)
  pureLayout NColumns{..} r (W.Stack focus lefts rights) =
      zip ws $ raiseFocused (length lefts) rects
    where
      rects = map (trans r) . concat $ zipWith3 mkRects actualWidths xdims ydimss
      mkRects w x = map (\(y,h) -> (x, y, w, h))

      xdims = scanl' (+) 0 actualWidths
      -- in case the layout doesn't provide enough columns, we split the last one
      actualWidths
        | length actualNums == length widths = widths
        | otherwise = chopLast 2 widths

      ydimss = map (\n -> [(i % n, 1 % n) | i <- [0..n-1]]) actualNums
      actualNums = distribute len nums

      ws  = focus : reverse lefts ++ rights

      len = length ws

  handleMessage l@NColumns{..} m = fmap join . sequence $ msum
      [ resize <$> fromMessage m
      , resizeCompat <$> fromMessage m
      , modNCol <$> fromMessage m
      , incMasterN <$> fromMessage m
      , debug <$> fromMessage m
      ]
    where
      resize = withFocusedColumn l . resize'

      resizeCompat m = withFocusedColumn l $ \i -> case m of
        Expand
          | i == length widths - 1 -> resize' ShrinkL i
          | otherwise -> resize' ExpandR i
        Shrink
          | i == 0 -> resize' ShrinkR i
          | otherwise -> resize' ExpandL i

      resize' m i = case m of
        ExpandL -> adjustAt i (i-1) l
        ExpandR -> adjustAt i (i+1) l
        ShrinkL -> adjustAt (i-1) i l
        ShrinkR -> adjustAt (i+1) i l

      modNCol (ModNCol n)
        | n < 0 = pure $ Just l {nums = consumeEnd n nums, widths = consumeEnd n widths}
        | 0 < n = pure $ Just l {nums = nums ++ replicate n 1, widths = chopLast (n+1) widths}
        | otherwise = pure Nothing

      incMasterN (IncMasterN n) = withFocusedColumn l $ \i ->
        Just l {nums = modifyAt i (\m -> max 1 (n+m)) nums}

      debug DMsg = do
        i <- withFocusedColumn l Just
        Nothing <$ notify (show (l,i))

-- | increment at first and decrement at second index
adjustAt :: Int -> Int -> NColumns a -> Maybe (NColumns a)
adjustAt i j l@NColumns{..}
  | 0 <= min i j, max i j < length widths = Just
    l {widths = modifyAt i (+delta) $ modifyAt j (subtract delta) widths}
  | otherwise = Nothing

withFocusedColumn :: NColumns a -> (Int -> Maybe r) -> X (Maybe r)
withFocusedColumn NColumns{..} x =
  gets (W.stack . W.workspace . W.current . windowset) <&> \case
    Just (W.Stack focus lefts rights) -> x $ column (length lefts) nums
    Nothing -> Nothing

-- expects negative @n@
consumeEnd :: Num n => Int -> [n] -> [n]
consumeEnd n xs = before ++ [sum rest] where
  (before, rest) = splitAt (length xs + n - 1) xs

-- | chops last element into @n@ uniform pieces
chopLast :: Int -> [Ratio Int] -> [Ratio Int]
chopLast n xs = init xs ++ replicate n ((1 % n) * last xs)

modifyAt :: Int -> (a -> a) -> [a] -> [a]
modifyAt i f xs = before ++ map f el ++ after
  where
    (before,rest) = splitAt i xs
    (el,after) = splitAt 1 rest

-- | pull the @n@th element to the front
raiseFocused :: Int -> [a] -> [a]
raiseFocused i xs = el ++ before ++ after
  where
    (before,rest) = splitAt i xs
    (el,after) = splitAt 1 rest

-- | figure out which column the @n@th window is at
column = go 0 where
  go i n (w:ws)
    | n < w     = i
    | otherwise = go (i+1) (n-w) ws
  go i _ _ = i

-- | distribute @n@ windows over columns which widths are given by @ms@;
-- left-over windows get appended to a new column
distribute :: Int -> [Int] -> [Int]
distribute n (w:ws)
  | n <= w    = [n]
  | otherwise = w : distribute (n-w) ws
distribute n [] = [n]

-- | fit /[0;1]x[0;1]/ to a given "Rectangle"
trans :: Rectangle -> (Ratio Int, Ratio Int, Ratio Int, Ratio Int) -> Rectangle
trans Rectangle{..} (x,y,w,h) = Rectangle x' y' w' h'
  where
    x' = floor (x * fi rect_width)  + rect_x
    y' = floor (y * fi rect_height) + rect_y
    w' = floor $ w * fi rect_width
    h' = floor $ h * fi rect_height

    fi = fromIntegral
