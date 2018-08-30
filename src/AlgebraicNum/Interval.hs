module AlgebraicNum.Interval where

-- 区間 [a,b] を表すデータ型
data Interval a = Iv !a !a deriving (Show)

-- 区間の幅を返す
width :: (Num a) => Interval a -> a
width (Iv a b) = b - a

-- 区間に対する max
maxInterval :: (Ord a) => Interval a -> Interval a -> Interval a
maxInterval (Iv a b) (Iv a' b') = Iv (max a a') (max b b')

-- 区間に対する min
minInterval :: (Ord a) => Interval a -> Interval a -> Interval a
minInterval (Iv a b) (Iv a' b') = Iv (min a a') (min b b')

-- 2つの区間の共通部分
intersectionInterval :: (Ord a) => Interval a -> Interval a -> Interval a
intersectionInterval (Iv a b) (Iv a' b') = Iv (max a a') (min b b')

-- 2つの区間が重なっているか判定する
compatible :: (Ord a) => Interval a -> Interval a -> Bool
compatible (Iv a b) (Iv a' b') = a <= b' && a' <= b

-- 区間が0を含むか判定する
isCompatibleWithZero :: (Num a, Ord a) => Interval a -> Bool
isCompatibleWithZero (Iv a b) = a <= 0 && 0 <= b

instance (Num a, Ord a) => Num (Interval a) where
  negate (Iv a b) = Iv (-b) (-a)
  Iv a b + Iv c d = Iv (a + c) (b + d)
  Iv a b - Iv c d = Iv (a - d) (b - c)
  Iv a b * Iv c d = Iv (minimum [a*c,a*d,b*c,b*d])
                       (maximum [a*c,a*d,b*c,b*d])
  abs x@(Iv a b) | 0 <= a = x
                 | b <= 0 = -x
                 | otherwise = Iv 0 (max (-a) b)
  signum (Iv a b) | 0 < a            = 1         -- 正の場合
                  | b < 0            = -1        -- 負の場合
                  | a == 0 && b == 0 = 0         -- 0 の場合
                  | 0 <= a           = Iv 0 1    -- 非負の場合
                  | b <= 0           = Iv (-1) 0 -- 非正の場合
                  | otherwise        = Iv (-1) 1 -- 符号不明の場合
  fromInteger n = Iv (fromInteger n) (fromInteger n)

instance (Fractional a, Ord a) => Fractional (Interval a) where
  recip (Iv a b) | 0 < a || b < 0 = Iv (recip b) (recip a)
                 | otherwise = error "divide by zero"
  fromRational x = Iv (fromRational x) (fromRational x)

-- 区間を比較する
maybeCompareInterval
  :: (Ord a) => Interval a -> Interval a -> Maybe Ordering
maybeCompareInterval (Iv a b) (Iv c d)
  | b < c = Just LT
  | d < a = Just GT
  | a == d && b == c = Just EQ
  -- b <= c = LE
  -- d <= a = GE
  | otherwise = Nothing
