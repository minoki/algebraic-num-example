module AlgebraicNum.Factor.Kronecker where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly
import Data.List (inits)
import Data.Maybe (listToMaybe,maybeToList)
import Data.Ratio
import Control.Monad (sequence,guard)

-- | ラグランジュ補間
lagrangePoly :: (Eq a, Fractional a) => [(a,a)] -> UniPoly a
lagrangePoly [] = 0
lagrangePoly s = loop [] s 0
  where
    loop _ [] m = m
    loop ss (t@(x,y):ts) m = loop (t:ss) ts
      $ m + scaleP y (product [ scaleP (recip (x - x')) (ind - constP x')
                              | x' <- map fst ss ++ map fst ts ])

-- | 有理数の分母が 1 の場合に整数 ('Integer') として返す
ratToInt :: Rational -> Maybe Integer
ratToInt x | denominator x == 1 = Just (numerator x)
           | otherwise = Nothing

-- | 有理数係数多項式の係数の分母がすべて 1 の場合に、整数係数多項式として返す
ratPolyToIntPoly :: UniPoly Rational -> Maybe (UniPoly Integer)
ratPolyToIntPoly f = fromCoeffAsc <$> mapM ratToInt (coeffAsc f)

-- | 整数係数の範囲でラグランジュ補間多項式を計算する
lagrangePolyI :: [(Integer,Integer)] -> Maybe (UniPoly Integer)
lagrangePolyI [] = Nothing
lagrangePolyI ts = ratPolyToIntPoly $ lagrangePoly
  $ map (\(x,y) -> (fromInteger x, fromInteger y)) ts

-- | 整数 n の全ての約数をリストとして返す
intDivisors :: Integer -> [Integer]
intDivisors 0 = error "intDivisors: zero"
intDivisors n | n < 0 = intDivisors (-n)
intDivisors n = loop 1 []
  where
    loop !i xs
      | i*i > n = xs
      | i*i == n = i : (-i) : xs
      | (q,0) <- divMod n i = i : (-i) : loop (i+1) (q : (-q) : xs)
      | otherwise = loop (i+1) xs

-- | Kronecker の方法で、整数係数多項式の自明でない因数を探す
oneFactor :: Int                      -- ^ 探すべき因数の次数の下限
          -> UniPoly Integer          -- ^ 因数を探す多項式
          -> Maybe (UniPoly Integer)  -- ^ 非自明な因数
oneFactor !_ 0 = Nothing
oneFactor !d f
  | n == 0 = Nothing
  | n == 1 = Nothing -- already irreducible
  | otherwise = listToMaybe $ do
      -- リストモナドを使い、非決定的計算っぽく書く

      -- nz は f(k) /= 0 となるような (k,f(k)) のリストである
      let nz = [(k,v) | k <- [0..], let v = valueAt k f, v /= 0]

      -- nz' は [[(k0,d) | d は f(k0) の約数],[(k1,d) | d は f(k1) の約数],..] の形のリストである
      let nz' = [[(x,d) | d <- intDivisors y] | (x,y) <- nz]

      -- inits によって、 nz' の先頭のいくつかを取り出したリストが得られる
      -- 非自明な因数が存在するなら n を f の次数として n/2 次以下のはずである
      -- d-1 次以下の因数は全て掃き出したという前提なので、補間によって d 次以上の多項式を作りたい
      -- 補間によって m 次 (d <= m <= n/2) の多項式を作りたい
      (m,ev) <- zip [d..] $ drop (d + 1) $ take (n `div` 2 + 2) $ inits nz'
      -- ここで length ev == m+1, d <= m <= n/2 が成り立つ

      -- 各 f(ki) について、その約数の組み合わせを全て試す
      ev' <- sequence ev
      -- ここでも length ev' == m+1 が成り立つ
      -- ev' は [(k0,d0),(k1,d1),...,(km,dm) | di は f(ki) の約数] の形のリストである

      -- ラグランジュ補間して多項式を得る
      g <- maybeToList (lagrangePolyI ev')

      guard (degree g == Just m) -- 欲しいのは \(m\) 次の多項式である
      guard (f `pseudoModP` g == 0) -- \(g\) が \(f\) を割り切ることを確認する

      -- 最高次の係数を正にして返す
      if leadingCoefficient g < 0
        then return (-g)
        else return g

  where n = degree' f

-- | Kronecker の方法で、整数係数多項式を因数分解する
factorKronecker :: UniPoly Integer -> [UniPoly Integer]
factorKronecker 0 = error "factor: zero"
factorKronecker f = loop 1 f
  where
    loop !d f
      | degree f == Just 0 = [] -- constant
      | otherwise = case oneFactor d f of
                      Just g -> g : loop (degree' g) (f `divide` g)
                      Nothing -> [f]
