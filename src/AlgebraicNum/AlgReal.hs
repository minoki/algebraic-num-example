module AlgebraicNum.AlgReal where
import AlgebraicNum.UniPoly
import AlgebraicNum.Interval
import AlgebraicNum.CReal
import qualified Data.Vector as V
import Data.List

data ExtReal a = NegativeInfinity
               | Finite !a
               | PositiveInfinity
               deriving (Eq,Ord,Show)

clamp :: (Ord a) => a -> a -> ExtReal a -> a
clamp lb _ NegativeInfinity = lb
clamp lb ub (Finite x) | x < lb = lb
                       | ub < x = ub
                       | otherwise = x
clamp _ ub PositiveInfinity = ub

-- | 数の符号を 'Int' で返す
sign :: (Ord a, Num a) => a -> Int
sign x = case compare x 0 of
           EQ -> 0; LT -> -1; GT -> 1

-- | 指定した点における多項式の値の符号を返す
signAt :: (Ord a, Num a) => a -> UniPoly a -> Int
signAt x p = sign (valueAt x p)

-- | 指定した点における多項式の値の符号を返す（補完数直線版）
signAtX :: (Ord a, Num a) => ExtReal a -> UniPoly a -> Int
signAtX (Finite x) p = signAt x p
signAtX PositiveInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p)
signAtX NegativeInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p) * (-1)^(degree' p)

-- | Negative polynomial remainder sequence
negativePRS :: (Eq a, Fractional a)
            => UniPoly a -> UniPoly a -> [UniPoly a]
negativePRS f 0 = [f]
negativePRS f g = let r = f `modP` g in f : negativePRS g (-r)

variance :: [Int] -> Int
variance = loop 0
  where
    loop :: Int -> [Int] -> Int
    loop !n [] = n
    loop !n [_] = n
    loop !n (x:xs@(y:ys))
      | x == 0 = loop n xs
      | y == 0 = loop n (x:ys)
      | x * y < 0 = loop (n + 1) xs
      | otherwise = loop n xs

varianceAt :: (Ord a, Num a) => a -> [UniPoly a] -> Int
varianceAt x ys = variance $ map (signAt x) ys

varianceAtX :: (Ord a, Num a) => ExtReal a -> [UniPoly a] -> Int
varianceAtX x ys = variance $ map (signAtX x) ys

countRealRootsBetween :: (Ord a, Fractional a)
                      => a -> a -> UniPoly a -> Int
countRealRootsBetween a b f = varianceAt a s - varianceAt b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenX :: (Ord a, Fractional a)
                       => ExtReal a -> ExtReal a -> UniPoly a -> Int
countRealRootsBetweenX a b f = varianceAtX a s - varianceAtX b s
  where s = negativePRS f (diffP f)

-- s: この代数的実数における f' の符号（正なら区間 (a,b) において f は負から正に変わり、負なら区間 (a,b) において f は正から負に変わる）
intervalsWithSign
  :: UniPoly Rational -> Int -> Rational -> Rational -> [Interval Rational]
intervalsWithSign !f !s !a !b = Iv a b : ivs a b
  where
    ivs !a !b | signAt c f == 0 = repeat (Iv c c)
              | s * signAt c f < 0 = Iv c b : ivs c b
              | s * signAt c f > 0 = Iv a c : ivs a c
      where c = (a + b) / 2

-- | 代数的実数を表す型
data AlgReal = FromRat !Rational
             | AlgReal !(UniPoly Rational) !Int !Rational !Rational
  deriving (Show)

-- | 定義多項式
definingPolynomial :: AlgReal -> UniPoly Rational
definingPolynomial (FromRat x) = ind - constP x
definingPolynomial (AlgReal p _ _ _) = p

-- | 実根の分離区間
isolatingInterval :: AlgReal -> Interval Rational
isolatingInterval (FromRat x) = Iv (x - 1) (x + 1)
isolatingInterval (AlgReal _ _ x y) = Iv x y

-- | 近似する区間の列
intervals :: AlgReal -> [Interval Rational]
intervals (FromRat x) = repeat (Iv x x)
intervals (AlgReal f s a b) = intervalsWithSign f s a b

-- | 与えられた定義多項式と、分離区間 (a,b] から、代数的実数を構築する。
mkAlgReal :: UniPoly Rational -> Interval Rational -> AlgReal
mkAlgReal f (Iv a b)
  -- 0 の場合は FromRat 0 を使う
  | a < 0 && b >= 0 && valueAt 0 f == 0 = FromRat 0
  -- 区間が空の場合はエラー
  | b <= a = error "mkAlgReal: empty range"
  -- 区間の端点で多項式の値が 0 でないようにする
  | valueAt b' f' == 0 = FromRat b'
  -- 定数項の 0 を取り除き、また、区間の符号が確定したものをデータ構築子として使う
  | otherwise = AlgReal f' s a' b'
  where nonZeroPart (0 : xs) = nonZeroPart xs
        nonZeroPart xs = xs
        f' = fromCoeffAsc $ nonZeroPart (coeffAsc f)
        s | signAt b f' > 0 = 1
          | signAt b f' < 0 = -1
          | otherwise = signAt b (diffP f')
        Just (Iv a' b') = find (\(Iv x y) -> 0 < x || y < 0) (intervalsWithSign f' s a b)

rootBound :: (Ord a, Fractional a) => UniPoly a -> a
rootBound f
  | f == 0 = error "rootBound: polynomial is zero"
  | otherwise = 1 + maximum (map (abs . (/ lc)) $ tail $ coeffDesc f)
  where lc = leadingCoefficient f

realRoots :: UniPoly Rational -> [AlgReal]
realRoots f = realRootsBetween f NegativeInfinity PositiveInfinity

realRootsBetween
  :: UniPoly Rational -> ExtReal Rational -> ExtReal Rational -> [AlgReal]
realRootsBetween f lb ub
  | f == 0 = error "realRoots: zero" -- 多項式 0 の実根を求めようとするのはエラー
  | degree' f == 0 = []  -- 多項式が 0 でない定数の場合、実根はない
  | otherwise = bisect (lb',varianceAtX lb seq) (ub',varianceAtX ub seq)
  where
    f' = squareFree f               -- 無平方多項式に直す
    seq = negativePRS f' (diffP f') -- f' のスツルム列
    bound = rootBound f'            -- 根の限界
    lb' = clamp (-bound) bound lb   -- 与えられた区間の下界（有限）
    ub' = clamp (-bound) bound ub   -- 与えられた区間の上界（有限）

    -- 実装のキモ：与えられた区間の実根を列挙する。区間の端点におけるスツルム列の符号の変化も受け取る。
    bisect :: (Rational,Int) -> (Rational,Int) -> [AlgReal]
    bisect p@(a,i) q@(b,j)
      | i <= j     = []  -- 区間に実根が存在しない場合
      | i == j + 1 = [mkAlgReal f (Iv a b)] -- 区間にちょうど一個の実根が存在する場合
      | otherwise  = bisect p r ++ bisect r q -- それ以外：複数個の実根が存在するので区間を分割する
      where c = (a + b) / 2
            r = (c,varianceAt c seq)

instance Eq AlgReal where
  -- 有理数同士は普通に比較
  FromRat x == FromRat y = x == y

  -- 有理数と代数的実数。後者が有理数である可能性は排除されていないので、愚直にチェックする。
  FromRat x == y
    | x <= a || b <= x = False      -- 区間の中にない場合
    | otherwise = valueAt x f == 0  -- 定義多項式に代入して0になれば等しい
    where f = definingPolynomial y
          Iv a b = isolatingInterval y
  x == y@(FromRat _) = y == x

  -- 代数的実数同士。持っている多項式が最小多項式とは限らないので、GCDを計算してそれが指定した区間に根を持っているか調べる。
  x == y
    | b  <= a' = False  -- 区間が重なっていない場合1
    | b' <= a  = False  -- 区間が重なっていない場合2
    | otherwise = countRealRootsBetween a'' b'' g == 1
    where f = definingPolynomial x
          Iv a b = isolatingInterval x
          f' = definingPolynomial y
          Iv a' b' = isolatingInterval y
          g = gcdP f f'
          a'' = max a a'
          b'' = min b b'

instance Ord AlgReal where
  -- 有理数同士の比較
  compare (FromRat x) (FromRat y) = compare x y

  -- 有理数と代数的実数の比較
  compare (FromRat x) y
    | x <= a = LT
    | b <= x = GT
    | countRealRootsBetween x b f == 1 = LT
    | valueAt x f == 0 = EQ
    | otherwise = GT
    where f = definingPolynomial y
          Iv a b = isolatingInterval y
  compare x y@(FromRat _) = compare EQ (compare y x)

  -- 代数的実数同士の比較
  compare x y
    | b  <= a' = LT -- 区間が重なっていない場合1（y の方が大きい）
    | b' <= a  = GT -- 区間が重なっていない場合2（x の方が大きい）
    | countRealRootsBetween a'' b'' g == 1 = EQ -- 等しいかどうか？
    -- x と y が等しくないことが確定した場合、計算可能実数として比較する
    | otherwise = unsafeCompareCReal (algRealToCReal x)
                                     (algRealToCReal y)
    where f = definingPolynomial x        -- x の定義多項式
          Iv a b = isolatingInterval x    -- x の区間
          f' = definingPolynomial y       -- y の定義多項式
          Iv a' b' = isolatingInterval y  -- y の区間
          g = gcdP f f'
          a'' = max a a'  -- x の区間と y の区間の共通部分の、下限
          b'' = min b b'  -- 同、上限

algRealToCReal :: AlgReal -> CReal
algRealToCReal x = CReal (intervals x)
