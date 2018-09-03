module AlgebraicNum.AlgReal where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly
import AlgebraicNum.Interval
import AlgebraicNum.CReal
import AlgebraicNum.Resultant
import AlgebraicNum.Factor.SquareFree
import AlgebraicNum.Factor.Hensel
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Vector as V
import Data.List
import Data.Ratio

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

signAtZQ :: Rational -> UniPoly Integer -> Int
signAtZQ x p = sign (valueAtT fromInteger x p)

isZeroAtZQ :: Rational -> UniPoly Integer -> Bool
isZeroAtZQ x p = valueAtT fromInteger x p == 0

-- | 指定した点における多項式の値の符号を返す（補完数直線版）
signAtX :: (Ord a, Num a) => ExtReal a -> UniPoly a -> Int
signAtX (Finite x) p = signAt x p
signAtX PositiveInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p)
signAtX NegativeInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p) * (-1)^(degree' p)

signAtZQX :: ExtReal Rational -> UniPoly Integer -> Int
signAtZQX (Finite x) p = signAtZQ x p
signAtZQX PositiveInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p)
signAtZQX NegativeInfinity p
  | p == 0 = 0
  | otherwise = sign (leadingCoefficient p) * (-1)^(degree' p)

-- | Negative polynomial remainder sequence using subresultant PRS
--
-- Assumption: 'degree f > degree g'
negativePRS :: (Ord a, IntegralDomain a)
            => UniPoly a -> UniPoly a -> [UniPoly a]
negativePRS f g = f : g : loop 1 f 1 g (subresultantPRS' f g)
  where
    loop !_ _ !_ _ [] = []
    loop !s f !t g ((b,x):xs)
      -- b * (lc g)^(degree f - degree g + 1) * s > 0
      | sign b * (sign lc_g)^(degree' f - degree' g + 1) * s > 0
      = -x : loop t g (-1) x xs
      | otherwise = x : loop t g 1 x xs
      where lc_g = leadingCoefficient g

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

varianceAtZQ :: Rational -> [UniPoly Integer] -> Int
varianceAtZQ x ys = variance $ map (signAtZQ x) ys

varianceAtX :: (Ord a, Num a) => ExtReal a -> [UniPoly a] -> Int
varianceAtX x ys = variance $ map (signAtX x) ys

varianceAtZQX :: ExtReal Rational -> [UniPoly Integer] -> Int
varianceAtZQX x ys = variance $ map (signAtZQX x) ys

countRealRootsBetween :: (Ord a, Fractional a, IntegralDomain a)
                      => a -> a -> UniPoly a -> Int
countRealRootsBetween a b f = varianceAt a s - varianceAt b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenZQ :: Rational -> Rational -> UniPoly Integer -> Int
countRealRootsBetweenZQ a b f = varianceAtZQ a s - varianceAtZQ b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenX :: (Ord a, Fractional a, IntegralDomain a)
                       => ExtReal a -> ExtReal a -> UniPoly a -> Int
countRealRootsBetweenX a b f = varianceAtX a s - varianceAtX b s
  where s = negativePRS f (diffP f)

countRealRootsBetweenZQX :: ExtReal Rational -> ExtReal Rational -> UniPoly Integer -> Int
countRealRootsBetweenZQX a b f = varianceAtZQX a s - varianceAtZQX b s
  where s = negativePRS f (diffP f)

-- s: この代数的実数における f' の符号（正なら区間 (a,b) において f は負から正に変わり、負なら区間 (a,b) において f は正から負に変わる）
intervalsWithSign
  :: UniPoly Integer -> Int -> Rational -> Rational -> [Interval Rational]
intervalsWithSign !f !s !a !b = Iv a b : ivs a b
  where
    ivs !a !b | signAtZQ c f == 0 = repeat (Iv c c)
              | s * signAtZQ c f < 0 = Iv c b : ivs c b
              | s * signAtZQ c f > 0 = Iv a c : ivs a c
      where c = (a + b) / 2

-- | 代数的実数を表す型
data AlgReal = FromRat !Rational
             | AlgReal !(UniPoly Integer) !Int !Rational !Rational
  deriving (Show)

-- 有理数体上代数的な数のクラス
class IsAlgebraic a where
  -- | 定義多項式
  definingPolynomial :: a -> UniPoly Integer

instance IsAlgebraic Integer where
  definingPolynomial x = fromCoeffAsc [- x, 1]
instance (Integral a) => IsAlgebraic (Ratio a) where
  definingPolynomial x = fromCoeffAsc [- numerator x', denominator x']
    where x' = toRational x

instance IsAlgebraic AlgReal where
  definingPolynomial (FromRat x) = definingPolynomial x
  definingPolynomial (AlgReal f _ _ _) = f

-- | 実根の分離区間
isolatingInterval :: AlgReal -> Interval Rational
isolatingInterval (FromRat x) = Iv (x - 1) (x + 1)
isolatingInterval (AlgReal _ _ x y) = Iv x y

-- | 近似する区間の列
intervals :: AlgReal -> [Interval Rational]
intervals (FromRat x) = repeat (Iv x x)
intervals (AlgReal f s a b) = intervalsWithSign f s a b

-- | 与えられた既約多項式と、分離区間 (a,b] から、代数的実数を構築する。
mkAlgRealWithIrreduciblePoly
  :: UniPoly Integer -> Interval Rational -> AlgReal
mkAlgRealWithIrreduciblePoly f (Iv a b)
  -- 区間が空の場合はエラー
  | b < a = error "mkAlgReal: empty range"
  -- 最小多項式が1次の場合は、ただの有理数
  | degree f == Just 1 = case coeffAsc f of
                           [a,b] -> FromRat (-a % b)
  -- 区間の符号が確定したものをデータ構築子として使う
  | otherwise = AlgReal f s a' b'
  where s | signAtZQ b f > 0 = 1
          | signAtZQ b f < 0 = -1
          | otherwise = error "f is not irreducible"
        Just (Iv a' b') = find (not . isCompatibleWithZero)
                               (intervalsWithSign f s a b)

-- | 与えられた多項式と、その根に収束する計算可能実数から、代数的実数を構築する。
mkAlgRealWithCReal :: UniPoly Integer -> CReal -> AlgReal
mkAlgRealWithCReal f (CReal xs) = sieve squareFreeFactors xs
  where
    squareFreeFactors :: [UniPoly Integer]
    squareFreeFactors = map fst $ yunSFF $ primitivePart f

    sieve :: [UniPoly Integer] -> [Interval Rational] -> AlgReal
    sieve [] _ = error "invalid real number"
    sieve [g] xs = sieve2 (unsafePerformIO (factorHenselIO g)) xs
    sieve gs (x:xs) = sieve
      (filter (isCompatibleWithZero . valueAtT fromInteger x) gs) xs

    sieve2 :: [UniPoly Integer] -> [Interval Rational] -> AlgReal
    sieve2 [] _ = error "invalid real number"
    sieve2 [g] xs
      = case dropWhile (\(Iv a b) ->
                           countRealRootsBetweenZQ a b g >= 2) xs of
          iv : _ -> mkAlgRealWithIrreduciblePoly g iv
    sieve2 gs (x:xs) = sieve2
      (filter (isCompatibleWithZero . valueAtT fromInteger x) gs) xs

rootBound :: UniPoly Integer -> Rational
rootBound f
  | f == 0 = error "rootBound: polynomial is zero"
  | otherwise = 1 + maximum (map (abs . (% lc)) $ tail $ coeffDesc f)
  where lc = leadingCoefficient f

realRoots :: UniPoly Integer -> [AlgReal]
realRoots f = map fst (realRootsM f)

realRootsM :: UniPoly Integer -> [(AlgReal,Int)]
realRootsM f = realRootsBetweenM f NegativeInfinity PositiveInfinity

-- 多項式の実根のうち、指定された区間にあるものを、重複度込みで返す
realRootsBetweenM :: UniPoly Integer
                  -> ExtReal Rational -> ExtReal Rational
                  -> [(AlgReal,Int)]
realRootsBetweenM f lb ub
  | f == 0 = error "realRoots: zero" -- 0 の実根を求めようとするのはエラー
  | degree' f == 0 = []  -- 多項式が 0 でない定数の場合、実根はない
  | otherwise = sortOn fst $ do
      (g,i) <- yunSFF (primitivePart f)       -- f を無平方分解する
      h <- unsafePerformIO (factorHenselIO g) -- g を因数分解する
      let seq = negativePRS h (diffP h)  -- h のスツルム列
          bound = rootBound h            -- 根の限界
          lb' = clamp (-bound) bound lb  -- 与えられた区間の下界（有限）
          ub' = clamp (-bound) bound ub  -- 与えられた区間の上界（有限）
      a <- bisect h seq (lb',varianceAtZQX lb seq)
                        (ub',varianceAtZQX ub seq)
      return (a,i)
  where
    -- 実装のキモ：与えられた区間の実根を列挙する
    -- 区間の端点におけるスツルム列の符号の変化を受け取る
    bisect :: UniPoly Integer -> [UniPoly Integer]
           -> (Rational,Int) -> (Rational,Int) -> [AlgReal]
    bisect f seq p@(a,i) q@(b,j)
      | i <= j     = []  -- 区間に実根が存在しない場合
      -- 区間にちょうど一個の実根が存在する場合
      | i == j + 1 = [mkAlgRealWithIrreduciblePoly f (Iv a b)]
      -- それ以外：複数個の実根が存在するので区間を分割する
      | otherwise  = bisect f seq p r ++ bisect f seq r q
      where c = (a + b) / 2
            r = (c,varianceAtZQ c seq)

realRootsBetween :: UniPoly Integer
                 -> ExtReal Rational -> ExtReal Rational
                 -> [AlgReal]
realRootsBetween f lb ub = map fst (realRootsBetweenM f lb ub)

realRootsBetweenQ :: UniPoly Rational -> ExtReal Rational -> ExtReal Rational -> [AlgReal]
realRootsBetweenQ f lb ub
  | f == 0 = error "realRoots: zero"
  | degree' f == 0 = []
  | otherwise = realRootsBetween fz lb ub
  where
    commonDenominator
      = foldl' (\a b -> lcm a (denominator b)) 1 (coeffAsc f)
    fz = primitivePart
         $ mapCoeff (\x -> numerator x * (commonDenominator `div` denominator x)) f

instance Eq AlgReal where
  -- 有理数同士は普通に比較
  FromRat x == FromRat y = x == y

  -- 有理数と代数的実数。後者が有理数である可能性は排除されていないので、愚直にチェックする。
  FromRat x == y
    | x <= a || b <= x = False    -- 区間の中にない場合
    | otherwise = isZeroAtZQ x f  -- 定義多項式に代入して0になれば等しい
    where f = definingPolynomial y
          Iv a b = isolatingInterval y
  x == y@(FromRat _) = y == x

  -- 代数的実数同士。持っている多項式が最小多項式とは限らないので、GCDを計算してそれが指定した区間に根を持っているか調べる。
  x == y
    | b  <= a' = False  -- 区間が重なっていない場合1
    | b' <= a  = False  -- 区間が重なっていない場合2
    | otherwise = countRealRootsBetweenZQ a'' b'' g == 1
    where f = definingPolynomial x
          Iv a b = isolatingInterval x
          f' = definingPolynomial y
          Iv a' b' = isolatingInterval y
          g = gcdD f f'
          a'' = max a a'
          b'' = min b b'

instance Ord AlgReal where
  -- 有理数同士の比較
  compare (FromRat x) (FromRat y) = compare x y

  -- 有理数と代数的実数の比較
  compare (FromRat x) y
    | x <= a = LT
    | b <= x = GT
    | countRealRootsBetweenZQ x b f == 1 = LT
    | isZeroAtZQ x f = EQ
    | otherwise = GT
    where f = definingPolynomial y
          Iv a b = isolatingInterval y
  compare x y@(FromRat _) = compare EQ (compare y x)

  -- 代数的実数同士の比較
  compare x y
    | b  <= a' = LT -- 区間が重なっていない場合1（y の方が大きい）
    | b' <= a  = GT -- 区間が重なっていない場合2（x の方が大きい）
    | countRealRootsBetweenZQ a'' b'' g == 1 = EQ -- 等しいかどうか？
    -- x と y が等しくないことが確定した場合、計算可能実数として比較する
    | otherwise = unsafeCompareCReal (algRealToCReal x)
                                     (algRealToCReal y)
    where f = definingPolynomial x        -- x の定義多項式
          Iv a b = isolatingInterval x    -- x の区間
          f' = definingPolynomial y       -- y の定義多項式
          Iv a' b' = isolatingInterval y  -- y の区間
          g = gcdD f f'
          a'' = max a a'  -- x の区間と y の区間の共通部分の、下限
          b'' = min b b'  -- 同、上限

algRealToCReal :: AlgReal -> CReal
algRealToCReal x = CReal (intervals x)

instance Num AlgReal where
  negate (FromRat x) = FromRat (negate x)
  negate (AlgReal f s a b) = AlgReal (compP f (-ind)) (-s) (-b) (-a)

  FromRat x + FromRat y = FromRat (x + y)
  FromRat k + AlgReal f _ a b
    = mkAlgRealWithIrreduciblePoly (primitivePart $ fst $ homogeneousCompP f (definingPolynomial (FromRat k)) (denominator k)) (Iv (a + k) (b + k))
  x@(AlgReal {}) + y@(FromRat _) = y + x
  x + y = mkAlgRealWithCReal (resultant f_x_y g) (algRealToCReal x + algRealToCReal y)
    where f = mapCoeff constP $ definingPolynomial x
          f_x_y = compP f (constP ind - ind) -- \(f(x-y)\)
          g = mapCoeff constP $ definingPolynomial y

  FromRat x - FromRat y = FromRat (x - y)
  FromRat k - AlgReal f _ a b
    = mkAlgRealWithIrreduciblePoly (primitivePart $ fst $ homogeneousCompP f (- definingPolynomial (FromRat k)) (denominator k)) (Iv (k - b) (k - a))
  AlgReal f _ a b - FromRat k
    = mkAlgRealWithIrreduciblePoly (primitivePart $ fst $ homogeneousCompP f (definingPolynomial (FromRat (-k))) (denominator k)) (Iv (a - k) (b - k))
  x - y = mkAlgRealWithCReal (resultant f_y_x g)
                             (algRealToCReal x - algRealToCReal y)
    where f = mapCoeff constP $ definingPolynomial x
          f_y_x = compP f (constP ind + ind) -- \(f(y+x)\)
          g = mapCoeff constP $ definingPolynomial y

  FromRat x * FromRat y = FromRat (x * y)
  FromRat k * AlgReal f s a b
    | k == 0 = 0
    | k > 0 = AlgReal f_x_k s (a * k) (b * k)
    | k < 0 = AlgReal f_x_k (-s) (b * k) (a * k)
    where
      f_x_k = fst $ homogeneousValueAt (scaleP (denominator k) ind)
              (fromInteger $ numerator k) (mapCoeff fromInteger f) -- \(f(x/k)\)
  x@(AlgReal {}) * y@(FromRat _) = y * x
  x * y = mkAlgRealWithCReal (resultant y_f_x_y g) (algRealToCReal x * algRealToCReal y)
    where f = definingPolynomial x
          y_f_x_y = fromCoeffVectAsc $ V.reverse
                    $ V.imap (\i a -> constP a * ind^i) $ coeffVectAsc f -- \(y^n f(x/y)\)
          g = mapCoeff constP $ definingPolynomial y

  abs x = if x >= 0 then x else negate x
  signum x = case compare x 0 of
               LT -> -1; EQ -> 0; GT -> 1
  fromInteger n = FromRat (fromInteger n)

instance Fractional AlgReal where
  recip (FromRat x) = FromRat (recip x)
  recip (AlgReal f s a b)
    = AlgReal (revPoly f) s' (recip b) (recip a)
    where s' | even (degree' f) || 0 < a = -s
             | otherwise = s
  fromRational = FromRat

sqrtQ :: Rational -> AlgReal
sqrtQ a | a > 0 = case realRootsBetweenQ (ind^2 - constP a)
                                         (Finite 0) PositiveInfinity of
                    [sqrt_a] -> sqrt_a
                    _ -> error "sqrt: none or multiple roots"
        | a == 0 = 0
        | otherwise = error "sqrt: negative"

nthRootQ :: Int -> Rational -> AlgReal
nthRootQ !n !a
  | n == 0 = error "0th root"
  | n < 0  = nthRootQ (-n) (recip a)
  | a > 0  = case realRootsBetweenQ (ind^n - constP a)
                                    (Finite 0) PositiveInfinity of
      [b] -> b
      l -> error ("nthRoot: none or multiple roots " ++ show l)
  | a == 0 = 0
  | odd n  = case realRootsBetweenQ (ind^n - constP a)
                                    NegativeInfinity (Finite 0) of
      [b] -> b
      l -> error ("nthRoot: none or multiple roots " ++ show l)
  | otherwise = error "nthRoot: negative"

sqrtA :: AlgReal -> AlgReal
sqrtA (FromRat x) = sqrtQ x
sqrtA x = case filter (\y -> FromRat a < y^2 && y^2 <= FromRat b)
               $ realRootsBetween (compP f (ind^2))
                                  (Finite 0) PositiveInfinity of
            [sqrtx] -> sqrtx
            r -> error $ "sqrt: none or multiple roots" ++ show r
    where f = definingPolynomial x
          Iv a b = isolatingInterval x

nthRootA :: Int -> AlgReal -> AlgReal
nthRootA !n (FromRat x) = nthRootQ n x
nthRootA !n x
  | n == 0 = error "0th root"
  | n < 0  = nthRootA (-n) (recip x)
  -- now n must be positive
  | x == 0 = 0
  | x > 0  = case filter (\x -> FromRat a < x^n && x^n <= FromRat b)
                  $ realRootsBetween (compP f (ind^n))
                                     (Finite 0) PositiveInfinity of
               [rx] -> rx
               _ -> error "nthRoot: none or multiple roots"
  -- x must be negative
  | odd n  = case filter (\x -> FromRat a < x^n && x^n <= FromRat b)
                  $ realRootsBetween (compP f (ind^n))
                                     NegativeInfinity (Finite 0) of
               [rx] -> rx
               _ -> error "nthRoot: none or multiple roots"
  | otherwise = error "nthRoot: negative"
  where f = definingPolynomial x
        Iv a b = isolatingInterval x

powIntA :: AlgReal -> Int -> AlgReal
powIntA _ 0 = 1
powIntA x n | n < 0 = recip $ powIntA x (-n)
powIntA (FromRat x) n = FromRat (x^n)
powIntA x n = let g = (ind^n) `modP` mapCoeff fromInteger (definingPolynomial x)
              in valueAt x (mapCoeff FromRat g)

valueAtA :: AlgReal -> UniPoly Rational -> AlgReal
valueAtA (FromRat x) f = FromRat (valueAt x f)
valueAtA x f = let g = f `modP` mapCoeff fromInteger (definingPolynomial x)
               in valueAt x (mapCoeff FromRat g)

powRatA :: AlgReal -> Rational -> AlgReal
powRatA x y = nthRootA (fromInteger $ denominator y) (powIntA x (fromInteger $ numerator y))

instance IntegralDomain AlgReal where
  divide = (/)
instance GCDDomain AlgReal where
  gcdD = fieldGcd; contentDesc = fieldContentDesc
