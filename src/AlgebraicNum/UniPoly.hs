module AlgebraicNum.UniPoly where
import AlgebraicNum.Class
import qualified Data.Vector as V
import Data.Vector ((!))

-- 一変数多項式 (univariate polynomial)
newtype UniPoly a = UniPoly (V.Vector a)
  deriving (Eq,Show)

-- 多項式としてのゼロ
-- 末尾の P は polynomial の頭文字のつもり（以下同様）
zeroP :: UniPoly a
zeroP = UniPoly V.empty

-- 定数項のみの多項式
constP :: (Eq a, Num a) => a -> UniPoly a
constP 0 = zeroP
constP a = UniPoly (V.singleton a)

-- 不定元 (indeterminate)
ind :: (Num a) => UniPoly a
ind = UniPoly (V.fromList [0,1])

-- 多項式の係数を Vector として得る（昇冪の順）
coeffVectAsc :: UniPoly a -> V.Vector a
coeffVectAsc (UniPoly xs) = xs

-- 多項式の係数をリストとして得る
coeffAsc, coeffDesc :: UniPoly a -> [a]
coeffAsc = V.toList . coeffVectAsc
coeffDesc = V.toList . V.reverse . coeffVectAsc

-- 係数の列から多項式を作る
-- 具体的には、最高次の係数が 0 にならないようにリストの後ろの方を取り除く
fromCoeffVectAsc :: (Eq a, Num a) => V.Vector a -> UniPoly a
fromCoeffVectAsc xs
  | V.null xs      = zeroP
  | V.last xs == 0 = fromCoeffVectAsc (V.init xs)
  | otherwise      = UniPoly xs

fromCoeffAsc, fromCoeffDesc :: (Eq a, Num a) => [a] -> UniPoly a
fromCoeffAsc = fromCoeffVectAsc . V.fromList
fromCoeffDesc = fromCoeffVectAsc . V.reverse . V.fromList

-- 多項式の係数に関数を適用する
mapCoeff :: (Eq b, Num b) => (a -> b) -> UniPoly a -> UniPoly b
mapCoeff f = fromCoeffVectAsc . fmap f . coeffVectAsc

-- 多項式の次数
-- ゼロの場合は Nothing を返す。
-- （Maybe 型については Nothing < Just _ となるため、
-- 　順序関係に関しては Nothing を -∞ として扱うことができる）
degree :: UniPoly a -> Maybe Int
degree (UniPoly xs) = case V.length xs - 1 of
  -1 -> Nothing
  n -> Just n

-- 多項式の次数
-- ゼロの場合はエラーとする。
degree' :: UniPoly a -> Int
degree' (UniPoly xs) = case V.length xs of
  0 -> error "degree': zero polynomial"
  n -> n - 1

-- 最高次の係数
leadingCoefficient :: (Num a) => UniPoly a -> a
leadingCoefficient (UniPoly xs)
  | V.null xs = 0
  | otherwise = V.last xs

-- モニック多項式への変換：係数を最高次の係数で割る
toMonic :: (Fractional a) => UniPoly a -> UniPoly a
toMonic f@(UniPoly xs)
  | V.null xs = zeroP
  | otherwise = UniPoly $ V.map (* recip (leadingCoefficient f)) xs

instance (Eq a, Num a) => Num (UniPoly a) where
  negate (UniPoly xs) = UniPoly $ V.map negate xs

  UniPoly xs + UniPoly ys
    | n < m = UniPoly $ V.accumulate (+) ys (V.indexed xs)
    | m < n = UniPoly $ V.accumulate (+) xs (V.indexed ys)
    | n == m = fromCoeffVectAsc $ V.zipWith (+) xs ys
    where n = V.length xs; m = V.length ys

  -- multiplication: naive method
  UniPoly xs * UniPoly ys
    | n == 0 || m == 0 = zeroP
    | otherwise = UniPoly $ V.generate (n + m - 1)
      (\i -> sum [(xs ! j) * (ys ! (i - j)) | j <- [0..i], j < n, i - j < m])
    where n = V.length xs; m = V.length ys

  fromInteger n = constP $ fromInteger n

  -- Not included in the article:
  abs = error "abs on UniPoly does not make sense"
  signum = error "signum on UniPoly does not make sense"

-- scalar multiplication
scaleP :: (Eq a, Num a) => a -> UniPoly a -> UniPoly a
scaleP a (UniPoly xs)
  | a == 0 = zeroP
  | otherwise = UniPoly $ V.map (* a) xs

unscaleP :: (Eq a, IntegralDomain a) => a -> UniPoly a -> UniPoly a
unscaleP a f = mapCoeff (`divide` a) f

valueAt :: (Num a) => a -> UniPoly a -> a
valueAt t (UniPoly xs) = V.foldr' (\a b -> a + t * b) 0 xs

valueAtT :: (Num b) => (a -> b) -> b -> UniPoly a -> b
valueAtT f t (UniPoly xs) = V.foldr' (\a b -> f a + t * b) 0 xs

-- homogeneousValueAt \(u\) \(v\) (\(a_n X^n + \cdots + a_1 X + a_0\))
-- = (\(a_n u^n + a_{n-1} u^{n-1} v + \cdots + a_1 u v^{n-1} + a_0 v^n\), \(v^n\))
homogeneousValueAt :: (Eq a, Num a) => a -> a -> UniPoly a -> (a, a)
homogeneousValueAt u v f@(UniPoly coeff)
  | f == 0 = (0, 1)
  | otherwise = (V.foldr' (\x y -> x + u * y) 0
                 $ V.zipWith (*) coeff denseq, V.head denseq)
  where denseq = V.reverse (V.iterateN (V.length coeff) (* v) 1)

-- 'f `compP` g = f(g(x))'
compP :: (Eq a, Num a) => UniPoly a -> UniPoly a -> UniPoly a
compP f g = valueAtT constP g f

-- homogeneousCompP (\(a_n X^n + \cdots + a_1 X + a_0\)) \(g\) \(v\)
-- = (\(a_n g^n + a_{n-1} g^{n-1} v + \cdots + a_1 g v^{n-1} + a_0 v^n\), \(v^n\))
homogeneousCompP :: (Eq a, Num a) => UniPoly a -> UniPoly a -> a -> (UniPoly a, a)
homogeneousCompP f@(UniPoly coeff) g v
  | f == 0 = (0, 1)
  | otherwise = (V.foldr' (\x y -> constP x + g * y) 0
                 $ V.zipWith (*) coeff denseq, V.head denseq)
  where denseq = V.reverse (V.iterateN (V.length coeff) (* v) 1)

-- \(x^n f(1/x)\)
revPoly :: (Eq a, Num a) => UniPoly a -> UniPoly a
revPoly = fromCoeffVectAsc . V.reverse . coeffVectAsc

divModP :: (Eq a, Fractional a)
        => UniPoly a -> UniPoly a -> (UniPoly a, UniPoly a)
divModP f g
  | g == 0    = error "divModP: divide by zero"
  | degree f < degree g = (zeroP, f)
  | otherwise = loop zeroP (scaleP (recip b) f)
  where
    g' = toMonic g
    b = leadingCoefficient g
    -- invariant: f == q * g + scaleP b p
    loop q p | degree p < degree g = (q, scaleP b p)
             | otherwise = loop (q + q') (p - q' * g')
      where q' = UniPoly (V.drop (degree' g) (coeffVectAsc p))

divP f g = fst (divModP f g)
modP f g = snd (divModP f g)

gcdP :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> UniPoly a
gcdP f g | g == 0    = f
         | otherwise = gcdP g (f `modP` g)

-- 余りを計算するごとにモニック多項式に変換する
monicGcdP :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> UniPoly a
monicGcdP f g | g == 0    = f
              | otherwise = monicGcdP g (toMonic (f `modP` g))

diffP :: (Eq a, Num a) => UniPoly a -> UniPoly a
diffP (UniPoly xs)
  | null xs = zeroP
  | otherwise = fromCoeffVectAsc $ V.tail
                $ V.imap (\i x -> fromIntegral i * x) xs

squareFree :: (Eq a, GCDDomain a) => UniPoly a -> UniPoly a
squareFree f = f `divide` gcdD f (diffP f)

pseudoDivModP :: (Eq a, Num a)
              => UniPoly a -> UniPoly a -> (UniPoly a, UniPoly a)
pseudoDivModP f g
  | g == 0 = error "pseudoDivModP: divide by zero"
  | degree f < degree g = (zeroP, f)
  | otherwise = case loop 0 zeroP f of
      (i,q,r) -> (scaleP (b^(l-i)) q, scaleP (b^(l-i)) r)
  where
    l = degree' f - degree' g + 1
    b = leadingCoefficient g
    -- invariant: scaleP i f == q * g + r
    loop i q r
      | degree r < degree g = (i, q, r)
      | otherwise = loop (i + 1) (scaleP b q + q') (scaleP b r - q' * g)
      where q' = UniPoly (V.drop (degree' g) (coeffVectAsc r))

pseudoDivP, pseudoModP :: (Eq a, Num a)
                       => UniPoly a -> UniPoly a -> UniPoly a
pseudoDivP f g = fst (pseudoDivModP f g)
pseudoModP f g = snd (pseudoDivModP f g)

-- | division by a monic polynomial
monicDivMod :: (Eq a, Num a) => UniPoly a -> UniPoly a -> (UniPoly a, UniPoly a)
monicDivMod f g
  -- leadingCoefficient g must be 1
  | leadingCoefficient g /= 1 = error "monicDivMod: g must be monic"
  | otherwise = loop zeroP f
  where
    -- invariant: f == q * g + r
    loop q r | degree r < degree g = (q, r)
             | otherwise = loop (q + q') (r - q' * g)
      where q' = UniPoly (V.drop (degree' g) (coeffVectAsc r))

-- | 多項式の内容を計算する
content :: (GCDDomain a) => UniPoly a -> a
content = contentDesc . coeffDesc

-- | 多項式の内容と原始部分を計算する
contentAndPrimitivePart
  :: (Eq a, GCDDomain a) => UniPoly a -> (a, UniPoly a)
contentAndPrimitivePart f
  | c == 1 = (c, f)
  | otherwise = (c, unscaleP c f)
  where c = content f

-- | 多項式の原始部分を計算する
primitivePart :: (Eq a, GCDDomain a) => UniPoly a -> UniPoly a
primitivePart = snd . contentAndPrimitivePart

instance (Eq a, IntegralDomain a) => IntegralDomain (UniPoly a) where
  divide f g
    | g == 0 = error "divide: divide by zero"
    | degree f < degree g = zeroP -- f should be zero
    | otherwise = loop zeroP f
    where
      l = degree' f - degree' g + 1
      b = leadingCoefficient g
      -- invariant: f == q * g + r
      loop q r | degree r < degree g = q -- r should be zero
               | otherwise = loop (q + q') (r - q' * g)
        where q' = unscaleP b (UniPoly (V.drop (degree' g) (coeffVectAsc r)))

gcdWithSubrPRS :: (Eq a, IntegralDomain a) => UniPoly a -> UniPoly a -> UniPoly a
gcdWithSubrPRS f 0 = f
gcdWithSubrPRS f g
  | degree f < degree g = gcdWithSubrPRS g f
  | otherwise = case pseudoModP f g of
      0 -> g
      rem -> let !d = degree' f - degree' g
                 !s = (-1)^(d + 1) * rem
             in loop d (-1) g s
  where
    loop !_ _ f 0 = f
    loop !d psi f g = case pseudoModP f g of
      0 -> g
      rem -> let !d' = degree' f - degree' g
                 !c = leadingCoefficient f
                 !psi' | d == 0 = psi
                       | d > 0 = ((-c)^d) `divide` (psi^(d-1))
                 !beta = -c * psi' ^ d'
                 !s = unscaleP beta rem
             in loop d' psi' g s

instance (Eq a, GCDDomain a) => GCDDomain (UniPoly a) where
  gcdD x y
    = scaleP (gcdD xc yc) $ primitivePart (gcdWithSubrPRS xp yp)
    where (xc,xp) = contentAndPrimitivePart x
          (yc,yp) = contentAndPrimitivePart y
  contentDesc [] = 0
  contentDesc xs = scaleP (contentDesc (map fst ys)) $ gcdV 0 (map snd ys)
    where
      ys = map contentAndPrimitivePart xs
      gcdV 1 _ = 1
      gcdV a [] = a
      gcdV a (x:xs) = gcdV (primitivePart $ gcdWithSubrPRS x a) xs

instance (Eq a, Fractional a, GCDDomain a) => EuclideanDomain (UniPoly a) where
  divModD = divModP
