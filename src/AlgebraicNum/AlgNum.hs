module AlgebraicNum.AlgNum where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly
import AlgebraicNum.Resultant
import AlgebraicNum.AlgReal
import AlgebraicNum.Interval
import AlgebraicNum.CReal
import AlgebraicNum.Complex
import AlgebraicNum.Factor.SquareFree
import AlgebraicNum.Factor.Hensel
import AlgebraicNum.MultPoly
import System.IO.Unsafe (unsafePerformIO)
import qualified Data.Vector as V (reverse, imap)
import Data.List
import Data.Ratio

negativePRSOnPath
  :: UniPoly (Complex Integer) -> UniPoly (Complex Integer) -> Complex Integer
  -> ([UniPoly Integer], UniPoly Integer)
negativePRSOnPath f c d = (s, uv)
  where
    fc = fst $ homogeneousCompP f c d
    u = mapCoeff realPart fc
    v = mapCoeff imagPart fc
    uv = gcdD u v
    u' = u `divide` uv
    v' = v `divide` uv
    s | degree u' > degree v' = negativePRS u' v'
      | otherwise = u' : negativePRS v' (-u')

negativePRSOnHorizontalLine, negativePRSOnVerticalLine
  :: UniPoly (Complex Integer) -> Rational -> ([UniPoly Integer], UniPoly Integer)
-- c(t) = t + k * sqrt (-1)
negativePRSOnHorizontalLine f k
  = negativePRSOnPath f (scaleP (fromReal q) ind + constP (fromImag p))
                        (fromReal q)
  where p = numerator k; q = denominator k

-- c(t) = k + t * sqrt (-1)
negativePRSOnVerticalLine f k
  = negativePRSOnPath f (constP (fromReal p) + scaleP (fromImag q) ind)
                        (fromReal q)
  where p = numerator k; q = denominator k

countRootsInRectangle
  :: UniPoly Integer -> Complex (Interval Rational) -> Bool -> Int
countRootsInRectangle f rect includeLeftAndBottomEdges
  | a == b && c == d = if atTopLeft then 1 else 0
  | a == b = onRightEdge + (if atTopRight then 1 else 0)
                         + (if atBottomRight then 1 else 0)
  | c == d = onTopEdge + (if atTopLeft then 1 else 0)
                       + (if atTopRight then 1 else 0)
  | otherwise = (totalVariation `div` 2) + corners
  where
    Iv a b = realPart rect
    Iv c d = imagPart rect
    -- 4隅に根をもたないようにする
    bottomLeft  = MkComplex a c
    bottomRight = MkComplex b c
    topLeft     = MkComplex a d
    topRight    = MkComplex b d
    atBottomLeft  = valueAtT fromInteger bottomLeft  f == 0
    atBottomRight = valueAtT fromInteger bottomRight f == 0
    atTopLeft     = valueAtT fromInteger topLeft     f == 0
    atTopRight    = valueAtT fromInteger topRight    f == 0
    cornerFactors = product
      [ if atBottomLeft  then complexLinearFactor bottomLeft  else 1
      , if atBottomRight then complexLinearFactor bottomRight else 1
      , if atTopLeft     then complexLinearFactor topLeft     else 1
      , if atTopRight    then complexLinearFactor topRight    else 1
      ]
    -- 4隅にある根の数
    corners = length $ filter id
      [ includeLeftAndBottomEdges && atBottomLeft
      , includeLeftAndBottomEdges && atBottomRight
      , includeLeftAndBottomEdges && atTopLeft
      , atTopRight
      ]
    fr :: UniPoly (Complex Integer) -- f から、長方形の4隅の根を取り除いたもの
    fr = mapCoeff fromReal f `divide` cornerFactors
    g1, g2, g3, g4 :: UniPoly Integer
    s1, s2, s3, s4 :: [UniPoly Integer]
    (s1,g1) = negativePRSOnHorizontalLine fr c
    (s2,g2) = negativePRSOnVerticalLine   fr b
    (s3,g3) = negativePRSOnHorizontalLine fr d
    (s4,g4) = negativePRSOnVerticalLine   fr a
    onBottomEdge = countRealRootsBetweenZQ a b g1
    onRightEdge  = countRealRootsBetweenZQ c d g2
    onTopEdge    = countRealRootsBetweenZQ a b g3
    onLeftEdge   = countRealRootsBetweenZQ c d g4
    varOnBottomEdge = varianceAtZQ b s1 - varianceAtZQ a s1
    varOnRightEdge  = varianceAtZQ d s2 - varianceAtZQ c s2
    varOnTopEdge    = varianceAtZQ a s3 - varianceAtZQ b s3
    varOnLeftEdge   = varianceAtZQ c s4 - varianceAtZQ d s4
    rootsOnEdges
      = if includeLeftAndBottomEdges
        then onRightEdge + onTopEdge + onBottomEdge + onLeftEdge
        else onRightEdge + onTopEdge - (onBottomEdge + onLeftEdge)
    totalVariation  = varOnBottomEdge + varOnRightEdge
                      + varOnTopEdge + varOnLeftEdge + rootsOnEdges

-- @complexLinearFactor z@ は、 @ind - z@ の分母を払ったもの
complexLinearFactor :: Complex Rational -> UniPoly (Complex Integer)
complexLinearFactor (MkComplex x y)
  = let m = lcm (denominator x) (denominator y)
        x' = numerator (x * fromInteger m)
        y' = numerator (y * fromInteger m)
    in scaleP (fromInteger m) ind - constP (MkComplex x' y')

data AlgNum = FromReal !AlgReal
            | AlgNum !(UniPoly Integer) !(Complex (Interval Rational))
            deriving (Show)

instance IsAlgebraic AlgNum where
  definingPolynomial (FromReal x) = primitivePart (definingPolynomial x) -- primitivePart???
  definingPolynomial (AlgNum f _) = f

isolatingRectangle :: AlgNum -> Complex (Interval Rational)
isolatingRectangle (FromReal x) = MkComplex (isolatingInterval x) 0
isolatingRectangle (AlgNum _ r) = r

isCompatibleWithZeroR :: Complex (Interval Rational) -> Bool
isCompatibleWithZeroR x = isCompatibleWithZero (realPart x)
                          && isCompatibleWithZero (imagPart x)

compatibleRectangles :: Complex (Interval Rational) -> Complex (Interval Rational) -> Bool
compatibleRectangles x y = compatible (realPart x) (realPart y)
                           && compatible (imagPart x) (imagPart y)

toRectangles :: Complex CReal -> [Complex (Interval Rational)]
toRectangles (MkComplex r i) = zipWith MkComplex (toIntervals r) (toIntervals i)

-- the polynomial: primitive, irreducible, leading coefficient > 0
mkAlgNumWithIsolatingRectangle
  :: UniPoly Integer -> Complex (Interval Rational) -> AlgNum
mkAlgNumWithIsolatingRectangle f rect
  | degree' f == 1 = case coeffAsc f of
                       [a,b] -> fromRational $ - a % b
  | isCompatibleWithZero (imagPart rect)
  , iv@(Iv a b) <- realPart rect
  , signAtZQ a f * signAtZQ b f < 0
  = FromReal (mkAlgRealWithIrreduciblePoly f iv)
  | otherwise = AlgNum f rect

mkAlgNumWithCComplex :: UniPoly Integer -> Complex CReal -> AlgNum
mkAlgNumWithCComplex f x = sieve squareFreeFactors
  $ zipWith MkComplex (toIntervals $ realPart x)
                      (toIntervals $ imagPart x)
  where
    squareFreeFactors :: [UniPoly Integer]
    squareFreeFactors = map fst $ yunSFF $ primitivePart f

    sieve :: [UniPoly Integer] -> [Complex (Interval Rational)] -> AlgNum
    sieve [] _ = error "invalid complex number"
    sieve [g] xs = sieve2 (unsafePerformIO (factorHenselIO g)) xs
    sieve gs (x:xs)
      = sieve (filter (\g -> isCompatibleWithZeroR (valueAtT fromInteger x g)) gs) xs

    sieve2
      :: [UniPoly Integer] -> [Complex (Interval Rational)] -> AlgNum
    sieve2 [] _ = error "invalid complex number"
    sieve2 [g] xs
      | degree g <= Just 0 = error "mkAlgRealWithCComplex: minimal polynomial is constant"
      | degree' g == 1 = case coeffAsc g of
                           [a,b] -> fromRational $ - a % b
      | otherwise = case dropWhile (\r -> countRootsInRectangle g r True >= 2) xs of
          r : _ -> mkAlgNumWithIsolatingRectangle g r
    sieve2 gs (x:xs) = sieve2 (filter (\g -> isCompatibleWithZeroR (valueAtT fromInteger x g)) gs) xs

algNumToCComplex :: AlgNum -> Complex CReal
algNumToCComplex (FromReal x) = fromReal (algRealToCReal x)
algNumToCComplex x = MkComplex (CReal $ map realPart rectangles)
                               (CReal $ map imagPart rectangles)
  where
    f = definingPolynomial x
    r0 = isolatingRectangle x
    rectangles = r0 : bisectReal r0
    bisectReal rect
      = let Iv a b = realPart rect
            leftHalf  = MkComplex (Iv a ((a + b) / 2)) (imagPart rect)
            rightHalf = MkComplex (Iv ((a + b) / 2) b) (imagPart rect)
        in if countRootsInRectangle f leftHalf True == 0
           then bisectImag rightHalf
           else bisectImag leftHalf
    bisectImag rect
      = let Iv c d = imagPart rect
            lowerHalf = MkComplex (realPart rect) (Iv c ((c + d) / 2))
            upperHalf = MkComplex (realPart rect) (Iv ((c + d) / 2) d)
        in if countRootsInRectangle f lowerHalf True == 0
           then upperHalf : bisectReal upperHalf
           else lowerHalf : bisectReal lowerHalf

-- 代数的数の実部を返す
realPartA :: AlgNum -> AlgReal
realPartA (FromReal x) = x
realPartA x = mkAlgRealWithCReal g (realPart (algNumToCComplex x))
  where f = definingPolynomial x
        g = resultant (mapCoeff constP f)
            (compP (mapCoeff constP f) $ constP (scaleP 2 ind) - ind) -- \(\resultant_y(f(y),f(2x-y))\)

-- 代数的数の虚部を返す
imagPartA :: AlgNum -> AlgReal
imagPartA (FromReal _) = 0
imagPartA x = mkAlgRealWithCReal h (imagPart (algNumToCComplex x))
  where f = definingPolynomial x
        g = resultant (mapCoeff (constP . fromReal) f)
            (compP (mapCoeff (constP . fromReal) f) $ ind - constP (scaleP (fromImag 2) ind)) -- \(\resultant_y(f(y),f(y-2ix))\)
        h = gcdD (mapCoeff realPart g) (mapCoeff imagPart g)

-- 実部と虚部から代数的数を作る
mkComplexA :: AlgReal -> AlgReal -> AlgNum
mkComplexA x y = mkAlgNumWithCComplex h (MkComplex (algRealToCReal x) (algRealToCReal y))
  where f = mapCoeff constP (definingPolynomial x)
        g = mapCoeff (constP . constP) (definingPolynomial y)
        h = resultant f $ resultant g $ (constP (constP ind - ind))^2 + ind^2 -- \(\resultant_y(f(y),\resultant_z(g(z),(x-y)^2+z^2))\)

rectangleToSquaredMagnitude :: Complex CReal -> CReal
rectangleToSquaredMagnitude z
  = (maxCReal 0 (realPart z))^2 + (maxCReal 0 (imagPart z))^2

-- 絶対値の2乗を計算する
squaredMagnitudeA :: AlgNum -> AlgReal
squaredMagnitudeA (FromReal x) = x * x
squaredMagnitudeA x = mkAlgRealWithCReal (resultant y_f_x_y g)
                      (rectangleToSquaredMagnitude $ algNumToCComplex x)
  where f = definingPolynomial x
        y_f_x_y = fromCoeffVectAsc $ V.reverse $ V.imap (\i a -> constP a * ind^i) $ coeffVectAsc f -- \(y^n f(x/y)\)
        g = mapCoeff constP $ definingPolynomial x

-- 代数的数の絶対値を計算する
magnitudeA :: AlgNum -> AlgReal
magnitudeA (FromReal x) = abs x
magnitudeA x = sqrtA (squaredMagnitudeA x)

-- 複素共役を計算する
complexConjugate :: AlgNum -> AlgNum
complexConjugate x@(FromReal _) = x
complexConjugate x = mkAlgNumWithIsolatingRectangle
  (definingPolynomial x) (conjugate (isolatingRectangle x))

instance Eq AlgNum where
  FromReal x == FromReal y = x == y
  x == y = f == f' && compatibleRectangles rect1 rect2
                   && countRootsInRectangle f rect True > 0
    where
      f = definingPolynomial x
      f' = definingPolynomial y
      rect1 = isolatingRectangle x
      rect2 = isolatingRectangle y
      rect = MkComplex (intersectionInterval (realPart rect1) (realPart rect2))
                       (intersectionInterval (imagPart rect1) (imagPart rect2))

instance Num AlgNum where
  negate (FromReal x) = FromReal (negate x)
  negate x = mkAlgNumWithIsolatingRectangle
    (primitivePart $ compP (definingPolynomial x) (-ind)) (- isolatingRectangle x)

  FromReal x + FromReal y = FromReal (x + y)
  x + y = mkAlgNumWithCComplex (resultant f_x_y g) (algNumToCComplex x + algNumToCComplex y)
    where f = mapCoeff constP $ definingPolynomial x
          f_x_y = compP f (constP ind - ind) -- \(f(x-y)\)
          g = mapCoeff constP $ definingPolynomial y

  FromReal x * FromReal y = FromReal (x * y)
  FromReal (FromRat k) * y
    | k == 0 = 0
    | otherwise = mkAlgNumWithIsolatingRectangle f_x_k (isolatingRectangle y * fromRational k)
    where f_x_k = fst $ homogeneousValueAt (scaleP (denominator k) ind) (fromInteger $ numerator k) (mapCoeff fromInteger (definingPolynomial y)) -- \(f(x/k)\)
  x * y@(FromReal (FromRat _)) = y * x
  x * y = mkAlgNumWithCComplex (resultant y_f_x_y g) (algNumToCComplex x * algNumToCComplex y)
    where f = definingPolynomial x
          y_f_x_y = fromCoeffVectAsc $ V.reverse $ V.imap (\i a -> constP a * ind^i) $ coeffVectAsc f -- \(y^n f(x/y)\)
          g = mapCoeff constP $ definingPolynomial y

  fromInteger n = FromReal (fromInteger n)

  abs x = FromReal (magnitudeA x)
  signum x | x == 0 = x
           | otherwise = x / abs x

instance Fractional AlgNum where
  recip (FromReal x) = FromReal (recip x)
  recip x = mkAlgNumWithCComplex (revPoly $ definingPolynomial x)
                                 (recip (algNumToCComplex x))
  fromRational x = FromReal (fromRational x)

instance IntegralDomain AlgNum where divide = (/)
instance GCDDomain AlgNum where gcdD = fieldGcd; contentDesc = fieldContentDesc

sqrtAN :: AlgNum -> AlgNum
sqrtAN (FromReal x)
  | x >= 0 = FromReal (sqrtA x)
  | otherwise = mkComplexA 0 (sqrtA (-x))
sqrtAN x = nthRootAN 2 x

nthRootAN :: Int -> AlgNum -> AlgNum
nthRootAN n (FromReal x)
  | x >= 0 || odd n = FromReal (nthRootA n x)
  | otherwise = mkComplexA 0 (nthRootA n (-x))
nthRootAN n x
  | n == 0 = error "0th root"
  | n < 0 = nthRootAN (-n) (recip x)
  | x == 0 = 0
  | otherwise = sieve $ map (\(y,_) -> (y, toRectangles $ algNumToCComplex y))
                      $ rootsI (compP f (ind^n))
  where f = definingPolynomial x
        sieve :: [(AlgNum,[Complex (Interval Rational)])] -> AlgNum
        sieve [] = error "nthRootAN"
        sieve [(y,_)] = y
        sieve ys = sieve $ map (\(y,cz) -> (y,tail cz)) $ filter (\(_,cz) -> isCompatible (head cz)) ys
        isCompatible :: Complex (Interval Rational) -> Bool
        isCompatible z = compatibleRectangles (isolatingRectangle x) (z^n) && if isImagPartPositive then b >= 0 else a <= 0
          where Iv a b = imagPart z
        -- x is assumed to be non-real
        isImagPartPositive = unsafeCompareCReal 0 (imagPart (algNumToCComplex x)) == LT

powIntAN :: AlgNum -> Int -> AlgNum
powIntAN _ 0 = 1
powIntAN (FromReal x) n = FromReal (powIntA x n)
powIntAN x n | n < 0 = recip $ powIntAN x (-n)
powIntAN x n = let g = (ind^n) `modP` f -- \(x^n \bmod f\)
               in valueAt x (mapCoeff fromRational g)
  where
    f = mapCoeff fromInteger $ definingPolynomial x :: UniPoly Rational

powRatAN :: AlgNum -> Rational -> AlgNum
powRatAN x y = powIntAN (nthRootAN (fromInteger $ denominator y) x)
                        (fromInteger $ numerator y)

valueAtAN :: AlgNum -> UniPoly Rational -> AlgNum
valueAtAN (FromReal x) f = FromReal (valueAtA x f)
valueAtAN x f = let h = f `modP` g
                in valueAt x (mapCoeff fromRational h)
  where
    g = mapCoeff fromInteger $ definingPolynomial x :: UniPoly Rational

rootsOfIrreduciblePolyInRectangle
  :: UniPoly Integer -> Complex (Interval Rational) -> Int -> [AlgNum]
rootsOfIrreduciblePolyInRectangle f rect expectedNumOfRoots
  = bisectReal rect expectedNumOfRoots
  where
    bisectReal rect n
      | n == 0 = []
      | n == 1 && countRootsInRectangle f rect True == 1
      = [mkAlgNumWithIsolatingRectangle f rect]
      | otherwise
      = let Iv a b = realPart rect
            leftHalf  = MkComplex (Iv a ((a + b) / 2)) (imagPart rect)
            rightHalf = MkComplex (Iv ((a + b) / 2) b) (imagPart rect)
            m = countRootsInRectangle f leftHalf False
        in bisectImag leftHalf m ++ bisectImag rightHalf (n - m)
    bisectImag rect n
      | n == 0 = []
      | n == 1 && countRootsInRectangle f rect True == 1
      = [mkAlgNumWithIsolatingRectangle f rect]
      | otherwise
      = let Iv c d = imagPart rect
            lowerHalf = MkComplex (realPart rect) (Iv c ((c + d) / 2))
            upperHalf = MkComplex (realPart rect) (Iv ((c + d) / 2) d)
            m = countRootsInRectangle f lowerHalf False
        in bisectReal lowerHalf m ++ bisectReal upperHalf (n - m)

rootsI :: UniPoly Integer -> [(AlgNum,Int)]
rootsI f | f == 0 = error "rootsI: zero"
         | otherwise
  = [ (x,i)
    | (g,i) <- yunSFF (primitivePart f)
    , h <- sortPolynomials $ unsafePerformIO (factorHenselIO g)
    , let bound = rootBound h
    , x <- rootsOfIrreduciblePolyInRectangle h (MkComplex (Iv (-bound) bound) (Iv (-bound) bound)) (degree' h)
    ]
  where sortPolynomials :: [UniPoly Integer] -> [UniPoly Integer]
        sortPolynomials = sortOn coeffVectAsc

rootsQ :: UniPoly Rational -> [(AlgNum,Int)]
rootsQ f = rootsI fz where
  commonDenominator = foldl' (\a b -> lcm a (denominator b)) 1 (coeffAsc f)
  fz = primitivePart $ mapCoeff (\x -> numerator x * (commonDenominator `div` denominator x)) f

rootsA :: UniPoly AlgReal -> [(AlgNum,Int)]
rootsA f =
  [ (x,i)
  | (g,i) <- yunSFF $ primitivePart f
  , let g' = squareFree $ elimN g
  , (x,_) <- rootsI g'
  , let xc = algNumToCComplex x
  , let y' = toRectangles $ valueAtT (algNumToCComplex . FromReal) xc g
  , isCompatibleWithZeroR (y' !! 3)
  , let rect = head $ dropWhile (\rect -> countRootsInRectangle g' rect True >= 2) $ toRectangles xc
  , countRootsInRectangleAN (mapCoeff FromReal g) rect True > 0
  ]

negativePRSOnPathAN :: UniPoly AlgNum -> UniPoly (Complex Integer) -> Complex Integer -> ([UniPoly AlgReal], UniPoly AlgReal)
negativePRSOnPathAN f c d = (s, uv)
  where
    fc = fst $ homogeneousCompP f (mapCoeff complexIntToAlgNum c) (complexIntToAlgNum d)
    u = mapCoeff realPartA fc
    v = mapCoeff imagPartA fc
    uv = gcdD u v
    u' = u `divide` uv
    v' = v `divide` uv
    s | degree u' > degree v' = negativePRS u' v'
      | otherwise = u' : negativePRS v' (-u')

complexIntToAlgNum :: Complex Integer -> AlgNum
complexIntToAlgNum z = mkComplexA (fromInteger $ realPart z) (fromInteger $ imagPart z)

complexRatToAlgNum :: Complex Rational -> AlgNum
complexRatToAlgNum z = mkComplexA (fromRational $ realPart z) (fromRational $ imagPart z)

negativePRSOnHorizontalLineAN, negativePRSOnVerticalLineAN
  :: UniPoly AlgNum -> Rational -> ([UniPoly AlgReal], UniPoly AlgReal)
-- c(t) = t + k * sqrt (-1)
negativePRSOnHorizontalLineAN f k = negativePRSOnPathAN f (scaleP (fromReal q) ind + constP (fromImag p)) (fromReal q)
  where p = numerator k; q = denominator k

-- c(t) = k + t * sqrt (-1)
negativePRSOnVerticalLineAN f k = negativePRSOnPathAN f (constP (fromReal p) + scaleP (fromImag q) ind) (fromReal q)
  where p = numerator k; q = denominator k

countRootsInRectangleAN :: UniPoly AlgNum -> Complex (Interval Rational) -> Bool -> Int
countRootsInRectangleAN f rect includeLeftAndBottomEdges
  | a == b && c == d = if atTopLeft then 1 else 0
  | a == b = onRightEdge + (if atTopRight then 1 else 0)
                         + (if atBottomRight then 1 else 0)
  | c == d = onTopEdge + (if atTopLeft then 1 else 0)
                       + (if atTopRight then 1 else 0)
  | otherwise = (totalVariation `div` 2) + corners
  where
    Iv a b = realPart rect
    Iv c d = imagPart rect
    -- corners
    -- 4隅に根をもたないようにする
    bottomLeft  = MkComplex a c
    bottomRight = MkComplex b c
    topLeft     = MkComplex a d
    topRight    = MkComplex b d
    atBottomLeft  = valueAt (complexRatToAlgNum bottomLeft)  f == 0
    atBottomRight = valueAt (complexRatToAlgNum bottomRight) f == 0
    atTopLeft     = valueAt (complexRatToAlgNum topLeft)     f == 0
    atTopRight    = valueAt (complexRatToAlgNum topRight)    f == 0
    cornerFactors = mapCoeff complexRatToAlgNum $ product
      [ if atBottomLeft  then ind - constP bottomLeft  else 1
      , if atBottomRight then ind - constP bottomRight else 1
      , if atTopLeft     then ind - constP topLeft     else 1
      , if atTopRight    then ind - constP topRight    else 1
      ]
    -- 4隅にある根の数
    corners = length $ filter id
      [ includeLeftAndBottomEdges && atBottomLeft
      , includeLeftAndBottomEdges && atBottomRight
      , includeLeftAndBottomEdges && atTopLeft
      , atTopRight
      ]
    fr :: UniPoly AlgNum -- f から、長方形の4隅の根を取り除いたもの
    fr = f `divide` cornerFactors
    g1, g2, g3, g4 :: UniPoly AlgReal
    s1, s2, s3, s4 :: [UniPoly AlgReal]
    (s1,g1) = negativePRSOnHorizontalLineAN fr c
    (s2,g2) = negativePRSOnVerticalLineAN   fr b
    (s3,g3) = negativePRSOnHorizontalLineAN fr d
    (s4,g4) = negativePRSOnVerticalLineAN   fr a
    onBottomEdge = countRealRootsBetween (fromRational a) (fromRational b) g1
    onRightEdge  = countRealRootsBetween (fromRational c) (fromRational d) g2
    onTopEdge    = countRealRootsBetween (fromRational a) (fromRational b) g3
    onLeftEdge   = countRealRootsBetween (fromRational c) (fromRational d) g4
    varOnBottomEdge = varianceAt (fromRational b) s1 - varianceAt (fromRational a) s1
    varOnRightEdge  = varianceAt (fromRational d) s2 - varianceAt (fromRational c) s2
    varOnTopEdge    = varianceAt (fromRational a) s3 - varianceAt (fromRational b) s3
    varOnLeftEdge   = varianceAt (fromRational c) s4 - varianceAt (fromRational d) s4
    rootsOnEdges = if includeLeftAndBottomEdges
                   then onRightEdge + onTopEdge + onBottomEdge + onLeftEdge
                   else onRightEdge + onTopEdge - (onBottomEdge + onLeftEdge)
    totalVariation  = varOnBottomEdge + varOnRightEdge + varOnTopEdge + varOnLeftEdge + rootsOnEdges

rootsAN :: UniPoly AlgNum -> [(AlgNum,Int)]
rootsAN f = [ (x,i)
            | (g,i) <- yunSFF $ primitivePart f
            , let g' = squareFree $ elimN g
            , (x,_) <- rootsI g'
            , let xc = algNumToCComplex x
            , let y' = toRectangles $ valueAtT algNumToCComplex xc g
            , isCompatibleWithZeroR (y' !! 3)
            , let rect = head $ dropWhile (\rect -> countRootsInRectangle g' rect True >= 2) $ toRectangles xc
            , countRootsInRectangleAN g rect True > 0
            ]
