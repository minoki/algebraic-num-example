module AlgebraicNum.CReal where
import AlgebraicNum.Interval
import Data.Maybe

-- 計算可能実数を表すデータ型
newtype CReal = CReal [Interval Rational]

-- 区間の列に変換する
toIntervals :: CReal -> [Interval Rational]
toIntervals (CReal xs) = xs

-- 大きい方を返す
maxCReal :: CReal -> CReal -> CReal
maxCReal (CReal xs) (CReal ys) = CReal (zipWith maxInterval xs ys)

-- 小さい方を返す
minCReal :: CReal -> CReal -> CReal
minCReal (CReal xs) (CReal ys) = CReal (zipWith minInterval xs ys)

instance Num CReal where
  negate (CReal xs)   = CReal (map negate xs)
  CReal xs + CReal ys = CReal (zipWith (+) xs ys)
  CReal xs - CReal ys = CReal (zipWith (-) xs ys)
  CReal xs * CReal ys = CReal (zipWith (*) xs ys)
  abs (CReal xs)      = CReal (map abs xs)
  signum (CReal xs)   = error "signum on CReal is not computable"
  fromInteger n       = CReal $ repeat (fromInteger n)

instance Fractional CReal where
  recip (CReal xs)
    = CReal $ map recip $ dropWhile isCompatibleWithZero xs
  fromRational x = CReal $ repeat $ fromRational x

unsafeCompareCReal :: CReal -> CReal -> Ordering
unsafeCompareCReal (CReal xs) (CReal ys)
  = head $ catMaybes $ zipWith maybeCompareInterval xs ys
