module AlgebraicNum.Class where
import Data.Ratio
import Data.List
import Data.FiniteField
import GHC.TypeLits (KnownNat)

-- | 整域
--
-- \(1 \ne 0\) となる可換環で、非自明な零因子を持たないものを整域という。
class (Num a) => IntegralDomain a where
  -- | 除算
  --
  -- @a@ が @b@ の倍数であるとき、 @divide a b@ は @a = b * c@ となる @c@ を返す。
  -- @a@ が @b@ の倍数でない時の挙動は規定しない。
  divide :: a -> a -> a

infixl 7 `divide`

instance (Integral a) => IntegralDomain (Ratio a) where
  divide = (/)
instance IntegralDomain Integer where
  divide = div

class (IntegralDomain a) => GCDDomain a where
  gcdD :: a -> a -> a
  contentDesc :: [a] -> a
  contentDesc = foldl' gcdD 0

-- | 体の場合の gcdD 関数のデフォルト実装
fieldGcd :: (Eq a, Fractional a) => a -> a -> a
fieldGcd 0 0 = 0
fieldGcd _ _ = 1

-- | 体の場合の contentDesc 関数のデフォルト実装
fieldContentDesc :: (Eq a, Fractional a) => [a] -> a
fieldContentDesc [] = 0
fieldContentDesc (x:_) = x

instance (Integral a) => GCDDomain (Ratio a) where
  gcdD = fieldGcd; contentDesc = fieldContentDesc

instance GCDDomain Integer where
  gcdD = gcd
  contentDesc [] = 0
  contentDesc (x:xs) | x < 0 = negate (gcdV x xs) -- 内容の符号に、最高次の係数の符号を反映させる
                     | otherwise = gcdV x xs -- 短絡評価を考えなければ foldr gcd 0 でも良い
    where
      -- foldl/foldr と gcd の組み合わせでは GCD が 1 になっても残りの部分が評価される。
      -- 列の途中で GCD が 1 になれば全体の GCD は 1 で確定なので、そういう短絡評価する。
      gcdV 1 _ = 1
      gcdV a [] = a
      gcdV a (x:xs) = gcdV (gcdD x a) xs

-- ユークリッド整域
class (Num a) => EuclideanDomain a where
  -- a, b に対して、 (q,r) = divModD a b は a = q * b + r を満たす
  divModD :: a -> a -> (a, a)
  modD :: a -> a -> a
  modD x y = snd (divModD x y)

infixl 7 `modD`

instance EuclideanDomain Integer where
  divModD = divMod

instance (KnownNat p) => IntegralDomain (PrimeField p) where
  divide = (/)
instance (KnownNat p) => GCDDomain (PrimeField p) where
  gcdD = fieldGcd; contentDesc = fieldContentDesc
