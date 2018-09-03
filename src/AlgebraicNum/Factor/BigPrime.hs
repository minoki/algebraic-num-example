{-# LANGUAGE ScopedTypeVariables #-}
module AlgebraicNum.Factor.BigPrime where
import AlgebraicNum.UniPoly
import AlgebraicNum.Factor.CantorZassenhaus (factorCZ)
import Data.FiniteField (PrimeField,char,toInteger)
import System.Random (RandomGen,getStdRandom)
import Control.Monad (guard)
import Data.Proxy (Proxy)
import GHC.TypeLits (KnownNat)
import Data.Reflection (reifyNat)
import Math.NumberTheory.Powers.Squares (integerSquareRoot)
import Math.NumberTheory.Primes.Sieve (sieveFrom)
import Data.Bifunctor (first,second)

-- 1-norm of coefficients
oneNorm :: (Ord a, Num a) => UniPoly a -> a
oneNorm f = sum $ map abs $ coeffAsc f

-- max-norm of coefficients
maxNorm :: (Ord a, Num a) => UniPoly a -> a
maxNorm f = maximum $ map abs $ coeffAsc f

factorCoefficientBound :: UniPoly Integer -> Integer
factorCoefficientBound f -- \({}\ge\lceil\sqrt{n+1}\rceil\cdot 2^n\cdot\norm{f}_\infty\)
  = (integerSquareRoot (n + 1) + 1) * 2^n * maxNorm f
  -- または\(2^n\cdot\norm{f}_1\)でも良い
  where n = fromIntegral (degree' f)

-- @partitions n s@ returns all possible partitions @(t,u)@ with @t ++ u == s@ (as a set) and @length t == n@
partitions :: Int -> [a] -> [([a],[a])]
partitions 0 [] = [([],[])]
partitions _ [] = []
partitions n (x : xs) = map (first (x :)) (partitions (n - 1) xs)
                        ++ map (second (x :)) (partitions n xs)

-- converts a @PrimeField p@ value into integer in \((-p/2,p/2]\)
toInteger' :: (KnownNat p) => PrimeField p -> Integer
toInteger' x | x' * 2 <= p = x'
             | otherwise = x' - p
  where p = char x
        x' = Data.FiniteField.toInteger x

-- Input: nonzero, primitive, squarefree, leading coefficient > 0
factorBigPrime :: (RandomGen g)
               => UniPoly Integer -> g -> ([UniPoly Integer], g)
factorBigPrime f =
      -- \(B\le\sqrt{n+1}\cdot2^n\cdot\norm{f}_\infty\cdot\leadingCoefficient(f)\)
  let bound = factorCoefficientBound f * leadingCoefficient f
      -- 適切な素数\(p\)を見つける
      p:_ = filter (\p -> reifyNat p coprimeModP f (diffP f))
            $ sieveFrom (2 * bound + 1)
      -- \(B\)と\(p\)を factorWithPrime 関数に渡し、後の処理を任せる
  in reifyNat p factorWithPrime bound f

factorBigPrimeIO :: UniPoly Integer -> IO [UniPoly Integer]
factorBigPrimeIO = getStdRandom . factorBigPrime

coprimeModP :: forall p. (KnownNat p)
            => Proxy p -> UniPoly Integer -> UniPoly Integer -> Bool
coprimeModP _proxy f g =
  let f' = mapCoeff fromInteger f :: UniPoly (PrimeField p)
      g' = mapCoeff fromInteger g :: UniPoly (PrimeField p)
  in degree (gcdP f' g') == Just 0

-- p must be prime
factorWithPrime :: forall p g. (KnownNat p, RandomGen g)
                => Proxy p -> Integer -> UniPoly Integer -> g
                -> ([UniPoly Integer], g)
factorWithPrime _proxy bound f gen =
  let f' = toMonic $ mapCoeff fromInteger f :: UniPoly (PrimeField p)
      -- \(\overline{f}\in\FiniteField_p\)は（\(p\)の選び方により）無平方である
      -- \(\overline{f}\)をモニック化したものを有限体係数のアルゴリズムで因数分解する：
      -- \(\mathrm{modularFactors}:=\{g_1,\ldots,g_r\}\), \(\overline{f}=\overline{\leadingCoefficient(f)}g_1\cdots g_r\)
      (modularFactors, gen') = factorCZ f' gen
  in (factorCombinations bound 1 f modularFactors, gen')

factorCombinations
  :: (KnownNat p)
  => Integer -> Int -> UniPoly Integer -> [UniPoly (PrimeField p)]
  -> [UniPoly Integer]
factorCombinations _bound _k _f [] = [] -- 集合\(T\)が空：\(f=1\)のはず
factorCombinations bound k f modularFactors
  -- modularFactors を以下\(T\)と呼ぶ
  | 2 * k > length modularFactors = [f] -- \(2k>\#T\): \(f\)は既に既約
  | otherwise -- 集合\(T\)から\(k\)個取り出すパターンを全て試す：
  = case tryFactorCombinations of
      -- 因数が見つからなかった：\(k+1\)個を試す（再帰呼び出し）
      [] -> factorCombinations bound (k+1) f modularFactors
      -- 因数が見つかった：残りの因数を探す（再帰呼び出し）
      (g,h,rest):_ -> g : factorCombinations bound k h rest
  where tryFactorCombinations = do
          -- 集合\(T\)から\(k\)個取り出したものを\(s\)、補集合を\(\mathrm{rest}\)とおく
          (s,rest) <- partitions k modularFactors
          let lc_f = fromInteger (leadingCoefficient f)
              -- \(g^*\): \(s\)に対応するものの積を整数係数にしたもの
              g = mapCoeff toInteger' (lc_f * product s)
              -- \(h^*\): \(s\)の補集合に対応するもの積を整数係数にしたもの
              h = mapCoeff toInteger' (lc_f * product rest)
          -- \(\norm{g^*}_1\norm{h^*}_1\le B\)なら、\(g\)は\(f\)の既約因数である
          guard (oneNorm g * oneNorm h <= bound)
          return (primitivePart g, primitivePart h, rest)
