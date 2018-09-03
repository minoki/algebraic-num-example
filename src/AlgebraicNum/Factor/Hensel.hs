{-# LANGUAGE ScopedTypeVariables #-}
module AlgebraicNum.Factor.Hensel where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly
import AlgebraicNum.Factor.BigPrime (factorCoefficientBound,coprimeModP,oneNorm,partitions)
import AlgebraicNum.Factor.CantorZassenhaus (factorCZ)
import Data.FiniteField (PrimeField,char,toInteger)
import System.Random (RandomGen,getStdRandom)
import GHC.TypeLits (KnownNat,natVal)
import Data.Reflection (reifyNat)
import Data.Proxy (Proxy)
import Math.NumberTheory.Primes.Sieve (primes)
import Control.Monad (guard)

-- 仮定：\(f\equiv g h \pmod{p}\), \(h\)はモニック
-- 出力 \((g^*,h^*)\)： \(f\equiv g^* h^* \pmod{p^l}\), \(h^*\)はモニック
henselLifting2 :: (KnownNat p)
               => Int -> UniPoly Integer
               -> UniPoly (PrimeField p) -> UniPoly (PrimeField p)
               -> (UniPoly Integer, UniPoly Integer)
henselLifting2 l f g h =
  let (u,s,t) = exEuclid g h -- \(sg+th=u\)
      g_ = mapCoeff Data.FiniteField.toInteger g
      h_ = mapCoeff Data.FiniteField.toInteger h
      s_ = mapCoeff Data.FiniteField.toInteger (s `divide` u)
      t_ = mapCoeff Data.FiniteField.toInteger (t `divide` u)
  in loop 1 p g_ h_ s_ t_
  where
    p = char (leadingCoefficient g)
    loop i m g h s t | i >= l = (g, h)
                     | otherwise = loop (2 * i) (m^2) g' h' s' t'
      where
        -- Hensel step
        -- 仮定:
        --   \(f - g h \equiv 0 \pmod{m}\), \(s g + t h \equiv 1 \pmod{m}\), \(h\)はモニック,
        --   \(\deg f = \deg g + \deg h\), \(\deg s < \deg h\), \(\deg t < \deg g\)
        -- 出力 \((g^*,h^*,s^*,t^*)\):
        --   \(f - g^* * h^* \equiv 0 \pmod{m^2}\), \(s^* * g^* + t^* * h^* \equiv 1 \pmod{m}\)
        --   \(h^*\)はモニック
        --   \(g \equiv g^*, h \equiv h^* \pmod{m}\), \(s \equiv s^*, t \equiv t^* \pmod{m}\)
        --   \(\deg g = \deg g^*\), \(\deg h == \deg h^*\)
        --   \(\deg s^* < \deg h^*\), \(\deg t^* < \deg g^*\)
        e = mapCoeff (`mod` m^2) (f - g * h)
        (q,r) = (s * e) `monicDivMod` h
        g' = mapCoeff (`mod` m^2) (g + t * e + q * g)
        h' = mapCoeff (`mod` m^2) (h + r)
        b = mapCoeff (`mod` m^2) (s * g' + t * h' - 1)
        (c,d) = (s * b) `monicDivMod` h'
        s' = mapCoeff (`mod` m^2) (s - d)
        t' = mapCoeff (`mod` m^2) (t - t * b - c * g')

-- 仮定：\(\gcd(x,m)=1\)
inverseMod :: Integer -> Integer -> Integer
inverseMod x m = case exEuclid x m of
  -- \(\pm 1 = t x + \mathtt{*}m\)
  (1,t,_)  -> t
  (-1,t,_) -> - t
  _ -> error (show x ++ " has no inverse modulo " ++ show m)

-- 入力：自然数\(l\), 整数係数多項式\(f\), \(\FiniteField_p\)係数の多項式の列\(\mathrm{gs}\)
-- 仮定：\(f\equiv\leadingCoefficient(f)\prod\mathrm{gs} \pmod{p}\), \(\mathrm{gs}\)の元はモニック
-- 出力\(\mathrm{gs}^*\)：
--   \(f\equiv\leadingCoefficient(f)\prod\mathrm{gs}^* \pmod{p^l}\)
--   \(\mathrm{gs}^*\)の元はモニック
henselLifting :: (KnownNat p)
              => Int -> UniPoly Integer -> [UniPoly (PrimeField p)]
              -> [UniPoly Integer]
henselLifting _ _f [] = [] -- \(\mathrm{gs}\)が空：\(f=1\)のはず
henselLifting l f [g]
  = [mapCoeff (\a -> inv_lc_f * a `mod` (p^l)) f] -- \(\mathrm{gs}\)の長さが1
  where inv_lc_f = inverseMod (leadingCoefficient f) (p^l)
        p = char (leadingCoefficient g)
henselLifting l f gs =
  let (gs1,gs2) = splitAt (length gs `div` 2) gs -- \(\mathrm{gs}=\mathrm{gs}_1\sqcup\mathrm{gs}_2\)（分割）
      -- \(g:=\overline{\leadingCoefficient(f)}\prod\mathrm{gs}_1\), \(h:=\prod\mathrm{gs}_2\)
      g = fromInteger (leadingCoefficient f) * product gs1
      h = product gs2
      -- \(f\equiv gh\pmod{p}\)から\(f\equiv g^* h^* \pmod{p^l}\)を得る：
      (g',h') = henselLifting2 l f g h
  in henselLifting l g' gs1 ++ henselLifting l h' gs2 -- 再帰的に持ち上げる

-- Input: nonzero, primitive, squarefree
factorHensel :: (RandomGen g)
             => UniPoly Integer -> g -> ([UniPoly Integer], g)
factorHensel f =
  let lc_f = leadingCoefficient f
      bound = factorCoefficientBound f * lc_f
      p:_ = filter (\p -> lc_f `mod` p /= 0
                          && reifyNat p coprimeModP f (diffP f))
            $ tail primes
  in reifyNat p factorWithPrime bound f

factorHenselIO :: UniPoly Integer -> IO [UniPoly Integer]
factorHenselIO = getStdRandom . factorHensel

-- p must be prime
factorWithPrime :: forall p g. (KnownNat p, RandomGen g)
                => Proxy p -> Integer -> UniPoly Integer -> g
                -> ([UniPoly Integer], g)
factorWithPrime proxy bound f gen =
  let p = natVal proxy
      f' = toMonic $ mapCoeff fromInteger f :: UniPoly (PrimeField p)
      (modularFactorsP, gen') = factorCZ f' gen
      -- Choose l and m so that  \(m = p^l > 2\cdot\mathrm{bound} + 1\)
      (l,m) | p^l' > 2 * bound + 1 = (l',p^l')
            | otherwise = head $ filter (\(_,m) -> m > 2 * bound + 1)
                          $ iterate (\(i,m) -> (i + 1, m * p)) (l',p^l')
        where l' = ceiling (log (fromInteger (2 * bound + 1) :: Double)
                            / log (fromInteger p :: Double)) :: Int
      modularFactors = henselLifting l f modularFactorsP
      -- \(f \equiv \leadingCoefficient(f)\cdot\prod\mathrm{modularFactors}\pmod{p^l}\)
  in (factorCombinationsModulo m bound 1 f modularFactors, gen')

-- \(m \ge 2 \cdot \mathrm{bound} + 1\)
-- \(f \equiv \leadingCoefficient(f)\cdot\prod\mathrm{modularFactors}\pmod{m}\)
factorCombinationsModulo
  :: Integer -> Integer -> Int -> UniPoly Integer -> [UniPoly Integer]
  -> [UniPoly Integer]
factorCombinationsModulo m bound k f modularFactors
  = loop k f modularFactors
  where loop _ _f [] = [] -- _f must be 1
        loop k f modularFactors
          | 2 * k > length modularFactors = [f] -- \(f\)は既約
          | otherwise = case tryFactorCombinations of
              [] -> loop (k+1) f modularFactors
              (g,h,rest):_ -> g : loop k h rest
          where tryFactorCombinations = do
                  (s,rest) <- partitions k modularFactors
                  let lc_f = fromInteger (leadingCoefficient f)
                      g = mapCoeff toInteger_ (lc_f * product s)
                      h = mapCoeff toInteger_ (lc_f * product rest)
                  guard (oneNorm g * oneNorm h <= bound)
                  return (primitivePart g, primitivePart h, rest)
        toInteger_ :: Integer -> Integer
        toInteger_ n = let k = n `mod` m
                       in if 2 * k > m then k - m else k
