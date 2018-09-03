module AlgebraicNum.Factor.CantorZassenhaus where
import Data.FiniteField
import System.Random
import Control.Monad
import Control.Monad.State
import AlgebraicNum.UniPoly

powMod :: (Eq k, Fractional k)
       => UniPoly k -> Integer -> UniPoly k -> UniPoly k
powMod _ 0 _ = 1
powMod a n m = let a' = a `modP` m in loop a' (n-1) a'
  where loop _ 0 acc = acc
        loop a n acc = case n `quotRem` 2 of
          (n',0) -> loop ((a * a) `modP` m) n' acc
          (n',_) -> loop ((a * a) `modP` m) n' ((acc * a) `modP` m)

-- Input: nonzero, monic, squarefree
distinctDegreeFactorization :: (FiniteField k, Eq k)
                            => UniPoly k -> [(Int,UniPoly k)]
distinctDegreeFactorization f = loop 1 ind f
  where
    q = order (leadingCoefficient f)
    -- \(k=1,2,\ldots\), \(u=x^{q^{k-1}}\), \(g=g_{k-1}\)
    loop k u g | degree' g == 0 = [] -- \(g=1\)
               | degree' g < 2*k = [(degree' g,g)]
               | f' == 1 = loop (k+1) u' g'
               | otherwise = (k,f') : loop (k+1) u' g'
      where u' = powMod u q f  -- \(x^{q^k} \mod f\)
            f' = toMonic $ gcdP g (u' - ind) -- \(f_k:=\gcd(g_{k-1},x^{q^k}-x)\)
            g' = g `divP` f'  -- \(g_k:=g_{k-1}/f_k\)

randomPolyOfDegreeLessThan :: (Eq k, Num k, Random k, RandomGen g)
                           => Int -> g -> (UniPoly k, g)
randomPolyOfDegreeLessThan n = runState
  $ fmap fromCoeffAsc $ sequence $ replicate n $ state random

-- Input: nonzero, monic, squarefree, equal-degree, reducible
equalDegreeFactorizationOne
  :: (FiniteField k, Eq k, Random k, RandomGen g)
  => Int -> UniPoly k -> g -> (Maybe (UniPoly k), g)
equalDegreeFactorizationOne d h g = (tryOne, g')
  where
    q = order (leadingCoefficient h) -- must be odd
    (u,g') = randomPolyOfDegreeLessThan (degree' h) g
    tryOne = do
      -- u: ランダムに選んだ次数\(\deg h\)未満の多項式
      guard (u /= 0) -- \(u=0\)なら失敗
      let v = toMonic $ gcdP h u -- \(v:=\gcd(h,u)\)
      if v /= 1
        then return v -- \(\gcd(h,u)\)が非自明な因数
        else do
        let w = powMod u ((q^d-1) `div` 2) h -- \(u^{(q^d-1)/2} \mod h\)
            h' = toMonic $ gcdP h (w-1) -- \(h^*:=\gcd\bigl(h,u^{(q^d-1)/2}-1\bigr)\)
        guard (h' /= 1 && h' /= h) -- \(h^*=1\)または\(h^*=h\)なら失敗
        return h'

-- Input: nonzero, monic, squarefree, equal-degree
equalDegreeFactorization
  :: (FiniteField k, Eq k, Random k, RandomGen g)
  => Int -> UniPoly k -> g -> ([UniPoly k], g)
equalDegreeFactorization d h = runState (loop h [])
  where
    -- 仮定：\(h\)の既約因数は全て\(d\)次である
    loop h acc
      | degree' h == 0 = return acc -- \(h=1\): 終了
      | degree' h == d = return (h:acc) -- \(\deg h=d\): 終了
      | otherwise = do -- \(h\)はまだ既約ではない：
          -- 自明でない引数を一つ見つけ出す
          m <- state (equalDegreeFactorizationOne d h)
          case m of
            Nothing -> loop h acc -- 失敗：もう一回試す
            Just h' -> do -- 自明でない因数 \(h^*\)が見つかった：
              acc' <- loop h' acc     -- \(h^*\)を因数分解
              loop (h `divP` h') acc' -- \(h/h^*\)を因数分解

-- Input: nonzero, monic, squarefree
factorCZ :: (FiniteField k, Eq k, Random k, RandomGen g)
         => UniPoly k -> g -> ([UniPoly k], g)
factorCZ f = runState
             $ fmap concat
             $ forM (distinctDegreeFactorization f)
             $ \(d,h) -> state (equalDegreeFactorization d h)

factorCZIO :: (FiniteField k, Eq k, Random k)
           => UniPoly k -> IO [UniPoly k]
factorCZIO = getStdRandom . factorCZ
