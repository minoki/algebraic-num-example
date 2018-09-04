module AlgebraicNum.Factor.Berlekamp where
import Prelude hiding (toInteger)
import Data.FiniteField
import System.Random
import Control.Monad.State
import Data.Array
import Data.List
import AlgebraicNum.UniPoly
import AlgebraicNum.Factor.CantorZassenhaus (powMod)

type Mat a = Array (Int,Int) a

-- \(\beta \colon x \mapsto x^q-x\) の表現行列を計算する。
betaMat :: (FiniteField k, Eq k) => UniPoly k -> Mat k
betaMat f
  = let q = order (leadingCoefficient f)
        n = degree' f
        xq = powMod ind q f -- \(x^q \bmod f\)
        ys = iterate (\y -> (y * xq) `modP` f) 1
    in array ((0,0),(n-1,n-1))
       [ ((i,j), mij - d)
       | (j,xqj) <- zip [0..n-1] ys
       , (i,mij) <- zip [0..n-1] (coeffAsc xqj ++ repeat 0)
       , let d = if i == j then 1 else 0
       ]

-- 列基本変形を行う
-- 非 0 な列の index と、変形後の行列を返す
elim :: (Fractional k, Eq k) => Int -> Mat k -> ([Int],Mat k)
elim imax m = loop [] i0 m
  where
    b@((i0,j0),(_,jn)) = bounds m
    loop seen i m
      | i > imax = (seen,m)
      | otherwise = case [k | k <- [j0..jn] \\ seen, m!(i,k) /= 0] of
          [] -> loop seen (i+1) m
          k:_ -> loop (k:seen) (i+1) $ array b
                    [ ((i',j),v)
                    | (i',j) <- indices m
                    , let v | j /= k = m!(i',j) - m!(i',k)*m!(i,j)/m!(i,k)
                            | j == k = m!(i',k)
                    ]

-- Input: nonzero, monic, squarefree
berlekampBasis :: (FiniteField k, Eq k) => UniPoly k -> [UniPoly k]
berlekampBasis f
  = let n = degree' f
        m = betaMat f
        -- \(m'\)は\(m\)の拡大係数行列（\(m\)の下に単位行列をくっつけたもの）
        m' = array ((0,0),(2*n-1,n-1))
             (assocs m ++ [ ((i+n,j),v)
                          | (i,j) <- indices m
                          , let v = if i == j then 1 else 0
                          ])
        (ix,l) = elim (n-1) m'
    in [ fromCoeffAsc [l!(n+i,j) | i<-[0..n-1]]
       | j <- [0..n-1] \\ ix ]

-- Input: nonzero, monic, squarefree
-- Returns Nothing if f is already irreducible
berlekampOne :: (FiniteField k, Eq k, Random k, RandomGen g)
             => UniPoly k -> State g (Maybe (UniPoly k))
berlekampOne f | l == 1 = return Nothing -- f は既に既約
               | otherwise = Just <$> findOne -- 非自明な因数を探す
  where
    q = order (leadingCoefficient f)
    bs = berlekampBasis f -- Berlekamp部分代数の基底：\(b_1,\ldots,b_l\in\mathcal{B}\)
    l = length bs -- Berlekamp部分代数の次元：\(\dim\mathcal{B}\)
    findOne = do -- \(f\)の非自明な因数を見つけて返す関数
      -- \(\mathrm{cs}:=\{c_1,\ldots,c_l\}\)：\(\FiniteField_q\)の元をランダムに\(l\)個選ぶ
      cs <- sequence $ replicate l $ state random
      -- \(a:=c_1b_1+\cdots+c_lb_l\)：基底のランダムな線形結合
      let a = sum (zipWith scaleP cs bs)
          w = powMod a ((q-1) `div` 2) f -- \(a^{(q-1)/2} \bmod f\)
          f' = toMonic $ gcdP f (w-1)    -- \(f^*:=\gcd(f,a^{(q-1)/2}-1)\)
      if f' /= 1 && f' /= f
        then return f' -- \(f^*\ne1\)かつ\(f^*\ne f\)：\(f^*\)は\(f\)の非自明な因数である
        else findOne   -- \(f^*\)は非自明な因数ではなかった；やり直し

-- Input: nonzero, monic, squarefree
factorBerlekamp :: (FiniteField k, Eq k, Random k, RandomGen g)
                => UniPoly k -> g -> ([UniPoly k], g)
factorBerlekamp f = runState (loop f [])
  where loop f acc
          | degree' f == 0 = return acc -- \(f=1\)
          | otherwise = do -- \(f\ne1\):
              r <- berlekampOne f -- 非自明な因数を探す
              case r of
                Nothing -> return (f:acc) -- 非自明な因数はない：既約
                Just f' -> do -- 非自明な因数\(f^*\)が見つかった
                  acc' <- loop f' acc     -- \(f^*\)を再帰的に因数分解する
                  loop (f `divP` f') acc' -- \(f/f^*\)を再帰的に因数分解する

factorBerlekampIO :: (FiniteField k, Eq k, Random k)
                  => UniPoly k -> IO [UniPoly k]
factorBerlekampIO = getStdRandom . factorBerlekamp
