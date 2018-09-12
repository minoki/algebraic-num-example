module AlgebraicNum.PartialFraction where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly
import AlgebraicNum.Factor
import AlgebraicNum.Fraction
import Control.Monad
import Control.Monad.State (State,runState,state)
import System.Random (RandomGen,getStdRandom)

partialFractionDecomposition
  :: (Eq a, GCDDomain a, Fractional a, PolynomialFactorization a, RandomGen g)
  => Fraction (UniPoly a) -> g -> (([([UniPoly a],UniPoly a)],UniPoly a), g)
partialFractionDecomposition (f :%% g) = runState $ do
  -- \(g\) は原始多項式と仮定する
  ys <- fmap concat $ forM (yunSFF g) $ \(h,i) -> do
    -- \(h\): 無平方多項式
    ks <- state (factorizeSFWithRandomGen h)
    return [(k,i) | k <- ks]
  -- ys = [(\(g_1\),\(i_1\)),(\(g_2\),\(i_2\)),...], \(g = g_1^{i_1} g_2^{i_2} \cdots\)
  let (q,r) = f `divModD` g
      -- f = q * g + r, f / g = q + r / g
      terms = do
        (k,i) <- ys
        let h = k^i
            g' = g `divide` h -- \(g = h g'\)
            (u,_,t') = exEuclid h g' -- \(u=\pm1\)
            t = t' `divide` u
            -- \(s h + t g' = 1\)
            b = (r * t) `modD` h
            dev 0 _ = []
            dev j c = let (c',a) = c `divModD` g -- \(c = c' g + a\)
                      in a : dev (j - 1) c'
        return (dev i b, k)
  return (terms, q)

partialFractionDecompositionIO
  :: (Eq a, GCDDomain a, Fractional a, PolynomialFactorization a)
  => Fraction (UniPoly a) -> IO ([([UniPoly a],UniPoly a)],UniPoly a)
partialFractionDecompositionIO = getStdRandom . partialFractionDecomposition
