module AlgebraicNum.Factor
  (PolynomialFactorization(..)
  ,yunSFF
  ) where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly
import AlgebraicNum.AlgReal
import AlgebraicNum.AlgNum
import AlgebraicNum.Factor.SquareFree
import AlgebraicNum.Factor.CantorZassenhaus (factorCZ)
import AlgebraicNum.Factor.Hensel (factorHensel)
import System.Random (RandomGen,getStdRandom)
import Control.Monad.State (runState,state)
import Data.FiniteField
import Data.Ratio
import Data.List
import GHC.TypeLits (KnownNat)

class PolynomialFactorization a where
  -- Assume that the input is non-zero, primitive and square-free
  factorizeSFWithRandomGen :: (RandomGen g) => UniPoly a -> g -> ([UniPoly a], g)
  factorizeSFIO :: UniPoly a -> IO [UniPoly a]
  factorizeSFIO = getStdRandom . factorizeSFWithRandomGen

instance PolynomialFactorization Integer where
  factorizeSFWithRandomGen = factorHensel

instance (Integral a, GCDDomain a, PolynomialFactorization a) => PolynomialFactorization (Ratio a) where
  factorizeSFWithRandomGen f = runState $ do
    let commonDenominator = foldl' (\a b -> Prelude.lcm a (denominator b)) 1 (coeffAsc f)
        pp = primitivePart $ mapCoeff (\x -> numerator x * (commonDenominator `Prelude.div` denominator x)) f
    map (toMonic . mapCoeff fromIntegral) <$> state (factorizeSFWithRandomGen pp)

instance PolynomialFactorization AlgReal where
  factorizeSFWithRandomGen f = runState $ return $ do
    (a,i) <- rootsA f
    if i /= 1
      then error "factorizeSF: input was not squarefree"
      else case a of
             FromReal a -> return (ind - constP a)
             a | imagPartA a > 0 -> return (ind^2 - scaleP (2 * realPartA a) ind + constP (squaredMagnitudeA a))
               | otherwise -> []

instance PolynomialFactorization AlgNum where
  factorizeSFWithRandomGen f = runState $ return $ do
    (a,i) <- rootsAN f
    -- i must be 1
    if i /= 1
      then error "factorizeSF: input was not squarefree"
      else return (ind - constP a)

instance (KnownNat p) => PolynomialFactorization (PrimeField p) where
  factorizeSFWithRandomGen = factorCZ
