module AlgebraicNum.MultPoly where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly

-- multivariate polynomial
data MultPoly a = Poly !(UniPoly (MultPoly a))
                | Scalar !a
                deriving (Show)

-- R[multInd n][multInd (n-1)] ... [multInd 1][multInd 0]
multInd :: (Eq a, Num a) => Int -> MultPoly a
multInd 0 = Poly ind
multInd n | n > 0 = Poly $ constP $ multInd (n - 1)

multToUni :: (Eq a, Num a) => MultPoly a -> UniPoly (MultPoly a)
multToUni (Poly f) = f
multToUni (Scalar k) = constP (Scalar k)

multToScalar :: (Eq a, Num a) => MultPoly a -> Maybe a
multToScalar (Poly _) = Nothing
multToScalar (Scalar k) = Just k

instance (Eq a, Num a) => Eq (MultPoly a) where
  Poly f == Poly g = f == g
  Scalar k == Scalar l = k == l
  f == g = multToUni f == multToUni g

instance (Eq a, Num a) => Num (MultPoly a) where
  negate (Poly x) = Poly (negate x)
  negate (Scalar x) = Scalar (negate x)
  Scalar x + Scalar y = Scalar (x + y)
  f + g = Poly (multToUni f + multToUni g)
  Scalar x * Scalar y = Scalar (x * y)
  Poly x * Poly y = Poly (x * y)
  Poly x * k@(Scalar _) = Poly (scaleP k x)
  k@(Scalar _) * Poly y = Poly (scaleP k y)
  fromInteger k = Scalar (fromInteger k)
  abs = undefined
  signum = undefined

instance (Eq a, IntegralDomain a) => IntegralDomain (MultPoly a) where
  divide (Scalar x) (Scalar y) = Scalar (divide x y)
  divide (Poly f) (Poly g) = Poly (divide f g)
  divide (Poly f) k@(Scalar _) = Poly (unscaleP k f)
  divide k@(Scalar _) (Poly g) = Poly (divide (constP k) g)

instance (Eq a, GCDDomain a) => GCDDomain (MultPoly a) where
  gcdD (Scalar f) (Scalar g) = Scalar (gcdD f g)
  gcdD f g = Poly (gcdD (multToUni f) (multToUni g))
