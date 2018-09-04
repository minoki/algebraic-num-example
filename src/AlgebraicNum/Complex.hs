{-# LANGUAGE DeriveFunctor #-}
module AlgebraicNum.Complex where
import AlgebraicNum.Class

data Complex a = MkComplex !a !a
               deriving (Eq,Show,Functor)

fromReal :: (Num a) => a -> Complex a
fromReal x = MkComplex x 0

fromImag :: (Num a) => a -> Complex a
fromImag y = MkComplex 0 y

realPart, imagPart :: Complex a -> a
realPart (MkComplex x _) = x
imagPart (MkComplex _ y) = y

conjugate :: (Num a) => Complex a -> Complex a
conjugate (MkComplex x y) = MkComplex x (- y)

instance (Num a) => Num (Complex a) where
  -- 'RealFrac a' is not required!
  negate (MkComplex x y) = MkComplex (negate x) (negate y)
  MkComplex x y + MkComplex x' y' = MkComplex (x + x') (y + y')
  MkComplex x y - MkComplex x' y' = MkComplex (x - x') (y - y')
  MkComplex x y * MkComplex x' y' = MkComplex (x * x' - y * y') (x * y' + y * x')
  fromInteger n = MkComplex (fromInteger n) 0
  abs = undefined
  signum = undefined

instance (Fractional a) => Fractional (Complex a) where
  recip (MkComplex x y) = let r = recip (x^2 + y^2)
                          in MkComplex (x * r) (negate y * r)
  fromRational x = MkComplex (fromRational x) 0

instance (IntegralDomain a) => IntegralDomain (Complex a) where
  divide (MkComplex x y) (MkComplex x' y') = let d = x'^2 + y'^2
                                             in MkComplex ((x * x' + y * y') `divide` d) ((y * x' - x * y') `divide` d)
