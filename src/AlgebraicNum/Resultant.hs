module AlgebraicNum.Resultant where
import AlgebraicNum.UniPoly

-- | 体係数多項式の終結式
resultantOverField :: (Eq a, Fractional a) => UniPoly a -> UniPoly a -> a
resultantOverField f g
  | (f == 0 && degree g == Just 0) || (degree f == Just 0 && g == 0) = 1
  | f == 0 || g == 0 = 0
  | degree' f == 0 = leadingCoefficient f ^ degree' g
  | otherwise = loop 1 f g
  where
    -- invariant: loop p f g = p * resultantOverField f g, f /= 0, g /= 0
    loop p f g
      | degree' g == 0 = p * lc_g ^ degree' f
      | r == 0 = 0
      | otherwise = let !s = degree' g * degree' f
                        !j = degree' f - degree' r
                    in loop ((-1)^s * lc_g^j * p) g r
      where r = f `modP` g
            lc_g = leadingCoefficient g
