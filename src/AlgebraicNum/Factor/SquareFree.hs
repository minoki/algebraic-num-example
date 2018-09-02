module AlgebraicNum.Factor.SquareFree where
import AlgebraicNum.Class
import AlgebraicNum.UniPoly

-- naive squarefree factorization for characteristic 0
naiveSFF :: (Eq a, GCDDomain a) => UniPoly a -> [(UniPoly a,Int)]
naiveSFF 0 = [(0,1)]
naiveSFF f = doSFF (primitivePart f) where
  -- 原始多項式 f を再帰的に無平方分解する
  doSFF f | degree f == Just 0 = [] -- constant
          | degree f == degree p = u -- t = 1 の場合
          | otherwise = (t,1) : u
    where
      gcd_f_df = primitivePart $ gcdD f (diffP f)
      -- \(\gcd(f,f')=f_2f_3^2\cdots f_m^{m-1}\) とおく
      r = doSFF gcd_f_df  -- 無平方分解：\(\{(f_2,1),(f_3,2),\ldots,(f_m,m-1)\}\)
      u = map (\(g,i) -> (g,i+1)) r  -- \(\{(f_2,2),(f_3,3),\ldots,(f_m,m)\}\)
      p = gcd_f_df * product (map fst r) -- \(f_2^2 f_3^3\cdots f_m^m\)
      t = f `divide` p  -- \(f_1\)

-- squarefree factorization for characteristic 0
yunSFF :: (Eq a, GCDDomain a) => UniPoly a -> [(UniPoly a,Int)]
yunSFF 0 = [(0,1)]
yunSFF f = loop 1 (f `divide` u) (f' `divide` u) where
  f' = diffP f
  u = gcdD f f'
  loop !i v w
    | degree' v == 0 = []
    | h == 1 = loop (i+1) v s
    | otherwise = (h,i) : loop (i+1) (v `divide` h) (s `divide` h)
    where s = w - diffP v
          h = gcdD v s
