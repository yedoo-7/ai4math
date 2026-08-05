import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 10：(2022·浙江高考) 在 △ABC 中，角 A,B,C 的对边分别为 a,b,c，已知 4a=√5 c，cosC=3/5。
(1) 求 sinA 的值；
(2) 若 b=11，求 △ABC 的面积。

【解法】
(1) 由 cosC=3/5, C∈(0,π) 得 sinC=4/5；由正弦定理 a sinC=c sinA 及 4a=√5 c 得 sinA=√5/5。
(2) 由余弦定理 c²=a²+b²-2ab cosC，结合 4a=√5 c 与 b=11 得 a=5，面积 S=(1/2)ab sinC=22。
-/



/-- 正弦定理（交叉相乘形式）：a·sinC = c·sinA。 -/
axiom tri_sine_cross (a c A C : ℝ) : a * Real.sin C = c * Real.sin A

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem10

variable (A B C a b c S : ℝ)

include A in
/-- (1) sinA = √5/5。 -/
theorem part1
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hc : 0 < c)
    (hcos : Real.cos C = 3 / 5)
    (hcond : 4 * a = Real.sqrt 5 * c) :
    Real.sin A = Real.sqrt 5 / 5 := by
  have hsin := tri_sine_cross a c A C
  have hsinC : Real.sin C = 4 / 5 := by
    nlinarith [ Real.sin_sq_add_cos_sq C, Real.sin_pos_of_pos_of_lt_pi hC0 hCpi ];
  grind

include S in
/-- (2) 面积 S = 22。 -/
theorem part2
    (ha : 0 < a) (hb : 0 < b)
    (hcos : Real.cos C = 3 / 5)
    (hsinC : Real.sin C = 4 / 5)
    (hbval : b = 11)
    (hcond : 4 * a = Real.sqrt 5 * c) :
    S = 22 := by
  have hcosC := tri_cos c a b C
  have harea := tri_area S a b C
  subst_vars; nlinarith [ Real.sqrt_nonneg 5, Real.sq_sqrt ( show 0 ≤ 5 by norm_num ) ] ;

end Problem10
