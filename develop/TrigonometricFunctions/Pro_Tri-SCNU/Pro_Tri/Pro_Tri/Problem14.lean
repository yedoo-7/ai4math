import Mathlib.Analysis.Complex.Trigonometric

open Real

/-
题目 14：(2022·全国新II卷) 记 △ABC 的内角 A,B,C 的对边分别为 a,b,c，分别以 a,b,c 为
边长的三个正三角形的面积依次为 S1,S2,S3，已知 S1 - S2 + S3 = √3/2，sinB = 1/3。
(1) 求 △ABC 的面积；
(2) 若 sinA sinC = √2/3，求 b。

【解法】
(1) 正三角形面积 Si=√3/4·(边)²，S1-S2+S3=√3/4(a²-b²+c²)=√3/2 ⇒ a²+c²-b²=2；
    由余弦定理 ac cosB=1，又 sinB=1/3 ⇒ cosB=2√2/3，ac=3√2/4，面积 S=(1/2)ac sinB=√2/8。
(2) b² = ac·sin²B/(sinA sinC)=1/4，故 b=1/2。
-/



/-- 正三角形面积公式：以 x 为边长的正三角形面积为 (√3/4)·x²。 -/
axiom tri_eqtri_area (S x : ℝ) : S = Real.sqrt 3 / 4 * x ^ 2

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

namespace Problem14

variable (A B C a b c S S1 S2 S3 R : ℝ)

include b S in
/-- (1) △ABC 的面积 S = √2/8。 -/
theorem part1
    (ha : 0 < a) (hc : 0 < c)
    (hsinB : Real.sin B = 1 / 3)
    (hsum : S1 - S2 + S3 = Real.sqrt 3 / 2) :
    S = Real.sqrt 2 / 8 := by
  have hS1 := tri_eqtri_area S1 a
  have hS2 := tri_eqtri_area S2 b
  have hS3 := tri_eqtri_area S3 c
  have hcosB := tri_cos b a c B
  have harea := tri_area S a c B
  have hac_cosB : a * c * Real.cos B = 1 := by
    grind +splitImp;
  have hcosB_val : Real.cos B = 2 * Real.sqrt 2 / 3 := by
    have := Real.sin_sq_add_cos_sq B ; norm_num [ hsinB ] at this;
    nlinarith only [ show 0 < Real.cos B from by nlinarith [ mul_pos ha hc ], this, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, hac_cosB ];
  grind

include R b in
/-- (2) b = 1/2。 -/
theorem part2
    (hsinB : Real.sin B = 1 / 3)
    (hac : a * c = 3 * Real.sqrt 2 / 4)
    (hAC : Real.sin A * Real.sin C = Real.sqrt 2 / 3) :
    b = 1 / 2 := by
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  rw [ hsa, hsc ] at hac;
  nlinarith [ show 0 < Real.sqrt 2 * R ^ 2 by positivity, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

end Problem14
