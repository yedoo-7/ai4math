import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 2：(2024·湖南常德三模) 在 △ABC 中，内角 A,B,C 的对边分别为 a,b,c，
且 sin²A + sin²B + sinA sinB = sin²C。
(1) 求角 C；
(2) 若 a,b,c 成等差数列，且 △ABC 的面积为 15√3/4，求 △ABC 的周长。

【解法】
(1) 由正弦定理将条件化为 a²+b²+ab=c²，再由余弦定理 cosC=-1/2，得 C=2π/3。
(2) 由等差得 a+c=2b；由 C=2π/3 与余弦定理得 c²=a²+b²+ab；
    由面积 (1/2)ab sinC=15√3/4 得 ab=15；联立解得 a=3,b=5,c=7，周长=15。
-/



/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem2

variable (A B C a b c S R : ℝ)

include a b c R in
/-- (1) C = 2π/3。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hB0 : 0 < B) (hBpi : B < Real.pi)
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hcond : (Real.sin A) ^ 2 + (Real.sin B) ^ 2 + Real.sin A * Real.sin B
        = (Real.sin C) ^ 2) :
    C = 2 * Real.pi / 3 := by
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have hcosC := tri_cos c a b C
  have hsinC : Real.sin C ^ 2 = Real.sin A ^ 2 + Real.sin B ^ 2 - 2 * Real.sin A * Real.sin B * Real.cos C := by
    exact mul_left_cancel₀ ( pow_ne_zero 2 hR.ne' ) ( by subst_vars; linarith );
  have hcosC_val : Real.cos C = -1 / 2 := by
    nlinarith [ mul_pos ( Real.sin_pos_of_pos_of_lt_pi hA0 hApi ) ( Real.sin_pos_of_pos_of_lt_pi hB0 hBpi ) ];
  exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num [ hcosC_val, Real.cos_two_mul, mul_div_assoc ] )

/-- (2) 周长 a+b+c = 15。 -/
theorem part2
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hC : C = 2 * Real.pi / 3)
    (harith : a + c = 2 * b)
    (hSval : S = 15 * Real.sqrt 3 / 4) :
    a + b + c = 15 := by
  have hcosC := tri_cos c a b C
  have harea := tri_area S a b C
  have hsinC : Real.sin C = Real.sqrt 3 / 2 := by
    rw [hC, show (2:ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  have hcosCval : Real.cos C = -(1 / 2) := by
    rw [hC, show (2:ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  rw [hsinC] at harea
  rw [hcosCval] at hcosC
  have hsqrt3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
  -- 由面积公式与题设面积得 ab = 15
  have hab : a * b = 15 := by
    have h1 : S = a * b * Real.sqrt 3 / 4 := by rw [harea]; ring
    rw [hSval] at h1
    have h2 : a * b * Real.sqrt 3 = 15 * Real.sqrt 3 := by linarith [h1]
    exact mul_right_cancel₀ (ne_of_gt hsqrt3) h2
  -- 由余弦定理：c² = a²+b²+ab
  have hc2 : c ^ 2 = a ^ 2 + b ^ 2 + a * b := by rw [hcosC]; ring
  have hb5 : b = 5 := by nlinarith [hab, hc2, harith, hb, ha, hc, sq_nonneg (b - 5)]
  have ha3 : a = 3 := by nlinarith [hab, hb5, ha]
  have hc7 : c = 7 := by linarith [harith, ha3, hb5]
  linarith [ha3, hb5, hc7]

end Problem2
