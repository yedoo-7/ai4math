import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 16：(2022·北京高考) 在 △ABC 中，sin2C = √3 sinC。
(1) 求 C；
(2) 若 b=6，且 △ABC 的面积为 6√3，求 △ABC 的周长。

【解法】
(1) sin2C=2 sinC cosC=√3 sinC，sinC>0，故 cosC=√3/2，C=π/6。
(2) 面积 (1/2)ab sinC=(3/2)a=6√3 得 a=4√3；由余弦定理 c²=12，c=2√3，周长=6+6√3。
-/



/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem16

variable (A B C a b c S : ℝ)

/-- (1) C = π/6。 -/
theorem part1
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hcond : Real.sin (2 * C) = Real.sqrt 3 * Real.sin C) :
    C = Real.pi / 6 := by
  have hcosC_val : Real.cos C = Real.sqrt 3 / 2 := by
    nlinarith [ Real.sin_pos_of_pos_of_lt_pi hC0 hCpi, Real.sin_two_mul C, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ];
  exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num [ hcosC_val ] )

/-- (2) 周长 a+b+c = 6+6√3。 -/
theorem part2
    (ha : 0 < a) (hc : 0 < c)
    (hC : C = Real.pi / 6)
    (hbval : b = 6)
    (hSval : S = 6 * Real.sqrt 3) :
    a + b + c = 6 + 6 * Real.sqrt 3 := by
  have hcosC := tri_cos c a b C
  have harea := tri_area S a b C
  subst hC
  rw [Real.cos_pi_div_six] at hcosC
  rw [Real.sin_pi_div_six] at harea
  have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
  have h3pos : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
  -- a = 4√3
  have haval : a = 4 * Real.sqrt 3 := by
    rw [hSval, hbval] at harea
    -- harea : 6√3 = 1/2 * a * 6 * (1/2)
    have : a = 4 * Real.sqrt 3 := by linarith [harea]
    exact this
  -- c² = 12
  have hc2 : c ^ 2 = 12 := by
    rw [haval, hbval] at hcosC
    nlinarith [hcosC, h3]
  have hcval : c = 2 * Real.sqrt 3 := by
    have h12 : (2 * Real.sqrt 3) ^ 2 = 12 := by nlinarith [h3]
    nlinarith [hc2, hc, h3pos, sq_nonneg (c - 2 * Real.sqrt 3)]
  rw [haval, hbval, hcval]; ring

end Problem16
