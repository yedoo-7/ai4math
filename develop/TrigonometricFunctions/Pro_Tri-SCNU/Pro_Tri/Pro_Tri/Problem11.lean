import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 11：(2016·全国高考) △ABC 的内角 A,B,C 的对边分别为 a,b,c，已知
2cosC(a·cosB + b·cosA) = c。
(1) 求角 C；
(2) 若 c=√7，△ABC 的面积为 3√3/2，求 △ABC 的周长。

【解法】
(1) 由射影定理 a·cosB + b·cosA = c，代入得 cosC=1/2，C∈(0,π)，C=π/3。
(2) 面积 (1/2)ab sinC=3√3/2 得 ab=6；由余弦定理 c²=a²+b²-ab=7 得 a²+b²=13，
    (a+b)²=25，a+b=5，周长 a+b+c=5+√7。
-/



/-- 射影定理：a·cosB + b·cosA = c。 -/
axiom tri_proj (a b c A B : ℝ) :
    a * Real.cos B + b * Real.cos A = c

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem11

variable (A B C a b c S : ℝ)

include A B in
/-- (1) C = π/3。 -/
theorem part1
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hc : 0 < c)
    (hcond : 2 * Real.cos C * (a * Real.cos B + b * Real.cos A) = c) :
    C = Real.pi / 3 := by
  have hproj := tri_proj a b c A B
  exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num; nlinarith )

/-- (2) 周长 a+b+c = 5+√7。 -/
theorem part2
    (ha : 0 < a) (hb : 0 < b)
    (hC : C = Real.pi / 3)
    (hcval : c = Real.sqrt 7)
    (hSval : S = 3 * Real.sqrt 3 / 2) :
    a + b + c = 5 + Real.sqrt 7 := by
  have hcosC := tri_cos c a b C
  have harea := tri_area S a b C
  subst hC
  rw [Real.cos_pi_div_three] at hcosC
  rw [Real.sin_pi_div_three] at harea
  have hsqrt3 : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num)
  -- ab = 6
  have hab : a * b = 6 := by
    rw [hSval] at harea
    have h7 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    nlinarith [harea, hsqrt3, h7]
  -- c² = 7
  have hc2 : c ^ 2 = 7 := by rw [hcval]; rw [Real.sq_sqrt (by norm_num)]
  -- a²+b² = 13
  have hab2 : a ^ 2 + b ^ 2 = 13 := by nlinarith [hcosC, hc2, hab]
  -- a+b = 5
  have habsum : a + b = 5 := by nlinarith [hab, hab2, ha, hb, sq_nonneg (a + b)]
  linarith [habsum, hcval]

end Problem11
