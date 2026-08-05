import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 4：(2024·浙江嘉兴二模) 在 △ABC 中，内角 A,B,C 所对的边分别是 a,b,c，
已知 2cosA - 3cos2A = 3。
(1) 求 cosA 的值；
(2) 若 △ABC 为锐角三角形，2b=3c，求 sinC 的值。

【解法】
(1) cos2A=2cos²A-1，代入化简得 2cosA(1-3cosA)=0 ⇒ cosA=0 或 cosA=1/3。
(2) 锐角三角形中 cosA≠0，故 cosA=1/3，sinA=2√2/3；2b=3c 由正弦定理得 2sinB=3sinC，
    又 sinB=sin(A+C)，化简得 4√2 cosC=7 sinC；结合 sin²C+cos²C=1 解得 sinC=4√2/9。
-/

/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

namespace Problem4

variable (A B C a b c R : ℝ)

/-- (1) cosA = 1/3 或 cosA = 0。 -/
theorem part1
    (hcond : 2 * Real.cos A - 3 * Real.cos (2 * A) = 3) :
    Real.cos A = 1 / 3 ∨ Real.cos A = 0 := by
  exact Classical.or_iff_not_imp_right.2 fun h => mul_left_cancel₀ h <| by rw [ Real.cos_two_mul ] at hcond; linarith;

include B R in
/-- (2) sinC = 4√2/9。 -/
theorem part2
    (hC0 : 0 < C) (hCpi : C < Real.pi / 2)
    (hcosA : Real.cos A = 1 / 3)
    (hsinA : Real.sin A = 2 * Real.sqrt 2 / 3)
    (hcond : 2 * b = 3 * c) :
    Real.sin C = 4 * Real.sqrt 2 / 9 := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have hsinBC : 2 * Real.sin B = 3 * Real.sin C := by
    grind;
  rw [ show B = Real.pi - A - C by linarith ] at hsinBC ; norm_num [ Real.sin_sub, hsinA, hcosA ] at hsinBC;
  nlinarith only [ Real.sin_sq_add_cos_sq C, Real.sin_pos_of_pos_of_lt_pi hC0 ( by linarith ), Real.cos_pos_of_mem_Ioo ⟨ by linarith, hCpi ⟩, hsinBC, Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ]

end Problem4
