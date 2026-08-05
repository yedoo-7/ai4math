import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 18：(2015·浙江高考) 在 △ABC 中，内角 A,B,C 所对的边分别为 a,b,c，
已知 A=π/4，b²-a²=(1/2)c²。
(1) 求 tanC 的值；
(2) 若 △ABC 的面积为 3，求 b。

【解法】
(1) 由余弦定理 a²=b²+c²-√2 bc，故 b²-a²=√2 bc-c²=(1/2)c²，得 √2 b=(3/2)c；
    由正弦定理与余弦定理算得 cosC=1/√5，sinC=2/√5，故 tanC=2。
(2) tanC=2 ⇒ sinC=2/√5, cosC=1/√5；sinB=sin(A+C)=(√2/2)(cosC+sinC)；
    由正弦定理及面积 S=(1/2)bc sinA=3 解得 R²=5/2，从而 b=2R sinB=3。
-/



/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem18

variable (A B C a b c S R : ℝ)

include R in
set_option maxHeartbeats 1000000 in
/-- (1) tanC = 2。 -/
theorem part1
    (hc : 0 < c)
    (hA : A = Real.pi / 4)
    (hcond : b ^ 2 - a ^ 2 = 1 / 2 * c ^ 2) :
    Real.tan C = 2 := by
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsc := tri_sine c R C
  have hcosA := tri_cos a b c A
  have hcosC := tri_cos c a b C
  have hcosAval : Real.cos A = Real.sqrt 2 / 2 := by rw [hA, Real.cos_pi_div_four]
  have hsinAval : Real.sin A = Real.sqrt 2 / 2 := by rw [hA, Real.sin_pi_div_four]
  rw [hcosAval] at hcosA
  have s2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hkey : Real.sqrt 2 * b = 3 / 2 * c := by
    have hcne : c ≠ 0 := ne_of_gt hc
    have h1 : (Real.sqrt 2 * b) * c = (3 / 2 * c) * c := by nlinarith [hcosA, hcond, s2]
    exact mul_right_cancel₀ hcne h1
  have hab_cosC : 2 * a * b * Real.cos C = 3 / 4 * c ^ 2 := by nlinarith [hcosC, hcosA, hkey, s2]
  have ha' : a = R * Real.sqrt 2 := by rw [hsa, hsinAval]; ring
  have hab_val : a * b = 3 * R * c / 2 := by rw [ha']; nlinarith [hkey, s2]
  have hsinC : Real.sin C = c / (2 * R) := by
    have hRne : (2 * R) ≠ 0 := by positivity
    rw [eq_div_iff hRne]; nlinarith [hsc]
  have hmul : a * b * Real.cos C = 3 * R * c / 2 * Real.cos C := by rw [hab_val]
  have hcosCval : Real.cos C = c / (4 * R) := by
    have h3 : 3 * R * c * Real.cos C = 3 / 4 * c ^ 2 := by nlinarith [hab_cosC, hmul]
    have hRne : (4 * R) ≠ 0 := by positivity
    rw [eq_div_iff hRne]; nlinarith [h3, hc, hR]
  rw [Real.tan_eq_sin_div_cos, hsinC, hcosCval]
  field_simp
  norm_num

include B R b c in
set_option maxHeartbeats 1000000 in
/-- (2) b = 3。 -/
theorem part2
    (hC0 : 0 < C) (hCpi : C < Real.pi / 2)
    (hA : A = Real.pi / 4)
    (htanC : Real.tan C = 2)
    (hSval : S = 3) :
    b = 3 := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have harea := tri_area S b c A
  have hsinAval : Real.sin A = Real.sqrt 2 / 2 := by rw [hA, Real.sin_pi_div_four]
  have s2 := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have s5 := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have s5pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have hcosCpos : 0 < Real.cos C := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hCpi⟩
  have htan2 : Real.sin C = 2 * Real.cos C := by
    rw [Real.tan_eq_sin_div_cos, div_eq_iff (ne_of_gt hcosCpos)] at htanC; linarith [htanC]
  have hcosC : Real.cos C = 1 / Real.sqrt 5 := by
    have hpyth := Real.sin_sq_add_cos_sq C
    rw [htan2] at hpyth
    rw [eq_div_iff (ne_of_gt s5pos)]
    nlinarith [hpyth, hcosCpos, s5, s5pos]
  have hsinC : Real.sin C = 2 / Real.sqrt 5 := by rw [htan2, hcosC]; ring
  have hsinB : Real.sin B = (Real.sqrt 2 / 2) * (Real.cos C + Real.sin C) := by
    rw [show B = Real.pi - (Real.pi / 4 + C) by linarith, Real.sin_pi_sub, Real.sin_add]; norm_num; ring
  rw [hcosC, hsinC] at hsinB
  have hR2 : R ^ 2 = 5 / 2 := by
    rw [hsb, hsc, hsinAval, hsinB, hsinC] at harea
    rw [hSval] at harea
    have hne : Real.sqrt 5 ≠ 0 := ne_of_gt s5pos
    field_simp at harea
    nlinarith [harea, s2, s5, s5pos, hR.le]
  have hb2 : b ^ 2 = 9 := by
    rw [hsb, hsinB]
    have hne : Real.sqrt 5 ≠ 0 := ne_of_gt s5pos
    field_simp
    nlinarith [hR2, s2, s5]
  have hbpos : 0 < b := by
    rw [hsb, hsinB]
    have h1 : (0:ℝ) < Real.sqrt 2 / 2 * (1 / Real.sqrt 5 + 2 / Real.sqrt 5) := by positivity
    exact mul_pos (mul_pos two_pos hR) h1
  nlinarith [hb2, hbpos, sq_nonneg (b - 3)]

end Problem18
