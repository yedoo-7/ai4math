import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Cases

open Real

/-
题目 19：在 △ABC 中，角 A,B,C 的对边分别为 a,b,c，已知 3cos(B-C) - 1 = 6 cosB cosC。
(1) 求 cosA 的值；
(2) 若 a=3，△ABC 的面积为 2√2，求 b,c 的边长。

【解法】
(1) 展开 cos(B-C) 化简得 3cos(B+C)=-1 ⇒ cos(B+C)=-1/3；又 B+C=π-A，故 cosA=1/3。
(2) cosA=1/3 ⇒ sinA=2√2/3；面积 (1/2)bc sinA=2√2 ⇒ bc=6；
    a²=b²+c²-2bc cosA ⇒ b²+c²=13；联立得 {b,c}={2,3}。
-/


/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem19

variable (A B C a b c S : ℝ)

include A in
/-- (1) cosA = 1/3。 -/
theorem part1
    (hcond : 3 * Real.cos (B - C) - 1 = 6 * Real.cos B * Real.cos C) :
    Real.cos A = 1 / 3 := by
  have hsum := tri_angle_sum A B C
  rw [ show A = Real.pi - B - C by linarith ] ; norm_num [ Real.cos_sub ] at * ; linarith;

/-- (2) 边长 (b,c) = (3,2) 或 (2,3)。 -/
theorem part2
    (hb : 0 < b) (hc : 0 < c)
    (hcos : Real.cos A = 1 / 3)
    (hsin : Real.sin A = 2 * Real.sqrt 2 / 3)
    (haval : a = 3)
    (hSval : S = 2 * Real.sqrt 2) :
    (b = 3 ∧ c = 2) ∨ (b = 2 ∧ c = 3) := by
  have hcosA := tri_cos a b c A
  have harea := tri_area S b c A
  have hbc : b * c = 6 := by
    grind
  have hb2c2 : b^2 + c^2 = 13 := by
    subst_vars; nlinarith;
  have hbplusc : b + c = 5 := by
    nlinarith only [ hb, hc, hbc, hb2c2 ]
  have hbminusc : b - c = 1 ∨ b - c = -1 := by
    grind +splitImp
  cases' hbminusc with hbc_pos hbc_neg;
  · exact Or.inl ⟨ by linarith, by linarith ⟩;
  · exact Or.inr ⟨ by linarith, by linarith ⟩

end Problem19
