import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 17：(2017·全国高考) △ABC 的内角 A,B,C 的对边分别为 a,b,c，
已知 sin(A+C) = 8 sin²(B/2)。
(1) 求 cosB；
(2) 若 a+c=6，△ABC 的面积为 2，求 b。

【解法】
(1) sin(A+C)=sinB；8 sin²(B/2)=4(1-cosB)。故 sinB=4(1-cosB)，平方化简得 cosB=15/17。
(2) cosB=15/17 ⇒ sinB=8/17；面积 (1/2)ac sinB=2 ⇒ ac=17/2；
    b²=(a+c)²-2ac(1+cosB)=36-32=4，故 b=2。
-/



/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 半角公式：8 sin²(B/2) = 4(1 - cosB)。 -/
axiom tri_half (B : ℝ) :
    8 * (Real.sin (B / 2)) ^ 2 = 4 * (1 - Real.cos B)

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem17

variable (A B C a b c S : ℝ)

include A C in
/-- (1) cosB = 15/17。 -/
theorem part1
    (hB0 : 0 < B) (hBpi : B < Real.pi)
    (hcond : Real.sin (A + C) = 8 * (Real.sin (B / 2)) ^ 2) :
    Real.cos B = 15 / 17 := by
  have hsum := tri_angle_sum A B C
  have hhalf := tri_half B
  rw [ show A + C = Real.pi - B by linarith, Real.sin_pi_sub ] at hcond;
  nlinarith [ Real.sin_sq_add_cos_sq B, Real.sin_pos_of_pos_of_lt_pi hB0 hBpi ]

/-- (2) b = 2。 -/
theorem part2
    (hb : 0 < b)
    (hcos : Real.cos B = 15 / 17)
    (hsin : Real.sin B = 8 / 17)
    (hac : a + c = 6)
    (hSval : S = 2) :
    b = 2 := by
  have hcosB := tri_cos b a c B
  have harea := tri_area S a c B
  rw [ ← sq_eq_sq₀ hb.le ];
  · grind;
  · norm_num

end Problem17
