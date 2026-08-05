import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

open Real

/-
题目 12：(2015·浙江高考) 在 △ABC 中，内角 A,B,C 所对的边分别为 a,b,c，已知 tan(π/4+A)=2。
(1) 求 sin2A/(sin2A+cos²A) 的值；
(2) 若 B=π/4，a=3，求 △ABC 的面积。

【解法】
(1) tan(π/4+A)=(1+tanA)/(1-tanA)=2 ⇒ tanA=1/3；
    sin2A/(sin2A+cos²A)=2tanA/(2tanA+1)=2/5。
(2) tanA=1/3 ⇒ sinA=1/√10, cosA=3/√10；由正弦定理 a=2R sinA=3 得 2R=3√10，
    sinC=sin(A+B)=2/√5，c=6√2，面积 S=(1/2)ac sinB=9。
-/



/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem12

variable (A B C a b c S R : ℝ)

/-- (1) sin2A/(sin2A+cos²A) = 2/5。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi / 4)
    (hcond : Real.tan (Real.pi / 4 + A) = 2) :
    Real.sin (2 * A) / (Real.sin (2 * A) + (Real.cos A) ^ 2) = 2 / 5 := by
  have htanA : Real.tan A = 1 / 3 := by
    rw [ Real.tan_add, Real.tan_pi_div_four ] at hcond;
    · grind +revert;
    · exact Or.inl ⟨ fun k => by cases k <;> ring_nf <;> norm_num <;> nlinarith [ Real.pi_pos ], fun k => by cases k <;> ring_nf <;> norm_num <;> nlinarith [ Real.pi_pos ] ⟩;
  rw [ Real.sin_two_mul, Real.tan_eq_sin_div_cos ] at *;
  grind

include C R c S in
/-- (2) 面积 S = 9。 -/
theorem part2
    (htanA : Real.tan A = 1 / 3)
    (hB : B = Real.pi / 4)
    (haval : a = 3) :
    S = 9 := by
  have hsum := tri_angle_sum A B C
  have hsa := tri_sine a R A
  have hsc := tri_sine c R C
  have harea := tri_area S a c B
  rw [ ← eq_sub_iff_add_eq' ] at hsum;
  simp_all +decide [ Real.tan_eq_sin_div_cos ];
  norm_num [ Real.sin_add ] at *;
  grind

end Problem12
