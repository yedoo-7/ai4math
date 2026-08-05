import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

open Real

/-
题目 1：(2024·江苏一模) 记 △ABC 的内角 A,B,C 的对边分别为 a,b,c，已知 2cosB+1 = c/a。
(1) 证明：B = 2A；
(2) 若 sinA = √2/4，b = √14，求 △ABC 的周长。

【解法】
(1) (2cosB+1)sinA = sinC = sin(A+B) = sinA cosB + cosA sinB
    ⇒ sinA = cosA sinB - sinA cosB = sin(B-A)。
    因 A,B∈(0,π)，由 sinA=sin(B-A) 解得 B-2A=0，即 B=2A。
(2) B=2A 且 C>0 ⇒ A<π/3，A 为锐角，cosA=√14/4；
    sinB=sin2A=√7/4，cosB=3/4，sinC=sin(A+B)=5√2/8；
    由 b=2R sinB=√14 得 2R=4√2，故 a=2，c=5，周长 a+b+c=7+√14。
-/


/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

namespace Problem1

variable (A B C a b c R : ℝ)

include C R in
/-- (1) B = 2A。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hB0 : 0 < B) (hBpi : B < Real.pi)
    (hcond : (2 * Real.cos B + 1) * a = c) :
    B = 2 * A := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsc := tri_sine c R C
  -- From the given condition, we have $\sin A = \sin (B - A)$
  have h_sin_eq : Real.sin A = Real.sin (B - A) := by
    simp_all +decide [ Real.sin_sub ];
    rw [ show C = Real.pi - A - B by linarith ] at hcond ; norm_num [ Real.sin_sub ] at hcond ; nlinarith [ mul_pos hR ( Real.sin_pos_of_pos_of_lt_pi hA0 hApi ) ] ;
  rw [ Real.sin_eq_sin_iff ] at h_sin_eq;
  rcases h_sin_eq with ⟨ k, hk | hk ⟩ <;> rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ]

include C R in
/-- (2) 周长 a+b+c = 7+√14。 -/
theorem part2
    (hB2A : B = 2 * A)
    (hsinA : Real.sin A = Real.sqrt 2 / 4)
    (hbval : b = Real.sqrt 14) :
    a + b + c = 7 + Real.sqrt 14 := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  -- Compute $R$ using $b = 2R \cdot \sin B$
  have hR_val : R = 2 * Real.sqrt 2 := by
    simp_all +decide [ Real.sin_two_mul ];
    rw [ ← sq_eq_sq₀ ?_ ?_ ] <;> ring_nf <;> norm_num;
    · have := congr_arg ( · ^ 2 ) hbval ; ring_nf at this ; norm_num at this;
      rw [ Real.cos_sq' ] at this ; rw [ hsinA ] at this ; ring_nf at this ; norm_num at this ; linarith;
    · positivity;
  subst_vars; norm_num [ Real.sin_two_mul, Real.sin_add ] at *;
  rw [ show C = Real.pi - 3 * A by linarith ] ; rw [ Real.sin_pi_sub, Real.sin_three_mul ] ; ring_nf at * ; norm_num at * ;
  grind

end Problem1
