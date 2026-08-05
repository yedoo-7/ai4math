import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

open Real

/-
题目 9：在 △ABC 中，内角 A,B,C 的对边分别为 a,b,c，且 sin2A/a = cosB/b + cosC/c。
(1) 求证：tanA = 2 sinB sinC；
(2) 若 c² - (3/2)bc = a² - b²，求 cosB cosC 的值。

【解法】
(1) 由正弦定理 2cosA = sinA/(sinB sinC)，故 2 sinB sinC cosA = sinA，cosA≠0，得 tanA = 2 sinB sinC。
(2) 由 c²-(3/2)bc=a²-b² 得 b²+c²-a²=(3/2)bc，由余弦定理 cosA=3/4，sinA=√7/4，tanA=√7/3，
    由 (1) sinB sinC=√7/6；又 cos(B+C)=-3/4，故 cosB cosC = √7/6 - 3/4。
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

namespace Problem9

variable (A B C a b c R : ℝ)

include R in
/-- (1) tanA = 2 sinB sinC。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hB0 : 0 < B) (hBpi : B < Real.pi)
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hcond : Real.sin (2 * A) * (b * c)
        = a * (c * Real.cos B + b * Real.cos C)) :
    Real.tan A = 2 * Real.sin B * Real.sin C := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  rw [ Real.tan_eq_sin_div_cos, div_eq_iff ];
  · simp_all +decide [ Real.sin_two_mul ];
    rw [ show A = Real.pi - B - C by linarith ] ; norm_num [ Real.sin_sub, Real.cos_sub ] ; ring_nf;
    have h_div : 4 * Real.cos A * Real.sin B * Real.sin C = 2 * Real.sin C * Real.cos B + 2 * Real.sin B * Real.cos C := by
      exact mul_left_cancel₀ ( show 2 * R ^ 2 * sin A ≠ 0 by exact mul_ne_zero ( mul_ne_zero two_ne_zero ( pow_ne_zero 2 hR.ne' ) ) ( ne_of_gt ( Real.sin_pos_of_pos_of_lt_pi hA0 hApi ) ) ) ( by linarith );
    rw [ show A = Real.pi - B - C by linarith ] at h_div ; norm_num [ Real.sin_sub, Real.cos_sub ] at h_div ; nlinarith [ Real.sin_pos_of_pos_of_lt_pi hB0 hBpi, Real.sin_pos_of_pos_of_lt_pi hC0 hCpi ] ;
  · contrapose! hcond;
    have hA : A = Real.pi / 2 := by
      rw [ ← Real.arccos_zero, ← hcond, Real.arccos_cos ] <;> linarith;
    norm_num [ hA, Real.sin_two_mul ];
    exact ⟨ by rw [ hsa ] ; exact ne_of_gt ( mul_pos ( mul_pos two_pos hR ) ( Real.sin_pos_of_pos_of_lt_pi hA0 hApi ) ), by rw [ hsb, hsc ] ; exact ne_of_gt ( add_pos ( mul_pos ( mul_pos two_pos hR |> mul_pos <| Real.sin_pos_of_pos_of_lt_pi hC0 hCpi ) ( Real.cos_pos_of_mem_Ioo ⟨ by linarith, by linarith ⟩ ) ) ( mul_pos ( mul_pos two_pos hR |> mul_pos <| Real.sin_pos_of_pos_of_lt_pi hB0 hBpi ) ( Real.cos_pos_of_mem_Ioo ⟨ by linarith, by linarith ⟩ ) ) ) ⟩

include a B C in
/-- (2) cosB cosC = √7/6 - 3/4。 -/
theorem part2
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hb : 0 < b) (hc : 0 < c)
    (htan : Real.tan A = 2 * Real.sin B * Real.sin C)
    (hcond : c ^ 2 - 3 / 2 * (b * c) = a ^ 2 - b ^ 2) :
    Real.cos B * Real.cos C = Real.sqrt 7 / 6 - 3 / 4 := by
  have hsum := tri_angle_sum A B C
  have hcosA := tri_cos a b c A
  have hcosA_val : Real.cos A = 3 / 4 := by
    nlinarith [ mul_pos hb hc ];
  have hsinA_val : Real.sin A = Real.sqrt 7 / 4 := by
    nlinarith only [ Real.sin_sq_add_cos_sq A, Real.sin_pos_of_pos_of_lt_pi hA0 hApi, Real.sqrt_nonneg 7, Real.sq_sqrt ( show 0 ≤ 7 by norm_num ), hcosA_val ];
  have htanA_val : Real.tan A = Real.sqrt 7 / 3 := by
    rw [ Real.tan_eq_sin_div_cos, hsinA_val, hcosA_val ] ; ring_nf;
  have hcosBC : Real.cos (B + C) = -Real.cos A := by
    rw [ ← Real.cos_pi_sub, ← hsum ] ; ring_nf;
  have hcosBC_val : Real.cos (B + C) = -3 / 4 := by
    linarith
  have hcosBC_eq : Real.cos B * Real.cos C - Real.sin B * Real.sin C = -3 / 4 := by
    rw [ ← hcosBC_val, Real.cos_add ]
  linarith [htan]

end Problem9
