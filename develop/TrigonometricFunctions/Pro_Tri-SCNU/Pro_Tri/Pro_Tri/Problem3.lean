import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.NormNum.RealSqrt

open Real

/-
题目 3：(2024·浙江温州二模) 记 △ABC 的内角 A,B,C 所对的边分别为 a,b,c，已知 2c sinB = √2 b。
(1) 求 C；
(2) 若 tanA = tanB + tanC，a=2，求 △ABC 的面积。

【解法】
(1) 由正弦定理 2 sinC sinB = √2 sinB，sinB>0，得 sinC=√2/2，C∈(0,π)，C=π/4 或 3π/4。
(2) tanA = -tan(B+C) = tanB+tanC，得 tanB tanC = 2；又取 C=π/4（tanC=1），故 tanB=2。
    于是 sinB=2/√5；由正弦定理与 tanA=3 得 sinA=3/√10，c=2√5/3，面积 S=4/3。
-/



/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem3

variable (A B C a b c S R : ℝ)

include R in
/-- (1) C = π/4 或 C = 3π/4。 -/
theorem part1
    (hB0 : 0 < B) (hBpi : B < Real.pi)
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hcond : 2 * c * Real.sin B = Real.sqrt 2 * b) :
    C = Real.pi / 4 ∨ C = 3 * Real.pi / 4 := by
  have hR := tri_R_pos R
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have hsinB_pos : 0 < Real.sin B := by
    exact Real.sin_pos_of_pos_of_lt_pi hB0 hBpi
  have hR_pos : 0 < R := hR
  have hsinC_eq : 2 * Real.sin C = Real.sqrt 2 := by
    have h := hcond
    rw [hsb, hsc] at h
    have hpos : 0 < 2 * R * Real.sin B := mul_pos (mul_pos two_pos hR_pos) hsinB_pos
    have h2 : (2 * Real.sin C) * (2 * R * Real.sin B) = Real.sqrt 2 * (2 * R * Real.sin B) := by
      linear_combination h
    exact mul_right_cancel₀ (ne_of_gt hpos) h2
  obtain ⟨ k, hk ⟩ := Real.sin_eq_sin_iff.mp ( show Real.sin C = Real.sin ( Real.pi / 4 ) by norm_num; linarith );
  rcases hk with ( hk | hk ) <;> [ left; right ] <;> rcases k with ⟨ _ | k ⟩ <;> norm_num at hk <;> nlinarith [ Real.pi_pos ]

include R c S in
-- set_option maxHeartbeats 800000 in
/-- (2) 面积 S = 4/3。 -/
theorem part2
    (hA0 : 0 < A) (hApi : A < Real.pi / 2)
    (hB0 : 0 < B) (hBpi : B < Real.pi / 2)
    (hC : C = Real.pi / 4)
    (haval : a = 2)
    (hcond : Real.tan A = Real.tan B + Real.tan C) :
    S = 4 / 3 := by
  have hsum := tri_angle_sum A B C
  have hsa := tri_sine a R A
  have hsc := tri_sine c R C
  have harea := tri_area S a c B
  have h_tanB : Real.tan B = 2 := by
    have h_tan_sum : Real.tan A = -Real.tan (B + Real.pi / 4) := by
      rw [ ← Real.tan_pi_sub, ← hC, ← hsum ] ; ring_nf;
    rw [ Real.tan_add ] at h_tan_sum;
    · norm_num [ hcond, hC ] at h_tan_sum;
      nlinarith [ Real.tan_pos_of_pos_of_lt_pi_div_two hB0 hBpi, mul_div_cancel₀ ( tan B + 1 ) ( show ( 1 - tan B ) ≠ 0 from fun h => by norm_num [ h ] at h_tan_sum; linarith [ Real.tan_pos_of_pos_of_lt_pi_div_two hB0 hBpi ] ) ];
    · exact Or.inl ⟨ fun k hk => by cases k <;> ring_nf at hk <;> norm_num at hk <;> nlinarith [ Real.pi_pos ], fun k hk => by cases k <;> ring_nf at hk <;> norm_num at hk <;> nlinarith [ Real.pi_pos ] ⟩;
  have h_sinB : Real.sin B = 2 / Real.sqrt 5 := by
    rw [ ← Real.sqrt_sq ( le_of_lt ( Real.sin_pos_of_pos_of_lt_pi hB0 ( by linarith ) ) ), Real.sin_sq, Real.cos_sq ] ; ring_nf ; norm_num [ h_tanB ];
    rw [ show B * 2 = 2 * B by ring, Real.cos_two_mul ] ; rw [ ← Real.inv_sqrt_one_add_tan_sq ] <;> norm_num [ h_tanB ] ; ring_nf;
    exact Real.cos_pos_of_mem_Ioo ⟨ by linarith, hBpi ⟩
  have h_tanA : Real.tan A = 3 := by
    exact hcond.trans ( by rw [ h_tanB, hC ] ; norm_num );
  have h_sinA : Real.sin A = 3 / Real.sqrt 10 := by
    rw [ ← sq_eq_sq₀ ] <;> ring_nf <;> norm_num;
    · rw [ Real.tan_eq_sin_div_cos, div_eq_iff ] at h_tanA <;> nlinarith [ Real.sin_sq_add_cos_sq A, Real.sin_pos_of_pos_of_lt_pi hA0 ( by linarith ), Real.cos_pos_of_mem_Ioo ⟨ by linarith, hApi ⟩ ];
    · exact Real.sin_nonneg_of_nonneg_of_le_pi hA0.le ( by linarith )
  -- 由正弦定理求出 c，再由面积公式计算
  have hsinC : Real.sin C = Real.sqrt 2 / 2 := by rw [hC, Real.sin_pi_div_four]
  have h10 : Real.sqrt 10 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (by norm_num)
  have h2R : 2 * R = 2 * Real.sqrt 10 / 3 := by
    rw [haval] at hsa
    rw [h_sinA] at hsa
    field_simp at hsa ⊢
    nlinarith [hsa, h10, Real.sq_sqrt (show (0:ℝ) ≤ 10 by norm_num)]
  have hc_val : c = 2 * Real.sqrt 5 / 3 := by
    rw [hsc, hsinC, h2R]
    rw [show (10:ℝ) = 2 * 5 by norm_num, Real.sqrt_mul (by norm_num)]
    ring_nf
    rw [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
    ring
  rw [harea, haval, hc_val, h_sinB]
  have h5' := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  field_simp
  nlinarith [h5', h5]

end Problem3
