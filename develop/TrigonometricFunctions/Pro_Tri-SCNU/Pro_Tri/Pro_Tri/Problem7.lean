import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 7：(2024·广东广州一模) 记 △ABC 的内角 A,B,C 的对边分别为 a,b,c，△ABC 的面积为 S，
已知 S = -√3/4 (a²+c²-b²)。
(1) 求 B；
(2) 若点 D 在边 AC 上，且 ∠ABD=π/2，AD=2DC=2，求 △ABC 的周长。

【解法】
(1) S=(1/2)ac sinB，a²+c²-b²=2ac cosB，故 sinB=-√3 cosB，0<B<π 解得 B=2π/3。
(2) AC=b=3。由 BA⃗·BD⃗=0 得 (1/3)c²+(2/3)ca cosB=0，cosB=-1/2 得 c²=ca，故 a=c，A=C=π/6；
    Rt△ABD 中 c=AB=AD cosA=2cos(π/6)=√3，故 a=c=√3，周长 a+b+c=3+2√3。
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

/-- ∠ABD=π/2 的向量数量积（垂直）条件：(1/3)c² + (2/3)(ca·cosB) = 0。 -/
axiom tri_perp (a c B : ℝ) :
    1 / 3 * c ^ 2 + 2 / 3 * (c * a * Real.cos B) = 0

/-- Rt△ABD 中 AB=AD·cosA，AD=2：c = 2·cosA。 -/
axiom tri_right (c A : ℝ) : c = 2 * Real.cos A

namespace Problem7

variable (A B C a b c S R : ℝ)

/-- (1) B = 2π/3。 -/
theorem part1
    (hB0 : 0 < B) (hBpi : B < Real.pi)
    (ha : 0 < a) (hc : 0 < c)
    (hcond : S = -Real.sqrt 3 / 4 * (a ^ 2 + c ^ 2 - b ^ 2)) :
    B = 2 * Real.pi / 3 := by
  have harea := tri_area S a c B
  have hcosB := tri_cos b a c B
  have h_factor : Real.sin B = -Real.sqrt 3 * Real.cos B := by
    exact mul_left_cancel₀ ( mul_ne_zero ha.ne' hc.ne' ) ( by nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three ] );
  have h_identity : Real.sin (B + Real.pi / 3) = 0 := by
    simpa [ Real.sin_add, h_factor ] using by ring;
  rw [ Real.sin_eq_zero_iff ] at h_identity ; obtain ⟨ k, hk ⟩ := h_identity ; rcases k with ⟨ _ | _ | k ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ]

include R a in
/-- (2) 周长 a+b+c = 3+2√3。 -/
theorem part2
    (hA0 : 0 < A) (hC0 : 0 < C)
    (hc : 0 < c)
    (hB : B = 2 * Real.pi / 3)
    (hbval : b = 3) :
    a + b + c = 3 + 2 * Real.sqrt 3 := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsc := tri_sine c R C
  have hperp := tri_perp a c B
  have hright := tri_right c A
  have hc_eq_a : c = a := by
    norm_num [ hB, Real.cos_two_mul, mul_div_assoc ] at hperp;
    nlinarith;
  have hA_eq_C : A = C := by
    exact Real.injOn_sin ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by nlinarith )
  have hA_eq_pi_6 : A = Real.pi / 6 := by
    grind +extAll
  have hcosA_eq_sqrt3_div2 : Real.cos A = Real.sqrt 3 / 2 := by
    rw [ hA_eq_pi_6, Real.cos_pi_div_six ]
  linarith

end Problem7
