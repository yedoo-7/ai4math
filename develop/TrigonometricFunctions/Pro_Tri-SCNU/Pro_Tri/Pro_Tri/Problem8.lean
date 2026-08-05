import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 8：(成都三诊·19) 在 △ABC 中，角 A,B,C 的对边分别为 a,b,c，且 √3 c + a = b cosC - c cosB。
(1) 求角 B 的大小；
(2) 若 D 是 AC 边上一点，且 BD=CD=b/3，求 cos∠BDA。

【解法】
(1) 由正弦定理 √3 sinC+sinA = sin(B-C)，又 sinA=sin(B+C)，代入得 cosB=-√3/2，B=5π/6。
(2) 由 BD=CD 与正弦定理得 sin(B-C)=2sinA；又 sin(B-C)=√3 sinC+sinA，故 sinA=√3 sinC，即 a=√3 c；
    由余弦定理 b²=7c²；在 △BDA 中由余弦定理 cos∠BDA = 13/14。
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

namespace Problem8

variable (A B C a b c R : ℝ)

include R in
/-- (1) B = 5π/6。 -/
theorem part1
    (hA0 : 0 < A)
    (hB0 : 0 < B)
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (hcond : Real.sqrt 3 * c + a = b * Real.cos C - c * Real.cos B) :
    B = 5 * Real.pi / 6 := by
  have hsum := tri_angle_sum A B C
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  rw [hsa, hsb, hsc] at hcond;
  have hsimp : Real.sqrt 3 * Real.sin C + Real.sin A = Real.sin B * Real.cos C - Real.sin C * Real.cos B := by
    nlinarith;
  have hsinA : Real.sin A = Real.sin (B + C) := by
    rw [ ← Real.sin_pi_sub, ← hsum ] ; ring_nf;
  rw [hsinA] at hsimp
  have hsinBC : Real.sin (B + C) = Real.sin B * Real.cos C + Real.cos B * Real.sin C := by
    exact Real.sin_add _ _
  rw [hsinBC] at hsimp
  have hcosB : Real.cos B = -Real.sqrt 3 / 2 := by
    nlinarith only [ hsimp, Real.sqrt_nonneg 3, Real.sq_sqrt zero_le_three, Real.sin_pos_of_pos_of_lt_pi hC0 hCpi ]
  have hB : B = 5 * Real.pi / 6 := by
    exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num [ ( by ring : 5 * Real.pi / 6 = Real.pi - Real.pi / 6 ), hcosB ] ; ring ) ;
  exact hB

include R A in
/-- (2) cos∠BDA = 13/14。 -/
theorem part2
    (R2 ADB : ℝ) (hR2 : 0 < R2) (hc : 0 < c)
    (hcond : Real.sqrt 3 * c + a = b * Real.cos C - c * Real.cos B)
    (hB : B = 5 * Real.pi / 6) :
    Real.cos ADB = 13 / 14 := by
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  -- (h1) 由题设条件经正弦定理化简：sin(B-C) = √3 sinC + sinA
  have hsinsub : Real.sin (B - C) = Real.sin B * Real.cos C - Real.cos B * Real.sin C :=
    Real.sin_sub B C
  have h1 : Real.sin (B - C) = Real.sqrt 3 * Real.sin C + Real.sin A := by
    rw [hsa, hsb, hsc] at hcond
    rw [hsinsub]; nlinarith [hcond, hR]
  -- (hsub) △ABD 正弦定理：AD = 2b/3 对应 ∠ABD = B-C，BD = b/3 对应 ∠BAD = A
  have e1 := tri_sine (2 * b / 3) R2 (B - C)
  have e2 := tri_sine (b / 3) R2 A
  have hsub : Real.sin (B - C) = 2 * Real.sin A := by nlinarith [e1, e2, hR2]
  -- 联立 h1、hsub 得 sinA = √3 sinC，从而 a = √3 c
  have hsinA : Real.sin A = Real.sqrt 3 * Real.sin C := by nlinarith [h1, hsub]
  have hac : a = Real.sqrt 3 * c := by rw [hsa, hsc, hsinA]; ring
  -- cos B = -√3/2
  have hcosB : Real.cos B = -Real.sqrt 3 / 2 := by
    rw [hB, show 5 * Real.pi / 6 = Real.pi - Real.pi / 6 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_six]; ring
  -- 由余弦定理得 b² = 7c²
  have hcosb := tri_cos b a c B
  have hsqrt3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hb2 : b ^ 2 = 7 * c ^ 2 := by
    rw [hcosB, hac] at hcosb; nlinarith [hcosb, hsqrt3]
  -- △ABD 余弦定理：c² = (b/3)² + (2b/3)² - 2·(b/3)·(2b/3)·cos∠BDA
  have hcosBDA := tri_cos c (b / 3) (2 * b / 3) ADB
  have key : 28 * c ^ 2 * Real.cos ADB = 26 * c ^ 2 := by
    linear_combination 9 * hcosBDA + (5 - 4 * Real.cos ADB) * hb2
  have h28 : (28 * c ^ 2 : ℝ) ≠ 0 := by positivity
  have heq : (28 * c ^ 2) * Real.cos ADB = (28 * c ^ 2) * (13 / 14) := by rw [key]; ring
  exact mul_left_cancel₀ h28 heq

end Problem8
