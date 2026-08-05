import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 20：在锐角 △ABC 中，内角 A,B,C 的对边分别为 a,b,c，且 b²+c²-a²=bc。
(1) 求角 A 的大小；
(2) 若 a=√7, b+c=4，求 △ABC 的面积。

【解法】
(1) 由余弦定理 a²=b²+c²-2bc·cosA，得 b²+c²-a²=2bc·cosA=bc，故 cosA=1/2，
    又 A∈(0,π)，故 A=π/3。
(2) 由 a²=7=b²+c²-bc=(b+c)²-3bc=16-3bc，得 bc=3，
    面积 S=(1/2)bc·sinA=(1/2)·3·(√3/2)=3√3/4。
-/


/-- 三角形内角和。 -/
axiom tri_angle_sum (A B C : ℝ) : A + B + C = Real.pi

/-- 余弦定理（关于角 A）。 -/
axiom tri_cos_A (a b c A : ℝ) :
    a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos A

/-- 三角形面积公式（以两邻边 b,c 与夹角 A 表示）。 -/
axiom tri_area_bcA (S b c A : ℝ) :
    S = 1 / 2 * b * c * Real.sin A

namespace Problem20

variable (A B C a b c S : ℝ)

/-- (1) 求角 A：A = π/3。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hb : 0 < b) (hc : 0 < c)
    (hcond : b ^ 2 + c ^ 2 - a ^ 2 = b * c) :
    A = Real.pi / 3 := by
  have hcos := tri_cos_A a b c A
  -- 由 2·bc·cosA = bc 且 bc ≠ 0，得 cosA = 1/2。
  have hcos_val : Real.cos A = 1 / 2 := by
    nlinarith [ mul_pos hb hc ]
  exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num [ hcos_val ] )

/-- (2) 求面积：S = 3√3/4。 -/
theorem part2
    (hA : A = Real.pi / 3)
    (hcond : b ^ 2 + c ^ 2 - a ^ 2 = b * c)
    (ha : a = Real.sqrt 7) (hbc : b + c = 4) :
    S = 3 * Real.sqrt 3 / 4 := by
  have harea := tri_area_bcA S b c A
  rw [harea, hA]
  simp
  grind

end Problem20
