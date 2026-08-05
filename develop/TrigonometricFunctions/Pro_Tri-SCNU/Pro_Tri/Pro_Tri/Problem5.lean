import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 5：(2024·浙江一模) 在 △ABC 中，内角 A,B,C 所对的边分别为 a,b,c，
已知 c²/(b²+c²-a²) = sinC/sinB。
(1) 求角 A；
(2) 设边 BC 的中点为 D，若 a=√7，且 △ABC 的面积为 3√3/4，求 AD 的长。

【解法】
(1) 由正弦定理 sinC/sinB=c/b，故 c²/(b²+c²-a²)=c/b，化简得 b²+c²-a²=bc，
    由余弦定理 cosA=1/2，又 0<A<π，故 A=π/3。
(2) 由面积 (1/2)bc sinA=3√3/4 得 bc=3；由 a²=7=b²+c²-bc 得 b²+c²=10；
    AD 为中线，|AD|²=(b²+c²+2bc cosA)/4=13/4，故 AD=√13/2。
-/



/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

/-- 中线长公式：A 到 BC 中点 D 的中线满足 AD² = (b²+c²+2bc·cosA)/4。 -/
axiom tri_median (AD b c A : ℝ) :
    AD ^ 2 = (b ^ 2 + c ^ 2 + 2 * b * c * Real.cos A) / 4

namespace Problem5

variable (A B C a b c S AD R : ℝ)

include R in
/-- (1) A = π/3。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hb : 0 < b) (hc : 0 < c)
    (hcond : c ^ 2 / (b ^ 2 + c ^ 2 - a ^ 2) = Real.sin C / Real.sin B) :
    A = Real.pi / 3 := by
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have hcosA := tri_cos a b c A
  have hcos_eq : (b ^ 2 + c ^ 2 - a ^ 2) = b * c := by
    grind;
  exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num; nlinarith [ mul_pos hb hc ] )

include b c in
/-- (2) AD = √13/2。 -/
theorem part2
    (hADpos : 0 ≤ AD)
    (hA : A = Real.pi / 3)
    (haval : a = Real.sqrt 7)
    (hSval : S = 3 * Real.sqrt 3 / 4) :
    AD = Real.sqrt 13 / 2 := by
  have hcosA := tri_cos a b c A
  have harea := tri_area S b c A
  have hmedian := tri_median AD b c A
  rw [hA] at hcosA harea hmedian
  rw [Real.cos_pi_div_three] at hcosA hmedian
  rw [Real.sin_pi_div_three] at harea
  rw [← sq_eq_sq₀ hADpos (by positivity)]
  have h7 : a ^ 2 = 7 := by rw [haval]; rw [Real.sq_sqrt (by norm_num)]
  have hbc : b * c = 3 := by
    rw [hSval] at harea
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), Real.sqrt_nonneg 3]
  nlinarith [Real.sq_sqrt (show (13:ℝ) ≥ 0 by norm_num)]

end Problem5
