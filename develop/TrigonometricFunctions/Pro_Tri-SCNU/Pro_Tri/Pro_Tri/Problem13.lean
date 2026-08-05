import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 13：(2015·全国高考) 已知 a,b,c 分别是 △ABC 内角 A,B,C 的对边，sin²B = 2 sinA sinC。
(1) 若 a=b，求 cosB；
(2) 若 B=90°，且 a=√2，求 △ABC 的面积。

【解法】
(1) 由正弦定理 b²=2ac；又 a=b，得 a=2c，由余弦定理 cosB=(a²+c²-b²)/(2ac)=1/4。
(2) 由 b²=2ac；B=90° 时 a²+c²=b²，故 (a-c)²=0，a=c=√2，面积 S=(1/2)ac sinB=1。
-/



/-- 正弦定理推论：由 sin²B = 2 sinA sinC 得 b² = 2ac。 -/
axiom tri_b2ac (a b c : ℝ) : b ^ 2 = 2 * a * c

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 三角形面积公式：S = (1/2)·x·y·sin X（x,y 为夹角 X 的两邻边）。 -/
axiom tri_area (S x y X : ℝ) : S = 1 / 2 * x * y * Real.sin X

namespace Problem13

variable (A B C a b c S : ℝ)

include B in
/-- (1) 若 a=b，则 cosB = 1/4。 -/
theorem part1
    (ha : 0 < a) (hc : 0 < c)
    (hab : a = b) :
    Real.cos B = 1 / 4 := by
  have hb2ac := tri_b2ac a b c
  have hcosB := tri_cos b a c B
  have hac : a = 2 * c := by
    subst hab; nlinarith;
  rw [hac] at hb2ac
  have hbac : b = 2 * c := by
    linarith
  rw [hbac] at hcosB
  nlinarith [mul_pos ha hc]

include S c in
/-- (2) 若 B=90°，a=√2，则面积 S = 1。 -/
theorem part2
    (ha : 0 < a)
    (hB : B = Real.pi / 2)
    (hpyth : b ^ 2 = a ^ 2 + c ^ 2)
    (haval : a = Real.sqrt 2) :
    S = 1 := by
  have hb2ac := tri_b2ac a b c
  have harea := tri_area S a c B
  subst_vars; norm_num at *; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two ] ;

end Problem13
