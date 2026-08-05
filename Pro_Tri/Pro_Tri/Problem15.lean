import Mathlib.Analysis.Complex.Trigonometric

open Real

/-
题目 15：(2022·全国乙卷) 记 △ABC 的内角 A,B,C 的对边分别为 a,b,c，
已知 sinC sin(A-B) = sinB sin(C-A)。
(1) 证明：2a² = b² + c²；
(2) 若 a=5，cosA=25/31，求 △ABC 的周长。

【解法】
(1) 由正弦定理与余弦定理，条件化简得 2a²=b²+c²。
(2) 由 a=5 得 b²+c²=2a²=50；由余弦定理得 bc=31/2；(b+c)²=81，b+c=9，周长=14。
-/



/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

namespace Problem15

variable (A B C a b c R : ℝ)

include a b c R in
/-- (1) 2a² = b² + c²。 -/
theorem part1
    (hcond : Real.sin C * Real.sin (A - B) = Real.sin B * Real.sin (C - A)) :
    2 * a ^ 2 = b ^ 2 + c ^ 2 := by
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have hcosA := tri_cos a b c A
  have hcosB := tri_cos b a c B
  have hcosC := tri_cos c a b C
  have h_subst : c * (a * Real.cos B - b * Real.cos A) = b * (c * Real.cos A - a * Real.cos C) := by
    convert congr_arg ( · * ( 2 * R ) ^ 2 ) hcond using 1 <;> push_cast [ hsa, hsb, hsc, Real.sin_sub ] <;> ring;
  nlinarith

/-- (2) 周长 a+b+c = 14。 -/
theorem part2
    (hb : 0 < b) (hc : 0 < c)
    (h2a2 : 2 * a ^ 2 = b ^ 2 + c ^ 2)
    (haval : a = 5)
    (hcos : Real.cos A = 25 / 31) :
    a + b + c = 14 := by
  have hcosA := tri_cos a b c A
  subst_vars ; nlinarith [ pow_two_nonneg ( b - c ) ]

end Problem15
