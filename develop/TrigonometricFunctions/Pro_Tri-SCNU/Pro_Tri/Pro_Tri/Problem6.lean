import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open Real

/-
题目 6：(2024·湖南邵阳·模拟预测) 在 △ABC 中，角 A,B,C 的对边分别为 a,b,c，
且 △ABC 的周长为 a sinB/(sinA+sinB-sinC)。
(1) 求 C；
(2) 若 a=2，b=4，D 为边 AB 上一点，∠BCD=π/6，求 △BCD 的面积。

【解法】
(1) 由正弦定理 a+b+c = ab/(a+b-c)，故 (a+b)²-c²=ab，a²+b²-c²=-ab，
    由余弦定理 cosC=-1/2，0<C<π，故 C=2π/3。
(2) ∠ACD=π/2；设 CD=d，由割补 S△ACD+S△BCD=S△ABC：
    (1/2)bd·sin(π/2)+(1/2)ad·sin(π/6)=(1/2)ab·sin(2π/3)，解得 d=4√3/5，
    故 S△BCD=(1/2)ad·sin(π/6)=2√3/5。
-/



/-- 外接圆半径为正。 -/
axiom tri_R_pos (R : ℝ) : 0 < R

/-- 正弦定理（外接圆半径形式）：x = 2R·sin X。 -/
axiom tri_sine (x R X : ℝ) : x = 2 * R * Real.sin X

/-- 余弦定理：x² = y²+z²-2yz·cos X（x 为角 X 的对边）。 -/
axiom tri_cos (x y z X : ℝ) :
    x ^ 2 = y ^ 2 + z ^ 2 - 2 * y * z * Real.cos X

/-- 割补法：S△ACD + S△BCD = S△ABC（∠ACD=π/2, ∠BCD=π/6, CD=d）。 -/
axiom tri_split (a b d C : ℝ) :
    1 / 2 * b * d * Real.sin (Real.pi / 2)
      + 1 / 2 * a * d * Real.sin (Real.pi / 6) = 1 / 2 * a * b * Real.sin C

/-- △BCD 的面积公式（∠BCD=π/6, CD=d）。 -/
axiom tri_area_bcd (Sbcd a d : ℝ) :
    Sbcd = 1 / 2 * a * d * Real.sin (Real.pi / 6)

namespace Problem6

variable (A B C a b c d Sbcd R : ℝ)

include R in
/-- (1) C = 2π/3。 -/
theorem part1
    (hA0 : 0 < A) (hApi : A < Real.pi)
    (hC0 : 0 < C) (hCpi : C < Real.pi)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcond : a + b + c
        = a * Real.sin B / (Real.sin A + Real.sin B - Real.sin C)) :
    C = 2 * Real.pi / 3 := by
  have hR := tri_R_pos R
  have hsa := tri_sine a R A
  have hsb := tri_sine b R B
  have hsc := tri_sine c R C
  have hcosC := tri_cos c a b C
  rw [ eq_div_iff ] at hcond;
  · exact Real.injOn_cos ⟨ by linarith, by linarith ⟩ ⟨ by linarith, by linarith ⟩ ( by norm_num [ Real.cos_two_mul, mul_div_assoc ] ; nlinarith [ mul_pos ha hb ] );
  · intro h; rw [ h ] at hcond; norm_num at hcond; linarith;

include d Sbcd in
/-- (2) S△BCD = 2√3/5。 -/
theorem part2
    (hC : C = 2 * Real.pi / 3)
    (haval : a = 2) (hbval : b = 4) :
    Sbcd = 2 * Real.sqrt 3 / 5 := by
  have hsplit := tri_split a b d C
  have hSbcd := tri_area_bcd Sbcd a d
  subst_vars; norm_num [ Real.sin_two_mul, mul_div_assoc ] at *; nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ] ;

end Problem6
