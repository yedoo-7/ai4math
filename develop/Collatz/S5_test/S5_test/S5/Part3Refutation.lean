import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## 定理 3 的原始证明

> 证明（强归纳法）。对数值 `n` 进行强归纳。
> 归纳基础：`n = 5`，`T(5) = 1`，收敛。
> 归纳假设：所有小于 `n` 的正奇数收敛到 1。
> 归纳步骤：`n` 是 S5 数。由定理 2，`T(n) < n`，于是由归纳假设 `T(n)` 收敛，
> 故 `n` 收敛。由强归纳法，所有 S5 数收敛到 1。□

## 证明过程错在哪里

该"强归纳"的归纳步骤**只**处理了 `n` 是 S5 的情形，但它使用的归纳假设是
"所有小于 `n` 的正奇数收敛"。一个对正奇数数值进行的强归纳，若要让"所有小于
`n` 的正奇数收敛"这一假设在递推中真正成立，就必须对**每一个**正奇数 `n`
（包括 S1/S3/S7）都完成归纳步骤；证明只做了 S5 一种情形，归纳根本无法闭合。

1. `collatzT_not_S5_closed`：压缩映射 `T` 并不把 S5 类映回 S5 类。
   因此若把强归纳限制在 S5 类上，归纳假设根本覆盖不到 `T(n)`
   （`T(n)` 通常是 S1/S3/S7 数）。反例：`T(109) = 41`，`41 % 8 = 1 ≠ 5`。

2. `collatzT_expands_S3_S7`：定理 2 的"收缩"性质（`T(n) < n`）是 S5 类**独有**的；
   对 S3/S7 数反而有 `T(n) > n`。于是"由 `T(n) < n` 加归纳假设即收敛"的
   论证模式对非 S5 的奇数根本不成立，无法补齐归纳缺口。

3. `first_S5_return_can_exceed`：论证隐含依赖"轨道不会升过 `n`"
   （即首次回到 S5 时值更小）。但存在 S5 数 `n`，其轨道在首次回到 S5 之前会
   升过 `n`。反例：从 `n = 109` 出发，首次回到 S5 的值是 `445 > 109`。

综合 1–3，定理 3 的那段强归纳证明是错误的（其推理依赖的隐含断言均为假）。
-/

namespace CollatzThm3Refutation

/-- 考拉兹压缩映射 `T(n) = (3n+1)/2^(ν₂(3n+1))`，即 `3n+1` 的奇数部分。 -/
def collatzT (n : ℕ) : ℕ := ordCompl[2] (3 * n + 1)

/-- S5 数 `109` 的考拉兹压缩轨道（用于说明反例的来源）：
`109 → 41 → 31 → 47 → 71 → 107 → 161 → 121 → 91 → 137 → 103 → 155 → 233
→ 175 → 263 → 395 → 593 → 445`，其中 `445` 是首次回到 S5 的值，且 `445 > 109`。 -/
example : collatzT^[17] 109 = 445 := by native_decide

/-- **错误点 1**：压缩映射 `T` 不保持 S5 类。

"强归纳"若限制在 S5 数上，则归纳假设只提供"所有小于 `n` 的 **S5** 数收敛"。
但归纳步骤要用的是 `T(n)` 的收敛性，而 `T(n)` 一般不是 S5 数，故归纳假设落不到它身上。
这里给出严格证伪：并非所有 S5 数 `n` 都满足 `T(n)` 仍是 S5。
反例 `n = 109`：`T(109) = 41`，`41 % 8 = 1`。 -/
theorem collatzT_not_S5_closed :
    ¬ (∀ n : ℕ, n % 8 = 5 → 1 < n → (collatzT n) % 8 = 5) := by
  intro h
  have := h 109 (by norm_num) (by norm_num)
  revert this
  native_decide

/-
**错误点 2**：定理 2 的"收缩"是 S5 独有的；对 S3/S7 数 `T` 是**扩张**的。

归纳步骤靠"`T(n) < n` + 归纳假设"得到收敛。但要把强归纳推广到全体奇数
（这正是让归纳假设成立的必要条件），就得处理 S3/S7 数，而对它们 `T(n) > n`，
完全没有可用的"下降"。这里证明：所有 S3/S7 数都满足 `collatzT n > n`。
-/
theorem collatzT_expands_S3_S7 :
    ∀ n : ℕ, (n % 8 = 3 ∨ n % 8 = 7) → collatzT n > n := by
  intro n hn; rcases hn with ( hn | hn ) <;> rw [ collatzT ] <;> norm_num [ Nat.factorization_eq_zero_of_not_dvd, Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hn ] ;
  · rw [ show ( 3 * n + 1 ) = 2 * ( 3 * n / 2 + 1 ) by linarith [ Nat.mod_add_div ( 3 * n ) 2, show ( 3 * n ) % 2 = 1 from by omega ], Nat.factorization_mul ] <;> norm_num;
    rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> norm_num [ Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod, hn ] ; omega;
    grind;
  · rw [ show 3 * n + 1 = 2 * ( ( 3 * n + 1 ) / 2 ) by rw [ Nat.mul_div_cancel' ] ; exact Nat.dvd_of_mod_eq_zero ( by omega ) ];
    rw [ Nat.factorization_mul ] <;> norm_num;
    · rw [ Nat.factorization_eq_zero_of_not_dvd ] <;> norm_num; all_goals omega;
    · omega

/-- **错误点 3**：存在 S5 数 `n`，其轨道在"首次回到 S5"之前会升过 `n`。

精确陈述：存在 S5 数 `n > 1` 以及步数 `k > 0`，使得 `collatzT^[k] n` 是首次回到
S5 的值（中间 `0 < j < k` 处都不是 S5），但该首次回到值**大于** `n`。
这直接证伪了强归纳隐含依赖的"轨道不升过 `n`/首次回到更小"的断言。
反例：`n = 109`，`k = 17`，首次回到 S5 的值为 `445 > 109`。 -/
theorem first_S5_return_can_exceed :
    ∃ n : ℕ, n % 8 = 5 ∧ 1 < n ∧
      ∃ k : ℕ, 0 < k ∧ (collatzT^[k] n) % 8 = 5 ∧
        (∀ j : ℕ, 0 < j → j < k → (collatzT^[j] n) % 8 ≠ 5) ∧
        n < collatzT^[k] n := by
  refine ⟨109, by norm_num, by norm_num, 17, by norm_num, ?_, ?_, ?_⟩
  · native_decide
  · have key : ∀ j : ℕ, j < 17 → 0 < j → (collatzT^[j] 109) % 8 ≠ 5 := by
      native_decide
    intro j hj0 hj
    exact key j hj hj0
  · native_decide

end CollatzThm3Refutation
