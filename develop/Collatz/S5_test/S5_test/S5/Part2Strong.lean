import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
## 记号

* 考拉兹压缩映射 `T(n) = (3n+1) / 2^(ν₂(3n+1))`，即 `3n+1` 的奇数部分，
  实现为 `collatzT n := ordCompl[2] (3 * n + 1)`。
* `S5` 数：`n % 8 = 5`。
* 收敛：`Converges n := ∃ k, collatzT^[k] n = 1`。

## 强化前提 `part1Strong`

对任意 `S1/S3/S7` 数 `m`（奇数、`1 < m`、`m % 8 ≠ 5`），存在步数 `k` 使得
`collatzT^[k] m` 是 `S5` 数且 **严格小于 `m`**。
-/

namespace CollatzPart2Strong

/-- 考拉兹压缩映射 `T(n) = (3n+1)/2^(ν₂(3n+1))`，即 `3n+1` 的奇数部分。 -/
def collatzT (n : ℕ) : ℕ := ordCompl[2] (3 * n + 1)

/-- `collatzT n` 永远是奇数（它是 `3n+1` 的奇数部分）。 -/
lemma collatzT_odd (n : ℕ) : Odd (collatzT n) := by
  unfold collatzT
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  exact Nat.not_dvd_ordCompl (by norm_num) (by omega)

/-- 对任意奇数 `n` 与任意步数 `k`，`collatzT^[k] n` 仍是奇数。 -/
lemma collatzT_iterate_odd (k n : ℕ) (h : Odd n) : Odd (collatzT^[k] n) := by
  induction k with
  | zero => simpa using h
  | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact collatzT_odd _

/-- 收敛到 1：存在有限步使迭代到 1。 -/
def Converges (n : ℕ) : Prop := ∃ k : ℕ, collatzT^[k] n = 1

/-- 若 `collatzT^[k] n` 收敛，则 `n` 收敛。 -/
lemma converges_of_iterate (n k : ℕ) (h : Converges (collatzT^[k] n)) : Converges n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [Function.iterate_add_apply]; exact hj⟩

/-- **定理 2（强制收缩定理）**。对任意 `S5` 数 `n`（`n % 8 = 5`），有 `collatzT n < n`。 -/
theorem collatz_thm2_forced_contraction {n : ℕ} (h : n % 8 = 5) :
    collatzT n < n := by
  have h_collatzT_def :
      collatzT n = (3 * n + 1) / 2 ^ (Nat.factorization (3 * n + 1) 2) := rfl
  have h_factorization : Nat.factorization (3 * n + 1) 2 ≥ 3 := by
    exact Nat.le_trans (by native_decide)
      (Nat.factorization_le_iff_dvd (by norm_num) (by norm_num) |>.2
        (show 8 ∣ 3 * n + 1 from Nat.dvd_of_mod_eq_zero (by omega)) 2)
  nlinarith [Nat.div_mul_le_self (3 * n + 1) (2 ^ (Nat.factorization (3 * n + 1) 2)),
    Nat.pow_le_pow_right (show 1 ≤ 2 by decide) h_factorization,
    show n > 0 from Nat.pos_of_ne_zero (by aesop_cat)]

/-
**所有正奇数收敛定理（在强化前提下）**。

对所有正奇数 `n` 做强归纳：
* `n = 1`：`collatzT^[0] 1 = 1`，收敛。
* `n` 是 `S5`（`n % 8 = 5`）：由定理 2，`collatzT n < n`；`collatzT n` 仍是奇数
  （`collatzT_odd`）。由强归纳假设 `collatzT n` 收敛，再由 `converges_of_iterate`
  （取 `k = 1`）得 `n` 收敛。
* `n` 是 `S1/S3/S7`（`1 < n` 且 `n % 8 ≠ 5`）：由 `part1Strong` 得到步数 `k`，
  使 `m := collatzT^[k] n` 是 `S5` 且 `m < n`；`m` 仍是奇数（`collatzT_iterate_odd`）。
  由强归纳假设 `m` 收敛，再由 `converges_of_iterate` 得 `n` 收敛。
-/
theorem all_odd_converges
    (part1Strong : ∀ m : ℕ, Odd m → 1 < m → m % 8 ≠ 5 →
      ∃ k : ℕ, (collatzT^[k] m) % 8 = 5 ∧ collatzT^[k] m < m) :
    ∀ n : ℕ, Odd n → Converges n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hodd
    rcases n with ( _ | _ | _ | _ | _ | n ) <;> simp_all +arith +decide;
    · exists 0;
    · exact ⟨ 7, by native_decide ⟩;
    · by_cases h5 : (n + 5) % 8 = 5;
      · -- By theorem 2, `collatzT (n + 5) < n + 5`.
        have h_contra : collatzT (n + 5) < n + 5 := by
          exact collatz_thm2_forced_contraction h5;
        convert converges_of_iterate ( n + 5 ) 1 _ using 1;
        convert ih ( collatzT ( n + 5 ) ) ( by linarith ) ( collatzT_odd _ ) using 1;
      · obtain ⟨ k, hk₁, hk₂ ⟩ := part1Strong ( n + 5 ) hodd ( by linarith ) h5 ; exact converges_of_iterate _ k ( ih _ ( by linarith ) ( by exact collatzT_iterate_odd _ _ hodd ) ) ;

/-- **定理 3（S5 收敛定理）**：在强化前提 `part1Strong` 下，所有 `S5` 数收敛到 1。 -/
theorem collatz_thm3_S5_converges
    (part1Strong : ∀ m : ℕ, Odd m → 1 < m → m % 8 ≠ 5 →
      ∃ k : ℕ, (collatzT^[k] m) % 8 = 5 ∧ collatzT^[k] m < m) :
    ∀ n : ℕ, Odd n → n % 8 = 5 → Converges n := by
  intro n hodd _
  exact all_odd_converges part1Strong n hodd

end CollatzPart2Strong
