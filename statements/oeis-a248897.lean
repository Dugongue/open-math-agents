import Mathlib

/-!
# OEIS A248897: a family of series for `2√3π/9`

Source: https://oeis.org/A248897
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Bala, 2021): for `k ≥ 0`,
`2√3 π/9 = (3/2)^k k! ∑_{n = -∞}^{∞} (-1)^n / ∏_{j=0}^{k} (3n + 3j + 1)`.

Conventions:
* For `k ≥ 1` the series converges absolutely and is a `tsum` over `n ∈ ℤ`; for `k = 0` it only
  converges symmetrically, so `main` is stated for `k ≥ 1`.
-/

namespace OMA.S_oeis_a248897

/-- The `k`-th bilateral series. -/
noncomputable def S (k : ℕ) : ℝ :=
  ∑' n : ℤ, (-1 : ℝ) ^ n.natAbs / ∏ j ∈ Finset.range (k + 1), ((3 * n + 3 * j + 1 : ℤ) : ℝ)

/-- Bala's identity for `k ≥ 1`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    2 * Real.sqrt 3 * Real.pi / 9 = (3 / 2 : ℝ) ^ k * k.factorial * S k := by
  sorry

end OMA.S_oeis_a248897
