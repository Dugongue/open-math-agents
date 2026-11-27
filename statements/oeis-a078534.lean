import Mathlib

/-!
# OEIS A078534: coefficients of `A^n - n² x A^(n+1) = 1`

Source: https://oeis.org/A078534
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A078534 is the power series with `A(x)⁵ - 25 x A(x)⁶ = 1`, `A(0) = 1`. Conjecture (OEIS entry):
if `A(x) = ∑ a(k) x^k` satisfies `A(x)ⁿ - n² x A(x)^(n+1) = 1`, then `a(n-1) = n^(2n-3)` and
`a(2n-1) = n^(4n-2)`.

Conventions:
* `n ≥ 2` and `A ∈ ℤ⟦x⟧` with constant term `1` (the equation determines `A` coefficientwise);
  `main` quantifies over every such `A`. `a(k)` is the coefficient of `x^k`.
-/

namespace OMA.S_oeis_a078534

open PowerSeries

/-- The conjectured coefficients. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∀ A : PowerSeries ℤ, constantCoeff A = 1 →
    A ^ n - (n : PowerSeries ℤ) ^ 2 * X * A ^ (n + 1) = 1 →
    coeff (n - 1) A = (n : ℤ) ^ (2 * n - 3) ∧ coeff (2 * n - 1) A = (n : ℤ) ^ (4 * n - 2) := by
  sorry

end OMA.S_oeis_a078534
