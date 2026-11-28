import Mathlib

/-!
# A025166: Expansion of e.g.f. -exp(-x / (1 - 2x)) / (1 - 2x)

Source: https://oeis.org/A025166
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: Let `a(n)` be the coefficients in the exponential generating function
`-exp(-x / (1 - 2x)) / (1 - 2x) = ∑_{n ≥ 0} a(n) x^n / n!`, i.e., `a(n) = f^(n)(0)`.
Then for all `n ≥ 2`, `a(n) + (-4n + 3) * a(n - 1) + 4 * (n - 1)^2 * a(n - 2) = 0`.
-/

namespace OMA.S_oeis_a025166

/-- The exponential generating function `f(x) = -exp(-x / (1 - 2x)) / (1 - 2x)`. -/
noncomputable def egf (x : ℝ) : ℝ :=
  -Real.exp (-x / (1 - 2 * x)) / (1 - 2 * x)

/-- The `n`-th coefficient `a(n) = f^(n)(0)` of the e.g.f. -/
noncomputable def a (n : ℕ) : ℝ :=
  iteratedDeriv n egf 0

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      a n + (-4 * (n : ℝ) + 3) * a (n - 1) + 4 * ((n : ℝ) - 1) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a025166
