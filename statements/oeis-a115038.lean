import Mathlib

/-!
# OEIS A115038: `x² + p` a perfect power

Source: https://oeis.org/A115038
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest `x` such that `x² + prime(n)` is a perfect power. Conjecture (OEIS entry):
for every prime `p` there are `x, y, n` with `x² + p = yⁿ`.

Conventions:
* `x ≥ 0`, `y ≥ 1` and `n ≥ 2` (perfect powers).
-/

namespace OMA.S_oeis_a115038

/-- Every prime is `yⁿ - x²` with `n ≥ 2`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ x y n : ℕ, 2 ≤ n ∧ x ^ 2 + p = y ^ n := by
  sorry

end OMA.S_oeis_a115038
