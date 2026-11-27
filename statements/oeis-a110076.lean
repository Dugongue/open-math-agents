import Mathlib

/-!
# OEIS A110076: solutions of `σ(m) = 10ⁿ`

Source: https://oeis.org/A110076
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the largest `m` with `σ(m) = 10ⁿ`, or `0` if there is none. Conjecture (OEIS entry):
for `n > 3`, `a(n)` is positive, i.e. `10ⁿ` is a value of `σ`.
-/

namespace OMA.S_oeis_a110076

/-- For `n > 3`, `σ(m) = 10ⁿ` has a solution. -/
theorem main : ∀ n : ℕ, 3 < n → ∃ m : ℕ, ArithmeticFunction.sigma 1 m = 10 ^ n := by
  sorry

end OMA.S_oeis_a110076
