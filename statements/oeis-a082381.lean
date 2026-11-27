import Mathlib

/-!
# OEIS A082381: iterating the sum of squared digits

Source: https://oeis.org/A082381
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Iterate the map `n ↦` (sum of the squares of the decimal digits of `n`). Conjecture (OEIS entry):
the iteration always terminates with `1` or enters the loop
`4, 16, 37, 58, 89, 145, 42, 20, 4, …`.

Conventions:
* `n ≥ 1`. Entering the loop is equivalent to reaching `4`, so `main` states that every `n ≥ 1`
  eventually reaches `1` or `4`.
-/

namespace OMA.S_oeis_a082381

/-- Sum of the squares of the decimal digits. -/
def f (n : ℕ) : ℕ := ((Nat.digits 10 n).map fun d => d ^ 2).sum

/-- Every positive integer eventually reaches `1` or `4`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, f^[i] n = 1 ∨ f^[i] n = 4 := by
  sorry

end OMA.S_oeis_a082381
