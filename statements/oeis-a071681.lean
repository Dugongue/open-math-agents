import Mathlib

/-!
# OEIS A071681: primes as arithmetic means of two other primes

Source: https://oeis.org/A071681
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ways to represent the `n`-th prime as the arithmetic mean of two other
primes. Conjecture (OEIS entry): `a(n) > 0` for `n > 2`, i.e. every prime `p ≥ 5` is `(q + r)/2`
for primes `q < p < r`.
-/

namespace OMA.S_oeis_a071681

/-- Every prime `p ≥ 5` is the mean of two other primes. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q < p ∧ q + r = 2 * p := by
  sorry

end OMA.S_oeis_a071681
