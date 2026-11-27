import Mathlib

/-!
# OEIS A098375: an Agoh-type primality criterion

Source: https://oeis.org/A098375
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A098375 lists `(1/p) |p (p^(p-1) - 1) B(p-1) - 1|` over the primes `p` (`B(k)` the Bernoulli
numbers). Conjecture (OEIS entry): `p` is an odd prime iff `p` divides `p (p^(p-1) - 1) B(p-1) - 1`.

Conventions:
* The criterion is read for all integers `n ≥ 3`: `n` is prime iff the rational number
  `n (n^(n-1) - 1) B(n-1) - 1` is `n` times an integer. `B` is Mathlib's `bernoulli` (the sign
  convention for `B(1)` does not matter here since `n - 1 ≥ 2`).
-/

namespace OMA.S_oeis_a098375

/-- For `n ≥ 3`: `n` prime iff `n ∣ n (n^(n-1) - 1) B(n-1) - 1`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n.Prime ↔ ∃ z : ℤ, (n : ℚ) * ((n : ℚ) ^ (n - 1) - 1) * bernoulli (n - 1) - 1 = n * z) := by
  sorry

end OMA.S_oeis_a098375
