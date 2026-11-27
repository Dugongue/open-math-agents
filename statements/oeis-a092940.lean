import Mathlib

/-!
# OEIS A092940: largest `p` with `2 prime(n) - p` prime

Source: https://oeis.org/A092940
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the largest prime `p` such that `2 prime(n) - p` is prime. Conjecture (OEIS entry):
`a(n) = prime(n)` only for `n = 1` and `2`; i.e. for `n ≥ 3` there is a prime `p > prime(n)` with
`2 prime(n) - p` prime.

Conventions:
* `prime(n) = Nat.nth Nat.Prime (n - 1)`; `p < 2 prime(n)` so that `2 prime(n) - p ≥ 1`.
-/

namespace OMA.S_oeis_a092940

/-- For `n ≥ 3`, `2 prime(n)` is a sum of two primes other than `prime(n) + prime(n)`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ∃ q : ℕ, q.Prime ∧ Nat.nth Nat.Prime (n - 1) < q ∧ q < 2 * Nat.nth Nat.Prime (n - 1) ∧
      (2 * Nat.nth Nat.Prime (n - 1) - q).Prime := by
  sorry

end OMA.S_oeis_a092940
