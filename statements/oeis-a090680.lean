import Mathlib

/-!
# OEIS A090680: a prime between `n` and `n + A033677(n)`

Source: https://oeis.org/A090680
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes `p` with `n < p < n + A033677(n)`, where A033677(n) is the smallest
divisor of `n` that is `≥ √n`. Conjecture (OEIS entry): no `a(n)` is zero.

Conventions:
* `n ≥ 1`; A033677(n) is the least `d ∣ n` with `d² ≥ n` (it exists: `d = n`).
-/

namespace OMA.S_oeis_a090680

/-- A033677: the least divisor `d` of `n` with `d² ≥ n`. -/
noncomputable def A033677 (n : ℕ) : ℕ := sInf {d : ℕ | d ∣ n ∧ n ≤ d ^ 2}

/-- For every `n ≥ 1` there is a prime in `(n, n + A033677(n))`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < n + A033677 n := by
  sorry

end OMA.S_oeis_a090680
