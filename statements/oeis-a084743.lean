import Mathlib

/-!
# OEIS A084743: primes of the form `n^k + k`

Source: https://oeis.org/A084743
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest prime of the form `n^k + k`, or `0` if no such prime exists. Conjecture
(OEIS entry): no entry is zero, i.e. for every `n` some `n^k + k` is prime.

Conventions:
* `n ≥ 1` and `k ≥ 1`.
-/

namespace OMA.S_oeis_a084743

/-- For every `n ≥ 1` some `n^k + k` (`k ≥ 1`) is prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ (n ^ k + k).Prime := by
  sorry

end OMA.S_oeis_a084743
