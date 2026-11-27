import Mathlib

/-!
# OEIS A085105: adding smaller primes until a prime appears

Source: https://oeis.org/A085105
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Starting with `prime(n)`, go on adding the next smaller primes `prime(n-1), prime(n-2), …` until
the running sum is prime; `a(n)` is this prime, or `0` if no such prime exists. Conjecture (OEIS
entry): except `a(3)`, no term is zero.

Conventions:
* `prime(i) = Nat.nth Nat.Prime (i - 1)` (`prime(1) = 2`). At least one smaller prime is added, so
  the sums are `prime(n) + prime(n-1) + ⋯ + prime(n-j)` with `1 ≤ j ≤ n - 1`.
-/

namespace OMA.S_oeis_a085105

/-- `prime(i)`, `prime(1) = 2`. -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- For `n ≥ 2`, `n ≠ 3`, some sum `prime(n) + ⋯ + prime(n-j)`, `1 ≤ j ≤ n-1`, is prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → n ≠ 3 →
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ n - 1 ∧ (∑ i ∈ Finset.Icc (n - j) n, p i).Prime := by
  sorry

end OMA.S_oeis_a085105
