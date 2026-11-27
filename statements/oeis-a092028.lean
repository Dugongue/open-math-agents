import Mathlib

/-!
# OEIS A092028: least `m > 1` with `m ∣ n^m - 1`

Source: https://oeis.org/A092028
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest `m > 1` such that `m ∣ n^m - 1`. Every prime factor of `n - 1` is such an
`m`, so `a(n)` exists for `n ≥ 3`. Conjecture 1 (OEIS entry): all terms are primes.
-/

namespace OMA.S_oeis_a092028

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 < m ∧ m ∣ n ^ m - 1}

/-- For `n ≥ 3`, `a(n)` is prime. -/
theorem main : ∀ n : ℕ, 3 ≤ n → (a n).Prime := by
  sorry

end OMA.S_oeis_a092028
