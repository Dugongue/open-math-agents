import Mathlib

/-!
# OEIS A127329: semiprimes that are sums of three primes in arithmetic progression

Source: https://oeis.org/A127329
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A127329 lists the semiprimes equal to the sum of three primes in arithmetic progression. Every
member is `3` times a prime (the middle term), and the entry records the conjecture
`a(n) = 3 prime(n+2)`, i.e. every prime `p ≥ 5` arises: `3p = (p - d) + p + (p + d)` with
`p - d` and `p + d` prime.

Conventions:
* The progression is nonconstant (`d ≥ 1`); `main` states that every prime `p ≥ 5` is the middle
  term of a three-term arithmetic progression of primes.
-/

namespace OMA.S_oeis_a127329

/-- Every prime `p ≥ 5` is the middle of a nonconstant three-term arithmetic progression of
primes. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ∃ d : ℕ, 1 ≤ d ∧ d < p ∧ (p - d).Prime ∧ (p + d).Prime := by
  sorry

end OMA.S_oeis_a127329
