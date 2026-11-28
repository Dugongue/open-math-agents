import Mathlib

/-!
A076044: Largest a(n) values with at most n primes between a(n) and a(n)+sqrt(a(n)) inclusive.

Source: https://oeis.org/A076044
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: for every m greater than a(n), there are more than n primes between m and m+sqrt(m); true if a(n) less than 1000000.
-/

namespace OMA.S_oeis_a076044

/-- Number of primes in the closed interval `[m, m + sqrt(m)]`. -/
def primesInSqrtInterval (m : ℕ) : ℕ :=
  ((Finset.Icc m (m + Nat.sqrt m)).filter Nat.Prime).card

/-- Conjecture: for every `n`, all sufficiently large `m` have more than `n` primes in `[m, m + sqrt(m)]`. -/
theorem main :
    ∀ n : ℕ, ∃ M : ℕ, ∀ m : ℕ, M < m → n < primesInSqrtInterval m := by sorry

end OMA.S_oeis_a076044
