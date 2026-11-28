import Mathlib

/-!
# A096380: Differences between the sum of the first three primes and the fourth prime in consecutive prime quadruples

Source: https://oeis.org/A096380
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

a(n) = prime(n) + prime(n+1) + prime(n+2) - prime(n+3).
Conjecture: The number of occurrences where the current term exceeds the next term is infinite.
-/

namespace OMA.S_oeis_a096380

noncomputable def a (n : ℕ) : ℤ :=
  (Nat.nth Nat.Prime n : ℤ) + (Nat.nth Nat.Prime (n + 1) : ℤ) +
    (Nat.nth Nat.Prime (n + 2) : ℤ) - (Nat.nth Nat.Prime (n + 3) : ℤ)

theorem main :
    Set.Infinite {n : ℕ | a (n + 1) < a n} := by
  sorry

end OMA.S_oeis_a096380
