import Mathlib

/-!
# A098058: Primes p(n) such that 4 does not divide p(n+1) - p(n)

Source: https://oeis.org/A098058
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

prime(n) such that 4 does not divide the difference between prime(n) and prime(n+1).
Conjecture: The sequence contains arbitrarily long strings of consecutive primes.
-/

namespace OMA.S_oeis_a098058

theorem main :
    ∀ k : ℕ, ∃ n : ℕ, ∀ j : ℕ, j < k →
      ¬ (4 ∣ (Nat.nth Nat.Prime (n + j + 1) - Nat.nth Nat.Prime (n + j))) := by
  sorry

end OMA.S_oeis_a098058
