import Mathlib

/-!
# A093245: a(n) is the lesser term of the smallest twin prime pair such that if P=(a(n)^2+n)^2+n, then P and P+2 are also twin primes.

Source: https://oeis.org/A093245
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: a(n) = 0 only if n is a multiple of 3. Note that this implies the existence
of infinitely many twin primes.
-/

namespace OMA.S_oeis_a093245

theorem main :
    ∀ n : ℕ, ¬ (3 ∣ n) →
      ∃ p : ℕ, Nat.Prime p ∧ Nat.Prime (p + 2) ∧
        Nat.Prime ((p ^ 2 + n) ^ 2 + n) ∧ Nat.Prime ((p ^ 2 + n) ^ 2 + n + 2) := by
  sorry

end OMA.S_oeis_a093245
