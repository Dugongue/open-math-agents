import Mathlib

/-!
A075469: Maximal m such that n^n-m and n^n+m are both primes, or -1 if there is no such m.

Source: https://oeis.org/A075469
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Of course the Goldbach conjecture implies that the answer is "no"; further, the first thousand terms are positive.
-/

namespace OMA.S_oeis_a075469

/-- Conjecture: for every `n ≥ 2`, there exists `m < n^n` such that `n^n - m` and `n^n + m` are both prime. -/
theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ∃ m : ℕ, m < n ^ n ∧ Nat.Prime (n ^ n - m) ∧ Nat.Prime (n ^ n + m) := by sorry

end OMA.S_oeis_a075469
