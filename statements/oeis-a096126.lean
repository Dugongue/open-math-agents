import Mathlib

/-!
# A096126: Least integer of the form (n^2)!/(n!)^k

Source: https://oeis.org/A096126
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the least integer of the form (n^2)!/(n!)^k.
(n^2)!/(n!)^(n+1) is an integer for every n (see A057599). Hence k >= n+1.
Conjecture: k = n+1 only when n is prime or a power of a prime.
-/

namespace OMA.S_oeis_a096126

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      (∀ k : ℕ, (n.factorial) ^ k ∣ (n ^ 2).factorial → k ≤ n + 1) →
      IsPrimePow n := by
  sorry

end OMA.S_oeis_a096126
