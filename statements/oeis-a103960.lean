import Mathlib

/-!
# A103960: Primes p <= q such that q*p - 2 is prime

Source: https://oeis.org/A103960
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = number of primes p <= prime(n) such that prime(n) * p - 2 is prime.
Conjecture: All terms of this sequence are >= 1.
-/

namespace OMA.S_oeis_a103960

theorem main :
    ∀ q : ℕ, Nat.Prime q →
      ∃ p : ℕ, Nat.Prime p ∧ p ≤ q ∧ Nat.Prime (q * p - 2) := by
  sorry

end OMA.S_oeis_a103960
