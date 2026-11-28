import Mathlib

/-!
# A099019: Odd composite numbers k such that k-2 and k+2 are also composite

Source: https://oeis.org/A099019
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Odd composite numbers k such that k-2 and k+2 are also composite.
Conjecture (implied by Goldbach's conjecture): This sequence contains all composite numbers
that cannot be expressed as the sum or difference of two primes.
-/

namespace OMA.S_oeis_a099019

theorem main :
    ∀ k : ℕ, 1 < k → ¬ Nat.Prime k →
      (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p + q ≠ k) →
      (∀ p q : ℕ, Nat.Prime p → Nat.Prime q → p - q ≠ k) →
      Odd k ∧ 1 < k - 2 ∧ ¬ Nat.Prime (k - 2) ∧ ¬ Nat.Prime (k + 2) := by
  sorry

end OMA.S_oeis_a099019
