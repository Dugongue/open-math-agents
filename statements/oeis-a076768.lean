import Mathlib

/-!
A076768: Positive integers not expressible as the sum of a prime and a triangular number.

Source: https://oeis.org/A076768
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

This is related to the Sun's conjecture (see A132399) that every number except 216 is the sum of a triangular number and a prime or 0.
-/

namespace OMA.S_oeis_a076768

/-- Sun's conjecture: every natural number except 216 is either a triangular number or the sum of
a triangular number and a prime. -/
theorem main :
    ∀ n : ℕ, n ≠ 216 →
      (∃ k : ℕ, n = k * (k + 1) / 2) ∨
      (∃ k p : ℕ, Nat.Prime p ∧ n = k * (k + 1) / 2 + p) := by sorry

end OMA.S_oeis_a076768
