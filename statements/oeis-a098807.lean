import Mathlib

/-!
# A098807: Numbers k such that p - k, p, p + k are all prime for some prime p

Source: https://oeis.org/A098807
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Numbers k such that there exists a prime p for which p - k and p + k are also prime.
Conjecture (implied by Dickson's conjecture): All positive multiples of 6 are terms.
-/

namespace OMA.S_oeis_a098807

theorem main :
    ∀ m : ℕ, 0 < m →
      ∃ p : ℕ, 6 * m < p ∧ Nat.Prime p ∧ Nat.Prime (p - 6 * m) ∧ Nat.Prime (p + 6 * m) := by
  sorry

end OMA.S_oeis_a098807
