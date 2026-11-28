import Mathlib

/-!
# A103274: Writing prime(n) as 2*prime(i) + prime(j)

Source: https://oeis.org/A103274
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) = number of ways of writing prime(n) in the form 2*prime(i) + prime(j).
Marnell conjectures that a(n) > 0 for n > 3 (i.e., for every prime p >= 7).
-/

namespace OMA.S_oeis_a103274

theorem main :
    ∀ p : ℕ, Nat.Prime p → 7 ≤ p →
      ∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ p = 2 * q + r := by
  sorry

end OMA.S_oeis_a103274
