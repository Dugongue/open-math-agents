import Mathlib

/-!
# A100570: Numbers that are not the sum of a square and a semiprime.

Source: https://oeis.org/A100570
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: every integer `n > 657` is the sum of a square and a semiprime.
-/

namespace OMA.S_oeis_a100570

/-- A natural number is semiprime if it is the product of two primes. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p * q

theorem main :
    ∀ n : ℕ, 657 < n → ∃ k s : ℕ, IsSemiprime s ∧ n = k ^ 2 + s := by
  sorry

end OMA.S_oeis_a100570
