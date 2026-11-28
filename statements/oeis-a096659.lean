import Mathlib

/-!
# A096659: Earliest value of C in y = x^2 + (2n-1)x + C prime for all x = 0 to n

Source: https://oeis.org/A096659
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

a(n) is the earliest value of C in y = x^2 + (2n-1)x + C such that y is prime
for all x = 0 to n.
Conjecture: This sequence is infinite (implied by Dickson's conjecture).
-/

namespace OMA.S_oeis_a096659

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ C : ℕ, ∀ x : ℕ, x ≤ n → Nat.Prime (x ^ 2 + (2 * n - 1) * x + C) := by
  sorry

end OMA.S_oeis_a096659
