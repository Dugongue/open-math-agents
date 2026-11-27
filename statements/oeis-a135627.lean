import Mathlib

/-!
# OEIS A135627: perfect numbers minus one

Source: https://oeis.org/A135627
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A135627 lists the numbers `n - 1` for perfect `n`. Conjecture (OEIS entry): every odd prime is a
factor of at least one number in this sequence.

Conventions:
* Perfect numbers are Mathlib's `Nat.Perfect`.
-/

namespace OMA.S_oeis_a135627

/-- Every odd prime divides `n - 1` for some perfect `n`. -/
theorem main : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ n : ℕ, n.Perfect ∧ p ∣ n - 1 := by
  sorry

end OMA.S_oeis_a135627
