import Mathlib

/-!
A076446: Differences of consecutive powerful numbers (definition 1).

Source: https://oeis.org/A076446
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

The term 1 appears infinitely often. Erdős conjectured that two consecutive 1's do not occur. (see Guy).
-/

namespace OMA.S_oeis_a076446

/-- A positive integer `m` is powerful if every prime dividing `m` has its square dividing `m`. -/
def IsPowerful (m : ℕ) : Prop :=
  0 < m ∧ ∀ p : ℕ, Nat.Prime p → p ∣ m → p ^ 2 ∣ m

/-- Erdős's conjecture: there do not exist three consecutive powerful numbers. -/
theorem main :
    ¬ ∃ n : ℕ, IsPowerful n ∧ IsPowerful (n + 1) ∧ IsPowerful (n + 2) := by sorry

end OMA.S_oeis_a076446
