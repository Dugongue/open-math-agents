import Mathlib

/-!
# A078111: a(n) = floor((n+2)^(n+2)/n^n).

Source: https://oeis.org/A078111
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) - e^2*(n+1)^2 is bounded.
Conjecture: there is a constant c = 2.462... such that a(n) = floor(e^2*(n+1)^2 - c).
-/

namespace OMA.S_oeis_a078111

/-- `a(n) = ⌊(n+2)^(n+2) / n^n⌋`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.floor (((n + 2 : ℝ) ^ (n + 2)) / ((n : ℝ) ^ n))

theorem main :
    ∃ c : ℝ, ∀ n : ℕ, 1 ≤ n →
      (a n : ℤ) = Int.floor (Real.exp 2 * ((n + 1 : ℝ) ^ 2) - c) := by sorry

end OMA.S_oeis_a078111
