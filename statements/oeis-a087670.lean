import Mathlib

/-!
# OEIS A087670: `b(k+1) = b(k) ⌊b(k)⌋` reaches an integer

Source: https://oeis.org/A087670
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A087670 starts the iteration `b(k+1) = b(k) ⌊b(k)⌋` at `b(0) = (2n+1)/n`. The entry records the
conjecture that an integer is always reached if the initial value is `≥ 2`.

Conventions:
* The initial value is any rational `q ≥ 2` (the entry's general form). `main`: some iterate is an
  integer.
-/

namespace OMA.S_oeis_a087670

/-- One step `x ↦ x ⌊x⌋`. -/
def step (x : ℚ) : ℚ := x * ⌊x⌋

/-- From every rational `q ≥ 2` the iteration reaches an integer. -/
theorem main : ∀ q : ℚ, 2 ≤ q → ∃ k : ℕ, ∃ z : ℤ, step^[k] q = z := by
  sorry

end OMA.S_oeis_a087670
