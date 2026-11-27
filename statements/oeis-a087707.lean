import Mathlib

/-!
# OEIS A087707: `x ↦ (5/3) ⌈x⌉` reaches an integer

Source: https://oeis.org/A087707
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A087707 counts the steps of the map `x ↦ (5/3) ⌈x⌉` needed to reach an integer `> n` when started
at `n`. It is conjectured that an integer is always reached.

Conventions:
* `n ≥ 1`; iterates are rationals. Every iterate after the first step is `> n`, so 'an integer
  `> n` is reached' is: some iterate `step^[k] n` with `k ≥ 1` is an integer.
-/

namespace OMA.S_oeis_a087707

/-- One step `x ↦ (5/3) ⌈x⌉`. -/
def step (x : ℚ) : ℚ := 5 / 3 * ⌈x⌉

/-- From every `n ≥ 1` some later iterate is an integer. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ ∃ z : ℤ, step^[k] (n : ℚ) = z := by
  sorry

end OMA.S_oeis_a087707
