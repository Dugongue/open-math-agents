import Mathlib

/-!
# OEIS A081169: the `3x - 1` problem

Source: https://oeis.org/A081169
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Under the map `x ↦ x/2` (`x` even), `x ↦ 3x - 1` (`x` odd), it is conjectured that every
trajectory ends in one of three loops: `1 → 2 → 1`, `5 → 14 → 7 → 20 → 10 → 5`, or the loop of
`17` (`17, 50, 25, 74, 37, 110, 55, 164, 82, 41, 122, 61, 182, 91, 272, 136, 68, 34, 17`).

Conventions:
* Positive integers `x ≥ 1`. Ending in one of the loops is equivalent to reaching `1`, `5` or `17`.
-/

namespace OMA.S_oeis_a081169

/-- The `3x - 1` map. -/
def T (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x - 1

/-- Every positive integer reaches `1`, `5` or `17`. -/
theorem main : ∀ x : ℕ, 1 ≤ x → ∃ i : ℕ, T^[i] x = 1 ∨ T^[i] x = 5 ∨ T^[i] x = 17 := by
  sorry

end OMA.S_oeis_a081169
