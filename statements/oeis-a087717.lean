import Mathlib

/-!
# OEIS A087717: iterating `2x - 1` on noncomposites and the largest proper divisor otherwise

Source: https://oeis.org/A087717
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Iterate the map `x ↦ 2x - 1` if `x` is noncomposite (`1` or prime), and `x ↦` (largest proper
divisor of `x`) otherwise. Conjecture (OEIS entry): for `n > 1` the iteration always leads to the
`3`-cycle `{3, 5, 9}` or the `6`-cycle `{19, 37, 73, 145, 29, 57}`.

Conventions:
* The largest proper divisor of a composite `x` is `x / minFac x`. Entering a cycle is equivalent
  to reaching one of its elements, so `main` states that some iterate equals `3` or `19`.
-/

namespace OMA.S_oeis_a087717

/-- The map. -/
def f (x : ℕ) : ℕ := if x = 1 ∨ x.Prime then 2 * x - 1 else x / x.minFac

/-- Every `n ≥ 2` eventually reaches `3` or `19`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → ∃ i : ℕ, f^[i] n = 3 ∨ f^[i] n = 19 := by
  sorry

end OMA.S_oeis_a087717
