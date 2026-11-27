import Mathlib

/-!
# OEIS A116943: base-5 digits `4` and non-final `3` in `2ⁿ`

Source: https://oeis.org/A116943
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of digits `4` plus non-final digits `3` in the base-`5` expansion of `2ⁿ`.
Adams-Watters conjectured that `2ⁿ` contains such a digit for `n ≥ 9`, i.e. `a(n) > 0` for
`n ≥ 9`.

Conventions:
* Base-`5` digits via `Nat.digits 5` (least significant first), so the final digit is the head of
  the list; non-final digits are the tail.
-/

namespace OMA.S_oeis_a116943

/-- For `n ≥ 9`, `2ⁿ` has a base-5 digit `4`, or a digit `3` other than the last one. -/
theorem main : ∀ n : ℕ, 9 ≤ n →
    4 ∈ Nat.digits 5 (2 ^ n) ∨ 3 ∈ (Nat.digits 5 (2 ^ n)).tail := by
  sorry

end OMA.S_oeis_a116943
