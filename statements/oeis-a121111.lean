import Mathlib

/-!
# OEIS A121111: multiplicative persistence at most `11`

Source: https://oeis.org/A121111
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A121111 is the trajectory of `277777788888899`, the smallest number of multiplicative persistence
`11`, under `x ↦` (product of the decimal digits of `x`). It is conjectured that no number has
persistence greater than `11`.

Conventions:
* The persistence of `x` is the number of applications of the digit-product map needed to reach a
  single digit (`< 10`). 'Persistence `≤ 11`' is: `11` applications reach a number `< 10`.
-/

namespace OMA.S_oeis_a121111

/-- Product of the decimal digits. -/
def dp (x : ℕ) : ℕ := (Nat.digits 10 x).prod

/-- Every number reaches a single digit within `11` steps. -/
theorem main : ∀ x : ℕ, dp^[11] x < 10 := by
  sorry

end OMA.S_oeis_a121111
