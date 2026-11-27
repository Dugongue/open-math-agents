import Mathlib

/-!
# OEIS A117896: perfect powers between consecutive squares

Source: https://oeis.org/A117896
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of perfect powers strictly between `n²` and `(n+1)²`. Stewart conjectures
that `a(n) < 3` for all but finitely many `n`.

Conventions:
* Perfect powers are `m^k` with `m ≥ 1`, `k ≥ 2` (counted as numbers, not representations).
-/

namespace OMA.S_oeis_a117896

/-- `x` is a perfect power. -/
def IsPerfectPower (x : ℕ) : Prop := ∃ m k : ℕ, 1 ≤ m ∧ 2 ≤ k ∧ x = m ^ k

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := {x : ℕ | n ^ 2 < x ∧ x < (n + 1) ^ 2 ∧ IsPerfectPower x}.ncard

/-- `a(n) < 3` for all but finitely many `n`. -/
theorem main : {n : ℕ | 3 ≤ a n}.Finite := by
  sorry

end OMA.S_oeis_a117896
