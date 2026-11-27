import Mathlib

/-!
# OEIS A104148: distance from `n³` down to a prime or a square

Source: https://oeis.org/A104148
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the difference between `n³` and the largest `m < n³`, `m > 0`, that is a prime or a
square. Conjecturally (OEIS entry) `a(n) ≪ log² n`.

Conventions:
* `n ≥ 2`; `≪` is `IsBigO` as `n → ∞`.
-/

namespace OMA.S_oeis_a104148

open Filter Asymptotics

/-- `a(n) = n³ - max {m < n³ | m > 0 prime or square}`. -/
noncomputable def a (n : ℕ) : ℕ :=
  n ^ 3 - sSup {m : ℕ | 0 < m ∧ m < n ^ 3 ∧ (m.Prime ∨ IsSquare m)}

/-- `a(n) = O(log² n)`. -/
theorem main : (fun n : ℕ => (a n : ℝ)) =O[atTop] fun n => Real.log n ^ 2 := by
  sorry

end OMA.S_oeis_a104148
