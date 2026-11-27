import Mathlib

/-!
# OEIS A113318: numbers with exclusionary fourth powers

Source: https://oeis.org/A113318
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A113318 lists the numbers `m` with no repeated (decimal) digits such that `m` and `m⁴` have no
digit in common. The listed terms are conjectured to be complete; `main` states that they are all
such numbers.
-/

namespace OMA.S_oeis_a113318

/-- `m` has distinct digits and shares no digit with `m⁴`. -/
def P (m : ℕ) : Prop :=
  (Nat.digits 10 m).Nodup ∧ Disjoint (Nat.digits 10 m).toFinset (Nat.digits 10 (m ^ 4)).toFinset

/-- The complete list (positive `m`). -/
theorem main : {m : ℕ | 1 ≤ m ∧ P m} = {2, 3, 4, 7, 8, 9, 24, 27, 28, 32, 42, 52, 53, 58, 59, 67,
    89, 93, 203, 258, 284, 324, 329, 832, 843, 2673} := by
  sorry

end OMA.S_oeis_a113318
