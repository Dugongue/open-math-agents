import Mathlib

/-!
# OEIS A112994: numbers with exclusionary cubes

Source: https://oeis.org/A112994
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A112994 lists the numbers `k` with no repeated (decimal) digits such that `k` and `k³` have no
digit in common. The listed terms are conjectured to be complete; `main` states that they are all
such numbers.
-/

namespace OMA.S_oeis_a112994

/-- `k` has distinct digits and shares no digit with `k³`. -/
def P (k : ℕ) : Prop :=
  (Nat.digits 10 k).Nodup ∧ Disjoint (Nat.digits 10 k).toFinset (Nat.digits 10 (k ^ 3)).toFinset

/-- The complete list (positive `k`). -/
theorem main : {k : ℕ | 1 ≤ k ∧ P k} = {2, 3, 7, 8, 27, 43, 47, 48, 52, 53, 63, 68, 92, 157, 172,
    187, 192, 263, 378, 408, 423, 458, 468, 478, 487, 527, 587, 608, 648, 692, 823, 843, 918, 1457,
    1587, 1592, 4657, 4732, 5692, 6058, 6378, 7658} := by
  sorry

end OMA.S_oeis_a112994
