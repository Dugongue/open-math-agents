import Mathlib

/-!
# A099143: Least k such that S(k) = S(k+n), or 0 if there is no k, where S is the Kempner function A002034.

Source: https://oeis.org/A099143
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

The case of n=1 corresponds to the Tutescu conjecture, which states that the equation
S(k) = S(k+1) has no solutions. It is conjectured that S(k) = S(k+6) also has no solutions.
-/

namespace OMA.S_oeis_a099143

/-- The Kempner function `S(k)` (OEIS A002034): the least positive integer `m` such that
`k ∣ m!`, with `S(0) = 0`. -/
noncomputable def kempner (k : ℕ) : ℕ :=
  if h : k = 0 then 0 else Nat.find (⟨k, Nat.dvd_factorial (Nat.pos_of_ne_zero h) le_rfl⟩ :
    ∃ m : ℕ, k ∣ m.factorial)

theorem main :
    (∀ k : ℕ, 1 ≤ k → kempner k ≠ kempner (k + 1)) ∧
    (∀ k : ℕ, 1 ≤ k → kempner k ≠ kempner (k + 6)) := by
  sorry

end OMA.S_oeis_a099143
