import Mathlib

/-!
# A099501: Least number of members in a subset of integers in the interval [n^2+1, (n+1)^2-1] whose product is twice a square.

Source: https://oeis.org/A099501
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Granville and Selfridge conjecture that `a(n) <= 3` for all `n >= 1`.
-/

namespace OMA.S_oeis_a099501

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc (n ^ 2 + 1) ((n + 1) ^ 2 - 1) ∧
        S.card ≤ 3 ∧ ∃ m : ℕ, ∏ x ∈ S, x = 2 * m ^ 2 := by
  sorry

end OMA.S_oeis_a099501
