import Mathlib

/-!
# A008366: Numbers whose smallest prime factor is >= 17

Source: https://oeis.org/A008366
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

## Problem Statement
Conjecture: An integer `n > 1` has smallest prime factor at least `17` if and only if
`n` divides `∑_{k=1}^n k^10` and `n` divides `∑_{k=1}^n k^12`.
-/

namespace OMA.S_oeis_a008366

theorem main :
    ∀ n : ℕ, 1 < n →
      ((∀ p : ℕ, Nat.Prime p → p ∣ n → 17 ≤ p) ↔
        (n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 10) ∧
        (n ∣ ∑ k ∈ Finset.Icc 1 n, k ^ 12)) := by
  sorry

end OMA.S_oeis_a008366
