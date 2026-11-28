import Mathlib

/-!
# A095189: Smallest prime formed by the digit string after decimal point of n^(1/n), or 0 if no such prime exists.

Source: https://oeis.org/A095189
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: a(n) is nonzero for all n > 1.
-/

namespace OMA.S_oeis_a095189

/-- The integer formed by the first `k` decimal digits after the decimal point of `x`. -/
noncomputable def fractionalPrefix (x : ℝ) (k : ℕ) : ℕ :=
  Nat.floor ((10 : ℝ) ^ k * (x - (Nat.floor x : ℝ)))

theorem main :
    ∀ n : ℕ, 1 < n →
      ∃ k : ℕ, 1 ≤ k ∧ (fractionalPrefix ((n : ℝ) ^ (1 / (n : ℝ))) k).Prime := by
  sorry

end OMA.S_oeis_a095189
