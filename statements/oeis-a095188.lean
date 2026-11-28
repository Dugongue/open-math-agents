import Mathlib

/-!
# A095188: Smallest prime formed by the digit string after decimal point of n^(1/2), or 0 if no such prime exists.

Source: https://oeis.org/A095188
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: a(n) is nonzero if n is not a perfect square.
-/

namespace OMA.S_oeis_a095188

/-- The integer formed by the first `k` decimal digits after the decimal point of `x`. -/
noncomputable def fractionalPrefix (x : ℝ) (k : ℕ) : ℕ :=
  Nat.floor ((10 : ℝ) ^ k * (x - (Nat.floor x : ℝ)))

theorem main :
    ∀ n : ℕ, ¬ IsSquare n →
      ∃ k : ℕ, 1 ≤ k ∧ (fractionalPrefix (Real.sqrt (n : ℝ)) k).Prime := by
  sorry

end OMA.S_oeis_a095188
