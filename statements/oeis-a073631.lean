import Mathlib

/-!
# OEIS A073631: nonprimes `k` dividing `3^(k-1) - 2^(k-1)`

Source: https://oeis.org/A073631
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A073631 lists the nonprime `k ≥ 1` with `k ∣ 3^(k-1) - 2^(k-1)`. Conjecture (OEIS entry): all
nonsquarefree terms are multiples of `23²`.
-/

namespace OMA.S_oeis_a073631

/-- Every nonsquarefree nonprime `k ≥ 1` with `k ∣ 3^(k-1) - 2^(k-1)` is a multiple of `529`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ¬ k.Prime → k ∣ 3 ^ (k - 1) - 2 ^ (k - 1) → ¬ Squarefree k →
    23 ^ 2 ∣ k := by
  sorry

end OMA.S_oeis_a073631
