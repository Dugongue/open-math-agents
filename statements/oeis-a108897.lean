import Mathlib

/-!
# OEIS A108897: twin primes `60k² + 30k - 30 ± 1`, consecutive terms

Source: https://oeis.org/A108897
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A108897 lists the `k` such that `60k² + 30k - 30 ± 1` is a twin prime pair. Some consecutive
integers are both terms (`102, 103`, `105, 106`, …). Conjecture (OEIS entry): there are infinitely
many such consecutive pairs.

Conventions:
* `k ≥ 1`.
-/

namespace OMA.S_oeis_a108897

/-- `k` is a term. -/
def P (k : ℕ) : Prop :=
  1 ≤ k ∧ (60 * k ^ 2 + 30 * k - 31).Prime ∧ (60 * k ^ 2 + 30 * k - 29).Prime

/-- Infinitely many `k` with both `k` and `k + 1` terms. -/
theorem main : {k : ℕ | P k ∧ P (k + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a108897
