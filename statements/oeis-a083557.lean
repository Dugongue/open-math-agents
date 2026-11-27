import Mathlib

/-!
# OEIS A083557: iterating `x ↦ gpf(3x + 2)`

Source: https://oeis.org/A083557
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the greatest prime factor of `3 a(n-1) + 2`. Conjecture (OEIS entry): for any start
`a(1) = m` the sequence becomes cyclic.

Conventions:
* `m ≥ 1`; `gpf` is `primeFactors.sup id` (`3x + 2 ≥ 5`). Becoming cyclic means some two iterates
  coincide.
-/

namespace OMA.S_oeis_a083557

/-- `x ↦ gpf(3x + 2)`. -/
def g (x : ℕ) : ℕ := (3 * x + 2).primeFactors.sup id

/-- Every orbit is ultimately periodic. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ∃ i j : ℕ, i < j ∧ g^[i] m = g^[j] m := by
  sorry

end OMA.S_oeis_a083557
