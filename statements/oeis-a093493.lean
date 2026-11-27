import Mathlib

/-!
# OEIS A093493: total divisor symmetry

Source: https://oeis.org/A093493
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `r` such that `n - r` and `n + r` have the same number of divisors.
Conjectures (OEIS entry): (1) no term is zero for `n > 3`; (2) every number `k` appears only
finitely many times, i.e. `a(n) → ∞`.

Conventions:
* `r` ranges over `1 ≤ r ≤ n - 1` (so that `n - r ≥ 1`; `r = 0` would always count).
-/

namespace OMA.S_oeis_a093493

open Filter

/-- `a(n)`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n - 1)).filter fun r => (n - r).divisors.card = (n + r).divisors.card).card

/-- Conjectures (1) and (2). -/
theorem main : (∀ n : ℕ, 3 < n → 0 < a n) ∧ Tendsto a atTop atTop := by
  sorry

end OMA.S_oeis_a093493
