import Mathlib

/-!
# OEIS A101349: a prime between consecutive cubes

Source: https://oeis.org/A101349
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of cubes between `prime(n)` and `prime(n+1)`. The entry notes that `a(n) ≤ 1`
for all `n` iff there is a prime between `k³` and `(k+1)³` for every `k ≥ 1`, an open conjecture
(verified for `k³ ≤ 1.649·10⁴⁰`); `main` states this conjecture.
-/

namespace OMA.S_oeis_a101349

/-- For every `k ≥ 1` there is a prime strictly between `k³` and `(k+1)³`. -/
theorem main : ∀ k : ℕ, 1 ≤ k → ∃ p : ℕ, p.Prime ∧ k ^ 3 < p ∧ p < (k + 1) ^ 3 := by
  sorry

end OMA.S_oeis_a101349
