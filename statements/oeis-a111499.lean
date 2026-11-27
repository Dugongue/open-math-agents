import Mathlib

/-!
# OEIS A111499: `⌊10ⁿ/π(10ⁿ)⌋ - 1`, successive differences

Source: https://oeis.org/A111499
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = ⌊10ⁿ/π(10ⁿ)⌋ - 1` (`n ≥ 1`). Conjecture (OEIS entry): except for the first `2` terms, the
difference between successive terms is `2` or `3`.

Conventions:
* `π` is `Nat.primeCounting`. 'Except for the first two terms' is read as: for `n ≥ 3`,
  `a(n+1) - a(n) ∈ {2, 3}`.
-/

namespace OMA.S_oeis_a111499

/-- `a(n) = ⌊10ⁿ/π(10ⁿ)⌋ - 1`. -/
def a (n : ℕ) : ℕ := 10 ^ n / Nat.primeCounting (10 ^ n) - 1

/-- Successive differences are `2` or `3` from `n = 3` on. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a (n + 1) = a n + 2 ∨ a (n + 1) = a n + 3 := by
  sorry

end OMA.S_oeis_a111499
