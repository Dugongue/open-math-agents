import Mathlib

/-!
# OEIS A094189: primes between `n² - n` and `n²`

Source: https://oeis.org/A094189
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes between `n² - n` and `n²` (inclusive). Oppermann conjectured that
`a(n) > 0` for `n > 1`; the entry conjectures more strongly that `a(n) > 1` for `n > 11`.
-/

namespace OMA.S_oeis_a094189

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc (n ^ 2 - n) (n ^ 2)).filter Nat.Prime).card

/-- `a(n) ≥ 2` for `n > 11`. -/
theorem main : ∀ n : ℕ, 11 < n → 1 < a n := by
  sorry

end OMA.S_oeis_a094189
