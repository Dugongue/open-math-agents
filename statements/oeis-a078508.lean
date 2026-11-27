import Mathlib

/-!
# OEIS A078508: primes between `n^(3/2)` and `(n+1)^(3/2)`

Source: https://oeis.org/A078508
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of primes between `√(n³)` and `√((n+1)³)`. Conjectures (OEIS entry):
(1) for `n > 1051` a prime always exists between `n^1.5` and `(n+1)^1.5`; (2) for `n > 7295` more
than `2` primes always exist there.

Conventions:
* 'Between' is the open interval `(n^(3/2), (n+1)^(3/2))` (its endpoints are integers only for
  perfect squares, which are not prime anyway).
-/

namespace OMA.S_oeis_a078508

/-- Number of primes in `(n^(3/2), (n+1)^(3/2))`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {p : ℕ | p.Prime ∧ (n : ℝ) ^ ((3 : ℝ) / 2) < p ∧ (p : ℝ) < ((n : ℝ) + 1) ^ ((3 : ℝ) / 2)}.ncard

/-- Conjectures (1) and (2). -/
theorem main : (∀ n : ℕ, 1051 < n → 1 ≤ a n) ∧ (∀ n : ℕ, 7295 < n → 2 < a n) := by
  sorry

end OMA.S_oeis_a078508
