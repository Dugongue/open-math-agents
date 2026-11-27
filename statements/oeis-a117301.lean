import Mathlib

/-!
# OEIS A117301: `prime(n+3) prime(n) - prime(n+1) prime(n+2)`

Source: https://oeis.org/A117301
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = prime(n+3) prime(n) - prime(n+1) prime(n+2)`. Conjecture (Hilliard): there are infinitely
many terms whose absolute value is `12`.

Conventions:
* `prime(n) = Nat.nth Nat.Prime (n - 1)`, `n ≥ 1`; values in `ℤ`.
-/

namespace OMA.S_oeis_a117301

/-- `prime(i)`. -/
noncomputable def p (i : ℕ) : ℤ := Nat.nth Nat.Prime (i - 1)

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℤ := p (n + 3) * p n - p (n + 1) * p (n + 2)

/-- Infinitely many `n` with `|a(n)| = 12`. -/
theorem main : {n : ℕ | 1 ≤ n ∧ |a n| = 12}.Infinite := by
  sorry

end OMA.S_oeis_a117301
