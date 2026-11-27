import Mathlib

/-!
# OEIS A093811: sums of digital products of divisors

Source: https://oeis.org/A093811
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the sum of the digital products (products of decimal digits) of the divisors of `n`.
Conjecture (OEIS entry): `a(n) < n` for all `n > 798` (hence `limsup a(n)/n = 0` is also
conjectured; `main` states the first part).
-/

namespace OMA.S_oeis_a093811

/-- Product of the decimal digits. -/
def dp (m : ℕ) : ℕ := (Nat.digits 10 m).prod

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := ∑ d ∈ n.divisors, dp d

/-- `a(n) < n` for `n > 798`. -/
theorem main : ∀ n : ℕ, 798 < n → a n < n := by
  sorry

end OMA.S_oeis_a093811
