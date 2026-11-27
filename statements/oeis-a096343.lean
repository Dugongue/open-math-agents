import Mathlib

/-!
# OEIS A096343: binary weight of the product of nonzero digits of `nⁿ`

Source: https://oeis.org/A096343
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `1`s in the binary expansion of the product of the nonzero decimal digits
of `nⁿ`. Conjecture (OEIS entry): `a(n) = a(n+1)` for infinitely many positive integers `n`.
-/

namespace OMA.S_oeis_a096343

/-- Product of the nonzero decimal digits. -/
def pnd (m : ℕ) : ℕ := ((Nat.digits 10 m).filter (· ≠ 0)).prod

/-- Binary weight. -/
def s2 (k : ℕ) : ℕ := ((Nat.digits 2 k).filter (· = 1)).length

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := s2 (pnd (n ^ n))

/-- `a(n) = a(n+1)` infinitely often. -/
theorem main : {n : ℕ | 1 ≤ n ∧ a n = a (n + 1)}.Infinite := by
  sorry

end OMA.S_oeis_a096343
