import Mathlib

/-!
# OEIS A143836: averages of two odd primes

Source: https://oeis.org/A143836
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`T(r, c) = (prime(r+2) + prime(c+1))/2` for `1 ≤ c ≤ r`. Conjecture (OEIS entry): every integer
`≥ 4` appears at least once in this sequence.

Conventions:
* `prime(i) = Nat.nth Nat.Prime (i - 1)`; with `1 ≤ c ≤ r` the two primes are odd and
  `prime(c+1) < prime(r+2)`.
-/

namespace OMA.S_oeis_a143836

/-- `prime(i)`. -/
noncomputable def p (i : ℕ) : ℕ := Nat.nth Nat.Prime (i - 1)

/-- Every `m ≥ 4` is some `T(r, c)`. -/
theorem main : ∀ m : ℕ, 4 ≤ m → ∃ r c : ℕ, 1 ≤ c ∧ c ≤ r ∧ 2 * m = p (r + 2) + p (c + 1) := by
  sorry

end OMA.S_oeis_a143836
