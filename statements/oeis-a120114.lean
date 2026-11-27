import Mathlib

/-!
# OEIS A120114: `lcm(1, …, 2n+4)/lcm(1, …, 2n+2)`

Source: https://oeis.org/A120114
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = lcm(1, …, 2n+4)/lcm(1, …, 2n+2)`. Conjecture (Rotondo, 2024): except for `2`, if `a(n)` is
even then `a(n)/2` is a Mersenne prime.

Conventions:
* `n ≥ 0`; a Mersenne prime is a prime of the form `2^q - 1`. 'Except for 2' means `a(n) ≠ 2`.
-/

namespace OMA.S_oeis_a120114

/-- `lcm(1, …, m)`. -/
def L (m : ℕ) : ℕ := (Finset.Icc 1 m).lcm id

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := L (2 * n + 4) / L (2 * n + 2)

/-- If `a(n)` is even and `≠ 2`, then `a(n)/2` is a Mersenne prime. -/
theorem main : ∀ n : ℕ, Even (a n) → a n ≠ 2 →
    (a n / 2).Prime ∧ ∃ q : ℕ, a n / 2 = 2 ^ q - 1 := by
  sorry

end OMA.S_oeis_a120114
