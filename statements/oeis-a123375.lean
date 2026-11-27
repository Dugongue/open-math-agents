import Mathlib

/-!
# OEIS A123375: every gap between consecutive semiprimes occurs

Source: https://oeis.org/A123375
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least `k` such that the difference between the `k`-th and `(k+1)`-st semiprimes is
`n`, or `0` if none exists. Conjecture (OEIS entry): `a(n) > 0` for all `n`, i.e. every positive
integer is a gap between consecutive semiprimes.

Conventions:
* Semiprimes have `Ω = 2`; consecutive semiprimes are `Nat.nth` at `k` and `k + 1`. `n ≥ 1`.
-/

namespace OMA.S_oeis_a123375

open ArithmeticFunction

/-- The semiprime predicate. -/
def S (m : ℕ) : Prop := cardFactors m = 2

/-- Every `n ≥ 1` is a gap between consecutive semiprimes. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, Nat.nth S (k + 1) = Nat.nth S k + n := by
  sorry

end OMA.S_oeis_a123375
