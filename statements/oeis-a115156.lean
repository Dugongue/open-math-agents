import Mathlib

/-!
# OEIS A115156: `n` binary ones and `n` prime factors

Source: https://oeis.org/A115156
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest number having exactly `n` ones in binary and exactly `n` prime factors
(counted with multiplicity). The entry asks whether `a(n)` exists for every `n` (it does for all
large `n`, by Drmota–Mauduit–Rivat); `main` states that it exists for every `n ≥ 1`.

Conventions:
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_oeis_a115156

/-- Binary weight. -/
def s2 (k : ℕ) : ℕ := ((Nat.digits 2 k).filter (· = 1)).length

/-- For every `n ≥ 1` some `m` has binary weight `n` and `Ω(m) = n`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ m : ℕ, s2 m = n ∧ ArithmeticFunction.cardFactors m = n := by
  sorry

end OMA.S_oeis_a115156
