import Mathlib

/-!
# OEIS A053728: primes that are aliquot sums

Source: https://oeis.org/A053728
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A053728 lists, for `n = 1, 2, 3, …`, the sum `s(n) = σ(n) - n` of the aliquot divisors of `n`
whenever it is prime. The entry notes that a slightly stronger form of Goldbach's conjecture
implies that every prime `> 7` appears in the sequence (and `3, 7` appear, `2, 5` do not); `main`
states that every prime `p > 7` is an aliquot sum.
-/

namespace OMA.S_oeis_a053728

open ArithmeticFunction

/-- Every prime `p > 7` equals `σ(n) - n` for some `n ≥ 1`. -/
theorem main : ∀ p : ℕ, p.Prime → 7 < p → ∃ n : ℕ, 1 ≤ n ∧ ArithmeticFunction.sigma 1 n - n = p := by
  sorry

end OMA.S_oeis_a053728
