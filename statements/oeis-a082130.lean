import Mathlib

/-!
# OEIS A082130: `2k - 1` and `2k + 1` both semiprimes

Source: https://oeis.org/A082130
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A082130 lists the `k` such that `2k - 1` and `2k + 1` are both semiprimes. The entry explains that
Dickson's conjecture implies the sequence is infinite (in many ways); `main` states that it is
infinite.

Conventions:
* A semiprime has exactly two prime factors counted with multiplicity (`Ω = 2`).
-/

namespace OMA.S_oeis_a082130

open ArithmeticFunction

/-- Infinitely many `k` have `2k - 1` and `2k + 1` semiprime. -/
theorem main : {k : ℕ | 1 ≤ k ∧ cardFactors (2 * k - 1) = 2 ∧ cardFactors (2 * k + 1) = 2}.Infinite := by
  sorry

end OMA.S_oeis_a082130
