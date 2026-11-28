import Mathlib

/-!
# A100593: Greatest positive integer that can be represented as the sum of exactly two semiprimes in exactly n ways.

Source: https://oeis.org/A100593
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Conjecture: `a(0) = 33`, i.e., `33` cannot be written as the sum of two semiprimes, while
every integer greater than `33` can be written as the sum of two semiprimes.
-/

namespace OMA.S_oeis_a100593

/-- A natural number is semiprime if it is the product of two primes. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ m = p * q

/-- `n` can be represented as the sum of two semiprimes. -/
def IsSumOfTwoSemiprimes (n : ℕ) : Prop :=
  ∃ s t : ℕ, IsSemiprime s ∧ IsSemiprime t ∧ n = s + t

theorem main :
    ¬ IsSumOfTwoSemiprimes 33 ∧ ∀ n : ℕ, 33 < n → IsSumOfTwoSemiprimes n := by
  sorry

end OMA.S_oeis_a100593
