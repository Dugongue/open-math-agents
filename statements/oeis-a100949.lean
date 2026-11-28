import Mathlib

/-!
# A100949: Number of partitions of n into a prime and a semiprime.

Source: https://oeis.org/A100949
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Draft from an earlier generic agent run; audited against the source and re-checked before submission.

Marnell conjectures that `a(n) > 0` for all `n > 10`, i.e., every integer `n > 10` can be
written as the sum of a prime and a semiprime.
-/

namespace OMA.S_oeis_a100949

/-- A natural number is semiprime if it is the product of two primes. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ m = q * r

theorem main :
    ∀ n : ℕ, 10 < n → ∃ p s : ℕ, Nat.Prime p ∧ IsSemiprime s ∧ n = p + s := by
  sorry

end OMA.S_oeis_a100949
