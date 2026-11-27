import Mathlib

/-!
# OEIS A114888: multiperfect numbers divisible by their sums of prime factors

Source: https://oeis.org/A114888
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A114888 lists the multiperfect numbers `n` (`σ(n) = k n` for an integer `k`) that are divisible by
their sum of prime factors with repetition and by their sum of prime factors without repetition.
Conjecture (OEIS entry): the sequence is finite.

Conventions:
* Multiperfect: `n ≥ 1` with `n ∣ σ(n)`. Sums of prime factors: with repetition
  `∑ p` over `n.primeFactorsList`, without repetition over `n.primeFactors`.
-/

namespace OMA.S_oeis_a114888

/-- The defining property. -/
def P (n : ℕ) : Prop :=
  1 ≤ n ∧ n ∣ ArithmeticFunction.sigma 1 n ∧ n.primeFactorsList.sum ∣ n ∧
    (∑ p ∈ n.primeFactors, p) ∣ n

/-- Only finitely many such `n`. -/
theorem main : {n | P n}.Finite := by
  sorry

end OMA.S_oeis_a114888
