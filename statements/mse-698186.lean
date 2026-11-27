import Mathlib

/-!
# A conjecture related to the Erdős discrepancy problem

Source: https://math.stackexchange.com/questions/698186
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (asker): if `k ∈ ℕ` and `S` is an infinite set of primes, then the completely
multiplicative `±1`-sequence `f` with `f(p) = -1` for `p ∈ S` and `f(p) = 1` for all other primes
contains `k` consecutive `+1`s infinitely often: there are infinitely many `x₀` with `f(x) = 1`
for all `x ∈ {x₀, …, x₀ + k - 1}`.

Conventions:
* `f(n) = (-1)^(number of prime factors of n in S, with multiplicity)` for `n ≥ 1`; starting
  points `x₀ ≥ 1`.
-/

namespace OMA.S_mse_698186

open Classical

/-- The completely multiplicative `±1` function determined by `S`. -/
noncomputable def f (S : Set ℕ) (n : ℕ) : ℤ :=
  (-1) ^ (n.primeFactorsList.filter fun p => decide (p ∈ S)).length

/-- `+1` blocks of every length occur infinitely often. -/
theorem main : ∀ (S : Set ℕ), (∀ p ∈ S, p.Prime) → S.Infinite → ∀ k : ℕ,
    {x₀ : ℕ | 1 ≤ x₀ ∧ ∀ j < k, f S (x₀ + j) = 1}.Infinite := by
  sorry

end OMA.S_mse_698186
