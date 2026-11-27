import Mathlib

/-!
# OEIS A103783: primes `P(k)·n - 1` with small `n`

Source: https://oeis.org/A103783
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A103783 lists the primes of the form `P(k) n - 1` with minimal `n > 0` (`P(k)` the `k`-th
primorial, `k ≥ 2`). Conjectures (OEIS entry): (weak) the sequence is defined for all `k ≥ 2`;
(strong) the minimal `n` satisfies `n < prime(k)²`.

Conventions:
* `P(k) = prime(1) ⋯ prime(k)` with `prime(i) = Nat.nth Nat.Prime (i - 1)`. The strong form
  implies the weak one; `main` states the strong form.
-/

namespace OMA.S_oeis_a103783

/-- The `k`-th primorial. -/
noncomputable def P (k : ℕ) : ℕ := ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i

/-- For `k ≥ 2` some `1 ≤ n < prime(k)²` makes `P(k) n - 1` prime. -/
theorem main : ∀ k : ℕ, 2 ≤ k →
    ∃ n : ℕ, 1 ≤ n ∧ n < Nat.nth Nat.Prime (k - 1) ^ 2 ∧ (P k * n - 1).Prime := by
  sorry

end OMA.S_oeis_a103783
