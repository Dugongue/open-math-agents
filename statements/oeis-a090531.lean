import Mathlib

/-!
# OEIS A090531: multiples of `n!` between twin primes

Source: https://oeis.org/A090531
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the least multiple of `n!` sandwiched between twin primes, or `0` if none exists.
Conjecture (OEIS entry; implied by Dickson's conjecture): no term is zero.
-/

namespace OMA.S_oeis_a090531

/-- For every `n` some positive multiple `m` of `n!` has `m - 1` and `m + 1` prime. -/
theorem main : ∀ n : ℕ, ∃ m : ℕ, 1 ≤ m ∧ n.factorial ∣ m ∧ (m - 1).Prime ∧ (m + 1).Prime := by
  sorry

end OMA.S_oeis_a090531
