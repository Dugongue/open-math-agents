import Mathlib

/-!
# OEIS A180247: prime Brier numbers have more than 11 digits

Source: https://oeis.org/A180247
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Prime Brier numbers are primes `p` such that `p 2^k + 1` and `p 2^k - 1` are composite for all
`k ≥ 1`. The entry records the conjecture that every such number has more than `11` digits; `main`
states that there is no prime Brier number below `10^11`.
-/

namespace OMA.S_oeis_a180247

/-- For every prime `p < 10^11` some `p 2^k ± 1` (`k ≥ 1`) is prime. -/
theorem main : ∀ p : ℕ, p.Prime → p < 10 ^ 11 →
    ∃ k : ℕ, 1 ≤ k ∧ ((p * 2 ^ k + 1).Prime ∨ (p * 2 ^ k - 1).Prime) := by
  sorry

end OMA.S_oeis_a180247
