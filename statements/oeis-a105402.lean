import Mathlib

/-!
# OEIS A105402: prime factors of `σ(k)` among those of `k`

Source: https://oeis.org/A105402
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A105402 lists the positive integers `k` such that the prime factors of `σ(k)` are a subset of the
prime factors of `k`. Pomerance has conjectured that all terms after the initial `1` are even.
-/

namespace OMA.S_oeis_a105402

/-- If `k > 1` and every prime factor of `σ(k)` divides `k`, then `k` is even. -/
theorem main : ∀ k : ℕ, 1 < k →
    (ArithmeticFunction.sigma 1 k).primeFactors ⊆ k.primeFactors → Even k := by
  sorry

end OMA.S_oeis_a105402
