import Mathlib

/-!
# OEIS A011257: geometric mean of `φ(k)` and `σ(k)` an integer

Source: https://oeis.org/A011257
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A011257 lists the `k` such that `√(φ(k) σ(k))` is an integer. Conjecture (OEIS entry): for these
numbers `σ(k)` is never odd.

Conventions:
* The first term `k = 1` (`φ(1) σ(1) = 1`, `σ(1) = 1`) is the trivial exception, so `main` is
  stated for `k ≥ 2`.
-/

namespace OMA.S_oeis_a011257

open ArithmeticFunction

/-- If `k ≥ 2` and `φ(k) σ(k)` is a perfect square, then `σ(k)` is even. -/
theorem main : ∀ k : ℕ, 2 ≤ k → IsSquare (Nat.totient k * ArithmeticFunction.sigma 1 k) → Even (ArithmeticFunction.sigma 1 k) := by
  sorry

end OMA.S_oeis_a011257
