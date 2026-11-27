import Mathlib

/-!
# OEIS A101042: every prime is the first prime of some prime pair `(p, p + d)`

Source: https://oeis.org/A101042
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest positive `d` such that the `n`-th prime is the smallest prime `p` for which
`p + d` is also prime. It is conjectured that `a(n)` always exists.

Conventions:
* `prime(n) = Nat.nth Nat.Prime (n - 1)`, `n ≥ 1`.
-/

namespace OMA.S_oeis_a101042

/-- For every `n ≥ 1` there is `d ≥ 1` such that `prime(n)` is the least prime `p` with `p + d`
prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ d : ℕ, 1 ≤ d ∧ (Nat.nth Nat.Prime (n - 1) + d).Prime ∧
    ∀ q : ℕ, q.Prime → q < Nat.nth Nat.Prime (n - 1) → ¬ (q + d).Prime := by
  sorry

end OMA.S_oeis_a101042
