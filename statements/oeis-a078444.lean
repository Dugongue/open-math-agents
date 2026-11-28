import Mathlib

/-!
# A078444: Floor of geometric mean of two consecutive primes.

Source: https://oeis.org/A078444
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

For n >= 2 these formulas are equivalent to sqrt(prime(n)*prime(n+1)) > (prime(n)+prime(n+1))/2 - 1,
and thus to A001223(n) <= 2 + 2*sqrt(2*prime(n)). This would be implied by Andrica's conjecture,
but is as yet unproven.
-/

namespace OMA.S_oeis_a078444

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      Real.sqrt ((Nat.nth Nat.Prime n : ℝ) * (Nat.nth Nat.Prime (n + 1) : ℝ)) >
        ((Nat.nth Nat.Prime n : ℝ) + (Nat.nth Nat.Prime (n + 1) : ℝ)) / 2 - 1 := by sorry

end OMA.S_oeis_a078444
