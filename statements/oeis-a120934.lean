import Mathlib

/-!
# A120934: Least prime p such that the interval [p, p + log(p)] contains n primes

Source: https://oeis.org/A120934
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: For every positive integer `n`, there exists a prime `p` such that the closed
interval `[p, p + log p]` contains `n` primes (so `a(n)` exists for all `n ≥ 1`).
-/

namespace OMA.S_oeis_a120934

/-- Number of primes in the interval `[p, p + log p]`. -/
noncomputable def primesInLogInterval (p : ℕ) : ℕ :=
  ((Finset.Icc p (p + Nat.floor (Real.log (p : ℝ)))).filter Nat.Prime).card

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ primesInLogInterval p = n := by
  sorry

end OMA.S_oeis_a120934
