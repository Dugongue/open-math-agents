import Mathlib

/-!
# A107740: Number of numbers m such that prime(n) = m + (digit sum of m).

Source: https://oeis.org/A107740
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

a(n) <= 2 for n <= 10^5. Conjecture: sequence is bounded.
-/

namespace OMA.S_oeis_a107740

/-- Number of natural numbers `m` such that `m + digitSum(m) = p`. -/
def selfCount (p : ℕ) : ℕ :=
  ((Finset.Icc 0 p).filter (fun m => m + (Nat.digits 10 m).sum = p)).card

theorem main :
    ∃ B : ℕ, ∀ p : ℕ, p.Prime → selfCount p ≤ B := by
  sorry

end OMA.S_oeis_a107740
