import Mathlib

/-!
# A093538: Number of primes between 10^n and 10^n+100.

Source: https://oeis.org/A093538
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: a(n) = 1 for infinitely many n, but a(n)>=2 for only finitely many;
in fact it may be that a(n)<=1 for n > 775.
-/

namespace OMA.S_oeis_a093538

/-- Number of primes in the interval `[10^n, 10^n + 100]`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc (10 ^ n) (10 ^ n + 100)).filter Nat.Prime).card

theorem main :
    {n : ℕ | a n = 1}.Infinite ∧ {n : ℕ | 2 ≤ a n}.Finite := by
  sorry

end OMA.S_oeis_a093538
