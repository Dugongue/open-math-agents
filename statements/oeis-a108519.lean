import Mathlib

/-!
# A108519: a(n) is the smallest natural number m such that (10^n)! - m is prime.

Source: https://oeis.org/A108519
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

If a(n) is composite then a(n) > 10^(2n) + 2*10^n.
Conjecture: All terms are noncomposite numbers.
-/

namespace OMA.S_oeis_a108519

/-- Smallest positive integer `m` such that `(10^n)! - m` is prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ m < Nat.factorial (10 ^ n) ∧ (Nat.factorial (10 ^ n) - m).Prime}

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a108519
