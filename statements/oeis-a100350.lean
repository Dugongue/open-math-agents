import Mathlib

/-!
# A100350: Primes p such that p-2^k is a prime or semiprime for all k > 0 with 2^k < p.

Source: https://oeis.org/A100350
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: this sequence is finite.
-/

namespace OMA.S_oeis_a100350

/-- A natural number is semiprime if it is the product of two (not necessarily distinct) primes. -/
def IsSemiprime (m : ℕ) : Prop :=
  ∃ q r : ℕ, Nat.Prime q ∧ Nat.Prime r ∧ m = q * r

theorem main :
    {p : ℕ | Nat.Prime p ∧
      ∀ k : ℕ, 0 < k → 2 ^ k < p →
        Nat.Prime (p - 2 ^ k) ∨ IsSemiprime (p - 2 ^ k)}.Finite := by
  sorry

end OMA.S_oeis_a100350
