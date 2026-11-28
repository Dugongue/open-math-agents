import Mathlib

/-!
# A099468: Numbers n such that there are no primes < 2n in the sequence m(0)=n, m(k+1)=m(k)+4k.

Source: https://oeis.org/A099468
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

No others < 10^8. This sequence is conjectured to be complete.
-/

namespace OMA.S_oeis_a099468

/-- The sequence `m(0) = n`, `m(k + 1) = m(k) + 4 * k`. -/
def seq (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => seq n k + 4 * k

theorem main :
    ∀ n : ℕ, 10 ^ 8 ≤ n → ∃ k : ℕ, seq n k < 2 * n ∧ Nat.Prime (seq n k) := by
  sorry

end OMA.S_oeis_a099468
