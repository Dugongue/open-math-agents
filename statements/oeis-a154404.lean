import Mathlib

/-!
# A154404: Sum of an odd prime, a positive Fibonacci number, and a Catalan number

Source: https://oeis.org/A154404
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (2009, cited in the entry): Every integer `n ≥ 5` can be expressed as
the sum of an odd prime `p`, a positive Fibonacci number `F_k` (`k ≥ 1`), and a Catalan
number `C_m = choose(2m, m) / (m + 1)` (`m ≥ 0`).
-/

namespace OMA.S_oeis_a154404

/-- The `m`-th Catalan number `C_m = choose(2m, m) / (m + 1)`. -/
def catalanNum (m : ℕ) : ℕ :=
  Nat.choose (2 * m) m / (m + 1)

theorem main :
    ∀ n : ℕ, 5 ≤ n →
      ∃ p k m : ℕ, Nat.Prime p ∧ Odd p ∧ 1 ≤ k ∧
        n = p + Nat.fib k + catalanNum m := by
  sorry

end OMA.S_oeis_a154404
