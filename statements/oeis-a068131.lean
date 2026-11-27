import Mathlib

/-!
# OEIS A068131: triangular numbers with prescribed digit sum

Source: https://oeis.org/A068131
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A068131 lists the triangular numbers with digit sum `21`. Conjecture (OEIS entry): for every
triangular number `T` there exist infinitely many triangular numbers with digit sum `T`.

Conventions:
* Triangular numbers are `m(m+1)/2`; `T` ranges over positive triangular numbers (digit sum `0`
  only occurs for `0`).
-/

namespace OMA.S_oeis_a068131

/-- For every positive triangular `T`, infinitely many triangular numbers have digit sum `T`. -/
theorem main : ∀ t : ℕ, 1 ≤ t →
    {m : ℕ | (Nat.digits 10 (m * (m + 1) / 2)).sum = t * (t + 1) / 2}.Infinite := by
  sorry

end OMA.S_oeis_a068131
