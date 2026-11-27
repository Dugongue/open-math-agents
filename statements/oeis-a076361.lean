import Mathlib

/-!
# OEIS A076361: `d(σ(k)) = σ(d(k))`

Source: https://oeis.org/A076361
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A076361 lists the `k` with `d(σ(k)) = σ(d(k))` (`d` = number of divisors). The entry notes that
Schinzel's hypothesis implies the sequence is infinite; `main` states that it is infinite.
-/

namespace OMA.S_oeis_a076361

open ArithmeticFunction

/-- Infinitely many `k` satisfy `d(σ(k)) = σ(d(k))`. -/
theorem main : {k : ℕ | 1 ≤ k ∧ ArithmeticFunction.sigma 0 (ArithmeticFunction.sigma 1 k) = ArithmeticFunction.sigma 1 (ArithmeticFunction.sigma 0 k)}.Infinite := by
  sorry

end OMA.S_oeis_a076361
