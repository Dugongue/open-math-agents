import Mathlib

/-!
# OEIS A054030: abundancies of multiply perfect numbers

Source: https://oeis.org/A054030
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A054030 lists `σ(k)/k` for the `k` with `k ∣ σ(k)`. Conjecture (OEIS entry): every value except
`2` appears only finitely many times, i.e. for every integer `m ≠ 2` there are only finitely many
`k` with `σ(k) = m k`.
-/

namespace OMA.S_oeis_a054030

open ArithmeticFunction

/-- For `m ≠ 2`, only finitely many `k ≥ 1` have abundancy `m`. -/
theorem main : ∀ m : ℕ, m ≠ 2 → {k : ℕ | 1 ≤ k ∧ ArithmeticFunction.sigma 1 k = m * k}.Finite := by
  sorry

end OMA.S_oeis_a054030
