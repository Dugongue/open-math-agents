import Mathlib

/-!
# OEIS A108518: least `m` with `(10ⁿ)! + m` prime

Source: https://oeis.org/A108518
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest natural number `m` such that `(10ⁿ)! + m` is prime. Conjecture (OEIS entry):
all terms are noncomposite (`1` or prime).
-/

namespace OMA.S_oeis_a108518

/-- `a(n)`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | ((10 ^ n).factorial + m).Prime}

/-- Every `a(n)` is `1` or prime. -/
theorem main : ∀ n : ℕ, a n = 1 ∨ (a n).Prime := by
  sorry

end OMA.S_oeis_a108518
