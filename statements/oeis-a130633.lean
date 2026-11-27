import Mathlib

/-!
# OEIS A130633: additive persistence of Fibonacci numbers

Source: https://oeis.org/A130633
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the additive persistence of `F(n)` (the number of digit-sum steps needed to reach a
single digit). Conjecture (OEIS entry): `a(n) > 1` for `n > 15`.

Conventions:
* `a(n) > 1` means that the decimal digit sum of `F(n)` is not a single digit, i.e. it is `≥ 10`.
-/

namespace OMA.S_oeis_a130633

/-- For `n > 15`, the digit sum of `F(n)` is at least `10`. -/
theorem main : ∀ n : ℕ, 15 < n → 10 ≤ (Nat.digits 10 (Nat.fib n)).sum := by
  sorry

end OMA.S_oeis_a130633
