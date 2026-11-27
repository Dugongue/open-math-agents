import Mathlib

/-!
# OEIS A154421: odd prime plus Fibonacci plus even Lucas number

Source: https://oeis.org/A154421
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of ways to write `n` as an odd prime plus a positive Fibonacci number plus an
even Lucas number. Conjecture (Sun, 2009): every integer `n > 5` can be written as
`p + F_s + L_{3t}` with `p` an odd prime, `s ≥ 1` and `t ≥ 0`.

Conventions:
* `F_s` is `Nat.fib s`; Lucas numbers `L_0 = 2`, `L_1 = 1`, `L_{m+2} = L_{m+1} + L_m` (the even
  ones are exactly `L_{3t}`).
-/

namespace OMA.S_oeis_a154421

/-- Lucas numbers. -/
def L : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | m + 2 => L (m + 1) + L m

/-- Every `n > 5` is `p + F_s + L_{3t}`. -/
theorem main : ∀ n : ℕ, 5 < n →
    ∃ p s t : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ s ∧ n = p + Nat.fib s + L (3 * t) := by
  sorry

end OMA.S_oeis_a154421
