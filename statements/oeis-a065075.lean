import Mathlib

/-!
# OEIS A065075: digit sums of partial sums

Source: https://oeis.org/A065075
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 1` and `a(n)` is the sum of the digits of `a(1) + ⋯ + a(n-1)`. Conjecture
(Adams-Watters, 2009): every positive non-multiple of `3` appears in the sequence.

Conventions:
* Indexing from `0`: `a 0 = 1`, `a (n+1) = s₁₀(a 0 + ⋯ + a n)`.
-/

namespace OMA.S_oeis_a065075

/-- The sequence together with its partial sums: `step n = (a n, a 0 + ⋯ + a n)`. -/
def step : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 =>
    let s := (step n).2
    let t := (Nat.digits 10 s).sum
    (t, s + t)

/-- `a n`. -/
def a (n : ℕ) : ℕ := (step n).1

/-- Every positive integer not divisible by `3` occurs. -/
theorem main : ∀ m : ℕ, 1 ≤ m → ¬ 3 ∣ m → ∃ n, a n = m := by
  sorry

end OMA.S_oeis_a065075
