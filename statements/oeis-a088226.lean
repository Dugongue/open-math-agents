import Mathlib

/-!
# OEIS A088226: `a(n) = |a(n-1) - a(n-2) - a(n-3)|` and distances to squares

Source: https://oeis.org/A088226
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(1) = 0, a(2) = 0, a(3) = 1`, and `a(n) = |a(n-1) - a(n-2) - a(n-3)|` for `n > 3`. Conjecture
(OEIS entry): `a(n) = m/2`, where `m` is the smallest even distance from `n` to a square.

Conventions:
* The formula matches the terms when they are indexed from `0` (`a(0) = a(1) = 0`, `a(2) = 1`,
  `a(3) = 1`, `a(4) = 0`, `a(5) = 2`, …), which is how `a` is defined below; e.g. `a(4) = 0` since
  `4` is a square. The even distances from `n` to squares are the even values of `|n - s²|`,
  `s ≥ 0`; one is even for `s ≡ n (mod 2)`, so the minimum exists.
-/

namespace OMA.S_oeis_a088226

/-- The sequence. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => |a (n + 2) - a (n + 1) - a n|

/-- Smallest even distance from `n` to a square. -/
noncomputable def m (n : ℕ) : ℕ := sInf {d : ℕ | Even d ∧ ∃ s : ℕ, (Int.natAbs ((n : ℤ) - s ^ 2)) = d}

/-- `a(n) = m(n)/2` for all `n`. -/
theorem main : ∀ n : ℕ, a n = (m n / 2 : ℕ) := by
  sorry

end OMA.S_oeis_a088226
