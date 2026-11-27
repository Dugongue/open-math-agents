import Mathlib

/-!
# OEIS A176479: `(n+1)` times the little Schröder numbers, a recurrence

Source: https://oeis.org/A176479
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = (n+1) s(n)`, where `s = A001003` are the little Schröder numbers `1, 1, 3, 11, 45, …`.
Conjecture (OEIS entry): `n(n-1) a(n) - 3(2n-1)(n-1) a(n-1) + n(n-2) a(n-2) = 0`.

Conventions:
* `s(0) = 1` and, for `n ≥ 1`, `s(n) = ∑_{k=1}^{n} N(n, k) 2^(k-1)` with the Narayana numbers
  `N(n, k) = C(n, k) C(n, k-1)/n`; computed in `ℚ`. The recurrence is stated for `n ≥ 2`.
-/

namespace OMA.S_oeis_a176479

/-- Little Schröder numbers. -/
def s (n : ℕ) : ℚ :=
  if n = 0 then 1
  else ∑ k ∈ Finset.Icc 1 n, (n.choose k : ℚ) * (n.choose (k - 1) : ℚ) / n * 2 ^ (k - 1)

/-- `a(n) = (n+1) s(n)`. -/
def a (n : ℕ) : ℚ := (n + 1) * s n

/-- The recurrence for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (n : ℚ) * (n - 1) * a n - 3 * (2 * n - 1) * (n - 1) * a (n - 1) + n * (n - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a176479
