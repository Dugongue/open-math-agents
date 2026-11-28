import Mathlib

/-!
# OEIS A001792: a(n) = (n+2)*2^(n-1)

Source: https://oeis.org/A001792

Conjecture recorded in the entry: with `a(-1) = 0`, `a(n-1) + A098156(n+1) = 2 a(n)`.

Conventions.
- `a n = (n + 2) * 2 ^ n / 2` (exact division, so `a 0 = 1`); `a(-1) = 0` is handled by a case
  split at `n = 0`.
- `A098156` is defined as in its entry: interleave `n + 1` and `2n + 1` (giving
  `1, 1, 2, 3, 3, 5, 4, 7, …`) and take the binomial transform.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a001792

/-- A001792: `a(n) = (n+2) 2^(n-1)`. -/
def a (n : ℕ) : ℕ := (n + 2) * 2 ^ n / 2

/-- Interleaving of `n + 1` and `2n + 1`. -/
def interleave (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 + 1 else 2 * (k / 2) + 1

/-- A098156: binomial transform of the interleaved sequence. -/
def A098156 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * interleave k

theorem main :
    ∀ n : ℕ, (if n = 0 then 0 else a (n - 1)) + A098156 (n + 1) = 2 * a n := by
  sorry

end OMA.S_oeis_a001792
