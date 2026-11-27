import Mathlib

/-!
# OEIS A086685: primes `in + 1` with `i < n`

Source: https://oeis.org/A086685
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `1 ≤ i < n` such that `i n + 1` is prime (the number of primes `p < n²`
with `p ≡ 1 (mod n)`). The standard conjecture recorded in the entry is
`a(n) ~ n²/(2 φ(n) log n)`.
-/

namespace OMA.S_oeis_a086685

open Filter Asymptotics

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := ((Finset.Ioo 0 n).filter fun i => (i * n + 1).Prime).card

/-- `a(n) ~ n²/(2 φ(n) log n)`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
    (fun n => (n : ℝ) ^ 2 / (2 * Nat.totient n * Real.log n)) := by
  sorry

end OMA.S_oeis_a086685
