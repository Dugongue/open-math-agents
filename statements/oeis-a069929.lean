import Mathlib

/-!
# OEIS A069929: divisors of `n³ + 1` of the form `k³ + 1`

Source: https://oeis.org/A069929
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of `k`, `1 ≤ k ≤ n`, with `k³ + 1 ∣ n³ + 1`. Conjecture (OEIS entry):
`(1/n) ∑_{k=1}^{n} a(k) = C log log n + o(log log n)` with `1 < C < 3/2`.
-/

namespace OMA.S_oeis_a069929

open Filter Asymptotics

/-- `a(n)`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => k ^ 3 + 1 ∣ n ^ 3 + 1).card

/-- The mean of `a` grows like `C log log n` with `1 < C < 3/2`. -/
theorem main : ∃ C : ℝ, 1 < C ∧ C < 3 / 2 ∧
    (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (a k : ℝ)) / n - C * Real.log (Real.log n)) =o[atTop]
      fun n => Real.log (Real.log n) := by
  sorry

end OMA.S_oeis_a069929
