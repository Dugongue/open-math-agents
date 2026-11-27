import Mathlib

/-!
# OEIS A127728: sums of squared coefficients of `q`-factorials

Source: https://oeis.org/A127728
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the sum of the squares of the coefficients of the `q`-factorial
`[n]_q! = ∏_{k=1}^{n} (1 + q + ⋯ + q^(k-1))`. Conjecture (OEIS entry):
`a(n) ~ 6 √π n^(2n - 1/2) / e^(2n)`.
-/

namespace OMA.S_oeis_a127728

open Polynomial Filter Asymptotics

/-- The `q`-factorial `[n]_q!`. -/
noncomputable def qfact (n : ℕ) : ℤ[X] := ∏ k ∈ Finset.Icc 1 n, ∑ j ∈ Finset.range k, X ^ j

/-- `a(n)`: sum of squared coefficients. -/
noncomputable def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range ((qfact n).natDegree + 1), (qfact n).coeff i ^ 2

/-- `a(n) ~ 6 √π n^(2n - 1/2) e^(-2n)`. -/
theorem main : IsEquivalent atTop (fun n : ℕ => (a n : ℝ))
    (fun n => 6 * Real.sqrt Real.pi * (n : ℝ) ^ (2 * (n : ℝ) - 1 / 2) / Real.exp (2 * n)) := by
  sorry

end OMA.S_oeis_a127728
