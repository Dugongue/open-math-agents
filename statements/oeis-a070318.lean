import Mathlib

/-!
# OEIS A070318: running maximum of aliquot sums

Source: https://oeis.org/A070318
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = max_{k ≤ n} (σ(k) - k)`. Conjecture (OEIS entry):
`lim_{n → ∞} (1/(n² log log n)) ∑_{i=1}^{n} a(i) = C = 0.7…`.

Conventions:
* `C = 0.7…` is read as `0.7 ≤ C < 0.8`.
-/

namespace OMA.S_oeis_a070318

open Filter Topology ArithmeticFunction

/-- `a(n) = max_{1 ≤ k ≤ n} (σ(k) - k)`. -/
def a (n : ℕ) : ℕ := (Finset.Icc 1 n).sup fun k => ArithmeticFunction.sigma 1 k - k

/-- The normalised partial sums converge to some `C ∈ [0.7, 0.8)`. -/
theorem main : ∃ C : ℝ, 0.7 ≤ C ∧ C < 0.8 ∧
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.Icc 1 n, (a i : ℝ)) / ((n : ℝ) ^ 2 * Real.log (Real.log n)))
      atTop (𝓝 C) := by
  sorry

end OMA.S_oeis_a070318
