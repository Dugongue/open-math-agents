import Mathlib

/-!
# OEIS A097945: `∑ μ(n)/φ(n) = 0`

Source: https://oeis.org/A097945
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = μ(n) φ(n)`. Conjecture (OEIS entry): `∑_{n ≥ 1} μ(n)/φ(n) = ∑_{n ≥ 1} a(n)/φ(n)² = 0`.

Conventions:
* The series is not absolutely convergent; it is read as the limit of its partial sums
  `∑_{n=1}^{N} μ(n)/φ(n)` as `N → ∞` (the two series in the source are termwise equal).
-/

namespace OMA.S_oeis_a097945

open Filter Topology

/-- The partial sums of `∑ μ(n)/φ(n)` tend to `0`. -/
theorem main : Tendsto (fun N : ℕ =>
    ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) / Nat.totient n) atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a097945
