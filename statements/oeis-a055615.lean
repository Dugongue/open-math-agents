import Mathlib

/-!
# OEIS A055615: Abel summation of `n μ(n)`

Source: https://oeis.org/A055615
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = n μ(n)`. Conjectures (OEIS entry): `lim_{b → 1⁺} ∑_{n ≥ 1} a(n) b^(-n) = -12` and
`lim_{b → 1⁻} ∑_{n ≥ 1} a(n) bⁿ = -12` (consistent with `1/ζ(-1) = -12`).

Conventions:
* For `0 < x < 1` the series `∑ n μ(n) xⁿ` converges absolutely; the sums are `tsum`s and the
  limits are one-sided (`𝓝[>] 1`, `𝓝[<] 1`). The first limit uses `b > 1`, `x = b⁻¹`.
-/

namespace OMA.S_oeis_a055615

open Filter Topology ArithmeticFunction

/-- Both Abel limits equal `-12`. -/
theorem main :
    Tendsto (fun b : ℝ => ∑' n : ℕ, (n : ℝ) * (ArithmeticFunction.moebius n : ℝ) * b ^ (-(n : ℤ))) (𝓝[>] 1) (𝓝 (-12)) ∧
    Tendsto (fun b : ℝ => ∑' n : ℕ, (n : ℝ) * (ArithmeticFunction.moebius n : ℝ) * b ^ n) (𝓝[<] 1) (𝓝 (-12)) := by
  sorry

end OMA.S_oeis_a055615
