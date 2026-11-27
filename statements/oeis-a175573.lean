import Mathlib

/-!
# OEIS A175573: `π^(1/4)/Γ(3/4)` as a theta value

Source: https://oeis.org/A175573
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (OEIS entry): `π^(1/4)/Γ(3/4) = ∑_{k ≥ 0} A000122(k)/e^(kπ)`, where A000122(k) is the
number of integers `x` with `x² = k` (the coefficients of `θ₃(q) = ∑_{x ∈ ℤ} q^(x²)`).

Conventions:
* `A000122(k) = #{x ∈ ℤ | x² = k}` (`1` for `k = 0`, `2` for positive squares, else `0`); the series
  is read as `HasSum`.
-/

namespace OMA.S_oeis_a175573

/-- `A000122(k)`. -/
def r (k : ℕ) : ℕ := if k = 0 then 1 else if IsSquare k then 2 else 0

/-- `∑ r(k) e^(-kπ) = π^(1/4)/Γ(3/4)`. -/
theorem main : HasSum (fun k : ℕ => (r k : ℝ) * Real.exp (-(k : ℝ) * Real.pi))
    (Real.pi ^ ((1 : ℝ) / 4) / Real.Gamma (3 / 4)) := by
  sorry

end OMA.S_oeis_a175573
