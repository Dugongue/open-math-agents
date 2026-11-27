import Mathlib

/-!
# OEIS A004402: `1/θ₃` evaluated at the nome `e^(-π)`

Source: https://oeis.org/A004402
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`∑ a(n) xⁿ = 1 / ∑_{n ∈ ℤ} x^(n²)`. Conjecture (OEIS entry):
`∑_{k ≥ 0} a(k)/e^(kπ) = Γ(3/4)/π^(1/4)`.

Conventions:
* `θ₃(x) = ∑_{n ∈ ℤ} x^(n²) = 1 + 2 ∑_{n ≥ 1} x^(n²)` in `ℤ⟦x⟧` has constant term `1`, so its
  inverse is a power series with integer coefficients `a(k)`. The series is read as `HasSum`.
-/

namespace OMA.S_oeis_a004402

open Classical

open PowerSeries

/-- `θ₃(x) = 1 + 2 ∑_{n ≥ 1} x^(n²)`. -/
noncomputable def theta3 : PowerSeries ℤ :=
  PowerSeries.mk fun m =>
    if m = 0 then 1 else if ∃ n ∈ Finset.range (m + 1), n ^ 2 = m then 2 else 0

/-- `a(k) = [x^k] (1/θ₃)`. -/
noncomputable def a (k : ℕ) : ℤ := coeff k (invOfUnit theta3 1)

/-- `∑ a(k) e^(-kπ) = Γ(3/4)/π^(1/4)`. -/
theorem main : HasSum (fun k : ℕ => (a k : ℝ) * Real.exp (-(k : ℝ) * Real.pi))
    (Real.Gamma (3 / 4) / Real.pi ^ ((1 : ℝ) / 4)) := by
  sorry

end OMA.S_oeis_a004402
