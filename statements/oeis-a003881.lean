import Mathlib

/-!
# OEIS A003881: `π/4` as a limit of ratios of Springer numbers

Source: https://oeis.org/A003881
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (OEIS entry): `π/4 = lim_{n → ∞} n · S(n-1) / S(n)`, where `S = A001586` are the
Springer numbers `1, 1, 3, 11, 57, 361, …`.

Conventions:
* The Springer numbers are defined by their exponential generating function
  `∑ S(n) xⁿ/n! = 1/(cos x - sin x)` (A001586), computed in `ℚ⟦x⟧` with Mathlib's
  `PowerSeries.cos`/`PowerSeries.sin`; `cos - sin` has constant term `1`, so it is invertible.
-/

namespace OMA.S_oeis_a003881

open PowerSeries Filter Topology

/-- The e.g.f. `1/(cos x - sin x)`. -/
noncomputable def egf : PowerSeries ℚ := invOfUnit (PowerSeries.cos ℚ - PowerSeries.sin ℚ) 1

/-- Springer numbers `S(n) = n! [xⁿ] egf`. -/
noncomputable def S (n : ℕ) : ℚ := n.factorial * coeff n egf

/-- `n S(n-1)/S(n) → π/4`. -/
theorem main :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (S n : ℝ) / (S (n + 1) : ℝ)) atTop
      (𝓝 (Real.pi / 4)) := by
  sorry

end OMA.S_oeis_a003881
