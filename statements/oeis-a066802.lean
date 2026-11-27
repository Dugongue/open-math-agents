import Mathlib

/-!
# OEIS A066802: `C(6n, 3n)` as a coefficient of a power of an algebraic series

Source: https://oeis.org/A066802
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n) = C(6n, 3n)`. Conjecture (OEIS entry): `a(n) = [xⁿ] G(x)^(2n)`, where
`G(x) = 1 + 10x + 81x² + 720x³ + ⋯` is the algebraic function with
`x G² - (1 - 5x - 5x² + x³) G + (1 + x)⁴ = 0`.

Conventions:
* `G` is the power series in `ℤ⟦x⟧` with constant term `1` satisfying the quadratic equation (the
  equation determines its coefficients one by one); `main` quantifies over every such `G`.
-/

namespace OMA.S_oeis_a066802

open PowerSeries

/-- `C(6n, 3n) = [xⁿ] G^(2n)`. -/
theorem main : ∀ G : PowerSeries ℤ, constantCoeff G = 1 →
    X * G ^ 2 - (1 - 5 * X - 5 * X ^ 2 + X ^ 3) * G + (1 + X) ^ 4 = 0 →
    ∀ n : ℕ, ((6 * n).choose (3 * n) : ℤ) = coeff n (G ^ (2 * n)) := by
  sorry

end OMA.S_oeis_a066802
