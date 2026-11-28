import Mathlib

/-!
# A101478: G.f. satisfies A(x) = x*(1+A(x))^4/(1+A(x)^2).

Source: https://oeis.org/A101478
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: `n*(n-1)*(n+1)*a(n) - 12*n*(n-1)*(2*n-3)*a(n-1)
+ 12*(n-1)*(16*n^2-64*n+65)*a(n-2) - 16*(2*n-5)*(4*n-9)*(4*n-11)*a(n-3) = 0` for `n >= 4`.
-/

namespace OMA.S_oeis_a101478

theorem main :
    ∀ A : PowerSeries ℤ,
      PowerSeries.constantCoeff A = 0 →
      A * (1 + A ^ 2) = PowerSeries.X * (1 + A) ^ 4 →
      ∀ n : ℕ, 4 ≤ n →
        let a : ℕ → ℤ := fun k => PowerSeries.coeff k A
        (n : ℤ) * (n - 1) * (n + 1) * a n
          - 12 * (n : ℤ) * (n - 1) * (2 * n - 3) * a (n - 1)
          + 12 * ((n : ℤ) - 1) * (16 * (n : ℤ) ^ 2 - 64 * n + 65) * a (n - 2)
          - 16 * (2 * (n : ℤ) - 5) * (4 * n - 9) * (4 * n - 11) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a101478
