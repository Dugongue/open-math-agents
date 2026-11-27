import Mathlib

/-!
# OEIS A135936: coefficients of Boubaker polynomials

Source: https://oeis.org/A135936
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Row `n` of A135936 lists the coefficients of the Boubaker polynomial `Bₙ(x)` in decreasing powers
(`B₀ = 1`, `B₁ = x`, `B₂ = x² + 2`, `Bₙ = x B_{n-1} - B_{n-2}` for `n ≥ 3`), so
`T(n, m) = [x^(n-2m)] Bₙ`. Conjecture (Baruchel, 2018):
`T(n, m) = (-1)^m (C(n-m, m) - 3 C(n-m-1, m-1))`.

Conventions:
* `n ≥ 1` and `0 ≤ m ≤ n/2`; for `m = 0` the second binomial is `0` (so `T(n, 0) = 1`), which is
  made explicit.
-/

namespace OMA.S_oeis_a135936

open Polynomial

/-- The Boubaker polynomials. -/
noncomputable def B : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | 2 => X ^ 2 + 2
  | n + 3 => X * B (n + 2) - B (n + 1)

/-- The conjectured coefficient formula. -/
theorem main : ∀ n m : ℕ, 1 ≤ n → 2 * m ≤ n →
    (B n).coeff (n - 2 * m) =
      if m = 0 then 1
      else (-1) ^ m * (((n - m).choose m : ℤ) - 3 * ((n - m - 1).choose (m - 1) : ℤ)) := by
  sorry

end OMA.S_oeis_a135936
